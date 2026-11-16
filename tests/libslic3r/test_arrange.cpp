#include <algorithm>
#include <catch2/catch_all.hpp>
#include "libslic3r/libslic3r.h"
#include "libslic3r/Polygon.hpp"
#include "libslic3r/Point.hpp"
#include <string>
#include "libslic3r/Config.hpp"
#include <vector>
#include <limits>
#include <cstddef>
#include <cmath>
#include <utility>

#include <catch2/matchers/catch_matchers_floating_point.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/catch_message.hpp>
#include "libslic3r/Arrange.hpp"
#include "libslic3r/BoundingBox.hpp"
#include "libslic3r/ClipperUtils.hpp"
#include "libslic3r/ExPolygon.hpp"
#include "libslic3r/Print.hpp"
#include "libslic3r/PrintConfig.hpp"
#include "libslic3r/MultiMaterialSegmentation.hpp"
#include "libslic3r/Model.hpp"
#include "libslic3r/ModelArrange.hpp"
#include "libslic3r/TriangleMesh.hpp"

using namespace Slic3r;
using namespace Slic3r::arrangement;

namespace {

using Catch::Matchers::WithinRel;

// Square of the given (scaled) side, lower-left at the origin. bed_idx starts at
// 0 because arrange() seeds the nester's bin from it (see ModelArrange.cpp).
ArrangePolygon make_square(coord_t side)
{
    ArrangePolygon ap;
    Polygon        p;
    p.points = {Point(0, 0), Point(side, 0), Point(side, side), Point(0, side)};
    ap.poly  = ExPolygon(p);
    ap.bed_idx = 0;
    return ap;
}

ArrangePolygons squares(int n, double side_mm, double height_mm = 0.)
{
    ArrangePolygons items;
    for (int i = 0; i < n; ++i) {
        items.emplace_back(make_square(scaled(side_mm)));
        items.back().height = height_mm;
    }
    return items;
}

// 64-gon disc of the given diameter, centred on the origin.
ArrangePolygon make_disc(double diameter_mm, double height_mm)
{
    Polygon p;
    for (int i = 0; i < 64; ++i) {
        const double a = 2. * PI * i / 64;
        p.points.emplace_back(scaled(diameter_mm / 2 * std::cos(a)), scaled(diameter_mm / 2 * std::sin(a)));
    }
    ArrangePolygon ap;
    ap.poly    = ExPolygon(p);
    ap.bed_idx = 0;
    ap.height  = height_mm;
    return ap;
}

// Bed [0,0]..[w,h] in scaled coordinates.
BoundingBox bed(double w_mm, double h_mm)
{
    return BoundingBox(Point(0, 0), Point(scaled(w_mm), scaled(h_mm)));
}

// The default progress callback prints to stdout; silence it.
ArrangeParams quiet_params(coord_t min_dist = 0)
{
    ArrangeParams p{min_dist};
    p.progressind = [](unsigned, std::string) {};
    return p;
}

ExPolygons placed_shapes(const ArrangePolygons &items)
{
    ExPolygons out;
    out.reserve(items.size());
    for (const ArrangePolygon &ap : items)
        out.emplace_back(ap.transformed_poly());
    return out;
}

// Area double-counted across the shapes: the sum counts overlaps twice, the
// union once, so the difference is the overlapping area (0 when disjoint).
double overlap_area(const ExPolygons &shapes)
{
    double sum = 0;
    for (const ExPolygon &e : shapes)
        sum += e.area();
    double uni = 0;
    for (const ExPolygon &e : union_ex(shapes))
        uni += e.area();
    return sum - uni;
}

// Relative tolerance absorbs the area-unit rounding the clipper union introduces.
bool disjoint(const ExPolygons &shapes)
{
    double total = 0;
    for (const ExPolygon &e : shapes)
        total += e.area();
    return overlap_area(shapes) <= total * 1e-9;
}

void require_no_overlap(const ArrangePolygons &items)
{
    REQUIRE(disjoint(placed_shapes(items)));
}

// The sequential-print floor is chosen by comparing object height against the nozzle,
// so the two are defined together and every expectation is derived from them.
constexpr double NOZZLE_HEIGHT_MM = 2.5;
constexpr double CLEARANCE_MM     = 30.;
constexpr double NOZZLE_FLOOR_MM  = MAX_OUTER_NOZZLE_DIAMETER;

ArrangeParams seq_print_params(coord_t min_dist)
{
    ArrangeParams p       = quiet_params(min_dist);
    p.is_seq_print        = true;
    p.clearance_radius    = float(CLEARANCE_MM);
    p.nozzle_height       = float(NOZZLE_HEIGHT_MM);
    p.object_skirt_offset = 0.f;
    return p;
}

// update_selected_items_inflation reads the bed out of the config to cap inflation.
DynamicPrintConfig bed_config()
{
    DynamicPrintConfig c;
    c.set_key_value("printable_area", new ConfigOptionPoints{{0, 0}, {200, 0}, {200, 200}, {0, 200}});
    return c;
}

ArrangePolygons squares_of_heights(const std::vector<double> &heights_mm)
{
    ArrangePolygons items;
    for (double height_mm : heights_mm)
        items.push_back(squares(1, 20., height_mm).front());
    return items;
}

// Arranges as the arrange job does for a sequential print, on the bed_config() bed.
void arrange_by_object(ArrangePolygons &items, ArrangePolygons &fixed)
{
    DynamicPrintConfig cfg = bed_config();
    ArrangeParams      p   = seq_print_params(0);
    p.bed_shrink_x         = BED_SHRINK_SEQ_PRINT;
    p.bed_shrink_y         = BED_SHRINK_SEQ_PRINT;
    // Rod and lid above the objects, so they need not each go to a bed of their own.
    p.clearance_height_to_rod = float(NOZZLE_HEIGHT_MM * 10);
    p.clearance_height_to_lid = float(NOZZLE_HEIGHT_MM * 40);
    for (ArrangePolygon &ap : items)
        ap.extrude_ids = {1}; // the sequential sort reads extrude_ids.front()

    update_arrange_params(p, &cfg, items);
    update_selected_items_inflation(items, &cfg, p);
    update_unselected_items_inflation(fixed, &cfg, p);
    arrange(items, fixed, get_shrink_bedpts(&cfg, p), p);
}

} // namespace

// Prove the overlap check the other tests rely on actually detects overlap.
TEST_CASE("overlap_area detects overlap and ignores touching edges", "[Arrange]")
{
    auto square_at = [](double x_mm) {
        ArrangePolygon ap = make_square(scaled(20.));
        ap.translation    = Vec2crd(scaled(x_mm), 0);
        return ap.transformed_poly();
    };
    ExPolygon a = square_at(0.);

    SECTION("disjoint shapes are reported disjoint") {
        REQUIRE(disjoint({a, square_at(30.)}));
    }
    SECTION("edge-touching shapes are reported disjoint") {
        REQUIRE(disjoint({a, square_at(20.)}));
    }
    SECTION("overlapping shapes are not, and the area is measured") {
        REQUIRE_FALSE(disjoint({a, square_at(10.)}));
        REQUIRE_THAT(overlap_area({a, square_at(10.)}),
                     WithinRel(double(scaled(10.)) * scaled(20.), 1e-9)); // 10x20 mm
    }
}

TEST_CASE("Arrange places every item on the physical bed", "[Arrange]")
{
    ArrangePolygons items = squares(5, 20.);
    arrange(items, bed(200, 200), quiet_params(scaled(1.)));

    for (const ArrangePolygon &ap : items)
        REQUIRE(ap.bed_idx == 0);
}

TEST_CASE("Arranged items stay within the bed", "[Arrange]")
{
    ArrangePolygons items = squares(6, 30.);
    arrange(items, bed(200, 200), quiet_params(scaled(1.)));

    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        REQUIRE(bed(200, 200).contains(ap.transformed_poly().contour.bounding_box()));
    }
}

TEST_CASE("Arranged items do not overlap", "[Arrange]")
{
    ArrangePolygons items = squares(6, 40.);
    arrange(items, bed(250, 250), quiet_params(scaled(2.)));

    require_no_overlap(items);
}

TEST_CASE("Arrange spaces items by their inflation", "[Arrange]")
{
    // Per-item inflation is how the arranger enforces clearance (the GUI fills it
    // from min_obj_distance). Two items inflated 4mm each end up >= 8mm apart.
    ArrangePolygons items = squares(4, 20.);
    for (ArrangePolygon &ap : items)
        ap.inflation = scaled(4.);
    arrange(items, bed(200, 200), quiet_params());

    // Axis-aligned squares are their own bounding boxes, so the clearance between
    // a pair is the distance between their boxes (1mm slack for nester rounding).
    std::vector<BoundingBox> boxes;
    for (const ExPolygon &e : placed_shapes(items))
        boxes.push_back(e.contour.bounding_box());

    double min_gap = std::numeric_limits<double>::max();
    for (size_t i = 0; i < boxes.size(); ++i)
        for (size_t j = i + 1; j < boxes.size(); ++j) {
            coord_t sx = std::max<coord_t>(0, std::max(boxes[j].min.x() - boxes[i].max.x(),
                                                       boxes[i].min.x() - boxes[j].max.x()));
            coord_t sy = std::max<coord_t>(0, std::max(boxes[j].min.y() - boxes[i].max.y(),
                                                       boxes[i].min.y() - boxes[j].max.y()));
            min_gap = std::min(min_gap, std::sqrt(double(sx) * sx + double(sy) * sy));
        }

    REQUIRE(min_gap >= double(scaled(8.)) - double(scaled(0.5)));
}

TEST_CASE("An item larger than the bed cannot be placed", "[Arrange]")
{
    ArrangePolygons items;
    items.emplace_back(make_square(scaled(20.)));
    items.emplace_back(make_square(scaled(400.))); // far bigger than the bed
    // An item that cannot be placed keeps the position it came in with, so the
    // caller can leave it where the user had it.
    items[1].translation = {scaled(10.), scaled(20.)};

    arrange(items, bed(200, 200), quiet_params(scaled(1.)));

    REQUIRE(items[0].bed_idx == 0);
    REQUIRE(items[1].bed_idx == UNARRANGED);
    REQUIRE(items[1].translation.x() == scaled(10.));
    REQUIRE(items[1].translation.y() == scaled(20.));
}

TEST_CASE("An item filling the printable area is arranged", "[Arrange]")
{
    // The arrange bed keeps a margin from the printable area and the item is widened by
    // its brim. Neither may keep an item that fits the printable area from being placed.
    DynamicPrintConfig cfg   = bed_config(); // 200 x 200
    ArrangeParams      p     = quiet_params();

    ArrangePolygons items = squares(1, 197.);
    items.front().brim_width = 1.;
    update_arrange_params(p, &cfg, items);
    update_selected_items_inflation(items, &cfg, p);
    arrange(items, get_shrink_bedpts(&cfg, p), p);
    REQUIRE(items.front().bed_idx == 0);

    // Larger than the printable area is still refused.
    ArrangeParams   p_large = quiet_params();
    ArrangePolygons large   = squares(1, 201.);
    update_arrange_params(p_large, &cfg, large);
    update_selected_items_inflation(large, &cfg, p_large);
    arrange(large, get_shrink_bedpts(&cfg, p_large), p_large);
    REQUIRE(large.front().bed_idx == UNARRANGED);
}

TEST_CASE("Arranging uses the whole bed when the extruders share no printable area", "[Arrange]")
{
    // Two half-bed areas that only touch. An item wider than either half still fits the bed.
    DynamicPrintConfig cfg = bed_config(); // 200 x 200
    cfg.set_key_value("extruder_printable_area", new ConfigOptionPointsGroups{
        { { 0., 0. }, { 100., 0. }, { 100., 200. }, { 0., 200. } },
        { { 100., 0. }, { 200., 0. }, { 200., 200. }, { 100., 200. } } });
    ArrangeParams p = quiet_params();

    ArrangePolygons items = squares(1, 150.);
    update_arrange_params(p, &cfg, items);
    update_selected_items_inflation(items, &cfg, p);
    const Points bedpts = get_shrink_bedpts(&cfg, p);
    // The arrange jobs read the four corners.
    REQUIRE(bedpts.size() == 4);
    arrange(items, bedpts, p);
    CHECK(items.front().bed_idx == 0);

    // The bed still bounds the arrangement.
    ArrangeParams   p_large = quiet_params();
    ArrangePolygons large   = squares(1, 201.);
    update_arrange_params(p_large, &cfg, large);
    update_selected_items_inflation(large, &cfg, p_large);
    arrange(large, get_shrink_bedpts(&cfg, p_large), p_large);
    CHECK(large.front().bed_idx == UNARRANGED);
}

TEST_CASE("Items overflowing one bed spill onto virtual beds", "[Arrange]")
{
    ArrangePolygons items = squares(8, 90.); // eight 90mm squares cannot share a 200x200 bed
    arrange(items, bed(200, 200), quiet_params(scaled(2.)));

    int max_bed = 0;
    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx >= 0); // placed somewhere
        max_bed = std::max(max_bed, ap.bed_idx);
    }
    REQUIRE(max_bed >= 1); // at least one on a virtual bed
}

TEST_CASE("Arrange handles an empty input", "[Arrange]")
{
    ArrangePolygons items;
    REQUIRE_NOTHROW(arrange(items, bed(200, 200), quiet_params()));
    REQUIRE(items.empty());
}

TEST_CASE("Arrange without final alignment keeps items disjoint", "[Arrange]")
{
    // do_final_align = false selects Alignment::DONT_ALIGN (skips recentering).
    ArrangePolygons items  = squares(6, 40.);
    ArrangeParams   params = quiet_params(scaled(2.));
    params.do_final_align  = false;

    arrange(items, bed(250, 250), params);

    for (const ArrangePolygon &ap : items)
        REQUIRE(ap.bed_idx == 0);
    require_no_overlap(items);
}

TEST_CASE("Arrange centers a pile that fits on the custom alignment point", "[Arrange]")
{
    ArrangePolygons items  = squares(4, 30.);
    ArrangeParams   params = quiet_params(scaled(2.));
    params.align_center    = Vec2d(0.3, 0.7);

    arrange(items, bed(250, 250), params);

    BoundingBox pile;
    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        pile.merge(ap.transformed_poly().contour.bounding_box());
    }
    // best_object_pos is align_center scaled to the bed.
    const Point expected(scaled(250. * 0.3), scaled(250. * 0.7));
    REQUIRE(std::abs(pile.center().x() - expected.x()) <= scaled(0.5));
    REQUIRE(std::abs(pile.center().y() - expected.y()) <= scaled(0.5));
    require_no_overlap(items);
}

// A row of four 40 mm parts centred on the 30% mark of a 200 x 50 mm bed would start 24 mm
// left of it (#15727). The pile stops at the left edge instead.
TEST_CASE("Arrange keeps a custom-aligned pile within the bed", "[Arrange]")
{
    const BoundingBox bed_   = bed(200, 50);
    ArrangePolygons   items  = squares(4, 40.);
    ArrangeParams     params = quiet_params(scaled(2.));
    params.align_center      = Vec2d(0.3, 0.5);

    arrange(items, bed_, params);

    coord_t leftmost = std::numeric_limits<coord_t>::max();
    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        const BoundingBox bb = ap.transformed_poly().contour.bounding_box();
        CHECK(bed_.contains(bb));
        leftmost = std::min(leftmost, bb.min.x());
    }
    // Stopped at the edge it was aimed at, not re-centred.
    CHECK(leftmost < scaled(10.));
    require_no_overlap(items);
}

// Arranging a selection leaves the unselected parts where they are, but the final alignment
// centres the box around both, so the selection does not move by its own centring. The check
// against the bed and the fixed part must test where the selection actually lands.
TEST_CASE("Arrange keeps a selection on the bed and clear of a fixed part", "[Arrange]")
{
    ArrangePolygons fixed = squares(1, 40.);
    fixed.front().translation = {scaled(80.), scaled(80.)};
    ArrangePolygons items = squares(3, 40.);
    for (ArrangePolygon &ap : items)
        ap.inflation = scaled(1.);

    arrange(items, fixed, bed(200, 200), quiet_params());

    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        REQUIRE(bed(200, 200).contains(ap.transformed_poly().contour.bounding_box()));
    }
    items.insert(items.end(), fixed.begin(), fixed.end());
    require_no_overlap(items);
}

// A belt printer starts its parts at the leading end of the belt (best_object_pos 0.5, 0.05).
// Centring a pile on a point that close to the edge pushed everything longer than the room
// around it off the bed: four 90 mm parts on a 95 x 500 mm belt ended with one across the
// edge and one outside, with 290 mm of belt free behind them. The pile stops at the edge.
TEST_CASE("Arrange keeps a pile aligned near an edge on the bed", "[Arrange][belt]")
{
    const BoundingBox belt   = bed(95, 500);
    ArrangePolygons   items  = squares(4, 90.);
    ArrangeParams     params = quiet_params(scaled(2.));
    params.align_center      = Vec2d(0.5, 0.05);
    params.is_belt           = true;
    params.belt_axis         = 1;
    params.belt_tilt_slope   = 1.f;

    arrange(items, belt, params);

    coord_t lowest = std::numeric_limits<coord_t>::max();
    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        const BoundingBox bb = ap.transformed_poly().contour.bounding_box();
        CHECK(belt.contains(bb));
        lowest = std::min(lowest, bb.min.y());
    }
    // Snapped to the edge it was aimed at, less the spacing margin, not re-centred.
    CHECK(lowest < scaled(10.));
    require_no_overlap(items);
}

// Flat-bed printers with an off-centre best_object_pos (the A1 mini and the H2 family) get
// the same clamp: centring the pile on that point used to push it off the bed (#15727).
TEST_CASE("Arrange keeps a flat-bed pile aligned near an edge on the bed", "[Arrange]")
{
    const BoundingBox bed_   = bed(95, 500);
    ArrangePolygons   items  = squares(4, 90.);
    ArrangeParams     params = quiet_params(scaled(2.));
    params.align_center      = Vec2d(0.5, 0.05);

    arrange(items, bed_, params);

    coord_t lowest = std::numeric_limits<coord_t>::max();
    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        const BoundingBox bb = ap.transformed_poly().contour.bounding_box();
        CHECK(bed_.contains(bb));
        lowest = std::min(lowest, bb.min.y());
    }
    // Stopped at the edge it was aimed at, not re-centred.
    CHECK(lowest < scaled(10.));
    require_no_overlap(items);
}

// On a belt the parts print in belt order, so two colours that alternate along the
// belt, or sit side by side, cost a filament change on every shared layer. Arrange
// keeps each colour together: no part shares belt length with a part of another
// colour, counting the tilted layers that run cot(angle) * height past its far edge,
// whichever end of the belt prints first.
TEST_CASE("Arrange groups the colours of a belt print along the belt", "[Arrange][belt]")
{
    const bool reversed = GENERATE(false, true);
    CAPTURE(reversed);
    const BoundingBox belt   = bed(95, 500);
    ArrangePolygons   items  = squares(6, 30., 20.);
    for (size_t i = 0; i < items.size(); ++i)
        items[i].extrude_ids = { int(i % 3) + 1 };   // three colours, two parts each
    ArrangeParams params     = quiet_params(scaled(2.));
    params.align_center      = Vec2d(0.5, 0.05);
    params.is_belt           = true;
    params.belt_axis         = 1;
    params.belt_reversed     = reversed;
    params.belt_tilt_slope   = 1.f;   // 45 degrees

    arrange(items, belt, params);
    require_no_overlap(items);

    // Belt position in print order, so the same check serves both directions.
    const coord_t dir = reversed ? -1 : 1;
    auto start = [&](const ArrangePolygon &ap) { const BoundingBox bb = ap.transformed_poly().contour.bounding_box(); return dir * (reversed ? bb.max.y() : bb.min.y()); };
    auto end   = [&](const ArrangePolygon &ap) { const BoundingBox bb = ap.transformed_poly().contour.bounding_box(); return dir * (reversed ? bb.min.y() : bb.max.y()) + scaled(ap.height * params.belt_tilt_slope); };

    for (const ArrangePolygon &ap : items) {
        REQUIRE(ap.bed_idx == 0);
        CHECK(belt.contains(ap.transformed_poly().contour.bounding_box()));
    }
    for (const ArrangePolygon &a : items)
        for (const ArrangePolygon &b : items) {
            if (a.extrude_ids == b.extrude_ids)
                continue;
            // The part printed later starts after the earlier one has finished.
            const coord_t earlier_end = start(a) <= start(b) ? end(a) : end(b);
            const coord_t later_start = std::max(start(a), start(b));
            INFO("colour " << a.extrude_ids.front() << " vs " << b.extrude_ids.front());
            CHECK(earlier_end <= later_start);
        }
}

TEST_CASE("Sequential print floors the object distance by object height", "[Arrange]")
{
    // The only place sequential-print clearance is enforced. The arrange menu offers
    // no floor of its own, so a stored 0 has to be raised here or not at all.
    struct Case
    {
        std::string         description;
        std::vector<double> heights;
        double              skirt_offset_mm;
        double              expected_floor_mm;
    };

    auto c = GENERATE(values<Case>({
        {"objects taller than the nozzle need the full clearance",     {NOZZLE_HEIGHT_MM * 2, NOZZLE_HEIGHT_MM * 2}, 0., CLEARANCE_MM},
        {"an object exactly at the nozzle height counts as tall",      {NOZZLE_HEIGHT_MM,     NOZZLE_HEIGHT_MM},     0., CLEARANCE_MM},
        {"one tall object among short ones is enough",                 {NOZZLE_HEIGHT_MM / 2, NOZZLE_HEIGHT_MM * 2}, 0., CLEARANCE_MM},
        {"objects the nozzle clears keep only the nozzle-width floor", {NOZZLE_HEIGHT_MM / 2, NOZZLE_HEIGHT_MM / 2}, 0., NOZZLE_FLOOR_MM},
        {"a wide skirt raises the floor for short objects",            {NOZZLE_HEIGHT_MM / 2, NOZZLE_HEIGHT_MM / 2}, 3., 6.},
    }));

    DYNAMIC_SECTION(c.description)
    {
        ArrangePolygons    items = squares_of_heights(c.heights);
        DynamicPrintConfig cfg   = bed_config();
        ArrangeParams      p     = seq_print_params(0);
        p.object_skirt_offset    = float(c.skirt_offset_mm);

        update_selected_items_inflation(items, &cfg, p);

        CHECK(p.min_obj_distance >= scaled(c.expected_floor_mm));
        CHECK(p.min_obj_distance <= scaled(c.expected_floor_mm + 0.01));
        // Half each, so a pair ends up a full min_obj_distance apart.
        CHECK(items.front().inflation == p.min_obj_distance / 2);
    }
}

TEST_CASE("Sequential print keeps an object distance already above the floor", "[Arrange]")
{
    const coord_t      stored = scaled(CLEARANCE_MM * 2);
    ArrangePolygons    items  = squares_of_heights({NOZZLE_HEIGHT_MM * 2, NOZZLE_HEIGHT_MM * 2});
    DynamicPrintConfig cfg    = bed_config();
    ArrangeParams      p      = seq_print_params(stored);

    update_selected_items_inflation(items, &cfg, p);
    CHECK(p.min_obj_distance == stored);
}

TEST_CASE("Layered printing does not floor the object distance", "[Arrange]")
{
    ArrangePolygons    items = squares_of_heights({NOZZLE_HEIGHT_MM * 2, NOZZLE_HEIGHT_MM * 2});
    DynamicPrintConfig cfg   = bed_config();
    ArrangeParams      p     = seq_print_params(0);
    p.is_seq_print           = false;

    update_selected_items_inflation(items, &cfg, p);
    CHECK(p.min_obj_distance == 0);
}

// Short objects only need a nozzle's width between them, far less than the clearance
// radius, so the bed may only grow by half that width. A row of four 50 mm objects and
// their gaps is wider than the 200 mm bed but would fit one grown by half the clearance
// radius. Twenty of them overfill the bed, so the pile reaches its edges.
TEST_CASE("Sequential print keeps short objects on the bed and a nozzle apart", "[Arrange]")
{
    ArrangePolygons items = squares(20, 50., NOZZLE_HEIGHT_MM / 2);
    ArrangePolygons fixed;
    arrange_by_object(items, fixed);

    // Grown as Print::sequential_print_clearance_valid() grows them.
    ExPolygons grown;
    for (const ArrangePolygon &ap : items) {
        if (ap.bed_idx != 0)
            continue;
        CHECK(bed(200, 200).contains(ap.transformed_poly().contour.bounding_box()));
        append(grown, offset_ex(ap.transformed_poly(), float(scale_(0.5 * MAX_OUTER_NOZZLE_DIAMETER - 0.1))));
    }
    REQUIRE(grown.size() > 1);
    REQUIRE(disjoint(grown));
}

// Only the disc has to fit the bed; the half gap it is inflated by may reach past the
// edge. Within the bed margin of filling the bed, the arrange bed is cut to the disc's
// size, and rounding must not leave it a hair too small.
TEST_CASE("Sequential print arranges a short object filling the printable area", "[Arrange]")
{
    ArrangePolygons items{make_disc(196., NOZZLE_HEIGHT_MM / 2)};
    ArrangePolygons fixed;
    arrange_by_object(items, fixed);

    REQUIRE(items.front().bed_idx == 0);
    REQUIRE(bed(200, 200).contains(items.front().transformed_poly().contour.bounding_box()));
}

// The largest object and its clearance are wider than the bed less its margins, though
// the object itself fits within them, so every object keeps the margin.
TEST_CASE("Sequential print keeps the bed margin beside a large tall object", "[Arrange]")
{
    ArrangePolygons items = squares(3, 10., NOZZLE_HEIGHT_MM * 2);
    items.push_back(make_disc(170., NOZZLE_HEIGHT_MM * 2));
    ArrangePolygons fixed;
    arrange_by_object(items, fixed);

    const coord_t     margin = scaled(BED_SHRINK_SEQ_PRINT - 0.01); // 0.01 mm for rounding
    const BoundingBox inner(Point(margin, margin), Point(scaled(200.) - margin, scaled(200.) - margin));
    for (const ArrangePolygon &ap : items)
        if (ap.bed_idx == 0)
            CHECK(inner.contains(ap.transformed_poly().contour.bounding_box()));
}

// Short objects keep off an extrusion calibration region. One along the back edge catches
// the region being moved back by a positive bed shrink, which lets objects onto it.
TEST_CASE("Sequential print keeps short objects off a calibration region", "[Arrange]")
{
    const BoundingBox region_bb(Point(0, scaled(185.)), Point(scaled(200.), scaled(200.)));
    ArrangePolygon    region;
    region.poly                     = ExPolygon(region_bb.polygon());
    region.bed_idx                  = 0;
    region.is_virt_object           = true;
    region.is_extrusion_cali_object = true;
    ArrangePolygons items = squares(20, 40., NOZZLE_HEIGHT_MM / 2);
    ArrangePolygons fixed{region};
    arrange_by_object(items, fixed);

    for (const ArrangePolygon &ap : items)
        if (ap.bed_idx == 0)
            CHECK(ap.transformed_poly().contour.bounding_box().max.y() <= region_bb.min.y());
}

// The nester packs an object turned and inflated, and the inflated corners of a turned square
// reach past its inflation, so cutting the arrange bed to the object's size must measure that
// outline. The square is 196 mm wide turned 30 degrees.
TEST_CASE("Sequential print arranges a turned short object filling the printable area", "[Arrange]")
{
    ArrangePolygon item = make_square(scaled(196. / (std::cos(PI / 6) + std::sin(PI / 6))));
    item.height   = NOZZLE_HEIGHT_MM / 2;
    item.rotation = PI / 6;
    ArrangePolygons items{item};
    ArrangePolygons fixed;
    arrange_by_object(items, fixed);

    REQUIRE(items.front().bed_idx == 0);
    REQUIRE(bed(200, 200).contains(items.front().transformed_poly().contour.bounding_box()));
}

// An object closer to the bed edge than the bed margin, as one placed by hand, still takes its
// room when Fill bed adds objects around it, though its inflation crosses the arrange bed's edge.
TEST_CASE("Sequential print keeps short objects off one at the bed edge", "[Arrange]")
{
    ArrangePolygon obstacle = make_square(scaled(40.));
    obstacle.translation    = {scaled(1.), scaled(80.)};
    obstacle.height         = NOZZLE_HEIGHT_MM / 2;
    obstacle.extrude_ids    = {1};
    ArrangePolygons fixed{obstacle};
    ArrangePolygons items = squares(20, 40., NOZZLE_HEIGHT_MM / 2);
    arrange_by_object(items, fixed);

    ExPolygons placed{obstacle.transformed_poly()};
    for (const ArrangePolygon &ap : items)
        if (ap.bed_idx == 0)
            placed.emplace_back(ap.transformed_poly());
    REQUIRE(placed.size() > 1);
    REQUIRE(disjoint(placed));
}

TEST_CASE("Bed exclusions apply by physical nozzle and overlapping Z range", "[Arrange][ExclusionVolume][MultiNozzle]")
{
    ArrangePolygon object = make_square(scaled(20.));
    object.has_z_range = true;
    object.z_min = 0.0;
    object.z_max = 20.0;
    object.bed_exclusion_extruder_ids = {1};

    ArrangePolygon exclusion = make_square(scaled(20.));
    exclusion.is_bed_exclusion = true;
    exclusion.has_z_range = true;
    exclusion.z_min = 10.0;
    exclusion.z_max = 30.0;
    exclusion.bed_exclusion_extruder_id = 1;

    CHECK(bed_exclusion_applies(object, exclusion));

    exclusion.bed_exclusion_extruder_id = 0;
    CHECK_FALSE(bed_exclusion_applies(object, exclusion));

    // Empty physical-nozzle assignments mean unresolved, so arrangement stays conservative.
    object.bed_exclusion_extruder_ids.clear();
    CHECK(bed_exclusion_applies(object, exclusion));

    object.bed_exclusion_extruder_ids = {0};
    object.z_max = 9.0;
    CHECK_FALSE(bed_exclusion_applies(object, exclusion));

    // Touching at one Z plane is intentionally treated as a collision.
    object.z_max = 10.0;
    CHECK(bed_exclusion_applies(object, exclusion));
}

TEST_CASE("Shared bed exclusions apply to every arranged object", "[Arrange][ExclusionVolume]")
{
    ArrangePolygon object = make_square(scaled(20.));
    object.bed_exclusion_extruder_ids = {1};

    ArrangePolygon shared = make_square(scaled(20.));
    shared.is_bed_exclusion = true;
    shared.bed_exclusion_extruder_id = -1;

    CHECK(has_bed_exclusion_regions({shared}));
    CHECK_FALSE(has_bed_exclusion_regions({object}));
    CHECK(bed_exclusion_applies(object, shared));
}

TEST_CASE("Arrange keeps relevant objects outside conditional exclusion obstacles", "[Arrange][ExclusionVolume]")
{
    ArrangePolygon exclusion = make_square(scaled(30.));
    exclusion.translation = Vec2crd(scaled(35.0), scaled(35.0));
    exclusion.is_bed_exclusion = true;
    exclusion.bed_exclusion_extruder_id = 0;

    ArrangePolygons items = squares(4, 20.0);
    for (ArrangePolygon &item : items)
        item.bed_exclusion_extruder_ids = {0};

    arrange(items, {exclusion}, bed(100.0, 100.0), quiet_params(scaled(1.0)));

    const ExPolygon excluded_shape = exclusion.transformed_poly();
    for (const ArrangePolygon &item : items) {
        REQUIRE(item.bed_idx == 0);
        CHECK(intersection(ExPolygons{item.transformed_poly()}, ExPolygons{excluded_shape}).empty());
    }
    require_no_overlap(items);
}

// A print config with support of this type turned on, and the settings how far it reaches on the bed depends on.
static DynamicPrintConfig support_config(const std::string &support_type)
{
    DynamicPrintConfig config = DynamicPrintConfig::full_print_config();
    config.set_deserialize_strict({ { "enable_support", "1" },
                                    { "support_type", support_type },
                                    { "support_style", "default" },
                                    { "initial_layer_print_height", "0.2" },
                                    { "support_expansion", "0" },
                                    { "raft_first_layer_expansion", "2" },
                                    { "tree_support_branch_diameter_organic", "2" },
                                    { "tree_support_branch_diameter", "2" },
                                    { "tree_support_branch_diameter_angle", "5" },
                                    { "tree_support_branch_angle_organic", "40" },
                                    { "tree_support_branch_angle", "40" },
                                    { "tree_support_auto_brim", "1" },
                                    { "support_object_xy_distance", "0.35" },
                                    { "support_object_first_layer_gap", "0.2" } });
    return config;
}

// The arrange polygon of an object made of these parts, standing on the bed, with support turned on.
static ArrangePolygon support_arrange_poly(std::vector<TriangleMesh> parts, const std::string &support_type,
                                           std::initializer_list<ConfigBase::SetDeserializeItem> settings = {},
                                           bool mirrored = false)
{
    Model model;
    ModelObject *object = model.add_object();
    for (TriangleMesh &part : parts)
        object->add_volume(std::move(part));
    ModelInstance *instance = object->add_instance();
    if (mirrored)
        instance->set_mirror(Vec3d(-1., 1., 1.));
    DynamicPrintConfig config = support_config(support_type);
    config.set_deserialize_strict(settings);
    return get_instance_arrange_poly(instance, config);
}

static std::vector<TriangleMesh> cube_on_bed() { return { make_cube(20., 20., 20.) }; }

// A 20 mm cube with a second block on its top half that sticks out 10 mm sideways: its bottom face, 10 mm
// above the bed, looks straight down.
static std::vector<TriangleMesh> cube_with_overhang()
{
    TriangleMesh ledge = make_cube(20., 20., 10.);
    ledge.translate(10.f, 0.f, 10.f);
    return { make_cube(20., 20., 20.), std::move(ledge) };
}

// The margin arrange keeps around the whole object, 1 mm without support, and whether it is tree support's, of which
// update_selected_items_inflation() keeps half on each side.
static void check_support_margin(const ArrangePolygon &ap, double margin, bool tree)
{
    CHECK_THAT(ap.brim_width, Catch::Matchers::WithinAbs(margin, 1e-9));
    CHECK(ap.has_tree_support == tree);
}

static void check_extent(const ArrangePolygon &ap, double min_x, double max_x, double min_y, double max_y)
{
    const BoundingBox bb = ap.poly.contour.bounding_box();
    CHECK_THAT(unscaled(bb.min.x()), Catch::Matchers::WithinAbs(min_x, 0.01));
    CHECK_THAT(unscaled(bb.max.x()), Catch::Matchers::WithinAbs(max_x, 0.01));
    CHECK_THAT(unscaled(bb.min.y()), Catch::Matchers::WithinAbs(min_y, 0.01));
    CHECK_THAT(unscaled(bb.max.y()), Catch::Matchers::WithinAbs(max_y, 0.01));
}

TEST_CASE("Arrange gives no support margin to an object with nothing to support", "[Arrange][Support]")
{
    const std::string support_type = GENERATE("tree(auto)", "normal(auto)");
    const bool        mirrored     = GENERATE(false, true);
    INFO("support_type = " << support_type << ", mirrored = " << mirrored);
    const ArrangePolygon ap = support_arrange_poly(cube_on_bed(), support_type, {}, mirrored);
    check_support_margin(ap, 1., false);
    check_extent(ap, mirrored ? -20. : 0., mirrored ? 0. : 20., 0., 20.);
}

// A 20 mm cube with a 10 mm ledge on the top half of its +X side, whose bottom face, 10 mm above the bed, looks
// straight down: support stands under the ledge only.
static std::vector<TriangleMesh> cube_with_ledge()
{
    TriangleMesh ledge = make_cube(10., 20., 10.);
    ledge.translate(20.f, 0.f, 10.f);
    return { make_cube(20., 20., 20.), std::move(ledge) };
}

// The room past support holding up points less than 31 mm above the bed, less the 1 mm margin the object keeps. Normal
// support reaches 6 mm. An organic trunk is 7.5 mm across at the bed, thicker only past 31 mm at a Branch Diameter Angle
// of 5 degrees and a 2 mm Branch Diameter, and its first layer grows by the 2 mm First layer expansion.
static double support_room(const std::string &support_type) { return support_type.rfind("tree", 0) == 0 ? 3.75 + 2. - 1. : 5.; }

TEST_CASE("Arrange leaves room for support on the side of an overhang only", "[Arrange][Support]")
{
    const std::string support_type = GENERATE("tree(auto)", "normal(auto)");
    const bool        mirrored     = GENERATE(false, true);
    INFO("support_type = " << support_type << ", mirrored = " << mirrored);
    const ArrangePolygon ap   = support_arrange_poly(cube_with_ledge(), support_type, {}, mirrored);
    const double         room = support_room(support_type);
    check_support_margin(ap, 1., false);
    // Past the ledge, on its sides, and not on the other side of the cube. Mirrored along X, it sticks out toward -X.
    if (mirrored)
        check_extent(ap, -30. - room, 0., -room, 20. + room);
    else
        check_extent(ap, 0., 30. + room, -room, 20. + room);
}

TEST_CASE("Arrange leaves room for support under the bottom of a sphere", "[Arrange][Support]")
{
    // A sphere on the bed: support holds up the faces near its bottom, flatter than the 60 degree threshold, out to
    // a radius of about sin(60 degrees) * 10 mm, and at most 5 mm above the bed.
    const std::string support_type = GENERATE("tree(auto)", "normal(auto)");
    INFO("support_type = " << support_type);
    TriangleMesh sphere = make_sphere(10.);
    sphere.translate(0.f, 0.f, 10.f);
    const ArrangePolygon ap = support_arrange_poly({ std::move(sphere) }, support_type, { { "support_threshold_angle", "60" } });
    check_support_margin(ap, 1., false);
    // The faces of the tessellated sphere flatter than 60 degrees end a little inside that radius, past 8 mm.
    const double room = support_room(support_type);
    const double min_width = 2. * (8. + room) - 0.1, max_width = 2. * (10. * std::sin(PI / 3.) + room) + 0.1;
    const BoundingBox bb = ap.poly.contour.bounding_box();
    for (const coord_t width : { bb.size().x(), bb.size().y() }) {
        CHECK(unscaled(width) > min_width);
        CHECK(unscaled(width) < max_width);
    }
}

TEST_CASE("Arrange leaves room for support under a sharp tail in the air", "[Arrange][Support]")
{
    // A steep cone hanging tip down beside the cube, its tip 5 mm above the bed at (30, 10). Its sides are 84 degrees
    // steep, far past the 30 degree threshold, but the tip starts an island in the air.
    TriangleMesh cone = make_cone(2., 20.);
    cone.rotate_x(float(PI));
    cone.translate(30.f, 10.f, 25.f);
    std::vector<TriangleMesh> parts = cube_on_bed();
    parts.push_back(std::move(cone));
    const ArrangePolygon ap = support_arrange_poly(std::move(parts), "tree(auto)", { { "support_threshold_angle", "30" } });
    check_support_margin(ap, 1., false);
    // Past the tip toward +X; on Y the room stays within the cube.
    check_extent(ap, 0., 30. + support_room("tree(auto)"), 0., 20.);
}

TEST_CASE("Arrange leaves room for support under an enforcer only", "[Arrange][Support]")
{
    // A 20 mm cube with a support enforcer volume over its +X half: manual support stands under the enforcer only.
    const std::string support_type = GENERATE("tree(manual)", "normal(manual)");
    INFO("support_type = " << support_type);
    Model        model;
    ModelObject *object = model.add_object();
    object->add_volume(make_cube(20., 20., 20.));
    TriangleMesh enforcer = make_cube(10., 20., 20.);
    enforcer.translate(15.f, 0.f, 0.f);
    object->add_volume(std::move(enforcer), ModelVolumeType::SUPPORT_ENFORCER);
    ModelInstance       *instance = object->add_instance();
    const ArrangePolygon ap       = get_instance_arrange_poly(instance, support_config(support_type));
    const double         room = support_room(support_type);
    check_support_margin(ap, 1., false);
    check_extent(ap, 0., 25. + room, -room, 20. + room);
}

TEST_CASE("Arrange gives no support margin to manual support without enforcers", "[Arrange][Support]")
{
    const std::string support_type = GENERATE("tree(manual)", "normal(manual)");
    INFO("support_type = " << support_type);
    check_support_margin(support_arrange_poly(cube_with_overhang(), support_type), 1., false);
}

// How far past the outline a tree trunk reaches that comes down beside the object, holding up a point at height z, less
// the 1 mm margin the object keeps: its middle stands past the 0.35 mm gap by its radius on the bed, and its first layer
// reaches around it. An organic trunk is 1 mm, half its Branch Diameter, thickened by z * tan(5 degrees), and at least
// 3.75 mm; its whole first layer, grown by the 2 mm First layer expansion, stays past the gap. A hybrid one thickens from
// 1 mm by (z - 1 mm) * 5 degrees in radians, and its first layer reaches 12 mm.
static double room_beside(const std::string &support_style, double z)
{
    if (support_style == "tree_hybrid")
        return 1. + (z - 1.) * 5. * PI / 180. + 0.35 + 12. - 1.;
    const double reach = std::max(1. + z * std::tan(5. * PI / 180.), 3.75) + 2.;
    return reach + 0.35 + reach - 1.;
}

TEST_CASE("Arrange keeps the support margin of an object on a raft", "[Arrange][Support]")
{
    // A raft is printed as support, so it is kept around the whole object. Normal support reaches 6 mm. A tree trunk
    // may come down beside the 20 mm cube anywhere, past the 0.35 mm gap, see room_beside().
    struct Raft { std::string support_type, support_style; double margin; bool tree; };
    const Raft raft = GENERATE(Raft{ "normal(auto)", "default", 6., false },
                               Raft{ "tree(auto)", "default", 2. * (room_beside("default", 20.) + 1.), true },
                               Raft{ "tree(auto)", "tree_hybrid", 2. * (room_beside("tree_hybrid", 20.) + 1.), true });
    INFO("support_type = " << raft.support_type << ", support_style = " << raft.support_style);
    check_support_margin(support_arrange_poly(cube_on_bed(), raft.support_type,
                                              { { "raft_layers", "2" }, { "support_style", raft.support_style } }),
                         raft.margin, raft.tree);
}

// A 20 mm column 110 mm tall with a 10 mm ledge on the top of its +X side, whose bottom face, 100 mm above the bed,
// looks straight down.
static std::vector<TriangleMesh> column_with_high_ledge()
{
    TriangleMesh ledge = make_cube(10., 20., 10.);
    ledge.translate(20.f, 0.f, 100.f);
    return { make_cube(20., 20., 110.), std::move(ledge) };
}

TEST_CASE("Arrange leaves room for support as far as its type and style reach", "[Arrange][Support]")
{
    // Normal support reaches 6 mm, and further by its expansion and by First layer expansion past 2 mm. An organic tree,
    // which tree support's default style prints, thickens toward the bed by its Branch Diameter Angle: from 1 mm, half
    // its Branch Diameter, by 100 mm * tan(5 degrees) under the ledge, and its first layer grows by First layer expansion.
    // Slim, strong and hybrid branches reach 10 mm at most, and their first layer gets a brim, 12 mm at most when
    // automatic. The object keeps its own 1 mm margin.
    const double organic = 1. + 100. * std::tan(5. * PI / 180.);
    struct Reach { std::string support_type, support_style; std::vector<std::pair<std::string, std::string>> settings; double reach; };
    const Reach r = GENERATE_COPY(Reach{ "normal(auto)", "default", {}, 6. },
                                  Reach{ "normal(auto)", "grid", {}, 6. },
                                  Reach{ "normal(auto)", "snug", {}, 6. },
                                  Reach{ "normal(auto)", "default", { { "support_expansion", "3" } }, 9. },
                                  Reach{ "normal(auto)", "default", { { "raft_first_layer_expansion", "4" } }, 8. },
                                  Reach{ "tree(auto)", "default", {}, organic + 2. },
                                  Reach{ "tree(auto)", "organic", {}, organic + 2. },
                                  Reach{ "tree(auto)", "organic", { { "raft_first_layer_expansion", "4" } }, organic + 4. },
                                  Reach{ "tree(auto)", "organic", { { "tree_support_branch_diameter_angle", "0" } }, 3.75 + 2. },
                                  Reach{ "tree(auto)", "tree_slim", {}, 12. },
                                  Reach{ "tree(auto)", "tree_strong", {}, 12. },
                                  Reach{ "tree(auto)", "tree_hybrid", {}, 12. },
                                  Reach{ "tree(auto)", "tree_hybrid", { { "tree_support_auto_brim", "0" }, { "tree_support_brim_width", "5" } }, 15. });
    INFO("support_type = " << r.support_type << ", support_style = " << r.support_style << ", settings = " << r.settings.size());
    Model        model;
    ModelObject *object = model.add_object();
    for (TriangleMesh &part : column_with_high_ledge())
        object->add_volume(std::move(part));
    ModelInstance     *instance = object->add_instance();
    DynamicPrintConfig config   = support_config(r.support_type);
    config.set_deserialize_strict("support_style", r.support_style);
    for (const auto &[key, value] : r.settings)
        config.set_deserialize_strict(key, value);
    const ArrangePolygon ap   = get_instance_arrange_poly(instance, config);
    const double         room = r.reach - 1.;
    check_support_margin(ap, 1., false);
    check_extent(ap, 0., 30. + room, -room, 20. + room);
}

// A 40 mm square base 5 mm thick, a 10 mm post in its middle up to 60 mm and a 30 mm cap on the post, which sticks out
// 10 mm on both sides over the base: support holds up its bottom over the base, 5 mm in from the base's edges.
static std::vector<TriangleMesh> cap_over_base()
{
    TriangleMesh post = make_cube(10., 10., 55.);
    post.translate(15.f, 15.f, 5.f);
    TriangleMesh cap = make_cube(30., 10., 5.);
    cap.translate(5.f, 15.f, 60.f);
    return { make_cube(40., 40., 5.), std::move(post), std::move(cap) };
}

TEST_CASE("Arrange leaves room beside the object for tree support over it", "[Arrange][Support]")
{
    // Normal support stands on the base. A tree branch at 60 mm reaches past the base's edge by its 40 degree Branch
    // Angle and comes down beside it, from the base's edge nearest to each of the cap's ends. The ends are as tall, so
    // each may lead an organic trunk down its own side.
    struct Beside { std::string support_type, support_style; double room; };
    const Beside b = GENERATE(Beside{ "normal(auto)", "default", 0. },
                              Beside{ "tree(auto)", "default", room_beside("default", 60.) },
                              Beside{ "tree(auto)", "tree_hybrid", room_beside("tree_hybrid", 60.) });
    INFO("support_type = " << b.support_type << ", support_style = " << b.support_style);
    const ArrangePolygon ap = support_arrange_poly(cap_over_base(), b.support_type, { { "support_style", b.support_style } });
    check_support_margin(ap, 1., false);
    check_extent(ap, -b.room, 40. + b.room, std::min(0., 15. - b.room), std::max(40., 25. + b.room));
}

// A 40 mm square base 5 mm thick, a 10 mm post in its middle up to 65 mm, and two 10 mm arms on the post over the base,
// 5 mm in from the base's edges: one toward -X with its bottom at 60 mm, one toward +X with its bottom at 50 mm.
static std::vector<TriangleMesh> arms_over_base()
{
    TriangleMesh post = make_cube(10., 10., 60.);
    post.translate(15.f, 15.f, 5.f);
    TriangleMesh high_arm = make_cube(10., 5., 5.);
    high_arm.translate(5.f, 17.5f, 60.f);
    TriangleMesh low_arm = make_cube(10., 5., 5.);
    low_arm.translate(25.f, 17.5f, 50.f);
    return { make_cube(40., 40., 5.), std::move(post), std::move(high_arm), std::move(low_arm) };
}

TEST_CASE("Arrange leaves room for one organic trunk on the side of the tallest branch", "[Arrange][Support]")
{
    // Both arms' branches reach past the base's edge by their 40 degree Branch Angle, and can meet on the way down.
    // Organic branches that meet merge into one trunk, which the higher arm's branch leads down on its own side, -X.
    // Hybrid branches each come down on their own side. The room is for a trunk holding up the higher arm.
    const std::string support_style = GENERATE("default", "tree_hybrid");
    INFO("support_style = " << support_style);
    const ArrangePolygon ap   = support_arrange_poly(arms_over_base(), "tree(auto)", { { "support_style", support_style } });
    const double         room = room_beside(support_style, 60.);
    check_support_margin(ap, 1., false);
    check_extent(ap, -room, support_style == "default" ? 40. : 40. + room, std::min(0., 17.5 - room), std::max(40., 22.5 + room));
}

TEST_CASE("Arrange leaves room for organic trunks too far apart to merge on both sides", "[Arrange][Support]")
{
    // A 200 mm long base, with an arm at 30 mm over it toward -Y near one end and an arm at 25 mm toward +Y near the
    // other. Their branches reach the base's edges by their 40 degree Branch Angle, 5 mm away, but are 100 mm apart:
    // too far to meet on the way down, so each comes down as its own trunk on its own side.
    TriangleMesh left_post = make_cube(10., 10., 30.);
    left_post.translate(40.f, 15.f, 5.f);
    TriangleMesh left_arm = make_cube(10., 10., 5.);
    left_arm.translate(40.f, 5.f, 30.f);
    TriangleMesh right_post = make_cube(10., 10., 25.);
    right_post.translate(150.f, 15.f, 5.f);
    TriangleMesh right_arm = make_cube(10., 10., 5.);
    right_arm.translate(150.f, 25.f, 25.f);
    std::vector<TriangleMesh> parts;
    parts.push_back(make_cube(200., 40., 5.));
    parts.push_back(std::move(left_post));
    parts.push_back(std::move(left_arm));
    parts.push_back(std::move(right_post));
    parts.push_back(std::move(right_arm));
    const ArrangePolygon ap   = support_arrange_poly(std::move(parts), "tree(auto)");
    const double         room = room_beside("default", 30.);
    check_support_margin(ap, 1., false);
    check_extent(ap, 0., 200., -room, 40. + room);
}

TEST_CASE("Arrange keeps the normal support margin when the threshold angle is zero", "[Arrange][Support]")
{
    // At 0 degrees normal support goes by the threshold overlap instead, which no angle stands for, while tree
    // support falls back to 30 degrees.
    check_support_margin(support_arrange_poly(cube_on_bed(), "normal(auto)", { { "support_threshold_angle", "0" } }), 6., false);
    check_support_margin(support_arrange_poly(cube_on_bed(), "tree(auto)", { { "support_threshold_angle", "0" } }), 1., false);
}

TEST_CASE("Arrange keeps the tree support margin around the supported object only", "[Arrange][Support]")
{
    // A tree supported object's margin is the branch diameter, half of it on each side, so its neighbors are clear
    // of its branches. The other objects keep their own 1 mm margin and may stand close to each other.
    DynamicPrintConfig cfg = bed_config();
    ArrangeParams      p   = quiet_params();
    ArrangePolygons items  = squares(3, 20.);
    for (ArrangePolygon &ap : items)
        ap.brim_width = 1.;
    items.front().brim_width       = 24.;
    items.front().has_tree_support = true;
    update_arrange_params(p, &cfg, items);
    update_selected_items_inflation(items, &cfg, p);
    CHECK(items[0].inflation == scaled(12.));
    CHECK(items[1].inflation == scaled(1.));
    CHECK(items[2].inflation == scaled(1.));
}
