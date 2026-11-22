#include "ModelArrange.hpp"

#include <cstddef>
#include <algorithm>
#include <iterator>
#include <libslic3r/Model.hpp>
#include <libslic3r/Geometry/ConvexHull.hpp>
#include <libslic3r/Print.hpp>
#include "Arrange.hpp"
#include <utility>
#include "Config.hpp"
#include <set>
#include <string>
#include "Point.hpp"
#include "PrintConfig.hpp"
#include "BoundingBox.hpp"
#include "ExPolygon.hpp"
#include "ClipperUtils.hpp"
#include "Polygon.hpp"
#include "Line.hpp"
#include "Geometry.hpp"
#include "TriangleSelector.hpp"
#include "AABBMesh.hpp"
#include "libslic3r.h"
#include "admesh/stl.h"
#include <cmath>
#include <limits>
#include <vector>

namespace Slic3r {

arrangement::ArrangePolygons get_arrange_polys(const Model &model, ModelInstancePtrs &instances)
{
    size_t count = 0;
    for (auto obj : model.objects) count += obj->instances.size();

    ArrangePolygons input;
    input.reserve(count);
    instances.clear(); instances.reserve(count);
    ArrangePolygon ap;
    for (ModelObject *mo : model.objects)
        for (ModelInstance *minst : mo->instances) {
            minst->get_arrange_polygon(&ap);
            // ModelInstance::get_arrange_polygon leaves bed_idx at its UNARRANGED
            // default; seed it to bed 0 (as get_instance_arrange_poly does) so the
            // nester treats the item as placeable instead of returning it unplaced.
            ap.bed_idx = 0;
            input.emplace_back(ap);
            instances.emplace_back(minst);
        }

    return input;
}

bool apply_arrange_polys(ArrangePolygons &input, ModelInstancePtrs &instances, VirtualBedFn vfn)
{
    bool ret = true;

    for(size_t i = 0; i < input.size(); ++i) {
        if (input[i].bed_idx != 0) { ret = false; if (vfn) vfn(input[i]); }
        if (input[i].bed_idx >= 0)
            instances[i]->apply_arrange_result(input[i].translation.cast<double>(),
                                               input[i].rotation);
    }

    return ret;
}

Slic3r::arrangement::ArrangePolygon get_arrange_poly(const Model &model)
{
    ArrangePolygon ap;
    Points &apts = ap.poly.contour.points;
    for (const ModelObject *mo : model.objects)
        for (const ModelInstance *minst : mo->instances) {
            ArrangePolygon obj_ap;
            minst->get_arrange_polygon(&obj_ap);
            ap.poly.contour.rotate(obj_ap.rotation);
            ap.poly.contour.translate(obj_ap.translation.x(), obj_ap.translation.y());
            const Points &pts = obj_ap.poly.contour.points;
            std::copy(pts.begin(), pts.end(), std::back_inserter(apts));
        }

    apts = std::move(Geometry::convex_hull(apts).points);
    return ap;
}

void duplicate(Model &model, Slic3r::arrangement::ArrangePolygons &copies, VirtualBedFn vfn)
{
    for (ModelObject *o : model.objects) {
        // make a copy of the pointers in order to avoid recursion when appending their copies
        ModelInstancePtrs instances = o->instances;
        o->instances.clear();
        for (const ModelInstance *i : instances) {
            for (arrangement::ArrangePolygon &ap : copies) {
                if (ap.bed_idx != 0) vfn(ap);
                ModelInstance *instance = o->add_instance(*i);
                Vec2d pos = unscale(ap.translation);
                instance->set_offset(instance->get_offset() + to_3d(pos, 0.));
            }
        }
        o->invalidate_bounding_box();
    }
}

void duplicate_objects(Model &model, size_t copies_num)
{
    for (ModelObject *o : model.objects) {
        // make a copy of the pointers in order to avoid recursion when appending their copies
        ModelInstancePtrs instances = o->instances;
        for (const ModelInstance *i : instances)
            for (size_t k = 2; k <= copies_num; ++ k)
                o->add_instance(*i);
    }
}

// Set up arrange polygon for a ModelInstance and Wipe tower
template<class T>
arrangement::ArrangePolygon get_arrange_poly(T obj, const Slic3r::DynamicPrintConfig& config)
{
    ArrangePolygon ap = obj.get_arrange_polygon(config);
    //BBS: always set bed_idx to 0 to use original transforms with no bed_idx
    //if this object is not arranged, it can keep the original transforms
    //ap.bed_idx        = ap.translation.x() / bed_stride_x(plater);
    ap.bed_idx = 0;
    ap.setter = [obj](const ArrangePolygon& p) {
        if (p.is_arranged()) {
            Vec2d t = p.translation.cast<double>();
            //BBS: change to sudoku-style computation, do it in partplate list
            //t.x() += p.bed_idx * bed_stride(plater);
            //t.x() += col * bed_stride_x(plater);
            //t.y() -= row * bed_stride_y(plater);
            T{ obj }.apply_arrange_result(t, p.rotation, p.itemid);
        }
    };

    return ap;
}

template<>
arrangement::ArrangePolygon get_arrange_poly(ModelInstance* inst, const Slic3r::DynamicPrintConfig& config)
{
    return get_arrange_poly(PtrWrapper{ inst },config);
}

namespace {

// Orca: where arrange leaves room for an instance's support.
struct SupportFootprint
{
    bool               needed       = false; // whether support holds anything up
    bool               whole_object = false; // where it stands can't be told, so it may stand anywhere around the object
    Points             under;                // the points it holds up over the bed, in the frame of the arrange polygon
    std::vector<Vec3d> over_object;          // the points it holds up over the object itself, with their height
    double             top = 0.;             // the height of the highest point it holds up
};

} // namespace

// Organic is also what tree support's default style prints.
static bool organic_tree_support(ModelObject &object, const DynamicPrintConfig &config)
{
    const auto *style = object.get_config_value<ConfigOptionEnum<SupportMaterialStyle>>(config, "support_style");
    return style == nullptr || (style->value != smsTreeSlim && style->value != smsTreeStrong && style->value != smsTreeHybrid);
}

static double object_float(ModelObject &object, const DynamicPrintConfig &config, const char *key)
{
    const ConfigOptionFloat *opt = object.get_config_value<ConfigOptionFloat>(config, key);
    return opt != nullptr ? opt->value : 0.;
}

// The radius of a tree trunk at the bed holding up a point at height z, before its first layer grows, in mm.
static double tree_trunk_radius(ModelObject &object, const DynamicPrintConfig &config, double z)
{
    const double angle = Geometry::deg2rad(std::clamp(object_float(object, config, "tree_support_branch_diameter_angle"), 0., 15.));
    if (organic_tree_support(object, config))
        // An organic branch thickens toward the bed by its Branch Diameter Angle, and a trunk is at least 7.5 mm across
        // at the bed (TreeSupportMeshGroupSettings::support_tree_bp_diameter).
        return std::max(object_float(object, config, "tree_support_branch_diameter_organic") / 2. + z * std::tan(angle), 3.75);
    // A slim, strong or hybrid branch thickens from half its Branch Diameter by the angle in radians, below a tip as
    // tall, up to 10 mm (TreeSupport::calc_branch_radius(), MAX_BRANCH_RADIUS).
    const double tip = std::max(0.4, object_float(object, config, "tree_support_branch_diameter") / 2.);
    return std::min(tip + std::max(0., z - tip) * angle, 10.);
}

// How far support reaches on the bed around where it stands, holding up a point at height z, in mm.
static double support_reach(ModelObject &object, const DynamicPrintConfig &config, SupportType support_type, double z)
{
    const double first_layer_expansion = std::max(0., object_float(object, config, "raft_first_layer_expansion"));
    if (!is_tree(support_type))
        // Normal support stands right under what it holds up. Arrange has always kept 6 mm for it, which covers its
        // default expansion; more Normal support expansion or First layer expansion reaches further.
        return 6. + std::max(0., object_float(object, config, "support_expansion")) + std::max(0., first_layer_expansion - 2.);
    if (organic_tree_support(object, config))
        // The first layer of an organic trunk grows by First layer expansion.
        return tree_trunk_radius(object, config, z) + first_layer_expansion;
    // The first layer of a slim, strong or hybrid trunk gets a brim, which reaches 12 mm at most when automatic
    // (MAX_BRANCH_RADIUS_FIRST_LAYER), see TreeSupport::draw_circles().
    const ConfigOptionBool *auto_brim = object.get_config_value<ConfigOptionBool>(config, "tree_support_auto_brim");
    return auto_brim != nullptr && !auto_brim->value ? 10. + object_float(object, config, "tree_support_brim_width") : 12.;
}

// The gap support keeps from the object on the bed.
static double support_gap(ModelObject &object, const DynamicPrintConfig &config)
{
    return std::max(object_float(object, config, "support_object_xy_distance"), object_float(object, config, "support_object_first_layer_gap"));
}

// How far the first layer of a raft reaches past what stands on it, in mm, or 0 without a raft. Slim, strong and hybrid
// tree support grow the raft by First layer expansion and its first layer by as much again (TreeSupport::generate_toolpaths()),
// the other support by Raft expansion and its first layer by First layer expansion.
static double raft_reach(ModelObject &object, const DynamicPrintConfig &config)
{
    const ConfigOptionInt *raft_layers = object.get_config_value<ConfigOptionInt>(config, "raft_layers");
    if (raft_layers == nullptr || raft_layers->value <= 0)
        return 0.;
    const double first_layer_expansion = std::max(0., object_float(object, config, "raft_first_layer_expansion"));
    return std::max(std::max(0., object_float(object, config, "raft_expansion")), first_layer_expansion) + first_layer_expansion;
}

// How far past the object's outline a tree trunk that comes down beside it reaches: its middle stands past the support
// gap by its radius on the bed, and its first layer reaches around it. An organic trunk keeps its whole first layer,
// grown by First layer expansion, past the gap. The brim of a slim, strong or hybrid trunk is cut where it would come
// closer than the gap (TreeSupport::draw_circles()), so only the trunk under it is.
static double tree_room_beside(ModelObject &object, const DynamicPrintConfig &config, SupportType support_type, double z)
{
    const double reach  = support_reach(object, config, support_type, z);
    const double radius = organic_tree_support(object, config) ? reach : tree_trunk_radius(object, config, z);
    return radius + support_gap(object, config) + reach;
}

// Where tree support for the points held up over the object comes down beside it, on the object's outline. A branch
// leaves the object at the nearest edge of the outline when it can reach past it, by its Branch Angle. Organic branches
// that can meet on the way down merge into one trunk (TreeSupport3D merges their influence areas), which the tallest of
// them leads down on its own side; the others leave on their own sides only when that is the same side. Slim, strong and
// hybrid branches each move to their own nearest edge (TreeSupport::drop_nodes()).
static Points tree_trunks_beside(ModelObject &object, const DynamicPrintConfig &config, const Polygon &outline, std::vector<Vec3d> over_object)
{
    const bool   organic   = organic_tree_support(object, config);
    const double angle     = object_float(object, config, organic ? "tree_support_branch_angle_organic" : "tree_support_branch_angle");
    const double tan_angle = std::tan(Geometry::deg2rad(std::clamp(angle, 0., 60.)));
    const double outward   = outline.is_counter_clockwise() ? 1. : -1.;
    struct Branch
    {
        Vec3d held;
        Point edge;
        Vec2d side;
    };
    std::vector<Branch> branches;
    std::stable_sort(over_object.begin(), over_object.end(), [](const Vec3d &a, const Vec3d &b) { return a.z() > b.z(); });
    for (const Vec3d &pt : over_object) {
        const Point held(scaled(pt.x()), scaled(pt.y()));
        Branch      branch{ pt, held, Vec2d::Zero() };
        double      dist2 = std::numeric_limits<double>::max();
        for (const Line &line : outline.lines()) {
            Point        foot;
            const double d2 = line.distance_to_squared(held, &foot);
            if (d2 < dist2) {
                dist2       = d2;
                branch.edge = foot;
                branch.side = outward * line.normal().cast<double>();
            }
        }
        if (std::sqrt(dist2) <= scaled(pt.z() * tan_angle))
            branches.push_back(branch);
    }
    Points beside;
    std::vector<const Branch *> leaders;
    for (const Branch &branch : branches) {
        const Branch *leader = nullptr;
        if (organic)
            for (const Branch *tall : leaders)
                if ((tall->held - branch.held).head<2>().norm() <= (tall->held.z() + branch.held.z()) * tan_angle) {
                    leader = tall;
                    break;
                }
        // A branch as tall as its leader may lead the trunk too.
        if (leader == nullptr || branch.held.z() > leader->held.z() - EPSILON)
            leaders.push_back(&branch);
        else if (branch.side.dot(leader->side) <= 0.)
            continue;
        beside.push_back(branch.edge);
    }
    return beside;
}

// Sorts the points support holds up by what is under them. Support for a point over the object stands on it, or, for
// tree support, may come down beside it.
static SupportFootprint place_support(ModelObject &object, const Geometry::Transformation &frame, std::vector<Vec3d> held, double above_bed)
{
    SupportFootprint support;
    support.needed = !held.empty();
    if (held.empty())
        return support;
    std::sort(held.begin(), held.end(), [](const Vec3d &a, const Vec3d &b) {
        return std::lexicographical_compare(a.data(), a.data() + 3, b.data(), b.data() + 3);
    });
    held.erase(std::unique(held.begin(), held.end()), held.end());

    indexed_triangle_set parts;
    for (const ModelVolume *volume : object.volumes) {
        if (!volume->is_model_part())
            continue;
        const Transform3d trafo = frame.get_matrix() * volume->get_matrix();
        const bool        mirrored = trafo.linear().determinant() < 0.;
        const int         first    = int(parts.vertices.size());
        for (const stl_vertex &pt : volume->mesh().its.vertices)
            parts.vertices.emplace_back((trafo * pt.cast<double>()).cast<float>());
        for (const stl_triangle_vertex_indices &face : volume->mesh().its.indices) {
            // Mirrored, the faces keep looking out.
            parts.indices.emplace_back(face + stl_triangle_vertex_indices::Constant(first));
            if (mirrored)
                std::swap(parts.indices.back()[1], parts.indices.back()[2]);
        }
    }
    const AABBMesh mesh(parts);
    for (const Vec3d &pt : held) {
        // Cast from just under the point, not to hit the face it is on, to the first face under it that isn't a wall: a
        // ray along a wall may hit it. Support stands on that face when it looks up, unless it is at the bed.
        const Vec3d                             from = pt - 0.001 * Vec3d::UnitZ();
        const std::vector<AABBMesh::hit_result> hits = mesh.query_ray_hits(from, -Vec3d::UnitZ());
        const auto floor = std::find_if(hits.begin(), hits.end(),
                                        [](const AABBMesh::hit_result &hit) { return hit.is_hit() && std::abs(hit.normal().z()) > EPSILON; });
        if (floor != hits.end() && floor->normal().z() > 0. && floor->position().z() > above_bed)
            support.over_object.emplace_back(pt);
        else
            support.under.emplace_back(scaled(pt.x()), scaled(pt.y()));
        support.top = std::max(support.top, pt.z());
    }
    return support;
}

// Support that is turned on but finds nothing to hold up generates nothing, and its margin would only spread the objects
// apart, and support that holds up one side of an object needs no room on the others. Arranging can't wait for a slice,
// so this reads the mesh, and keeps the margin around the whole object whenever it can't tell.
static SupportFootprint instance_support(ModelObject &object, const ModelInstance &instance, const DynamicPrintConfig &config, SupportType support_type)
{
    SupportFootprint whole_object;
    whole_object.needed       = true;
    whole_object.whole_object = true;
    const auto object_int = [&](const char *key) {
        const ConfigOptionInt *opt = object.get_config_value<ConfigOptionInt>(config, key);
        return opt != nullptr ? opt->value : 0;
    };
    // A tilted plate or a belt measures overhangs against another direction.
    bool tilted = false;
    for (const char *key : { "build_plate_tilt_x", "build_plate_tilt_y" })
        if (const ConfigOptionFloat *tilt = config.option<ConfigOptionFloat>(key); tilt != nullptr && tilt->value != 0.)
            tilted = true;
    if (const ConfigOptionBool *belt = config.option<ConfigOptionBool>("belt_printer"); belt != nullptr && belt->value)
        tilted = true;

    // The frame of ModelInstance::get_arrange_polygon(): the arrange turns the polygon about Z and moves it on the bed.
    Vec3d rotation = instance.get_rotation();
    rotation.z()   = 0.;
    Geometry::Transformation frame(instance.get_transformation());
    frame.set_offset(instance.get_offset().z() * Vec3d::UnitZ());
    frame.set_rotation(rotation);

    std::vector<Vec3d> held;
    const auto         holds_up = [&held](const Vec3d &pt) { held.emplace_back(pt); };
    // Enforcers and negative volumes add overhangs the parts don't show, under the enforced facets and within the volumes.
    for (const ModelVolume *volume : object.volumes) {
        const Transform3d trafo = frame.get_matrix() * volume->get_matrix();
        if (volume->is_support_enforcer() || volume->is_negative_volume())
            for (const stl_vertex &pt : volume->mesh().its.vertices)
                holds_up(trafo * pt.cast<double>());
        else if (volume->is_model_part() && volume->supported_facets.has_facets(*volume, EnforcerBlockerType::ENFORCER))
            for (const stl_vertex &pt : volume->supported_facets.get_facets(*volume, EnforcerBlockerType::ENFORCER).vertices)
                holds_up(trafo * pt.cast<double>());
    }
    // Tilted, where it stands can't be told: around the whole object whenever there may be support.
    if (tilted)
        return !held.empty() || is_auto(support_type) ? whole_object : SupportFootprint{};
    // Nothing gets support within the first layer.
    const ConfigOptionFloat *first_layer = config.option<ConfigOptionFloat>("initial_layer_print_height");
    const double above_bed = (first_layer != nullptr ? first_layer->value : 0.) + EPSILON;
    // Manual support is only generated on enforcers.
    if (!is_auto(support_type))
        return place_support(object, frame, std::move(held), above_bed);
    int threshold_deg = object_int("support_threshold_angle");
    if (threshold_deg == 0) {
        // Normal support then goes by the threshold overlap, which no angle stands for. Tree support takes 30 degrees.
        if (!is_tree(support_type))
            return whole_object;
        threshold_deg = 30;
    }
    const double cos_threshold = std::cos(Geometry::deg2rad(double(threshold_deg)));

    for (const ModelVolume *volume : object.volumes) {
        if (!volume->is_model_part())
            continue;
        const Transform3d trafo = frame.get_matrix() * volume->get_matrix();
        const bool mirrored = trafo.linear().determinant() < 0.;
        const indexed_triangle_set &its = volume->mesh().its;
        std::vector<Vec3d> pts(its.vertices.size());
        for (size_t i = 0; i < pts.size(); ++i)
            pts[i] = trafo * its.vertices[i].cast<double>();
        // A vertex of a face looking down, with no neighbor below it, is where an island starts in the air: both
        // support types hold up such a sharp tail whatever the slope around it.
        std::vector<bool> has_lower(pts.size(), false), on_face_looking_down(pts.size(), false);
        for (const stl_triangle_vertex_indices &face : its.indices) {
            Vec3d normal = (pts[face[1]] - pts[face[0]]).cross(pts[face[2]] - pts[face[0]]);
            if (mirrored)
                normal = -normal;
            const double area2 = normal.norm();
            if (area2 <= 0.)
                continue;
            const double top = std::max({ pts[face[0]].z(), pts[face[1]].z(), pts[face[2]].z() });
            if (top > above_bed && -normal.z() > cos_threshold * area2)
                // An overhang flatter than the threshold angle.
                for (int i = 0; i < 3; ++i)
                    holds_up(pts[face[i]]);
            for (int i = 0; i < 3; ++i) {
                const int a = face[i], b = face[(i + 1) % 3];
                if (pts[b].z() < pts[a].z() - EPSILON)
                    has_lower[a] = true;
                if (pts[a].z() < pts[b].z() - EPSILON)
                    has_lower[b] = true;
                if (normal.z() < -EPSILON * area2)
                    on_face_looking_down[a] = true;
            }
        }
        for (size_t i = 0; i < pts.size(); ++i)
            if (!has_lower[i] && on_face_looking_down[i] && pts[i].z() > above_bed)
                holds_up(pts[i]);
    }
    return place_support(object, frame, std::move(held), above_bed);
}

ArrangePolygon get_instance_arrange_poly(ModelInstance* instance, const Slic3r::DynamicPrintConfig& config)
{
    ArrangePolygon ap = get_arrange_poly(PtrWrapper{ instance }, config);

    //BBS: add temperature information
    if (config.has("curr_bed_type")) {
        ap.bed_temp = 0;
        ap.first_bed_temp = 0;
        BedType curr_bed_type = config.opt_enum<BedType>("curr_bed_type");

        const ConfigOptionInts* bed_opt = config.option<ConfigOptionInts>(get_bed_temp_key(curr_bed_type));
        if (bed_opt != nullptr)
            ap.bed_temp = bed_opt->get_at(ap.extrude_ids.front()-1);

        const ConfigOptionInts* bed_opt_1st_layer = config.option<ConfigOptionInts>(get_bed_temp_1st_layer_key(curr_bed_type));
        if (bed_opt_1st_layer != nullptr)
            ap.first_bed_temp = bed_opt_1st_layer->get_at(ap.extrude_ids.front()-1);
    }

    if (config.has("nozzle_temperature")) //get the print temperature
        ap.print_temp = config.opt_int("nozzle_temperature", ap.extrude_ids.front() - 1);
    if (config.has("nozzle_temperature_initial_layer")) //get the nozzle_temperature_initial_layer
        ap.first_print_temp = config.opt_int("nozzle_temperature_initial_layer", ap.extrude_ids.front() - 1);

    if (config.has("temperature_vitrification")) {
        ap.vitrify_temp = config.opt_int("temperature_vitrification", ap.extrude_ids.front() - 1);
    }

    // get filament temp types
    auto* filament_types_opt = dynamic_cast<const ConfigOptionStrings*>(config.option("filament_type"));
    if (filament_types_opt) {
        std::set<int> filament_temp_types;
        for (auto i : ap.extrude_ids) {
            std::string type_str = filament_types_opt->get_at(i-1);
            int temp_type = Print::get_filament_temp_type(type_str);
            filament_temp_types.insert(temp_type);
        }
        ap.filament_temp_type = Print::get_compatible_filament_type(filament_temp_types);
    }

    // get brim width
    auto obj = instance->get_object();

    // Orca: a raft reaches past the object, with support on or off, and past the support standing on it.
    const double raft = raft_reach(*obj, config);
    ap.brim_width     = 1.0 + raft;
    // For by-layer printing, need to shrink bed a little, so the support won't go outside bed.
    // Orca: an object whose support has nothing to hold up gets no support margin, an object whose support stands on
    // one side gets it on that side only, and the margin is as wide as the support's type and style reach.
    auto supp_type_ptr = obj->get_config_value<ConfigOptionBool>(config, "enable_support");
    auto support_type_ptr = obj->get_config_value<ConfigOptionEnum<SupportType>>(config, "support_type");
    auto support_type = support_type_ptr->value;
    const SupportFootprint support = supp_type_ptr->getBool() ? instance_support(*obj, *instance, config, support_type) : SupportFootprint{};
    const bool tree_support = is_tree(support_type);
    const BoundingBoxf3 bbox = obj->instance_convex_hull_bounding_box(instance);

    if (support.whole_object) {
        if (tree_support) {
            // A trunk may come down beside the object anywhere, see below. update_selected_items_inflation() keeps
            // half the brim width of tree support around the object.
            ap.brim_width       = 2. * (tree_room_beside(*obj, config, support_type, bbox.max.z()) + raft);
            ap.has_tree_support = true;
        } else
            ap.brim_width = support_reach(*obj, config, support_type, bbox.max.z()) + raft;
    } else if (support.needed) {
        const double reach  = support_reach(*obj, config, support_type, support.top) + raft;
        const Points beside = tree_support ? tree_trunks_beside(*obj, config, ap.poly.contour, support.over_object) : Points{};
        // The polygon reaches past the support by its reach, and the object keeps its own margin.
        Points     points    = std::move(ap.poly.contour.points);
        Polygons   support_room; // each ring's hull, for the outline the packer places
        const auto keep_room = [&points, &support_room](const Points &around, double room) {
            if (around.empty() || room <= 0.)
                return;
            // Fewer than three points, such as the tip of a sharp tail, have no hull.
            const Polygon hull = Geometry::convex_hull(around);
            Points        ring;
            for (const Point &pt : hull.empty() ? around : hull.points)
                for (int i = 0; i < 64; ++i) {
                    const double angle = 2. * PI * i / 64;
                    ring.emplace_back(pt + Point(scaled(room * std::cos(angle)), scaled(room * std::sin(angle))));
                }
            support_room.push_back(Geometry::convex_hull(ring));
            append(points, std::move(ring));
        };
        keep_room(support.under, reach - ap.brim_width);
        keep_room(beside, tree_room_beside(*obj, config, support_type, support.top) + raft - ap.brim_width);
        ap.poly = ExPolygon(Geometry::convex_hull(std::move(points)));
        // The packer places the true outline, so it keeps the support's room too. Support that
        // stands apart from the outline leaves several islands: the packer then takes the hull.
        if (!ap.outline.empty() && !support_room.empty()) {
            ExPolygons grown = union_ex(ExPolygons{ap.outline}, support_room);
            ap.outline       = grown.size() == 1 ? std::move(grown.front()) : ExPolygon();
        }
    }

    ap.height = bbox.size().z();
    ap.z_min = bbox.min.z();
    ap.z_max = bbox.max.z();
    ap.has_z_range = bbox.defined;
    ap.name = obj->name;
    return ap;
}

} // namespace Slic3r
