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
#include "Polygon.hpp"
#include "Geometry.hpp"
#include "TriangleSelector.hpp"
#include "admesh/stl.h"
#include <cmath>
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
    bool   needed = false; // whether support holds anything up
    Points under;          // where it stands, in the frame of the arrange polygon; none when it may stand anywhere around the object
};

} // namespace

// Support that is turned on but finds nothing to hold up generates nothing, and its margin would only spread the objects
// apart, and support that holds up one side of an object needs no room on the others. Arranging can't wait for a slice,
// so this reads the mesh, and keeps the margin around the whole object whenever it can't tell.
static SupportFootprint instance_support(ModelObject &object, const ModelInstance &instance, const DynamicPrintConfig &config, SupportType support_type)
{
    SupportFootprint whole_object;
    whole_object.needed = true;
    const auto object_int = [&](const char *key) {
        const ConfigOptionInt *opt = object.get_config_value<ConfigOptionInt>(config, key);
        return opt != nullptr ? opt->value : 0;
    };
    // A raft is printed as support.
    if (object_int("raft_layers") > 0)
        return whole_object;
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

    SupportFootprint support;
    const auto stands_under = [&support](const Vec3d &pt) {
        support.needed = true;
        support.under.emplace_back(scaled(pt.x()), scaled(pt.y()));
    };
    // Enforcers and negative volumes add overhangs the parts don't show, under the enforced facets and within the volumes.
    for (const ModelVolume *volume : object.volumes) {
        const Transform3d trafo = frame.get_matrix() * volume->get_matrix();
        if (volume->is_support_enforcer() || volume->is_negative_volume())
            for (const stl_vertex &pt : volume->mesh().its.vertices)
                stands_under(trafo * pt.cast<double>());
        else if (volume->is_model_part() && volume->supported_facets.has_facets(*volume, EnforcerBlockerType::ENFORCER))
            for (const stl_vertex &pt : volume->supported_facets.get_facets(*volume, EnforcerBlockerType::ENFORCER).vertices)
                stands_under(trafo * pt.cast<double>());
    }
    // Tilted, where it stands can't be told: around the whole object whenever there may be support.
    if (tilted)
        return support.needed || is_auto(support_type) ? whole_object : support;
    // Manual support is only generated on enforcers.
    if (!is_auto(support_type))
        return support;
    int threshold_deg = object_int("support_threshold_angle");
    if (threshold_deg == 0) {
        // Normal support then goes by the threshold overlap, which no angle stands for. Tree support takes 30 degrees.
        if (!is_tree(support_type))
            return whole_object;
        threshold_deg = 30;
    }
    const double cos_threshold = std::cos(Geometry::deg2rad(double(threshold_deg)));
    // Nothing gets support within the first layer.
    const ConfigOptionFloat *first_layer = config.option<ConfigOptionFloat>("initial_layer_print_height");
    const double above_bed = (first_layer != nullptr ? first_layer->value : 0.) + EPSILON;

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
                    stands_under(pts[face[i]]);
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
                stands_under(pts[i]);
    }
    return support;
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

    ap.brim_width = 1.0;
    // For by-layer printing, need to shrink bed a little, so the support won't go outside bed.
    // We set it to 5mm because that's how much a normal support will grow by default.
    // normal support 5mm, other support 22mm, no support 0mm
    // Orca: an object whose support has nothing to hold up gets no support margin, and an object whose support
    // stands on one side gets it on that side only.
    auto supp_type_ptr = obj->get_config_value<ConfigOptionBool>(config, "enable_support");
    auto support_type_ptr = obj->get_config_value<ConfigOptionEnum<SupportType>>(config, "support_type");
    auto support_type = support_type_ptr->value;
    const SupportFootprint support = supp_type_ptr->getBool() ? instance_support(*obj, *instance, config, support_type) : SupportFootprint{};
    const bool tree_support = support_type != stNormalAuto && support_type != stNormal;

    if (support.needed && support.under.empty() && !tree_support)
        ap.brim_width = 6.0;
    else if (support.needed && support.under.empty()) {
        ap.brim_width = 24.0; // 2*MAX_BRANCH_RADIUS_FIRST_LAYER
        ap.has_tree_support = true;
    } else if (support.needed) {
        // The polygon reaches past the support by the room update_selected_items_inflation() keeps around a supported
        // object, 6 mm for normal support and a branch's first layer radius for tree support, and the object keeps its
        // own margin.
        const double room   = (tree_support ? 12. : 6.) - ap.brim_width;
        Points       points = std::move(ap.poly.contour.points);
        // Fewer than three points, such as the tip of a sharp tail, have no hull.
        const Polygon under = Geometry::convex_hull(support.under);
        for (const Point &pt : under.empty() ? support.under : under.points)
            for (int i = 0; i < 64; ++i) {
                const double angle = 2. * PI * i / 64;
                points.emplace_back(pt + Point(scaled(room * std::cos(angle)), scaled(room * std::sin(angle))));
            }
        ap.poly = ExPolygon(Geometry::convex_hull(std::move(points)));
    }

    const BoundingBoxf3 bbox = obj->instance_convex_hull_bounding_box(instance);
    ap.height = bbox.size().z();
    ap.z_min = bbox.min.z();
    ap.z_max = bbox.max.z();
    ap.has_z_range = bbox.defined;
    ap.name = obj->name;
    return ap;
}

} // namespace Slic3r
