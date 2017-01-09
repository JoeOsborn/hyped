import xmlparser as xml
import schema as h
from collections import namedtuple
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import BitVector as bv
True

OrderedAutomaton = namedtuple("OrderedAutomaton", h.Automaton._fields+("ordering", "ordered_modes"))

OrderedMode = namedtuple("OrderedMode", h.Mode._fields+("index","descendant_count","ancestor_set","descendant_set","self_set"))

OrderedEdge = namedtuple("OrderedEdge", h.Edge._fields+("target_index",))

def translate_automaton(aut):
    group_deps, ordered_list = safe_ordered_mode_list(aut.groups)
    ordering = {qn:num for num,qn in enumerate(ordered_list)}
    translated_modes = []
    for modename in ordered_list:
        m = modename.mode_in(aut.groups)
        tmode = translate_mode(m, ordering)
        translated_modes.append(tmode)
    props = aut._asdict()
    props["ordering"] = ordering
    props["ordered_modes"] = translated_modes  
    return OrderedAutomaton(**props)

def safe_ordered_mode_list(groups):
    group_deps = group_dependencies(groups)
    ordered_groups = order_groups(groups, group_deps)
    ordered_list = []
    for g in ordered_groups:
        ordered_list.extend(h.flat_modes({g:groups[g]}))
    return (group_deps, ordered_list)

def group_dependencies(groups):
    group_deps = {}
    flat_list = h.flat_modes(groups)
    for modename in flat_list:
        gid = modename.groups[0]
        if not (gid in group_deps):
            group_deps[gid] = set()
        m = modename.mode_in(groups)
        for e in m.edges:
            assert isinstance(e, h.Edge)
            deps = guard_dependencies(e.guard)
            for dep in deps:
                group_deps[gid].add(dep)
    return group_deps

def order_groups(groups, group_deps):
    ordered_groups = []
    group_ids = groups.keys()
    tries = 0
    max_tries = len(group_ids)**2
    while len(group_ids) > 0 and tries < max_tries:
        gid = group_ids.pop(0)
        all_met = True
        for dep in group_deps[gid]:
            this_found = False
            for present_dep in ordered_groups:
                if present_dep == dep:
                    this_found = True
            if not this_found:
                all_met = False
                break
        if all_met:
            ordered_groups.append(gid)
        else:
            group_ids.append(gid)
        tries += 1
    if len(group_ids) > 0:
        raise ValueError("No safe group order", groups, group_deps)
    return ordered_groups

def guard_dependencies(guard):
    # Only care about root group IDs given the constraints above
    if isinstance(guard, h.GuardConjunction):
        ret = set()
        for g in guard.conjuncts:
            ret.update(guard_dependencies(g))
        return ret
    elif isinstance(guard, h.GuardJointTransition):
        return set([guard.mode.groups[0]])
    return set()

def dep_path(a, b, deps, stack=set()):
    # find simple cycles only
    if a in stack: return False
    # find self-cycles
    if a == b: return True
    # find one-step cycles
    if b in deps[a]: return True
    # recurse for each dep, adding a to stack to avoid non-simple cycles.
    for mid in deps[a]:
        if dep_path(mid, b, deps, stack | a):
            return True
    # otherwise: no cycle!
    return False

def translate_guard(g, ordering):
    if isinstance(g, h.GuardConjunction):
        return g._replace(conjuncts=[translate_guard(gc, ordering) for gc in g.conjuncts])
    elif isinstance(g, h.GuardJointTransition):
        return g._replace(mode=ordering[g.mode])
    elif isinstance(g, h.GuardInMode):
        return g._replace(mode=ordering[g.mode])
    return g


def translate_mode(m, ordering):
    modenum = ordering[m.qualified_name]
    if len(m.groups) > 1:
        return "Too many groups in a non-root mode for now!"
    new_edges = []
    descendant_count = len(h.flat_modes(m.groups, m.qualified_name))
    for e in m.edges:
        eprops = e._asdict()
        eprops["target_index"] = ordering[e.qualified_target]
        eprops["guard"] = translate_guard(e.guard, ordering)
        new_edges.append(OrderedEdge(**eprops))
    props = m._asdict()
    props["index"] = modenum
    props["edges"] = new_edges
    props["descendant_count"] = descendant_count
    props["ancestor_set"] = qname_to_ancestors(m.qualified_name, ordering, include_self=False)
    props["descendant_set"] = mode_set(start=modenum, count=descendant_count, order=ordering)
    props["self_set"] = mode_set(start=modenum, count=1, order=ordering)
    return OrderedMode(**props)

def mode_set(start=None, count=1, order=None):
    bvec = bv.BitVector(size=len(order))
    # Not sure this is the most efficient way!
    if not (start is None):
        for v in range(start,start+count):
            bvec[v] = 1
    return bvec

def qname_to_ancestors(qname, ordering, include_self=False):
    ms = mode_set(order=ordering)
    if not include_self:
        qname = qname.parent_mode
    while qname != None:
        ms[ordering[qname]] = 1
        qname = qname.parent_mode
    return ms

class Valuation(object):
    __slots__ = ["automaton_index", 
                 "parameters", "variables", 
                 "active_modes",
                 "entered", "exited"]
    def __init__(self, aut, aut_i, parameters, variables, active_modes):
        self.automaton_index = aut_i
        self.parameters = parameters
        self.variables = variables
        self.active_modes = active_modes
        self.entered = active_modes.deep_copy()
        self.exited = mode_set(order=aut.ordering)

class World(object):
    __slots__ = ["theories", "automata", "automata_indices", "valuations"]
    def __init__(self, automata):
        for a in automata:
            assert isinstance(a, OrderedAutomaton)
        self.automata_indices = {a.name : i for i,a in enumerate(automata)}
        self.automata = automata
        self.valuations = [[] for a in automata]
        # TODO: include automata
        self.theories = Theories()
    def make_valuation(self, automaton_name, params={}, vbls={}):
        assert automaton_name in self.automata_indices
        aut_i = self.automata_indices[automaton_name]
        aut = self.automata[aut_i]
        params = {pn: p.value.value for pn, p in aut.parameters.items()}
        vars = {vn: v.init.value for vn, v in aut.variables.items()}
        params.update(params)
        vars.update(vars)
        initial_modes = initial_mask(aut)
        val = Valuation(aut, aut_i, params, vars, initial_modes)
        self.valuations[aut_i].append(val)
        return val

class Theories(object):
    __slots__ = ["input", "collision"]
    def __init__(self):
        self.input = InputTheory()
        self.collision = CollisionTheory([],[],[])

def step(world, input_data, dt):
    world.theories.input.update(input_data, dt)
    discrete_step(world)
    #flows = flows_from_has(world)
    #continuous_step(world, flows, dt)
    continuous_step(world, dt)
    #colliders = colliders_from_has(world) # or something
    #world.theories.collision.update(world, dt)

def discrete_step(world):
    for vals in world.valuations:
        for val in vals:
            exit_set, enter_set, updates = determine_available_transitions(world, val)
            # Perform the transitions and updates.  This is where the bitmask representation pays off!
            val.active_modes &= ~exit_set
            val.active_modes |= enter_set
            # Apply all the updates at once.
            for uk, uv in updates.items():
                val.variables[uk] = uv

def determine_available_transitions(world, val):
    exit_set = mode_set(order=world.automata[val.automaton_index].ordering)
    enter_set = mode_set(order=world.automata[val.automaton_index].ordering)
    # Clear the exited and enter sets of the valuation.
    val.exited = exit_set
    val.entered = enter_set
    updates = {}
    mi = 0
    modes = world.automata[val.automaton_index].ordered_modes
    mode_count = len(modes)
    active = val.active_modes
    while mi < mode_count:
        if active[mi]:
            mode = modes[mi]
            for e in mode.edges:
                if eval_guard(e.guard, world, val):
                    exit_set, enter_set = update_transition_sets(
                        world,
                        val,
                        mode, modes[e.target_index],
                        enter_set, exit_set)
                    # Each time we get a new mask, update the valuation's exited
                    # and entered modes.
                    # We need to do this since some guards depend on it.
                    val.exited = exit_set
                    val.entered = enter_set
                    # skip descendants
                    mi += mode.descendant_count
                    # figure out and merge in updates
                    for euk, euv in e.updates.items():
                        updates[euk] = eval_value(euv, world, val)
                    # skip any other transitions of this mode
                    break
        mi += 1
    return (exit_set, enter_set, updates)

def update_transition_sets(world, val, src, dest, enters, exits):
    all_srcs = src.descendant_set | src.ancestor_set | src.self_set
    exits |= all_srcs & ~dest.ancestor_set
    enters |= dest.ancestor_set | dest.self_set
    enters |= initial_mask(world.automata[val.automaton_index], dest)
    return (exits, enters)

def initial_mask(automaton, mode=None):
    modes = automaton.ordered_modes
    # Handle the root case (seen in Valuation initialization)
    mask = None
    if mode is None:
        mask = mode_set(order=automaton.ordering)
        mi = 0
        mlim = len(mask)
    else:
        # Handle the case where we're only looking for descendants of a particular mode
        mask = mode.ancestor_set | mode.self_set
        mi = mode.index
        mlim = mi + mode.descendant_count
    # TODO: Use entry edges to determine which mode to start in. 
    # May involve enters/exits, val, and maybe world being passed into this function!
    while mi < mlim:
        this_descendant = modes[mi]
        # If this is the mode we want, use it and proceed to check its children
        if this_descendant.is_initial:
            mask[mi] = 1
        else:
            # Otherwise, skip its children and move on.
            mi += this_descendant.descendant_count
        mi += 1
    return mask

def eval_guard(guard, world, val):
    if isinstance(guard, h.GuardConjunction):
        result = True
        for c in guard.conjuncts:
            # TODO: If evaluation needs a context (e.g. bindings), pass result as well
            result = result & eval_guard(c, world, val)
            if not result:
                return False
        return result
    elif isinstance(guard, h.GuardTrue):
        return True
    elif isinstance(guard, h.GuardInMode):
        assert guard.character is None
        return val.active_modes[guard.mode] != 0
    elif isinstance(guard, h.GuardJointTransition):
        assert guard.character is None
        if guard.direction == "enter":
            return val.entered[guard.mode]
        elif guard.direction == "exit":
            return val.exited[guard.mode]
        else:
            raise ValueError("Unrecognized direction", guard)
    elif isinstance(guard, h.GuardColliding):
        # TODO: how to specify "the collider(s) of this val"?
        return 0 < world.theories.collision.count_contacts(
            val,
            guard.self_type,
            guard.normal_check,
            guard.other_type)
    elif isinstance(guard, h.GuardButton):
        if guard.status == "pressed":
            return world.theories.input.is_pressed(guard.playerID, guard.buttonID)
        elif guard.status == "on":
            return world.theories.input.is_on(guard.playerID, guard.buttonID)
        elif guard.status == "off":
            return world.theories.input.is_off(guard.playerID, guard.buttonID)
        elif guard.status == "released":
            return world.theories.input.is_released(guard.playerID, guard.buttonID)
        else:
            raise ValueError("Unrecognized status", guard)
    else:
        raise ValueError("Unrecognized guard", guard)

def eval_value(expr, world, val):
    if isinstance(expr, h.ConstantExpr):
        return expr.value
    elif isinstance(expr, h.Parameter):
        return eval_value(expr.value, world, val)
    else:
        raise ValueError("Unhandled expr", expr)

def continuous_step(world, dt):
    for i,vals in enumerate(world.valuations):
        for val in vals:
            aut = world.automata[i]
            flows = {}
            # TODO: Ordering variables would give us a way around using dicts here.
            # We could store [v1, v1', v1'', v2, v2', v2'', ...]
            # Let's revisit it once we have a better representation for variable storage.
            # Even namedtuples (one per HA type) would be an improvement.  pos, vel, and acc vbls
            # could be stored separately.
            for f in aut.flows.values():
                fvar = f.var
                fvalexpr = f.value
                fval = eval_value(fvalexpr, world, val)
                flows[fvar.basename] = (fvar, fval)
            modes = aut.ordered_modes
            active = val.active_modes
            mi = 0
            mlim = len(modes)
            while mi < mlim:
                if not active[mi]:
                    mi += modes[mi].descendant_count
                else:
                    for f in modes[mi].flows.values():
                        fvar = f.var
                        fvalexpr = f.value
                        fval = eval_value(fvalexpr, world, val)
                        flows[fvar.basename] = (fvar, fval)
                mi += 1
            vbls = aut.variables
            pos_vbls = [v for v in vbls.values() if v.degree == 0]
            vel_vbls = [v for v in vbls.values() if v.degree == 1]
            acc_vbls = [v for v in vbls.values() if v.degree == 2]
            for vi in range(len(pos_vbls)):
                pos = pos_vbls[vi]
                vel = vel_vbls[vi]
                acc = acc_vbls[vi]
                val_pos = val.variables[pos.name]
                val_vel = val.variables[vel.name]
                val_acc = val.variables[acc.name]
                # see if it's in the flow dict.
                if pos.basename in flows:
                    # If so, update its vel or acc according to the flow, set any
                    # higher degrees to 0, and update lower degrees as above
                    # (acc->vel, vel->pos).
                    (fvar, fval) = flows[pos.basename]
                    if fvar.degree == 2:
                        val_acc = fval
                        val_vel = val_vel + val_acc * dt
                        val_pos = val_pos + val_vel * dt
                    elif fvar.degree == 1:
                        val_acc = 0
                        val_vel = fval
                        val_pos = val_pos + val_vel * dt
                    else:
                        val_acc = 0
                        val_vel = 0
                        val_pos = fval
                else:
                    # If not, update its vel according to its acc and its pos
                    # according to its vel.
                    # Note that implicit or "uncontrolled" flows like this have
                    # different semantics from default flows like "y'' = gravity"!
                    # val_acc = val_acc
                    val_vel = val_vel + val_acc * dt
                    val_pos = val_pos + val_vel * dt
                val.variables[pos.name] = val_pos
                val.variables[vel.name] = val_vel
                val.variables[acc.name] = val_acc

class InputTheory(object):
    __slots__ = ["pressed", "on", "released"]
    def __init__(self):
        self.pressed = set()
        self.on = set()
        self.released = set()
    def update(self, inputs, dt):
        # update on, off, pressed, released accordingly
        buttons = set(inputs)
        # clear pressed and released
        self.pressed.clear()
        self.released.clear()
        # move ON to RELEASED if not in buttons
        for b in self.on:
            if not (b in buttons):
                self.released.add(b)
        for b in self.released:
            self.on.remove(b)
        # put new buttons into PRESSED and ON
        for b in buttons:
            self.pressed.add(b)
            self.on.add(b)
    # TODO: Handle players
    def is_pressed(self, player, button):
        return button in self.pressed
    def is_on(self, player, button):
        return button in self.on
    def is_off(self, player, button):
        return not self.is_pressed(player, button)
    def is_released(self, player, button):
        return button in self.released

class CollisionTheory(object):
    __slots__ = ["contacts", "dynamic_colliders", "static_colliders",
                 "types", "blocking_types", "nonblocking_types"]
    def __init__(self, types, blocking, nonblocking):
        self.contacts = []
        self.static_colliders = []
        self.dynamic_colliders = []
        self.types = types
        self.blocking_types = blocking
        self.nonblocking_types = nonblocking
    # TODO: Later, use some kind of grid for dynamic stuff instead of a list.
    def add_static_collider(self, col):
        self.static_colliders.append(col)
    def add_dynamic_collider(self, col):
        self.dynamic_colliders.append(col)
    def remove_static_collider(self, col):
        self.static_colliders.remove(col)
    def remove_dynamic_collider(self, col):
        self.dynamic_colliders.remove(col)
    def update(self, val, dt):
        # Find all contacts.
        for col in self.dynamic_colliders:
            for col2 in self.dynamic_colliders:
                if col == col2: continue
                self.update_collision(col, col2)
            for s in self.static_colliders:
                self.update_collision_static(col, s)
        # For every contact between blocking types, clear velocities and do restitution.
        for c in self.contacts:
            if self.blocking_contact(c):
                if c.normal[0] != 0:
                    c.a_owner.variables["x'"] = 0
                if c.normal[1] != 0:
                    c.a_owner.variables["y'"] = 0
                ox, oy = c.a_restitution
                c.a_owner.variables["x"] += ox
                c.a_owner.variables["y"] += oy
    # THIS IS FEelING GROSS, see notes from plane
    def update_collison(self):
        pass
    def update_collision_static(self):
        pass
    def get_contacts(self, val, self_type, normal_check, other_type):
        # Return contacts between blocking and nonblocking types.
        # When a collision happens, we put both directions into the contacts list.
        return [c for c in self.contacts 
                if (self_type in c.a_types and 
                    other_type in c.b_types and 
                    c.normal == normal_check)]
    def count_contacts(self, val, self_type, normal_check, other_type):
        return len(self.get_contacts(val, self_type, normal_check, other_type))

raw_automaton = xml.parse_automaton("resources/flappy.char.xml")
automaton = translate_automaton(raw_automaton)
{v:str(k) for k, v in automaton.ordering.items()}.values()

dt = 1.0/60.0
history = []
world = World([automaton])
valuation = world.make_valuation(automaton.name, {}, {"x":32, "y":32})
for steps in [(60, []), (60, ["flap"]), (60, [])]:
    for i in range(steps[0]):
        step(world, steps[1], dt)
        history.append(world.valuations[0][0].variables["y"])

plt.plot(history)
plt.gca().invert_yaxis()
plt.savefig('ys')
print history
