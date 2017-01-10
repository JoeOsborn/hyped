"""HyPED 2 "Flattening" Python interpreter.

Author: Joseph C. Osborn
E-mail: jcosborn@ucsc.edu"""


import xmlparser as xml
import schema as h
from collections import namedtuple
import BitVector as bv
import vectormath as vm
import matplotlib
matplotlib.use('Agg')

"""
# The Interpreter

## Objective

Given an automaton defined by the ~schema~ module, we have a few
options: for example, we could transform it into some more efficiently
executable formalism, we could interpret it directly, or we could
translate it to C.  The object-oriented interpreter seems like a
natural step, but the graph structure induces a fair number of
challenges around maintaining certain runtime invariants, and things
would quickly get tedious in Python (Visitors everywhere).  It's a
little too much ceremony.  So for this interpreter, I'd like to take
advantage of the structure of the problem and explore an approach that
might be able to take advantage of numpy or be translated to C.

The key insight is that we know all the modes of an automaton in
advance of trying to execute it, so we can use information about that
fixed structure to optimize our representation both for simplicity and
speed.  The specific move we make is to number each mode and group in
a depth-first order, which lets us easily go between mode definitions
and numerically indexed arrays.  Automata usually have fairly few
distinct modes, and numbering them all lets us easily scan through
them without chasing pointers everywhere.

## Definitions

Let an automaton be as in ~schema.py~, a tree of groups and modes
along with a set of global default flows, a set of continuous
variables and a set of discrete variables (not yet implemented), and a
set of parameters which are fixed once the automaton is initialized.
A group is a collection of modes and a mode is a collection of groups
along with a set of flows and edges.  A mode defines a set of flows
and a set of transitions (or /edges/).  Flows choose a continuous
variable, the degree to control it by (i.e. its position, velocity, or
acceleration), and a constant value to force that effect.  Flows in
child states on the same variable override those of parent states
which override those of the automaton root; note that this means an
acceleration flow in a child could override a velocity flow in the
parent or vice versa.

We can load up an automaton from some XML like so:

'''
raw_automaton = xml.parse_automaton("resources/flappy.char.xml")
'''

A valuation is a set of assignments to parameters and variables (which
we will optimize later), along with an active set.  The obvious
implementation of the active set would be as a set or a dict mapping
qualified mode names to runtime data, or perhaps a tree of active
groups and modes.  This requires lots of pointer chasing and
reorganizing data structures, which is unnecessary given that the
number of modes and groups in an automaton is small, fixed, and known
a priori.  So we use an array for the active set whose indices can be
known in advance.  The next section describes how we approach this
problem.

## Constraints

Without loss of generality, let us restrict our attention to automata
with only top-level parallelism, i.e. every non-root mode has at most
one group.  This simplifies the transition semantics since we can say
that an edge may only point to a mode which is a child of the same
root group.  To further simplify the interpreter, it will be useful to
define a total order over all the groups and modes of an automaton;
let's say that the order is the preorder traversal order, so all
parent modes are visited before their child modes.  We'll introduce
new types for the interpreter (while leaving the automaton definition
alone) to track a mode's ordering and its number of descendants (to
aid in efficiently implementing transitions) along with some useful
pre-calculated mode sets.  We will also replace the ~qualified_target~
and ~mode~ properties of edges and certain guards respectively to use
these indices instead of qualified names.
"""


OrderedAutomaton = namedtuple(
    "OrderedAutomaton",
    h.Automaton._fields + ("ordering", "ordered_modes"))

OrderedMode = namedtuple(
    "OrderedMode",
    h.Mode._fields + ("index", "descendant_count",
                      "ancestor_set", "descendant_set",
                      "self_set"))

OrderedEdge = namedtuple(
    "OrderedEdge",
    h.Edge._fields + ("target_index",))

"""In our semantics, transitions of a parent mode are taken at a
higher priority than transitions of a child mode, so this ordering
lets us enforce that by taking a linear scan of an array of active
modes.  We also want to be sure that joint transitions are always to a
mode of a different group and that this joint transition relation has
no cycles.  This is more cautious than we strictly need to be but it
simplifies the code.  We define a ~translate_automaton~ function to
convert a "stock" automaton into one that has the required ordering
(or throw an error if this is not possible)."""


def translate_automaton(aut):
    group_deps, ordered_list = safe_ordered_mode_list(aut.groups)
    ordering = {qn: num for num, qn in enumerate(ordered_list)}
    translated_modes = []
    for modename in ordered_list:
        m = modename.mode_in(aut.groups)
        tmode = translate_mode(m, ordering)
        translated_modes.append(tmode)
    props = aut._asdict()
    props["ordering"] = ordering
    props["ordered_modes"] = translated_modes
    return OrderedAutomaton(**props)


"""First, we want to order the modes properly.  We begin by finding
the group dependencies and then pick a group ordering that satisfies
them, if that's possible.  Finally, we build a flat mode list in the
safe order and return the group dependencies and mode ordering.
~schema.flat_modes~ accepts any dict of groups as an argument, so we
pass just one group at a time to build the ideal mode order."""


def safe_ordered_mode_list(groups):
    group_deps = group_dependencies(groups)
    ordered_groups = order_groups(groups, group_deps)
    ordered_list = []
    for g in ordered_groups:
        ordered_list.extend(h.flat_modes({g: groups[g]}))
    return (group_deps, ordered_list)


"""Group dependencies are found by iterating through all the
descendant modes of every root group and determining the dependencies
of guards of edges of modes of that group (phew).  The relation is
one-to-many and binary, so we store it as a dictionary from group IDs
to sets of group IDs."""


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


"""Once we have a group dependency relation, we can find an ordering.
We start by putting all the root groups in their default order into a
queue (implemented as an array).  Until that queue is empty (or until
we've made too many trips through the queue without solving the
constraints), we pop its first element and see if its dependencies are
satisfied by the groups currently in the safe ordering; of course a
group with no dependencies is trivially satisfied.  If the
dependencies are not met, we throw it back into the queue; otherwise,
we append it to the safe ordering."""


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


"""Finally, we define algorithms for finding the dependencies of a
guard or finding a path through that dependency relation."""


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
    if a in stack:
        return False
    # find self-cycles
    if a == b:
        return True
    # find one-step cycles
    if b in deps[a]:
        return True
    # recurse for each dep, adding a to stack to avoid non-simple cycles.
    for mid in deps[a]:
        if dep_path(mid, b, deps, stack | a):
            return True
    # otherwise: no cycle!
    return False


"""Recall that once we have the safe mode ordering, we can translate
the modes of the automaton (and the guards of their edges) and store
their indices and other useful information according to that ordering.
Guard translation is just replacing mode references with mode indices.
Mode traslation also includes translating edges and caching some
useful sets."""


def translate_guard(g, ordering):
    if isinstance(g, h.GuardConjunction):
        return g._replace(conjuncts=[translate_guard(gc, ordering)
                                     for gc in g.conjuncts])
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
    props["ancestor_set"] = qname_to_ancestors(
        m.qualified_name, ordering, include_self=False)
    props["descendant_set"] = mode_set(
        start=modenum, count=descendant_count, order=ordering)
    props["self_set"] = mode_set(start=modenum, count=1, order=ordering)
    return OrderedMode(**props)


"""At this point, we ought to give a definition of a "mode set" in
this indexed regime.  We'll define mode sets as bitvectors, and
provide a convenience instructor given an ordering dict.  We also
provide a quick way to get all the ancestors of a qualified mode
name."""


def mode_set(start=None, count=1, order=None):
    bvec = bv.BitVector(size=len(order))
    # Not sure this is the most efficient way!
    if not (start is None):
        for v in range(start, start + count):
            bvec[v] = 1
    return bvec


def qname_to_ancestors(qname, ordering, include_self=False):
    ms = mode_set(order=ordering)
    if not include_self:
        qname = qname.parent_mode
    while qname is not None:
        ms[ordering[qname]] = 1
        qname = qname.parent_mode
    return ms


# TODO: change it so the world initializer does the transformation
# when it sets up theories.

"""To wrap things up, let's look at usage.  To translate the automaton
we loaded earlier, we can write:

'''
automaton = translate_automaton(raw_automaton)
{v:str(k) for k, v in automaton.ordering.items()}.values()
'''
"""


"""## Valuations

Recall that a valuation is an active mode set, an assignment to
parameters, and an assignment to variables.  We'll put potentially
many of these valuations inside of a World with theory-specific data,
where theories are things like user input, collisions, et cetera.
Valuations are ordered and grouped according to their automaton (to
which they store an index handle)."""


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
        self.automata_indices = {a.name: i for i, a in enumerate(automata)}
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
        self.collision = CollisionTheory([], [], [])


"""Calling ~make_valuation~ is relatively straightforward, especially
when using default initializers:

'''
world = World([automaton])
valuation = world.make_valuation(automaton.name, {}, {"x":32, "y":32})
'''

The main operations we want to perform on valuations are to effect
continuous flows, discrete jumps, and theory updates.  For simplicity,
this interpreter will use a fixed timestep and update the input
theory, the discrete state, the continuous state, and the collision
theory, in that order.
"""


def step(world, input_data, dt):
    world.theories.input.update(input_data, dt)
    discrete_step(world)
    # flows = flows_from_has(world)
    # continuous_step(world, flows, dt)
    continuous_step(world, dt)
    # Need a way to avoid allocating colliders every frame, but I
    # don't know that I want to have [[[collider]]] lists or attach
    # collider objects to valuations.  Ideally we have references from
    # valuations to colliders (to query contacts, but maybe we can
    # iterate contacts and use the backlinks instead; also to turn
    # colliders on and off) and from colliders to valuations (to
    # determine restitution adjustments).  Because we have the option
    # of iterating contacts to check collisions, which we probably
    # ought to do anyway (?), we may be in better shape.  We can even
    # use the link from colliders to valuations to apportion contacts
    # to specific valuations in one go.  but turning colliders on and
    # off seems tough unless they always exist and then check their
    # guards on their own.  that seems fine.  so let's create
    # colliders when we create the valuation, point the collider back
    # to the valuation, and update colliders' position and on/off
    # statuses after the continuous step.  making new valuations and
    # thus colliders is easy, updating colliders is not too bad,
    # removing valuations and thus colliders is OK but we need to
    # update the backlinks when the valuation moves.  the backlink
    # should also be a [index, index] pair or else colliders should be
    # grouped by automaton type.  leaning towards the former, since
    # the valuation accessor doesn't matter at all to the collision
    # logic probably.

    # colliders = colliders_from_has(world) # or something
    # world.theories.collision.update(world, dt)


"""## Interpreting automata

### Discrete step

The discrete step is tricky!  It has two main jobs: determining
whether any edges of active modes can be taken, and then actually
performing those transitions.  These are separated because each edge
evaluation needs to be done with the same valuation data, and we may
have parallel composition of modes.
"""


def discrete_step(world):
    for vals in world.valuations:
        for val in vals:
            exit_set, enter_set, updates = determine_available_transitions(
                world, val)
            # Perform the transitions and updates.  This is where the bitmask
            # representation pays off!
            val.active_modes &= ~exit_set
            val.active_modes |= enter_set
            # Apply all the updates at once.
            for uk, uv in updates.items():
                val.variables[uk] = uv


"""To find available transitions, we iterate through every mode in the
safe ordering.  If that mode has an edge with a satisfied guard, we
take that edge and skip the rest of the mode's edges and its
descendants.  The edge's update dictionary is merged with the net
update dictionary (these updates may include functions of variables,
so we have to evaluate them explicitly).  Any possible conflicts
between updates should have been handled at automaton creation time,
as would any invalid edges (e.g., transitions from a parent to its own
child).
"""


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
                    # Each time we get a new mask, update the valuation's
                    # exited and entered modes.
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


"""Updating ~enter_set~ and ~exit_set~ is a bit subtle, since 1.) we
may be going from a mode to one of its ancestors or their siblings,
and 2.) when entering a mode we also need to enter the appropriate
sub-mode (recursively).  Adding to ~exit_set~ is relatively easy,
since we can mask in all of the source mode's ancestors and
descendants and mask out any of those which are common ancestors with
the destination mode.  ~enter_set~ requires a loop to do properly; as
it turns out, we need this same sort of loop when initializing a
valuation's active set, so we can explore that here as well."""


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
        # Handle the case where we're only looking for descendants of a
        # particular mode
        mask = mode.ancestor_set | mode.self_set
        mi = mode.index
        mlim = mi + mode.descendant_count
    # TODO: Use entry edges to determine which mode to start in.
    # May involve enters/exits, val, and maybe world being passed into this
    # function!
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


"""Guards are a restricted class of predicate which, ideally, we would
compile using sympy or some other method.  For now, we'll interpret
them.  Recall that ~mode~ properties of guards have been replaced by
canonical indices at this point."""


def eval_guard(guard, world, val):
    if isinstance(guard, h.GuardConjunction):
        result = True
        for c in guard.conjuncts:
            # TODO: If evaluation needs a context (e.g. bindings), pass result
            # as well
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
            return world.theories.input.is_pressed(guard.playerID,
                                                   guard.buttonID)
        elif guard.status == "on":
            return world.theories.input.is_on(guard.playerID,
                                              guard.buttonID)
        elif guard.status == "off":
            return world.theories.input.is_off(guard.playerID,
                                               guard.buttonID)
        elif guard.status == "released":
            return world.theories.input.is_released(guard.playerID,
                                                    guard.buttonID)
        else:
            raise ValueError("Unrecognized status", guard)
    else:
        raise ValueError("Unrecognized guard", guard)


"""Expressions, like guards, ought to be compiled.  For now we accept
only a very limited set and interpret them.
"""


def eval_value(expr, world, val):
    if isinstance(expr, h.ConstantExpr):
        return expr.value
    elif isinstance(expr, h.Parameter):
        return eval_value(expr.value, world, val)
    else:
        raise ValueError("Unhandled expr", expr)


"""### Continuous step

The continuous step applies accelerations and velocities to update
continuous variables.  The complexity comes in properly stacking and
giving precedence to the various currently active modes.  We can
assume that no two potentially simultaneously active modes of
different groups conflict on flows, and we can assert that flows of
children supersede flows of parents.  These two rules suffice to
prevent all conflicts and admit a relatively simple definition of
continuous steps, though one that could probably be improved by
incorporating something like numpy and finding a nice matrix
multiplication encoding.
"""

# TODO: Explain this better once it's rewritten and variable storage is
# rewritten.  This should be doable without any allocations at all.


def continuous_step(world, dt):
    for i, vals in enumerate(world.valuations):
        for val in vals:
            aut = world.automata[i]
            flows = {}
            # TODO: Ordering variables would give us a way around
            # using dicts here.  We could store [v1, v1', v1'', v2,
            # v2', v2'', ...]  Let's revisit it once we have a better
            # representation for variable storage.  Even namedtuples
            # (one per HA type) would be an improvement.  pos, vel,
            # and acc vbls could be stored separately.
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
                    # If so, update its vel or acc according to the
                    # flow, set any higher degrees to 0, and update
                    # lower degrees as above (acc->vel, vel->pos).
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
                    # different semantics from default flows like
                    # "y'' = gravity"!

                    # val_acc = val_acc
                    val_vel = val_vel + val_acc * dt
                    val_pos = val_pos + val_vel * dt
                val.variables[pos.name] = val_pos
                val.variables[vel.name] = val_vel
                val.variables[acc.name] = val_acc


"""### Input theory

For now we're just looking at a digital binary input theory, where
individual buttons can be on or off and spend one frame in the pressed
and released states respectively when transitioning from one to the
other.
"""


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


"""### Collision theory

For now, we'll only consider collision of boxes and tilemaps.
Each character is made of colliders, which we tell the
collision theory about when characters are created or destroyed.
Colliders may be active or inactive, but we'll let the collision
theory know about them all whether they're active or not.  Collisions
between colliders with given type tags can be blocking or
non-blocking, but by default no tags collide with each other."""


class CollisionTheory(object):
    __slots__ = ["contacts",
                 "types", "blocking", "touching"]

    def __init__(self, types, blocking_pairs, nonblocking_pairs):
        self.contacts = []
        # TODO: use bitvectors here too. give an index to each type in types,
        # pairs should be inspected and turned into masks.
        self.blocking = blocking_pairs
        self.touching = nonblocking_pairs

    def update(self, old_contacts, colliders, out_contacts, dt):
        # Find all contacts.  Note that colliding with a tilemap
        # may produce many contacts!
        # TODO: spatial partition
        for coli in range(len(colliders)):
            col = colliders[coli]
            if col.is_static:
                continue
            for col2i in range(coli + 1, len(colliders)):
                col2 = colliders[col2i]
                if self.collidable_typesets(col.types, col2.types):
                    self.check_contacts(col, col2, out_contacts)
        self.contacts = out_contacts

    def get_contacts(self, key, self_type, normal_check, other_type):
        # Return contacts between blocking and nonblocking types.
        return [c for c in self.contacts
                if ((c.a_key == key and
                     self_type in c.a_types and
                     other_type in c.b_types and
                     c.normal == normal_check) or
                    (c.b_key == key and
                     self_type in c.b_types and
                     other_type in c.a_types and
                     (-c.normal) == normal_check))]

    def count_contacts(self, key, self_type, normal_check, other_type):
        return len(self.get_contacts(key, self_type, normal_check, other_type))

    def collidable_typesets(self, t1s, t2s):
        return (self.blocking_typesets(t1s, t2s) or
                self.touching_typesets(t1s, t2s))

    def blocking_typesets(self, t1s, t2s):
        # do any types in t1s block any types in t2s or vice versa?
        for i in range(0, len(t1s)):
            if self.blocking[i] & t2s:
                return True
        return False

    def touching_typesets(self, t1s, t2s):
        for i in range(0, len(t1s)):
            if self.touching[i] & t2s:
                return True
        return False

    def check_contacts(self, col, col2, cs):
        if isinstance(col.shape, Rect) and isinstance(col2.shape, TileMap):
            assert col2.is_static
            vx1 = col.nx - col.px
            x1 = col.nx
            vy1 = col.ny - col.py
            y1 = col.ny
            xw1 = col.x1 + col.shape.w
            yh1 = col.y1 + col.shape.h
            c1hw = col.shape.w / 2.0
            c1hh = col.shape.h / 2.0
            x1c = x1 + c1hw
            y1c = y1 + c1hh
            tox = col2.nx
            toy = col2.ny
            c2hw = col2.shape.tile_width / 2.0
            c2hh = col2.shape.tile_height / 2.0
            # Do the rectangle's corners or any point lining up with the grid
            # touch a colliding tile in the tilemap?
            x1g = quantize(x1 - tox, col2.shape.tile_width)
            xw1g = quantize(xw1 - tox, col2.shape.tile_width) + 1
            y1g = quantize(y1 - toy, col2.shape.tile_height)
            yh1g = quantize(yh1 - toy, col2.shape.tile_height) + 1
            for xi in range(x1g, xw1g):
                for yi in range(y1g, yh1g):
                    if self.collidable_typesets(col.types,
                                                col2.shape.tile_types(xi, yi)):
                        # rect is definitely overlapping tile at xi, yi.
                        # the normal should depend on whether the overlapping
                        # edge of the rect is above/below/left/right of the
                        # tile's center
                        x2c = xi * col2.shape.tile_width + tox + c2hw
                        y2c = yi * col2.shape.tile_height + toy + c2hh
                        # GENERAL CASE separate according to SAT
                        dcx = abs(x2c - x1c)
                        dcy = abs(y2c - y1c)
                        sep = vm.Vector2((c1hw + c2hw) - dcx,
                                         (c1hh + c2hh) - dcy)
                        norm = vm.Vector2(0, 0)
                        # assume sep.x > 0 and sep.y > 0
                        if sep.x < sep.y:
                            sep.y = 0
                            if x1c < x2c:
                                sep.x = -sep.x
                            norm.x = 1 if sep.x > 0 else -1
                        else:
                            sep.x = 0
                            if y1c < y2c:
                                sep.y = -sep.y
                            norm.y = 1 if sep.y > 0 else -1
                        # SPECIAL CASES for rounding corners
                        # about to clear top with a horizontal move, nudge them
                        # up and over to avoid collision
                        if ((vx1 != 0) and yh1 > (y2c - c2hh) and
                            yh1 - (y2c - c2hh) < (c2hh / 4.0) and
                            not self.is_blocking(
                                col.types, col2.shape.tile_types(xi, yi - 1))):
                            # nudge up above
                            sep = vm.Vector2(0, y2c - c2hh - yh1)
                            norm = vm.Vector2(0, -1)
                        # about to clear bottom, nudge them over
                        elif ((vx1 != 0) and y1 < (y2c + c2hh) and
                              (y2c + c2hh) - y1 < (c2hh / 4.0) and
                              not self.is_blocking(
                                  col.types,
                                  col2.shape.tile_types(xi, yi + 1))):
                            # nudge down below
                            sep = vm.Vector2(0, y2c + c2hh - y1)
                            norm = vm.Vector2(0, 1)
                        # about to clear right edge with a vertical move, nudge
                        # them right to avoid collision
                        if ((vy1 != 0) and x1 < (x2c + c2hw) and
                            (x2c + c2hw) - x1 < (c2hw / 4.0) and
                            not self.is_blocking(
                                col.types,
                                col2.shape.tile_types(xi + 1, yi))):
                            sep = vm.Vector2(x2c + c2hw - x1, 0)
                            norm = vm.Vector2(1, 0)
                        # about to clear left edge with a vertical move, nudge
                        # them left to avoid collision
                        elif ((vy1 != 0) and xw1 > (x2c - c2hw) and
                              xw1 - (x2c - c2hw) < (c2hw / 4.0) and
                              not self.is_blocking(
                                  col.types,
                                  col2.shape.tile_types(xi - 1, yi))):
                            sep = vm.Vector2(x2c - c2hw - xw1, 0)
                            norm = vm.Vector2(-1, 0)
                        cs.append(Contact(col.key, col2.key, col.types,
                                          col2.types, sep, norm,
                                          self.is_blocking(col, col2)))
        elif isinstance(col.shape, Rect) and isinstance(col2.shape, Rect):
            # GENERAL CASE separate according to SAT
            c1hw = col.shape.w / 2.0
            c1hh = col.shape.h / 2.0
            c2hw = col2.shape.w / 2.0
            c2hh = col2.shape.h / 2.0
            x1c = col.nx + c1hw
            y1c = col.ny + c1hh
            x2c = col2.nx + c2hw
            y2c = col2.ny + c2hh
            dcx = abs(x2c - x1c)
            dcy = abs(y2c - y1c)
            sep = vm.Vector2((c1hw + c2hw) - dcx, (c1hh + c2hh) - dcy)
            norm = vm.Vector2(0, 0)
            if sep.x < 0 or sep.y < 0:
                return
            if sep.x < sep.y:
                sep.y = 0
                if x1c < x2c:
                    sep.x = -sep.x
                norm.x = 1 if sep.x > 0 else -1
            else:
                sep.x = 0
                if y1c < y2c:
                    sep.y = -sep.y
                norm.y = 1 if sep.y > 0 else -1
            cs.append(Contact(col.key, col2.key, col.types,
                              col2.types, sep, norm,
                              self.is_blocking(col, col2)))


Collider = namedtuple(
    "Collider",
    "key types is_static shape px py nx ny")
Contact = namedtuple(
    "Contact",
    "a_key b_key a_types b_types separation normal")
Rect = namedtuple("Rect", "w h")


def quantize(val, precision):
    return precision * (val // precision)


class TileMap(object):
    __slots__ = ["tile_width", "tile_height", "tile_defs", "tiles"]

    def __init__(self, tw, th, defs, tiles):
        self.tile_width = tw
        self.tile_height = th
        self.tile_defs = defs
        self.tiles = tiles

    def tile_types(self, tx, ty):
        return self.tile_defs[self.tiles[tx, ty]].types


"""# The test case"""


def test():
    import matplotlib.pyplot as plt
    raw_automaton = xml.parse_automaton("resources/flappy.char.xml")
    automaton = translate_automaton(raw_automaton)
    {v: str(k) for k, v in automaton.ordering.items()}.values()

    dt = 1.0 / 60.0
    history = []
    world = World([automaton])
    world.make_valuation(automaton.name, {}, {"x": 32, "y": 32})
    for steps in [(60, []), (60, ["flap"]), (60, [])]:
        for i in range(steps[0]):
            step(world, steps[1], dt)
            history.append(world.valuations[0][0].variables["y"])

    plt.plot(history)
    plt.gca().invert_yaxis()
    plt.savefig('ys')
    print history


test()
