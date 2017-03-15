"""HyPED 2 "Flattening" Python interpreter.

Author: Joseph C. Osborn
E-mail: jcosborn@ucsc.edu"""

import array
import xmlparser as xml
import schema as h
from collections import namedtuple
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
(or throw an error if this is not possible).  At the same time, we
translate guards (both on the automaton's colliders and on the edges
of its modes) and edge targets to use these orderings."""


def translate_automaton(aut):
    assert isinstance(aut, h.Automaton)
    assert not isinstance(aut, OrderedAutomaton)
    group_deps, ordered_list = safe_ordered_mode_list(aut.groups)
    ordering = {qn: num for num, qn in enumerate(ordered_list)}
    translated_modes = []
    for modename in ordered_list:
        m = modename.mode_in(aut.groups)
        tmode = translate_mode(m, ordering)
        translated_modes.append(tmode)
    translated_colliders = []
    for c in aut.colliders:
        translated_colliders.append(
            c._replace(guard=translate_guard(c.guard, ordering, None)))
    props = aut._asdict()
    props["ordering"] = ordering
    props["ordered_modes"] = translated_modes
    props["colliders"] = translated_colliders
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
    elif isinstance(guard, h.GuardDisjunction):
        ret = set()
        for g in guard.disjuncts:
            ret.update(guard_dependencies(g))
        return ret
    elif isinstance(guard, h.GuardNegation):
        ret = set()
        ret.update(guard_dependencies(guard.guard))
        return ret
    elif isinstance(guard, h.GuardJointTransition):
        return set([guard.mode.groups[0]])
    # TODO: GuardCompare in the future? With refs?
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
"""


class GuardTimerIndexed(namedtuple("GuardTimerIndexed",
                                   h.GuardTimer._fields + ("timer_index",)),
                        h.Guard):
    __slots__ = ()


def translate_guard(g, ordering, modenum):
    if isinstance(g, h.GuardConjunction):
        return g._replace(conjuncts=[translate_guard(gc, ordering, modenum)
                                     for gc in g.conjuncts])
    elif isinstance(g, h.GuardDisjunction):
        return g._replace(disjuncts=[translate_guard(gc, ordering, modenum)
                                     for gc in g.disjuncts])
    elif isinstance(g, h.GuardNegation):
        return g._replace(guard=translate_guard(g.guard, ordering, modenum))
    elif isinstance(g, h.GuardJointTransition):
        return g._replace(mode=ordering[g.mode])
    elif isinstance(g, h.GuardInMode):
        return g._replace(mode=ordering[g.mode])
    elif isinstance(g, h.GuardTimer):
        assert modenum is not None
        return GuardTimerIndexed(
            g.threshold,
            g.provenance,
            modenum
        )
    return g


"""Mode translation also includes translating edges along with their guards
and caching some sets (bitmasks) that will be useful later.
"""


def translate_mode(m, ordering):
    modenum = ordering[m.qualified_name]
    if len(m.groups) > 1:
        return "Too many groups in a non-root mode for now!"
    new_edges = []
    descendant_count = len(h.flat_modes(m.groups, m.qualified_name))
    for e in m.edges:
        eprops = e._asdict()
        eprops["target_index"] = ordering[e.qualified_target]
        eprops["guard"] = translate_guard(e.guard, ordering, modenum)
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
provide a convenience constructor given an ordering dict.  We also
provide a quick way to get all the ancestors of a qualified mode
name.
"""


def mode_set(start=None, count=1, order=None):
    bvec = 0  # bv.BitVector(size=len(order))
    # Not sure this is the most efficient way!
    if not (start is None):
        for v in range(start, start + count):
            bvec |= 1 << v
    return bvec


def qname_to_ancestors(qname, ordering, include_self=False):
    ms = mode_set(order=ordering)
    if not include_self:
        qname = qname.parent_mode
    while qname is not None:
        ms |= 1 << ordering[qname]
        qname = qname.parent_mode
    return ms


"""## Runtime data

### Valuations

Recall that a valuation is an active mode set, an assignment to
parameters, and an assignment to variables.  We'll put potentially
many of these valuations inside of a World.  Valuations also have an
identifier that lets us tie them to colliders or other things later
on.  Finally, a valuation stores which states were just entered or
exited to help implement joint transition guards.

Within a Valuation, the set of variables is fixed.  So for efficiency
we store the variables in a canonical ordering so that reads and writes
during the continuous step can avoid dictionary lookups.  Random reads
and writes still incur some lookup and indirection cost, but should be
much less frequent.
"""


class Valuation(object):
    __slots__ = ["automaton_index", "index",
                 "parameters", "variables", "timers",
                 # TODO: These two could live in automaton instead
                 "var_names", "var_mapping",
                 "active_modes",
                 "entered", "exited"]

    def __init__(self, aut, aut_i, i, parameters, variables, active_modes):
        self.automaton_index = aut_i
        self.index = i
        self.parameters = parameters
        sorted_vars = sorted(variables.items(), key=lambda item: item[0])
        self.var_names = map(lambda item: item[0], sorted_vars)
        self.var_mapping = {name: idx
                            for idx, name in enumerate(self.var_names)}
        self.variables = map(lambda item: item[1], sorted_vars)
        self.active_modes = active_modes
        self.timers = array.array('d', [0]*len(aut.ordered_modes))
        self.entered = active_modes
        self.exited = mode_set(order=aut.ordering)

    def get_var(self, vname):
        return self.variables[self.var_mapping[vname]]

    def set_var(self, vname, val):
        self.variables[self.var_mapping[vname]] = val


"""### The world at large

A World manages a list of automata types, valuations (grouped by
automaton), theory data (concerning e.g. user input and collisions),
and active colliders.  Exactly which theories are present is somewhat
dependent on the game, or rather the particular composition of
operational logics at work.  In HyPED 2, we consider character-state
logics (the discrete steps), physics logics (the continuous steps),
collision logics, and input logics for now.  The first two could be
separated out into theories (and indeed probably should be in the
future), but at the moment they are more tightly integrated.

At initialization time, the World also receives a Context, which
carries information on which collision types block each others'
movement, which types should be checked for collisions but don't
impede movement, the initial automata valuations in the world, and
other initialization data.  Honestly, it's a bit of a grab bag for
material that hasn't been fully incorporated into the theory of
operational logics.  Concepts which are yet unimplemented---for
example, persistence logics which determine which objects are active
at which times or within particular scopes like levels---will replace
much of Context in the future.
"""


class Context(object):

    def __init__(self,
                 blocking_types={},
                 touching_types={},
                 static_colliders=[],
                 initial_automata=[]):
        self.blocking_types = blocking_types
        self.touching_types = touching_types
        self.static_colliders = static_colliders
        self.initial_automata = initial_automata


"""During World initialization, we also transform the raw automata
into the ordered format described above.  Then we initialize
operational logic-specific theories, making further changes to the
automata or modifying data in the Context to support each theory.  Our
collision logic of choice uses bitmasks instead of sets of tags, so
this adapts our system to one more easily consumed by the collision
logic.  From this, it should be clear that the ~translate_automaton~
function is in some sense a specially-cased operation for the
character-state and physics logics, and could be refactored cleanly
into Theories with some work.
"""


class World(object):
    __slots__ = ["context", "theories", "automata",
                 "automata_indices", "valuations", "colliders"]

    def __init__(self, raw_automata, context):
        automata = [translate_automaton(ra) for ra in raw_automata]
        (theories, automata, context) = init_theories(automata, context)
        self.context = context
        self.theories = theories
        self.automata_indices = {a.name: i for i, a in enumerate(automata)}
        self.automata = automata
        self.valuations = [[] for a in automata]
        self.colliders = []
        for ia in self.context.initial_automata:
            self.make_valuation(*ia)

    def make_valuation(self, automaton_name, init_params={}, vbls={}):
        assert automaton_name in self.automata_indices
        aut_i = self.automata_indices[automaton_name]
        aut = self.automata[aut_i]
        params = {pn: p.value.value for pn, p in aut.parameters.items()}
        vars = {vn: v.init.value for vn, v in aut.variables.items()}
        params.update(init_params)
        vars.update(vbls)
        initial_modes = initial_mask(aut)
        idx = len(self.valuations[aut_i])
        val = Valuation(aut, aut_i, idx, params, vars, initial_modes)
        self.valuations[aut_i].append(val)

        """
        When we create a Valuation, we add it to the appropriate group and
        additionally create a Collider for each schema Collider definition in
        the automaton.  Colliders at runtime will be discussed in more detail
        in the Collision Theory section.  The key remark to make at this time
        is that each Collider has a key pointing to its owner, which is opaque
        to the collision logic but is used during queries.

        Note that when removing valuations is implemented, these links
        will have to be repaired in the Colliders, in any Contacts
        referring to them, and likely by re-compacting/shifting down the
        indices of existing Valuations.
        """

        for ci, c in enumerate(aut.colliders):
            assert isinstance(c.shape, h.Rect)
            x = val.get_var("x")
            y = val.get_var("y")
            ox = eval_value(c.shape.x, self, val)
            oy = eval_value(c.shape.y, self, val)
            self.colliders.append(
                Collider((val.automaton_index, idx, ci),
                         c.types,
                         eval_guard(c.guard, self, val),
                         False,
                         Rect(eval_value(c.shape.w, self, val),
                              eval_value(c.shape.h, self, val)),
                         x + ox, y + oy, x + ox, y + oy))
        return val

"""~Theories~ is just a tidy container for the OL-specific theories."""
Theories = namedtuple("Theories", "input collision")


def init_theories(automaton_specs, context):
    input = InputTheory()
    # Replace collision tags on colliders and guards with bitmasks.
    # Update context with relevant mappings/orderings.
    (translated, context) = translate_for_collision(automaton_specs, context)
    collision = CollisionTheory(context.collider_type_names,
                                context.blocking_types,
                                context.touching_types)
    return (Theories(input, collision), translated, context)


"""
Now, we can finally make a World and Valuation:

'''
world = World([automaton], Context(...))
world.make_valuation(automaton.name, {}, {"x":32, "y":32})
'''

The main operations we want to perform on valuations (in fact, on the
world as a whole) are to effect continuous flows, discrete jumps, and
theory updates.  For simplicity, this interpreter will use a fixed
timestep and update the input theory, the discrete state, the
continuous state, and the collision theory, in that order.
"""


def step(world, input_data, dt):
    world.theories.input.update(input_data, dt)
    # update envelope state before, after, or inside of discrete step?
    # do envelopes need any runtime state maintenance (i.e. any discrete step) or can we know just from button, guard, and variable values?
    discrete_step(world)
    # flows = flows_from_has(world)
    # continuous_step(world, flows, dt)
    continuous_step(world, dt)
    for c in world.colliders:
        aut_def = world.automata[c.key[0]]
        val = world.valuations[c.key[0]][c.key[1]]
        col_def = aut_def.colliders[c.key[2]]
        c.is_active = eval_guard(col_def.guard, world, val)
        c.px = c.nx
        c.py = c.ny
        c.nx = val.get_var("x") + eval_value(col_def.shape.x, world, val)
        c.ny = val.get_var("y") - eval_value(col_def.shape.y, world, val)
        if isinstance(c.shape, Rect):
            c.shape.w = eval_value(col_def.shape.w, world, val)
            c.shape.h = eval_value(col_def.shape.h, world, val)
        # TODO other shapes
    new_contacts = []
    world.theories.collision.update(([c for c in world.colliders
                                      if c.is_active] +
                                     world.context.static_colliders),
                                    new_contacts,
                                    dt)
    do_restitution(world, new_contacts)

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
                val.set_var(uk, uv)


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
        if active & (1 << mi):
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
        mlim = len(modes)
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
            mask |= 1 << mi
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
            if result == 0:
                return False
        return result
    elif isinstance(guard, h.GuardDisjunction):
        result = False
        for c in guard.disjuncts:
            # TODO: If evaluation needs a context (e.g. bindings), pass result
            # as well
            result = result | eval_guard(c, world, val)
            if result == 1:
                return True
        return result
    elif isinstance(guard, h.GuardNegation):
        return not eval_guard(guard.guard, world, val)
    elif isinstance(guard, h.GuardTrue):
        return True
    elif isinstance(guard, h.GuardInMode):
        assert guard.character is None
        return (val.active_modes & (1 << guard.mode)) != 0
    elif isinstance(guard, h.GuardJointTransition):
        assert guard.character is None
        if guard.direction == "enter":
            return val.entered & (1 << guard.mode)
        elif guard.direction == "exit":
            return val.exited & (1 << guard.mode)
        else:
            raise ValueError("Unrecognized direction", guard)
    elif isinstance(guard, h.GuardColliding):
        # TODO: avoid tuple creation
        return 0 < world.theories.collision.count_contacts(
            (val.automaton_index, val.index),
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
    elif isinstance(guard, GuardTimerIndexed):
        threshold = eval_value(guard.threshold, world, val)
        timer_value = val.timers[guard.timer_index]
        return timer_value >= threshold
    elif isinstance(guard, h.GuardCompare):
        left = eval_value(guard.left, world, val)
        right = eval_value(guard.right, world, val)
        op = guard.operator
        if op == "=":
            return left == right
        elif op == ">=":
            return left >= right
        elif op == ">":
            return left > right
        elif op == "<=":
            return left <= right
        elif op == "<":
            return left < right
        else:
            raise ValueError("Unrecognized comparator", guard)
    else:
        raise ValueError("Unrecognized guard", guard)


"""Expressions, like guards, ought to be compiled.  For now we accept
only a very limited set and interpret them.
"""


def eval_value(expr, world, val):
    # in the future:
    # expr(world, val)
    if isinstance(expr, h.ConstantExpr):
        return expr.value
    elif isinstance(expr, h.Parameter):
        return eval_value(expr.value, world, val)
    elif isinstance(expr, h.Variable):
        # TODO: maybe there's a faster path by
        #  tagging with the variable index earlier?
        return val.get_var(expr.name)
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


def continuous_step(world, dt):
    for i, vals in enumerate(world.valuations):
        for val in vals:
            aut = world.automata[i]
            flows = {}
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
                if active & (1 << mi) == 0:
                    mi += modes[mi].descendant_count
                    val.timers[mi] = 0.0
                else:
                    val.timers[mi] += dt
                    for f in modes[mi].flows.values():
                        fvar = f.var
                        fvalexpr = f.value
                        fval = eval_value(fvalexpr, world, val)
                        flows[fvar.basename] = (fvar, fval)
                    # apply active envelope flows too
                    # TODO: document and also extract into another function?
                    for e in modes[mi].envelopes:
                        # TODO: generalize to N ways, different ADSR functions, etc.
                        assert e.reflections == 2
                        axis_value = world.theories.input.get_axis(
                            e.axes[0][0], e.axes[0][1]
                        )
                        variable = e.variables[0]
                        cur_value = val.variables[
                            val.var_mapping[variable.name]
                        ]
                        target_value = cur_value
                        guard = e.invariant
                        guard_ok = eval_guard(guard, world, val)
                        dir = 1
                        if axis_value < 0:
                            dir = -1
                        if guard_ok and axis_value != 0:
                            # A[D]S
                            sustain_lev = eval_value(
                                e.sustain[1],
                                world,
                                val
                            ) * dir
                            if (((dir == 1 and cur_value < sustain_lev) or
                                 (dir == -1 and cur_value > sustain_lev))):
                                # A
                                # accelerate value towards sustain_lev
                                # by ev(e.attack[1])
                                acc = eval_value(e.attack[1], world, val) * dir
                                target_value = cur_value + acc * dt
                                if dir == -1 and target_value < sustain_lev:
                                    target_value = sustain_lev
                                elif dir == 1 and target_value > sustain_lev:
                                    target_value = sustain_lev
                            elif ((dir == 1 and cur_value > sustain_lev) or
                                  (dir == -1 and cur_value < sustain_lev)):
                                # D?
                                # fix value to sustain_lev
                                target_value = sustain_lev
                            elif cur_value == sustain_lev:
                                # S, do nothing
                                target_value = cur_value
                            else:
                                assert False
                        else:
                            # R
                            if e.release[0] == "hold":
                                # Do nothing, flow = 0
                                target_value = 0
                            elif e.release[0] == "acc":
                                # Accelerate towards e.release[2]
                                # by e.release[1]
                                acc = eval_value(
                                    e.release[1],
                                    world,
                                    val
                                )
                                target = eval_value(
                                    e.release[2],
                                    world,
                                    val
                                )
                                if cur_value > target:
                                    acc = -acc
                                target_value = cur_value + acc * dt
                                if acc > 0 and target_value > target:
                                    target_value = target
                                elif acc < 0 and target_value < target:
                                    target_value = target
                            elif e.release[0] == "set":
                                # fix value to e.release[1]
                                target_value = eval_value(
                                    e.release[1],
                                    world,
                                    val
                                )
                            else:
                                assert False, str(e.release)
                        # control variable = target_value
                        flows[variable.basename] = (variable, target_value)
                mi += 1
            val_vbls = val.variables
            for vi in range(0, len(val_vbls), 3):
                vname = val.var_names[vi]
                val_pos = val_vbls[vi]
                val_vel = val_vbls[vi + 1]
                val_acc = val_vbls[vi + 2]
                # see if it's in the flow dict.
                if vname in flows:
                    # If so, update its vel or acc according to the
                    # flow, set any higher degrees to 0, and update
                    # lower degrees as above (acc->vel, vel->pos).
                    (fvar, fval) = flows[vname]
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
                val_vbls[vi] = val_pos
                val_vbls[vi + 1] = val_vel
                val_vbls[vi + 2] = val_acc


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

    # TODO: generalize
    def get_axis(self, player, axis):
        assert axis == "x"
        if self.is_on(player, "left"):
            return -1
        if self.is_on(player, "right"):
            return 1
        return 0


"""### Collision theory

For now, we'll only consider collision of boxes and tilemaps.
Each character is made of colliders, which we tell the
collision theory about when characters are created or destroyed.
Colliders may be active or inactive, but we'll let the collision
theory know about them all whether they're active or not.  Collisions
between colliders with given type tags can be blocking or
non-blocking, but by default no tags collide with each other.

Later, the CollisionTheory class will likely be moved to another file,
while the ~translate_for_collision~ function should remain here.
"""


def translate_for_collision(automata_specs, context):
    # Make sure every blocking/touching relationship is commutative.
    # It suffices to add C to the set of blockers of each thing it's
    # blocked by.
    mirror_relation(context.blocking_types)
    mirror_relation(context.touching_types)
    # Gather up all collider types
    all_tags = set()
    for c in context.static_colliders:
        all_tags |= c.types
        if isinstance(c.shape, TileMap):
            for d in c.shape.tile_defs:
                all_tags |= d
    for a in automata_specs:
        for c in a.colliders:
            all_tags |= c.types
    for t, ts in (context.blocking_types.items() +
                  context.touching_types.items()):
        all_tags |= set([t])
        all_tags |= set(ts)
    sorted_tags = list(all_tags)
    sorted_tags.sort()
    for t in sorted_tags:
        if t not in context.blocking_types:
            context.blocking_types[t] = []
        if t not in context.touching_types:
            context.touching_types[t] = []
    context.collider_types = {t: ti for ti, t in enumerate(sorted_tags)}
    context.collider_type_names = sorted_tags
    context.blocking_types = {
        context.collider_types[t]: types_to_bv(context.collider_types, ts)
        for t, ts in context.blocking_types.items()}
    context.touching_types = {
        context.collider_types[t]: types_to_bv(context.collider_types, ts)
        for t, ts in context.touching_types.items()}
    # These are concrete colliders so we can just modify them in-place.
    for c in context.static_colliders:
        c.types = types_to_bv(context.collider_types, c.types)
        if isinstance(c.shape, TileMap):
            c.shape.tile_defs = [types_to_bv(context.collider_types, td)
                                 for td in c.shape.tile_defs]
    automata = []
    for a in automata_specs:
        # These colliders are "schema colliders", not concrete ones
        new_colliders = [
            c._replace(types=types_to_bv(context.collider_types, c.types))
            for c in a.colliders]
        new_modes = [
            m._replace(edges=[
                e._replace(guard=translate_guard_collider_types(
                    context.collider_types,
                    e.guard))
                for e in m.edges])
            for m in a.ordered_modes]
        automata.append(a._replace(
            colliders=new_colliders,
            ordered_modes=new_modes))
    return (automata, context)


def types_to_bv(mapping, ts):
    vec = 0  # bv.BitVector(size=len(mapping))
    for t in ts:
        if t in mapping:
            vec |= 1 << mapping[t]
    return vec


def types_bv_any(mapping):
    return int((2 ** len(mapping)) - 1)


def translate_guard_collider_types(mapping, g):
    if isinstance(g, h.GuardConjunction):
        return g._replace(
            conjuncts=[translate_guard_collider_types(mapping, gi)
                       for gi in g.conjuncts])
    elif isinstance(g, h.GuardDisjunction):
        return g._replace(
            disjuncts=[translate_guard_collider_types(mapping, gi)
                       for gi in g.disjuncts])
    elif isinstance(g, h.GuardNegation):
        return g._replace(guard=translate_guard_collider_types(mapping,
                                                               g.guard))
    elif isinstance(g, h.GuardColliding):
        return g._replace(
            self_type=(types_bv_any(mapping)
                       if g.self_type is None
                       else types_to_bv(mapping, [g.self_type])),
            other_type=(types_bv_any(mapping)
                        if g.other_type is None
                        else types_to_bv(mapping, [g.other_type])))
    else:
        return g


def mirror_relation(rel):
    for c, cs in rel.items():
        for c2 in cs:
            if c2 not in rel:
                rel[c2] = []
            # if c is not already in rel[c2]:
            found = False
            for c3 in rel[c2]:
                if c3 == c2:
                    found = True
            if not found:
                rel[c2].append(c)


class CollisionTheory(object):
    __slots__ = ["contacts",
                 "types", "blocking", "touching"]

    def __init__(self, type_names, blocking_pairs, nonblocking_pairs):
        self.types = type_names
        self.contacts = []
        self.blocking = blocking_pairs
        self.touching = nonblocking_pairs

    def update(self, colliders, out_contacts, dt):
        # Find all contacts.  Note that colliding with a tilemap
        # may produce many contacts!
        # TODO: spatial partition
        for coli in range(len(colliders)):
            col = colliders[coli]
            for col2i in range(coli + 1, len(colliders)):
                col2 = colliders[col2i]
                if self.collidable_typesets(col.types, col2.types):
                    self.check_contacts(col, col2, out_contacts)
        self.contacts = out_contacts

    def get_contacts(self, key, self_type, normal_check, other_type):
        # Return contacts between blocking and nonblocking types.
        # TODO: Remove assumption that key is a >=2-tuple
        # TODO: remove some uses of BitVector in favor of plain ints? Maybe
        # just for collision stuff?
        # normal_check
        # print [c for c in self.contacts
        #         if ((c.a_key[0] == key[0] and
        #              c.a_key[1] == key[1] and
        #              (self_type & c.a_types) != 0 and
        #              (other_type & c.b_types) != 0 and
        #              ((not normal_check) or (c.normal[0] == normal_check[0] and c.normal[1] == normal_check[1])))) or
        #             (c.b_key[0] == key[0] and
        #              c.b_key[1] == key[1] and
        #              (self_type & c.b_types) != 0 and
        #              (other_type & c.a_types) != 0 and
        #              ((not normal_check) or (c.normal[0] == -normal_check[0] and c.normal[1] == -normal_check[1])))]

        return [c for c in self.contacts
                if ((c.a_key[0] == key[0] and
                     c.a_key[1] == key[1] and
                     (self_type & c.a_types) != 0 and
                     (other_type & c.b_types) != 0 and
                     (normal_check is not None and c.normal[0] == normal_check[0] and c.normal[1] == normal_check[1])) or
                    (c.b_key[0] == key[0] and
                     c.b_key[1] == key[1] and
                     (self_type & c.b_types) != 0 and
                     (other_type & c.a_types) != 0 and
                     (normal_check is not None and c.normal[0] == -normal_check[0] and c.normal[1] == -normal_check[1])))]

    def count_contacts(self, key, self_type, normal_check, other_type):
        return len(self.get_contacts(key, self_type, normal_check, other_type))

    def collidable_typesets(self, t1s, t2s):
        return (self.blocking_typesets(t1s, t2s) or
                self.touching_typesets(t1s, t2s))

    def blocking_typesets(self, t1s, t2s):
        # do any types in t1s block any types in t2s or vice versa?
        for i in range(0, len(self.types)):
            if t1s & (1 << i) and (self.blocking[i] & t2s) != 0:
                return True
        return False

    def touching_typesets(self, t1s, t2s):
        for i in range(0, len(self.types)):
            if t1s & (1 << i) and (self.touching[i] & t2s) != 0:
                return True
        return False

    def check_contacts(self, col, col2, cs):
        assert col.is_active
        assert col2.is_active
        assert col != col2
        # Origin of col
        x1, y1 = col.nx, col.ny
        # Half Width and Height of col
        c1hw, c1hh = col.shape.w / 2.0, col.shape.h / 2.0
        # Center of col
        x1c, y1c = x1 + c1hw, y1 - c1hh

        # If other collider is Rect
        if isinstance(col2.shape, Rect):
            x2, y2 = col2.nx, col2.ny
            c2hw, c2hh = col2.shape.w / 2.0, col2.shape.h / 2.0
            x2c, y2c = x2 + c2hw, y2 - c2hh
            # Difference between centers
            dcx, dcy = x2c - x1c, y2c - y1c
            sep = vm.Vector2()
            # Normalize Vector
            norm = vm.Vector2(dcx, dcy)
            norm.normalize()

            # SAT Check
            if abs(dcx) > abs(dcy):
                norm.y = 0
                sep.y = 0
                if norm.x < 0:
                    sep.x = -sep.x
            else:
                norm.x = 0
                sep.x = 0
                if norm.y < 0:
                    sep.y = -sep.y
            cs.append(Contact(col.key, col2.key,
                      col.types, col2.types,
                      col.is_static, col2.is_static,
                      sep, norm,
                      self.blocking_typesets(col.types, col2.types)))

        # Else if is TileMap
        elif isinstance(col2.shape, TileMap):
            x1g = int(x1 // col2.shape.tile_width)
            x1wg = int((x1 + col.shape.w) // col2.shape.tile_width) + 1
            y1hg = int(y1 // col2.shape.tile_height) + 1
            y1g = int((y1 - col.shape.h) // col2.shape.tile_height)
            c2hw, c2hh = col2.shape.tile_width / 2.0, col2.shape.tile_height / 2.0
            for x in range(x1g, x1wg):
                for y in range(y1g, y1hg):
                    tile_types = col2.shape.tile_types(x, y)
                    if self.collidable_typesets(col.types, tile_types):
                        blocking = self.blocking_typesets(col.types,
                                                          tile_types)
                        #print col.is_active
                        #print col2.types | tile_types
                        #print "Colliding"
                        x2c = x * col2.shape.tile_width + c2hw
                        y2c = y * col2.shape.tile_height + c2hh
                        # Difference between centers
                        dcx, dcy = x2c - x1c, y2c - y1c
                        sepx = abs(dcx) - c1hw - c2hw
                        sepy = abs(dcy) - c1hh - c2hh
                        # SAT Check
                        if sepx > 0 or sepy > 0:
                            break
                        # Normalize Vector

                        d_mag = dcx*dcx+dcy*dcy
                        normx = dcx/d_mag
                        normy = dcy/d_mag

                        if abs(dcx) > abs(dcy):
                            normy = 0
                            sepy = 0
                            if normx < 0:
                                normx = -1
                                sepx = -sepx
                            else:
                                normx = 1
                        else:
                            normx = 0
                            sepx = 0
                            if normy < 0:
                                normy = -1
                                sepy = -sepy
                            else:
                                normy = 1
                        cs.append(Contact(
                            col.key, (col2.key, (x, y), 0),
                            col.types, col2.types | tile_types,
                            col.is_static, col2.is_static,
                            vm.Vector2(sepx, sepy), vm.Vector2(normx, normy),
                            blocking))
        else:
            # Collider type incorrect
            return None


class Collider(object):
    __slots__ = ["key", "types",
                 "is_active", "is_static",
                 "shape",
                 "px", "py", "nx", "ny"]

    def __init__(self, key=None, types=None,
                 is_active=None, is_static=None,
                 shape=None,
                 px=0, py=0, nx=0, ny=0):
        self.key = key
        self.types = types
        self.is_active = is_active
        self.is_static = is_static
        self.shape = shape
        self.px = px
        self.py = py
        self.nx = nx
        self.ny = ny

Contact = namedtuple(
    "Contact",
    "a_key b_key a_types b_types a_static b_static separation normal blocking")


class Rect(object):
    __slots__ = ["w", "h"]

    def __init__(self, w, h):
        self.w = w
        self.h = h


class TileMap(object):
    __slots__ = ["tile_width", "tile_height", "tile_defs", "tiles"]

    def __init__(self, tw, th, defs, tiles):
        self.tile_width = tw
        self.tile_height = th
        self.tile_defs = defs
        self.tiles = tiles

    def tile_types(self, tx, ty):
        if (tx < 0 or
            tx >= len(self.tiles[0]) or
            ty < 0 or
                ty >= len(self.tiles)):
            return self.tile_defs[0]
        return self.tile_defs[self.tiles[(len(self.tiles)-1) - ty][tx]]


"""
### Collision restitution

Collision restitution is always hairy,
especially when one HA might have several Colliders or one Collider
may be contacting multiple other Colliders.  The key difficulty is
that we don't want to restitute an automaton (i.e., stop it from
colliding with something) multiple times along the same vector.
Consider Mario standing on top of two ground tiles at once: Gravity
will pull him under the floor, and two tiles will want to push him up
and out by the same amount.  We only want to apply one of those
restitutions.  On the other hand, if Mario is simultaneously running
rightwards into a wall, we want to restitute both in ~x~ and in ~y~.
So, we scan through the Contacts from the collision theory to find the
maximum ~x~ and ~y~ restitutions we need to get the world right again
for each HA, and then execute just those.  At the same time, we kill
any velocity vector which has been restituted against: killing ~x~
velocity if we are actively bumping into a wall, for example.
"""


def do_restitution(world, new_contacts):
    for grp in world.valuations:
        for val in grp:
            contacts = 0
            max_x = 0
            max_y = 0
            # TODO: should the corner-rounding from CollisionTheory
            # be moved here?  It's a bit special-case-y in the sense
            # that it implicitly addresses restitution, right?
            # IOW, should collision theory calculate the restitution
            # as well as whether a collision occurred?

            # TODO: either here or in collision theory, prevent two
            # colliders with the same owner from colliding!  Probably
            # in collision theory!

            for con in new_contacts:
                #print con.normal
                is_a = (con.a_key[0] == val.automaton_index and
                        con.a_key[1] == val.index)
                is_b = (con.b_key[0] == val.automaton_index and
                        con.b_key[1] == val.index)
                if con.blocking and (is_a or is_b):
                    contacts += 1
                    #print con.separation.x, con.separation.y
                    if abs(con.separation.x) > abs(max_x):
                        max_x = con.separation.x
                    if abs(con.separation.y) > abs(max_y):
                        max_y = con.separation.y
                if isinstance(con.b_types, Rect):
                    max_x /= 2.0
                    max_y /= 2.0
            if contacts > 0:
                #print "Max_X, Max_Y: " + str(max_x) + ", " + str(max_y)
                if abs(max_x) < abs(max_y):
                    val.set_var("y", val.get_var("y") + max_y)
                    val.set_var("y'", 0)
                elif abs(max_y) < abs(max_x):
                    val.set_var("x", val.get_var("x") + max_x)
                    val.set_var("x'", 0)
                else:
                    return


"""# The test case"""


def load_test(files=None, tilemap=None, initial=None):
    automata = []
    if not files:
        automata.append(xml.parse_automaton("resources/mario.char.xml"))
    else:
        for f in files:
            automata.append(xml.parse_automaton("resources/" + f))

    if tilemap:
        tm = tilemap
    else:
        tm = TileMap(16, 16, [set(), set(["wall"])],
                     [[0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]])

    if initial:
        initial_aut = initial
    else:
        initial_aut = [(automata[0].name, {}, {"x": 0, "y": 450})]

    world = World(automata, Context(
            blocking_types={"body": ["wall", "body"], "solid": ["solid"]},
            touching_types={},
            static_colliders=[
                Collider(
                        "map",
                        set(["wall"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
            ],
            initial_automata= initial_aut
    ))
    print world.valuations[0][0].parameters
    #print world.valuations[0][0].parameters['gravity']
    return world


def run_test(filename=None, tilename=None, initial=None):
    import time
    import matplotlib.pyplot as plt

    test_world = load_test(filename, tilename, initial)

    dt = 1.0 / 60.0
    history = []

    t = time.time()
    for steps in [(120, ["right"]), (120, ["left"]), (60, [])]:
        for i in range(steps[0]):
            step(test_world, steps[1], dt)
            history.append(test_world.valuations[0][0].get_var("x"))
    t2 = time.time()
    print ("DT:",
           t2 - t, "seconds,",
           len(history), "frames,",
           len(history) / (t2 - t), "FPS",
           (len(history) / (t2 - t)) / 60.0, "x realtime")
    plt.figure()
    plt.plot(history)
    plt.savefig('xs')
    plt.close()


if __name__ == "__main__":
    run_test()
