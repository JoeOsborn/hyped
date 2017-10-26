"""HyPED 2 "Flattening" Python interpreter.

Author: Joseph C. Osborn
E-mail: jcosborn@ucsc.edu"""

import array
import copy
import math
import matplotlib
import schema as h
import sympy
import vectormath as vm
import xmlparser as xml
from collections import namedtuple
import numpy as np

matplotlib.use('Agg')

"""
# The Interpreter

# Objective

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

# Definitions

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

# Constraints

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
                      "self_set", "needs_timer"))

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
    elif isinstance(g, h.GuardJointTransition):
        return g._replace(mode=ordering[g.mode])
    elif isinstance(g, h.GuardTimer):
        assert modenum is not None
        return GuardTimerIndexed(
            g.threshold,
            g.provenance,
            modenum
        )
    return g


def guard_uses_timer(g):
    if isinstance(g, h.GuardConjunction):
        return any(map(guard_uses_timer, g.conjuncts))
    elif isinstance(g, h.GuardDisjunction):
        return any(map(guard_uses_timer, g.disjuncts))
    elif isinstance(g, h.GuardNegation):
        return guard_uses_timer(g.guard)
    elif isinstance(g, h.GuardTimer):
        return True
    return False


"""Mode translation also includes translating edges along with their guards
and caching some sets (bitmasks) that will be useful later.
"""


def translate_mode(m, ordering):
    modenum = ordering[m.qualified_name]
    if len(m.groups) > 1:
        return "Too many groups in a non-root mode for now!"
    new_edges = []
    descendant_count = len(h.flat_modes(m.groups, m.qualified_name))
    props = m._asdict()
    needs_timer = False
    for e in m.edges:
        eprops = e._asdict()
        eprops["target_index"] = ordering[e.qualified_target]
        eprops["guard"] = translate_guard(e.guard, ordering, modenum)
        if guard_uses_timer(eprops["guard"]):
            needs_timer = True
        new_edges.append(OrderedEdge(**eprops))
    for e in m.envelopes:
        if guard_uses_timer(e.invariant):
            needs_timer = True
    new_follow_links = []
    for f in m.follow_links:
        new_follow_links.append(
            f._replace(
                guard=translate_guard(f.guard, ordering, modenum)
            ))
        if guard_uses_timer(new_follow_links[-1].guard):
            needs_timer = True
    props["index"] = modenum
    props["edges"] = new_edges
    props["follow_links"] = new_follow_links
    props["descendant_count"] = descendant_count
    props["ancestor_set"] = qname_to_ancestors(
        m.qualified_name,
        ordering,
        include_self=False)
    props["descendant_set"] = mode_set(
        start=modenum,
        count=descendant_count + 1,
        order=ordering)
    props["self_set"] = mode_set(
        start=modenum,
        count=1,
        order=ordering)
    props["needs_timer"] = needs_timer
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

# Valuations

Recall that a valuation is an active mode set, an assignment to
parameters, and an assignment to variables.  We'll put potentially
many of these valuations inside of a World (grouped into disjoint
linking-logic spaces).  Valuations also have an identifier that lets
us tie them to colliders or other things later on.  Finally, a
valuation stores which states were just entered or exited to help
implement joint transition guards.

Within a Valuation, the set of variables is fixed.  So for efficiency
we store the variables in a canonical ordering so that reads and writes
during the continuous step can avoid dictionary lookups.  Random reads
and writes still incur some lookup and indirection cost, but should be
much less frequent.
"""


"""### The world at large

A World manages a list of automata types, valuations (grouped by
automaton and space), theory data (concerning e.g. user input and
collisions), and active colliders (including static colliders).
Exactly which theories are present is somewhat dependent on the game,
or rather the particular composition of operational logics at work.
In HyPED 2, we consider character-state logics (the discrete steps),
physics logics (the continuous steps), linking logics (organization by
a graph of spaces), collision logics, and input logics for now.  The
first three could be separated out into theories (and indeed probably
should be in the future), but at the moment they are more tightly
integrated.

At initialization time, the World also receives a Context, which
carries information on which collision types block each others'
movement, which types should be checked for collisions but don't
impede movement, the initial automata valuations in each space in the
world (defined in ContextSpaces along with static colliders and
linkages between rooms), and other initialization data.  Honestly,
it's a bit of a grab bag for material that hasn't been fully
incorporated into the theory of operational logics.  Concepts which
are yet unimplemented---for example, persistence logics which
determine which objects are active at which times or within particular
scopes like levels---will replace much of Context in the future.

"""


class Context(object):
    __slots__ = ["blocking_types",
                 "touching_types",
                 "spaces",
                 "val_limit", "param_limit", "dvar_limit", "cvar_limit"]

    def __init__(self, blocking_types={}, touching_types={}, spaces={}, val_limit=4):
        self.blocking_types = blocking_types
        self.touching_types = touching_types
        self.spaces = spaces
        self.val_limit = val_limit
        self.param_limit = 10
        self.dvar_limit = 2
        self.cvar_limit = 3


class ContextSpace(object):
    __slots__ = ["static_colliders",
                 "initial_automata",
                 "links"]

    def __init__(self, static_colliders=[], initial_automata=[], links=[]):
        self.static_colliders = static_colliders
        self.initial_automata = initial_automata
        self.links = links


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
    __slots__ = [
        "theories",
        "automata", "automata_indices",
        "context",
        "_spaces",
        "space_ordering",
        "links", "static_colliders",
        "colliders", "contacts",
        "modes",
        "params", "param_ordering",
        "dvars", "dvar_ordering",
        "cvars", "var_ordering",
        "timers"
        # Later, resource locations and whatever else also,
        # though maybe those are not space-linked?
    ]

    def __init__(self, raw_automata, context):
        # TODO: get val_limit per automata type from context
        automata = [translate_automaton(ra) for ra in raw_automata]
        (theories, automata, context) = init_theories(automata, context)
        self.theories = theories
        self.context = context
        self.automata_indices = {a.name: i for i, a in enumerate(automata)}
        self.automata = automata
        sorted_spaces = sorted(context.spaces.items())
        self._spaces = sorted_spaces
        self.space_ordering = {id: i
                               for i, (id, space) in enumerate(sorted_spaces)}
        self.links = [ws.links for id, ws in self._spaces]
        self.static_colliders = [
            ws.static_colliders for id, ws in self._spaces]
        self.contacts = [[] for _ in self._spaces]
        self.colliders = [[] for _ in self._spaces]
        self.modes = np.zeros(
            shape=(3, len(self._spaces),
                   len(self.automata), context.val_limit),
            dtype=np.int64)
        self.params = np.zeros(
            shape=(len(self._spaces),
                   len(self.automata), context.val_limit, context.param_limit))
        assert not any(map(lambda a: len(a.parameters) > context.param_limit,
                           self.automata)), "too many params " + str(map(lambda a: len(a.parameters), self.automata))
        self.param_ordering = [{
            pn: i for i, pn in enumerate(sorted(a.parameters.keys()))}
            for a in self.automata]
        self.dvars = np.zeros(
            shape=(len(self._spaces),
                   len(self.automata), context.val_limit, context.dvar_limit,))
        assert not any(map(lambda a: len(a.dvariables) >= context.dvar_limit,
                           self.automata))
        self.dvar_ordering = [{
            pn: i for i, pn in enumerate(sorted(a.dvariables.keys()))}
            for a in self.automata]
        self.cvars = np.zeros(
            shape=(3,
                   len(self._spaces),
                   len(self.automata), context.val_limit,
                   context.cvar_limit))
        assert not any(map(lambda a: len(a.variables) / 3 >= context.cvar_limit,
                           self.automata))
        self.var_ordering = [{
            vn: i for i, vn in enumerate(sorted(filter(lambda vk: a.variables[vk].degree == 0, a.variables.keys())))}
            for a in self.automata]
        self.timers = np.zeros(
            shape=(len(self._spaces),
                   len(self.automata), context.val_limit,
                   max(map(lambda a: len(a.ordered_modes), self.automata)),
                   ))
        for idx, (id, space) in enumerate(self._spaces):
            for ia in space.initial_automata:
                self.make_valuation_idx(idx, *ia)
            self.theories.collision.update(([c for c in self.colliders[idx]
                                             if c.is_active] +
                                            self.static_colliders[idx]),
                                           self.contacts[idx],
                                           0)

    def get_val_active_modes(self, space_id, auti, vali):
        spacei = self.space_ordering[space_id]
        return self.modes[0, spacei, auti, vali]

    def get_val_var(self, space_id, auti, vali, nom):
        spacei = self.space_ordering[space_id]
        return self.param_or_var_lookup(spacei, auti, vali, nom)

    def get_val_param(self, space_id, auti, vali, nom):
        idx = self.param_ordering[auti][nom]
        spacei = self.space_ordering[space_id]
        return self.params[spacei, auti, vali, idx]

    def clone(self):
        w2 = copy.copy(self)
        w2.theories = self.theories.clone()
        w2.contacts = copy.copy(self.contacts)
        w2.colliders = copy.deepcopy(self.colliders)
        w2.modes = np.copy(self.modes)
        w2.params = np.copy(self.params)
        w2.dvars = np.copy(self.dvars)
        w2.cvars = np.copy(self.cvars)
        w2.timers = np.copy(self.timers)
        return w2

    def store_to_hybrid_space(self):
        return (np.hstack(map(lambda n: n.reshape(-1),
                              [self.cvars, self.dvars,
                               self.timers, self.params])),
                self.modes.reshape(-1))

    def load_from_hybrid_space(self, cont, disc):
        """Note: This does not copy cont or disc so it might just have views on those.  Beware!"""
        split0 = self.cvars.size
        self.cvars = cont[0:split0].reshape(
            self.cvars.shape
        )
        split1 = split0 + self.dvars.size
        self.dvars = cont[split0:split1].reshape(
            self.dvars.shape
        )
        split2 = split1 + self.timers.size
        self.timers = cont[split1:split2].reshape(
            self.timers.shape
        )
        split3 = split2 + self.params.size
        self.params = cont[split2:split3].reshape(
            self.params.shape
        )
        self.modes = disc.reshape(self.modes.shape)

    def is_active_entity(self, space, aut, vi):
        return self.modes[0, space, aut, vi]

    def parameter_idx(self, auti, nom):
        return self.param_ordering[auti][nom]

    def param_or_var_lookup(self, spacei, auti, vali, nom):
        aut = self.automata[auti]
        if nom in aut.parameters:
            return self.params[spacei, auti, vali, self.parameter_idx(auti, nom)]
        if nom in aut.dvariables:
            return self.dvars[spacei, auti, vali, self.dvar_ordering[auti][nom]]
        if nom in aut.variables:
            var = aut.variables[nom]
            deg = var.degree
            return self.cvars[deg, spacei, auti, vali, self.var_ordering[auti][var.basename]]
        assert False

    def var_set(self, spacei, auti, vali, nom, val):
        aut = self.automata[auti]
        if nom in aut.dvariables:
            self.dvars[spacei, auti, vali, self.dvar_ordering[auti][nom]] = val
            return
        if nom in aut.variables:
            var = aut.variables[nom]
            deg = var.degree
            self.cvars[deg, spacei, auti, vali,
                       self.var_ordering[auti][var.basename]] = val
            return
        assert False

    def make_valuation_idx(
            self,
            space_idx, automaton_name,
            init_params={}, vbls={}, dvbls={},
            initial_modes=None,
            timers=None,
            entered=None,
            exited=None):
        assert automaton_name in self.automata_indices
        aut_i = self.automata_indices[automaton_name]
        aut = self.automata[aut_i]
        params = {pn: p.value.value for pn, p in aut.parameters.items()}
        vars = {vn: v.init.value for vn, v in aut.variables.items()}
        dvars = {vn: v.init.value for vn, v in aut.dvariables.items()}
        params.update(init_params)
        vars.update(vbls)
        dvars.update(dvbls)
        initial_modes = initial_mask(
            aut
        ) if initial_modes is None else initial_modes
        entered = initial_modes if entered is None else entered
        exited = mode_set(
            order=aut.ordering
        ) if exited is None else exited
        for i in range(0, self.context.val_limit):
            if not self.is_active_entity(space_idx, aut_i, i):
                self.modes[:, space_idx, aut_i, i] = [
                    initial_modes, entered, exited
                ]
                self.params[space_idx, aut_i,
                            i, :len(params)] = map(
                                lambda (pk, pv): pv,
                                sorted(params.items()))
                self.dvars[space_idx, aut_i,
                           i, :len(dvars)] = map(
                               lambda (pk, pv): pv,
                               sorted(dvars.items()))
                self.cvars[0, space_idx, aut_i,
                           i, :len(vars) / 3] = map(
                               lambda (pk, pv): vars[pk],
                               sorted(
                                   filter(
                                       lambda (pk, pv): pv.degree == 0,
                                       aut.variables.items()
                                   )))
                self.cvars[1, space_idx, aut_i,
                           i, :len(vars) / 3] = map(
                               lambda (pk, pv): vars[pk],
                               sorted(
                                   filter(
                                       lambda (pk, pv): pv.degree == 1,
                                       aut.variables.items()
                                   )))
                self.cvars[2, space_idx, aut_i,
                           i, :len(vars) / 3] = map(
                               lambda (pk, pv): vars[pk],
                               sorted(
                                   filter(
                                       lambda (pk, pv): pv.degree == 2,
                                       aut.variables.items()
                                   )))
                # TODO: take timers as an argument too!
                self.timers[space_idx, aut_i,
                            i, :] = np.zeros(shape=(self.timers.shape[3]))
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
                    x = vars["x"]
                    y = vars["y"]
                    ox = eval_value(c.shape.x, self, space_idx, aut_i, i)
                    oy = eval_value(c.shape.y, self, space_idx, aut_i, i)
                    self.colliders[space_idx].append(
                        Collider((aut_i, i, ci),
                                 c.types,
                                 eval_guard(c.guard, self,
                                            space_idx, aut_i, i),
                                 c.is_static,
                                 Rect(eval_value(c.shape.w, self,
                                                 space_idx, aut_i, i),
                                      eval_value(c.shape.h, self,
                                                 space_idx, aut_i, i)),
                                 x + ox, y + oy, x + ox, y + oy))
                return i
        assert False


"""~Theories~ is just a tidy container for the OL-specific theories."""


class Theories(object):
    __slots__ = ["input", "collision"]

    def __init__(self, input, collision):
        self.input = input
        self.collision = collision

    def clone(self):
        return Theories(self.input.clone(), self.collision.clone())


def init_theories(automaton_specs, context):
    input = InputTheory()
    # Replace collision tags on colliders and guards with bitmasks.
    # Update context with relevant mappings/orderings.
    (translated,
     collider_type_names,
     context) = translate_for_collision(automaton_specs, context)
    collision = CollisionTheory(collider_type_names,
                                context.blocking_types,
                                context.touching_types)
    return (Theories(input, collision), translated, context)


"""
Now, we can finally make a World and Valuation:

'''
world = World([automaton], Context(...))
world.make_valuation(space_id, automaton.name, {}, {"x":32, "y":32})
'''

The main operations we want to perform on valuations (in fact, on the
world as a whole) are to effect continuous flows, discrete jumps, and
theory updates.  For simplicity, this interpreter will use a fixed
timestep and update the input theory, the discrete state, the
continuous state, and the collision theory, in that order.
"""


def step(world, input_data, dt, log=None):
    if log is not None:
        log.advance_t(dt)
    world.theories.input.update(input_data, dt)
    # update envelope state before, after, or inside of discrete step?
    # do envelopes need any runtime state maintenance (i.e. any discrete step)
    # or can we know just from button, guard, and variable values?
    xfers = []
    for spacei in range(0, len(world._spaces)):
        # Calculate any removals/additions/transfers
        discrete_step(world, spacei, xfers, log)
    # OK, now do all the removals/additions/transfers
    do_transfers(world, xfers)
    for spacei in range(0, len(world._spaces)):
        # flows = flows_from_has(world)
        # continuous_step(world, flows, dt)
        continuous_step(world, spacei, dt)
        for c in world.colliders[spacei]:
            auti, vali, ci = c.key
            aut_def = world.automata[auti]
            col_def = aut_def.colliders[ci]
            c.is_active = eval_guard(col_def.guard, world, spacei, auti, vali)
            c.px = c.nx
            c.py = c.ny
            # TODO: cache var ordering lookup
            c.nx = (world.cvars[0, spacei, auti, vali,
                                world.var_ordering[auti]["x"]] +
                    eval_value(col_def.shape.x, world, spacei, auti, vali))
            c.ny = (world.cvars[0, spacei, auti, vali,
                                world.var_ordering[auti]["y"]] +
                    eval_value(col_def.shape.y, world, spacei, auti, vali))
            if isinstance(c.shape, Rect):
                c.shape.w = eval_value(
                    col_def.shape.w, world, spacei, auti, vali)
                c.shape.h = eval_value(
                    col_def.shape.h, world, spacei, auti, vali)
                # TODO other shapes
        world.contacts[spacei] = []
        world.theories.collision.update(([c for c in world.colliders[spacei]
                                          if c.is_active] +
                                         world.static_colliders[spacei]),
                                        world.contacts[spacei],
                                        dt)
        do_restitution(world, spacei, world.contacts[spacei])
    return world


def do_transfers(world, xfers):
    # Do all the removals, setting spots to None in valuations and
    # colliders.
    xfer_types = {}
    xfer_spaces = set()
    # TODO: handle case where from_space = to_space specially here or above
    for (spacei, aut_i, index, valdata, link) in xfers:
        world.modes[:, spacei, aut_i, index] = 0
        key = (spacei, aut_i)
        if key not in xfer_types:
            xfer_types[key] = []
        xfer_types[key].append((valdata, link))
        xfer_spaces.add(spacei)
        for ci, c in enumerate(world.colliders[spacei]):
            if c.key[0] == aut_i and c.key[1] == index:
                world.colliders[spacei][ci] = None
                cnext = world.colliders[spacei][ci + 1] if ci + \
                    1 < len(world.colliders[spacei]) else None
                if cnext is not None and (cnext.key[0] != aut_i or cnext.key[1] != index):
                    for c2 in world.colliders[spacei][ci + 1:]:
                        c2.key[1] -= 1
        # NOTE: contacts will be stale, but it's OK
        # because they get clobbered soon.  Right?
    # Then compact collider IDs in old space
    # TODO: this is pretty inefficient but I just wanted something easily
    # implemented for now
    for spacei in xfer_spaces:
        world.colliders[spacei] = filter(lambda v: v is not None,
                                         world.colliders[spacei])
    for (spacei, auti), vdls in xfer_types.items():
        # Then add val to new space's valuations using make_valuation,
        # updating the pos in the process
        autname = world.automata[auti].name
        for valdata, ((fx, fy, fw, fh), to_space_id, (tx, ty, tw, th)) in vdls:
            tospacei = world.space_ordering[to_space_id]
            vali = world.make_valuation_idx(
                tospacei,
                autname
            )
            world.modes[:, tospacei, auti, vali] = valdata[0]
            world.params[tospacei, auti, vali, :] = valdata[1]
            world.dvars[tospacei, auti, vali, :] = valdata[2]
            world.cvars[:, tospacei, auti, vali, :] = valdata[3]
            world.timers[tospacei, auti, vali, :] = valdata[4]
            x = world.param_or_var_lookup(tospacei, auti, vali, "x")
            y = world.param_or_var_lookup(tospacei, auti, vali, "y")
            x_pct = (x - fx) / float(fw)
            y_pct = (y - fy) / float(fh)
            nx = tx + tw * x_pct
            ny = ty + th * y_pct
            world.var_set(tospacei, auti, vali, "x", nx)
            world.var_set(tospacei, auti, vali, "y", ny)
    # TODO: is it a problem that discrete updates already happened?
    # They may have been clobbered by the position forcing above.
    # Does that bother me?


"""## Interpreting automata

The automata groups valuations by linked spaces, giving a clean way to
update and modify the dynamic objects in each space in turn.  Each of
the steps below is executed for the automata in each space; in other
words, we assume for now that all spaces progress time in lockstep,
but objects in one space cannot influence objects in another.

### Discrete step

The discrete step is tricky!  It has two main jobs: determining
whether any edges of active modes can be taken, and then actually
performing those transitions.  These are separated because each edge
evaluation needs to be done with the same valuation data, and we may
have parallel composition of modes.
"""


def ok_mode(aut, mask):
    # take a list of all active modes in each top level group.
    # if any such list has two modes that are siblings we are in a bad state.
    for gk, gv in aut.groups.items():
        present_parents = set()
        present_modes = set()
        for mp in h.flat_modes({gk: gv}):
            om = 1 << aut.ordering[mp]
            om_active = (mask & om) != 0
            if om_active:
                present_modes.add(mp)
                if mp.parent_group in present_parents:
                    print "mode conflict", map(str, present_parents)
                    print mp
                    print map(str, present_modes)
                    return False
                else:
                    present_parents.add(mp.parent_group)
    return True


def discrete_step(world, spacei, out_transfers, log):
    # TODO: avoid allocations all over the place
    all_updates = {}
    for auti, aut in enumerate(world.automata):
        for vali in range(world.context.val_limit):
            # TODO: avoid allocation of updates!
            (exit_set, enter_set,
             updates, transfer) = determine_available_transitions(
                 world,
                 spacei,
                 auti,
                 vali,
                 log
            )
            if transfer is not None:
                out_transfers.append(transfer)
            # Perform the transitions and updates.  This is where the bitmask
            # representation pays off!
            # old_active = val.active_modes
            world.modes[0, spacei, auti, vali] &= ~exit_set
            world.modes[0, spacei, auti, vali] |= enter_set
            world.modes[1, spacei, auti, vali] = enter_set
            world.modes[2, spacei, auti, vali] = exit_set
            # if not ok_mode(world.automata[aut_i], val.active_modes):
            #     print map(lambda om: str(om.qualified_name), world.automata[aut_i].ordered_modes)
            #     print old_active, val.active_modes, exit_set, enter_set
            #     print (old_active & ~exit_set)
            #     assert False
            # We can do the above immediately because we have a
            # canonical safe ordering (right?)
            # But transfers and updates must be done in a batch:
            all_updates.update(updates)
    # Apply all the updates at once
    for uk, uv in all_updates.items():
        spacei, auti, vali, nom = uk
        world.var_set(spacei, auti, vali, nom, uv)


"""To find available transitions, we iterate through every mode in the
safe ordering.  If that mode has an edge with a satisfied guard, we
take that edge and skip the rest of the mode's edges and its
descendants.  The edge's update dictionary is merged with the net
update dictionary (these updates may include functions of variables,
so we have to evaluate them explicitly).  Any possible conflicts
between updates should have been handled at automaton creation time,
as would any invalid edges (e.g., transitions from a parent to its own
child).

We also look for the case where the HA's position is in a link area
and the HA is willing to traverse a link.  In that case, we signal
that the HA should be transferred over to the linked space/position
(which may be a different position in the same space) and perform any
variable updates.
"""


def links_under_val(world, spacei, auti, vali):
    for l in world.links[spacei]:
        x, y, w, h = l[0]
        # TODO: use indices
        val_x = world.cvars[0, spacei, auti,
                            vali, world.var_ordering[auti]["x"]]
        val_y = world.cvars[0, spacei, auti,
                            vali, world.var_ordering[auti]["y"]]
        if (((x <= val_x <= (x + w)) and
             (y <= val_y <= (y + h)))):
            # TODO: return all such links
            return (l,)
    return ()


def determine_available_transitions(world, spacei, auti, vali, log):
    exit_set = mode_set(order=world.automata[auti].ordering)
    enter_set = mode_set(order=world.automata[auti].ordering)
    world.modes[1:3, spacei, auti, vali] = (enter_set, exit_set)
    updates = {}
    mi = 0
    modes = world.automata[auti].ordered_modes
    mode_count = len(modes)
    active = world.modes[0, spacei, auti, vali]
    transfer = None
    while mi < mode_count:
        if active & (1 << mi):
            mode = modes[mi]
            # TODO: is this the best place for this?
            if len(mode.follow_links) > 0:
                links = links_under_val(world, spacei, auti, vali)
                for f in mode.follow_links:
                    if len(links) > 0 and eval_guard(f.guard,
                                                     world,
                                                     spacei,
                                                     auti,
                                                     vali):
                        # TODO: don't just arbitrarily pick first
                        link = links[0]
                        # print "Follow", link
                        for euk, euv in f.updates.items():
                            key = (spacei, auti, vali, euk)
                            updates[key] = eval_value(
                                euv, world, spacei, auti, vali)
                        # TODO: ensure transfers don't conflict!
                        mode_data = world.modes[:, spacei, auti, vali].copy()
                        param_data = world.params[spacei, auti, vali, :].copy()
                        dvar_data = world.dvars[spacei, auti, vali, :].copy()
                        cvar_data = world.cvars[:, spacei,
                                                auti, vali, :].copy()
                        timer_data = world.timers[spacei, auti, vali, :].copy()
                        transfer = (spacei, auti, vali,
                                    (mode_data, param_data,
                                     dvar_data, cvar_data,
                                     timer_data),
                                    link)
                        if log is not None:
                            log.followed_link(
                                world, spacei, auti, vali, mode, f, link)
            for e in mode.edges:
                if eval_guard(e.guard, world, spacei, auti, vali):
                    exit_set, enter_set = update_transition_sets(
                        world,
                        spacei,
                        auti,
                        vali,
                        mode, modes[e.target_index],
                        enter_set, exit_set)
                    # Each time we get a new mask, update the valuation's
                    # exited and entered modes.
                    # We need to do this since some guards depend on it.
                    world.modes[1:3, spacei, auti, vali] = (
                        enter_set, exit_set)
                    # skip descendants
                    mi += mode.descendant_count
                    # figure out and merge in updates
                    # TODO: ensure updates don't conflict!
                    for euk, euv in e.updates.items():
                        key = (spacei, auti, vali, euk)
                        updates[key] = eval_value(
                            euv, world, spacei, auti, vali)
                    # skip any other transitions of this mode
                    if log is not None:
                        log.followed_edge(world, spacei, auti, vali, mode, e)
                    break
        mi += 1
    return (exit_set, enter_set, updates, transfer)


"""Updating ~enter_set~ and ~exit_set~ is a bit subtle, since 1.) we
may be going from a mode to one of its ancestors or their siblings,
and 2.) when entering a mode we also need to enter the appropriate
sub-mode (recursively).  Adding to ~exit_set~ is relatively easy,
since we can mask in all of the source mode's ancestors and
descendants and mask out any of those which are common ancestors with
the destination mode.  ~enter_set~ requires a loop to do properly; as
it turns out, we need this same sort of loop when initializing a
valuation's active set, so we can explore that here as well."""


def update_transition_sets(world, spacei, auti, vali, src, dest, enters, exits):
    all_srcs = src.descendant_set | src.ancestor_set | src.self_set
    exits |= all_srcs & (~dest.ancestor_set)
    enters |= dest.ancestor_set | dest.self_set
    enters |= initial_mask(world.automata[auti], dest)
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


def eval_guard(guard, world, spacei, auti, vali):
    if isinstance(guard, h.GuardConjunction):
        result = True
        for c in guard.conjuncts:
            # TODO: If evaluation needs a context (e.g. bindings), pass result
            # as well
            result = result & eval_guard(c, world, spacei, auti, vali)
            if result == 0:
                return False
        return result
    elif isinstance(guard, h.GuardDisjunction):
        result = False
        for c in guard.disjuncts:
            # TODO: If evaluation needs a context (e.g. bindings), pass result
            # as well
            result = result | eval_guard(c, world, spacei, auti, vali)
            if result == 1:
                return True
        return result
    elif isinstance(guard, h.GuardNegation):
        return not eval_guard(guard.guard, world, spacei, auti, vali)
    elif isinstance(guard, h.GuardTrue):
        return True
    elif isinstance(guard, h.GuardInMode):
        assert guard.character is None
        return (world.modes[0, spacei, auti, vali] & (1 << guard.mode)) != 0
    elif isinstance(guard, h.GuardJointTransition):
        assert guard.character is None
        if guard.direction == "enter":
            return world.modes[1, spacei, auti, vali] & (1 << guard.mode)
        elif guard.direction == "exit":
            return world.modes[2, spacei, auti, vali] & (1 << guard.mode)
        else:
            raise ValueError("Unrecognized direction", guard)
    elif isinstance(guard, h.GuardColliding):
        # TODO: avoid tuple creation
        return 0 < world.theories.collision.count_contacts(
            world.contacts[spacei],
            (auti, vali),
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
        threshold = eval_value(guard.threshold, world, spacei, auti, vali)
        timer_value = world.timers[spacei, auti, vali, guard.timer_index]
        return timer_value >= threshold
    elif isinstance(guard, h.GuardCompare):
        left = eval_value(guard.left, world, spacei, auti, vali)
        right = eval_value(guard.right, world, spacei, auti, vali)
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


def eval_value(expr, world, spacei, auti, vali):
    # in the future:
    # expr(world, val)
    if isinstance(expr, h.ConstantExpr):
        return expr.value
    elif isinstance(expr, h.Parameter):
        # TODO: maybe a faster path by tagging with the variable index earlier?
        idx = world.parameter_idx(auti, expr.name)
        return world.params[spacei, auti, vali, idx]
    elif isinstance(expr, h.Variable):
        # TODO: maybe a faster path by tagging with the variable index earlier?
        return world.param_or_var_lookup(spacei, auti, vali, expr.name)
    elif isinstance(expr, sympy.Expr):
        # TODO: refs, cache this somehow
        substitutions = {}
        for sym in expr.atoms(sympy.Symbol):
            substitutions[sym] = world.param_or_var_lookup(
                spacei, auti, vali,
                str(sym))
        return expr.evalf(subs=substitutions)
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


def continuous_step(world, spacei, dt):
    for auti, aut in enumerate(world.automata):
        for vali in range(world.context.val_limit):
            if not world.is_active_entity(spacei, auti, vali):
                break
            flows = {}
            for f in aut.flows.values():
                fvar = f.var
                fvalexpr = f.value
                fval = eval_value(fvalexpr, world, spacei, auti, vali)
                flows[fvar.basename] = (fvar, fval)
            modes = aut.ordered_modes
            active = world.modes[0, spacei, auti, vali]
            mi = 0
            mlim = len(modes)
            while mi < mlim:
                if active & (1 << mi) == 0:
                    world.timers[spacei, auti, vali, mi] = 0.0
                    mi += modes[mi].descendant_count
                else:
                    world.timers[spacei, auti, vali, mi] += dt
                    for f in modes[mi].flows.values():
                        fvar = f.var
                        fvalexpr = f.value
                        fval = eval_value(fvalexpr, world, spacei, auti, vali)
                        flows[fvar.basename] = (fvar, fval)
                    # apply active envelope flows too
                    # TODO: document and also extract into another function?
                    for e in modes[mi].envelopes:
                        # TODO: generalize to N ways, different ADSR functions,
                        # etc.
                        assert e.reflections >= 2

                        # Char is moving in VX,VY
                        # Axes are pointing in AX,AY
                        # attack, decay, sustain, release use scalar parameters
                        # p and influence magnitude of VX,VY projected on AX,AY
                        # So, 2-way fixes AY = 0
                        # and 4-way fixes AX & AY to be one of -1,0,1 & normal
                        # IOW it quantizes the angle and yields a normal back.
                        # n-way just normalizes the axis values.
                        # Let's solve for n-way and deal with the rest later.

                        axis1_value = world.theories.input.get_axis(
                            e.axes[0][0], e.axes[0][1]
                        )
                        axis2_value = world.theories.input.get_axis(
                            e.axes[1][0], e.axes[1][1]
                        ) if e.reflections > 2 else 0
                        variable1 = e.variables[0]
                        variable2 = (e.variables[1]
                                     if e.reflections > 2 else None)
                        # TODO: use indices rather than names?
                        cur1_value = eval_value(variable1,
                                                world, spacei, auti, vali)
                        cur2_value = eval_value(variable2,
                                                world,
                                                spacei,
                                                auti,
                                                vali) if variable2 is not None else 0
                        ax = (axis1_value, axis2_value)
                        cur = (cur1_value, cur2_value)
                        cur_dir = quantize_dir(norm(cur), e.reflections)
                        target_point = cur
                        axis_value = axis1_value**2 + axis2_value**2
                        axis_dir = quantize_dir(norm(ax), e.reflections)
                        if axis_value != 0 and eval_guard(e.invariant,
                                                          world,
                                                          spacei,
                                                          auti,
                                                          vali):
                            sustain_value = eval_value(e.sustain[1],
                                                       world,
                                                       spacei,
                                                       auti,
                                                       vali)
                            # TODO: if attack has a different target
                            # or something, distinguish A and D
                            attack_acc = eval_value(
                                e.attack[1], world, spacei, auti, vali)
                            sustain_point = vmult_s(axis_dir, sustain_value)
                            delta = vsub(sustain_point, cur)
                            if mag(delta) > 0.1:
                                # A
                                # TODO: what about D?
                                target_point = vadd(
                                    cur,
                                    vmult_s(norm(delta), attack_acc * dt))
                                now_delta = vsub(sustain_point, target_point)
                                # avoid overshooting
                                angle_d = abs(angle(now_delta) - angle(delta))
                                if angle_d > math.pi / 8.0:
                                    target_point = sustain_point
                                # print "TP", cur, target_point
                            else:
                                # S
                                target_point = sustain_point
                        else:
                            # R
                            if e.release[0] == "hold":
                                target_point = cur
                            elif e.release[0] == "acc":
                                release_acc = eval_value(
                                    e.release[1],
                                    world,
                                    spacei,
                                    auti,
                                    vali)
                                release_value = eval_value(
                                    e.release[2],
                                    world,
                                    spacei,
                                    auti,
                                    vali)
                                release_point = vmult_s(cur_dir, release_value)
                                delta = vsub(release_point, cur)
                                if mag(delta) > 0.1:
                                    target_point = vadd(
                                        cur,
                                        vmult_s(norm(delta), release_acc * dt))
                                    # avoid overshooting
                                    now_delta = vsub(
                                        release_point,
                                        target_point)
                                    angle_d = abs(angle(now_delta) -
                                                  angle(delta))
                                    if angle_d > math.pi / 8.0:
                                        target_point = release_point
                                else:
                                    target_point = release_point
                            elif e.release[0] == "set":
                                release_value = eval_value(
                                    e.release[1],
                                    world,
                                    spacei,
                                    auti,
                                    vali
                                )
                                target_point = vmult_s(cur_dir, release_value)
                            else:
                                assert False, str(e.release)
                        # control variable = target_value
                        flows[variable1.basename] = (
                            variable1,
                            target_point[0]
                        )
                        if e.reflections > 2:
                            flows[variable2.basename] = (
                                variable2,
                                target_point[1]
                            )
                mi += 1
            for vname, vari in world.var_ordering[auti].items():
                val_pos, val_vel, val_acc = world.cvars[:, spacei, auti,
                                                        vali, vari]
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
                world.cvars[:, spacei, auti, vali, vari] = (
                    val_pos, val_vel, val_acc)


def mag(v2):
    return math.sqrt(v2[0]**2 + v2[1]**2)


def angle(v2):
    return math.atan2(v2[1], v2[0])


def norm(v2):
    m = mag(v2)
    if m == 0:
        return v2
    return (v2[0] / m, v2[1] / m)


def sign(val):
    if val < 0:
        return -1
    elif val == 0:
        return 0
    else:
        return 1


def quantize_dir(v2, posns):
    if posns == 2:
        assert v2[1] == 0
        return v2
    elif posns == -1:
        # TODO: not actually reachable
        return v2
    else:
        m = mag(v2)
        # might not have any magnitude, just return if so
        if m == 0:
            return v2
        theta = angle(v2)
        # Go to degrees for easy rounding
        arclen_deg = 360 / float(posns)
        theta_deg = theta * (180 / math.pi)
        qtheta_deg = round(theta_deg / arclen_deg) * arclen_deg
        qtheta = qtheta_deg * (math.pi / 180)
        # come on back
        return (m * math.cos(qtheta), m * math.sin(qtheta))


def vadd(v2a, v2b):
    return (v2a[0] + v2b[0], v2a[1] + v2b[1])


def vsub(v2a, v2b):
    return (v2a[0] - v2b[0], v2a[1] - v2b[1])


def vmult_s(v2, s):
    return (v2[0] * s, v2[1] * s)


def dot(v1, v2):
    return v1[0] * v2[0] + v1[1] * v2[1]


def angle_between(v1, v2):
    m1 = mag(v1)
    m2 = mag(v2)
    if m1 == 0 or m2 == 0:
        return math.acos(0)
    dp = dot(v1, v2)
    return math.acos(dp / (m1 * m2))


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

    def clone(self):
        return copy.deepcopy(self)

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
            if b not in self.on:
                self.pressed.add(b)
            self.on.add(b)
    # TODO: Handle players

    def is_pressed(self, player, button):
        return button in self.pressed

    def is_on(self, player, button):
        return button in self.on

    def is_off(self, player, button):
        return not self.is_on(player, button)

    def is_released(self, player, button):
        return button in self.released

    # TODO: generalize, admit ranges of values, ...
    axis_defs = {
        "x": ["left", "right"],
        "y": ["down", "up"]
    }

    # TODO: generalize
    def get_axis(self, player, axis):
        ax = self.axis_defs[axis]
        if self.is_on(player, ax[0]):
            return -1
        if self.is_on(player, ax[1]):
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
    for id, space in context.spaces.items():
        for c in space.static_colliders:
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
    collider_types = {t: ti for ti, t in enumerate(sorted_tags)}
    collider_type_names = sorted_tags
    context.blocking_types = {
        collider_types[t]: types_to_bv(collider_types, ts)
        for t, ts in context.blocking_types.items()}
    context.touching_types = {
        collider_types[t]: types_to_bv(collider_types, ts)
        for t, ts in context.touching_types.items()}
    for id, space in context.spaces.items():
        for c in space.static_colliders:
            c.types = types_to_bv(collider_types, c.types)
            if isinstance(c.shape, TileMap):
                c.shape.tile_defs = [types_to_bv(collider_types, td)
                                     for td in c.shape.tile_defs]

    automata = []
    for a in automata_specs:
        # These colliders are "schema colliders", not concrete ones
        new_colliders = [
            c._replace(types=types_to_bv(collider_types, c.types))
            for c in a.colliders]
        new_modes = [
            m._replace(edges=[
                e._replace(guard=translate_guard_collider_types(
                    collider_types,
                    e.guard))
                for e in m.edges])
            for m in a.ordered_modes]
        automata.append(a._replace(
            colliders=new_colliders,
            ordered_modes=new_modes))
    return (automata,
            collider_type_names,
            context)


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
    # For each key C ensure C appears as a value in each value C2
    for c, cs in rel.items():
        for c2 in cs:
            if c2 not in rel:
                rel[c2] = []
            # if c is not already in rel[c2]:
            found = False
            for c3 in rel[c2]:
                if c3 == c:
                    found = True
            if not found:
                rel[c2].append(c)


class CollisionTheory(object):
    __slots__ = ["types", "blocking", "touching"]

    def __init__(self, type_names, blocking_pairs, nonblocking_pairs):
        self.types = type_names
        self.blocking = blocking_pairs
        self.touching = nonblocking_pairs

    def clone(self):
        return self

    def update(self, colliders, out_contacts, dt):
        # Find all contacts.  Note that colliding with a tilemap
        # may produce many contacts!
        # TODO: spatial partition
        for coli in range(len(colliders)):
            col = colliders[coli]
            # TODO: ordering-sensitive: if A collides with B we assume only A
            # will restitute.  This seems wrong.
            for col2i in range(coli + 1, len(colliders)):
                col2 = colliders[col2i]
                if self.collidable_typesets(col.types, col2.types):
                    self.check_contacts(col, col2, out_contacts)
        return out_contacts

    def get_contacts(self, contacts, key, self_type, normal_check, other_type):
        # Return contacts between blocking and nonblocking types.
        # TODO: Remove assumption that key is a >=2-tuple
        # TODO: hi, refactor me
        return [c for c in contacts
                if ((c.a_key[0] == key[0] and
                     c.a_key[1] == key[1] and
                     (self_type & c.a_types) != 0 and
                     (other_type & c.b_types) != 0 and
                     (normal_check is None or
                      (normal_check is not None and
                       c.normal[0] == normal_check[0] and
                       c.normal[1] == normal_check[1]))) or
                    (c.b_key[0] == key[0] and
                     c.b_key[1] == key[1] and
                     (self_type & c.b_types) != 0 and
                     (other_type & c.a_types) != 0 and
                     (normal_check is None or
                      (normal_check is not None and
                       c.normal[0] == -normal_check[0] and
                       c.normal[1] == -normal_check[1]))))]

    def count_contacts(self, contacts,
                       key, self_type, normal_check, other_type):
        return len(self.get_contacts(contacts,
                                     key, self_type, normal_check, other_type))

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
        # TODO: refactor these two cases, they're almost identical inside!
        if isinstance(col2.shape, Rect):
            x2, y2 = col2.nx, col2.ny
            c2hw, c2hh = col2.shape.w / 2.0, col2.shape.h / 2.0
            x2c, y2c = x2 + c2hw, y2 - c2hh
            # Difference between centers
            dcx, dcy = x2c - x1c, y2c - y1c
            sepx = abs(dcx) - c1hw - c2hw
            sepy = abs(dcy) - c1hh - c2hh

            d_mag = dcx * dcx + dcy * dcy
            # TODO: get rid of these ifs which can happen with non-blocking
            # collisions
            normx = dcx / d_mag if d_mag != 0 else 1
            normy = dcy / d_mag if d_mag != 0 else 0

            if sepx > 0 or sepy > 0:
                return

            # SAT Check
            # both are smaller than 0 and we
            # want the one closest to 0, ie of least magnitude.
            if sepx > sepy:
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
            contact = Contact(col.key, col2.key,
                              col.types, col2.types,
                              col.is_static, col2.is_static,
                              vm.Vector2(float(sepx), float(sepy)),
                              vm.Vector2(float(normx), float(normy)),
                              self.blocking_typesets(col.types, col2.types))
            cs.append(contact)
        # Else if is TileMap
        elif isinstance(col2.shape, TileMap):
            x1g = int(int(x1) // col2.shape.tile_width)
            x1wg = int((int(x1) + col.shape.w) // col2.shape.tile_width) + 1
            y1hg = int(int(y1) // col2.shape.tile_height) + 1
            y1g = int((int(y1) - col.shape.h) // col2.shape.tile_height)
            c2hw, c2hh = (col2.shape.tile_width / 2.0,
                          col2.shape.tile_height / 2.0)
            for x in range(x1g, x1wg):
                for y in range(y1g, y1hg):
                    tile_types = col2.shape.tile_types(x, y)
                    if self.collidable_typesets(col.types, tile_types):
                        blocking = self.blocking_typesets(col.types,
                                                          tile_types)
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

                        d_mag = dcx * dcx + dcy * dcy
                        # TODO: get rid of these ifs which can happen with
                        # non-blocking collisions
                        normx = dcx / d_mag if d_mag != 0 else 1
                        normy = dcy / d_mag if d_mag != 0 else 0

                        # both are smaller than 0 and we
                        # want the one closest to 0, ie of least magnitude.
                        if sepx > sepy:
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
                            col.types, tile_types,
                            col.is_static, col2.is_static,
                            vm.Vector2(float(sepx), float(sepy)),
                            vm.Vector2(float(normx), float(normy)),
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

    def __repr__(self):
        return str(("Collider:", self.key, self.types, self.is_active, self.is_static, self.shape, self.px, self.py, self.nx, self.ny))


class Contact(namedtuple(
    "Contact",
    ["a_key", "b_key", "a_types", "b_types", "a_static", "b_static",
     "separation", "normal", "blocking"])):

    def flipped(self):
        return Contact(
            self.b_key, self.a_key,
            self.b_types, self.a_types,
            self.b_static, self.a_static,
            -self.separation, -self.normal,
            self.blocking
        )


class Rect(object):
    __slots__ = ["w", "h"]

    def __init__(self, w, h):
        self.w = w
        self.h = h

    def __repr__(self):
        return "Rect(" + str(self.w) + "," + str(self.h) + ")"


class TileMap(object):
    __slots__ = ["tile_width",
                 "tile_height",
                 "tile_defs",
                 "tiles"]

    def __init__(self, tw, th, tds, tiles):
        self.tile_width = tw
        self.tile_height = th
        self.tile_defs = tds
        self.tiles = tiles

    def tile_types(self, tx, ty):
        if (tx < 0 or
            tx >= len(self.tiles[0]) or
            ty < 0 or
                ty >= len(self.tiles)):
            return self.tile_defs[0]
        return self.tile_defs[self.tiles[(len(self.tiles) - 1) - ty][tx]]


"""
# Collision restitution

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


def do_restitution(world, spacei, new_contacts):
    # print new_contacts
    offsets = np.zeros(shape=(len(world.automata),
                              world.context.val_limit,
                              2))
    contacts = 0
    for con in new_contacts:
        aauti, avali, aci = con.a_key
        bauti, bvali, bci = con.b_key
        # TODO: should the corner-rounding from CollisionTheory
        # be moved here?  It's a bit special-case-y in the sense
        # that it implicitly addresses restitution, right?
        # IOW, should collision theory calculate the restitution
        # as well as whether a collision occurred?

        # TODO: either here or in collision theory, prevent two
        # colliders with the same owner from colliding!  Probably
        # in collision theory!
        sx, sy = con.separation
        if con.blocking and con.a_static and not con.b_static:
            bsx, bsy = offsets[bauti, bvali, :]
            # print con.separation.x, con.separation.y
            if isinstance(con.b_types, Rect):
                sx /= 2.0
                sy /= 2.0
            if abs(sx) > abs(bsx):
                offsets[bauti, bvali, 0] = -sx
            if abs(sy) > abs(bsy):
                offsets[bauti, bvali, 1] = -sy
        if con.blocking and con.b_static and not con.a_static:
            asx, asy = offsets[aauti, avali, :]
            if isinstance(con.a_types, Rect):
                sx /= 2.0
                sy /= 2.0
            # print con.separation.x, con.separation.y
            if abs(sx) > abs(asx):
                offsets[aauti, avali, 0] = sx
            if abs(sy) > abs(asy):
                offsets[aauti, avali, 1] = sy
    for auti in range(offsets.shape[0]):
        xidx = world.var_ordering[auti]["x"]
        yidx = world.var_ordering[auti]["y"]
        for vali in range(offsets.shape[1]):
            if not world.is_active_entity(spacei, auti, vali):
                break
            ox = offsets[auti, vali, 0]
            oy = offsets[auti, vali, 1]
            if ox == 0 and oy == 0:
                continue
            if abs(ox) < abs(oy):
                world.cvars[0, spacei, auti, vali, yidx] += oy
                world.cvars[1, spacei, auti, vali, yidx] = 0
            else:
                world.cvars[0, spacei, auti, vali, xidx] += ox
                world.cvars[1, spacei, auti, vali, xidx] = 0


# Transition logging

class TransitionLog(object):
    __slots__ = ("t", "path")

    def __init__(self):
        self.t = 0
        self.path = []

    def clone(self):
        nlog = TransitionLog()
        nlog.t = self.t
        nlog.path = copy.copy(self.path)
        if len(nlog.path) > 0 and len(nlog.path[-1][1]) == 0:
            nlog.path[-1] = copy.deepcopy(self.path[-1])
        return nlog

    def advance_t(self, dt):
        self.t += dt
        if len(self.path) > 0 and len(self.path[-1][1]) == 0:
            self.path[-1][0] = self.t
        else:
            self.path.append([self.t, {}])

    def follow_path(self, world, spacei, auti, vali):
        step = self.path[-1][1]
        # FIXME
        spaceid = world._spaces[spacei][0]
        if spaceid not in step:
            step[spaceid] = [{} for aut in world.automata]
        vals = step[spaceid][auti]
        if vali not in vals:
            vals[vali] = {"followed_edges": [], "followed_link": None}
        return vals[vali]

    def followed_link(self, world, spacei, auti, vali, m, f, link):
        val_data = self.follow_path(world, spacei, auti, vali)
        val_data["followed_link"] = (m, f, link)

    def followed_edge(self, world, spacei, auti, vali, m, e):
        val_data = self.follow_path(world, spacei, auti, vali)
        val_data["followed_edges"].append((m, e))

    def __str__(self):
        return str(self.path)

    # TODO: create/destroy vals too


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
        blocking_types={"body": ["wall", "body", "platform"]},
        touching_types={"wall": ["wall", "platform"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=initial_aut
            )
        }
    ))
    # print world.valuations[0][0].parameters
    # print world.valuations
    # print world.valuations[0][0].parameters['gravity']
    return world


def load_test2():
    automata = []
    automata.append(xml.parse_automaton("resources/mario.char.xml"))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                 [[1, 1, 1, 1, 1, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 2],
                  [1, 1, 1, 1, 1, 1]])

    tm2 = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                  [[1, 1, 1, 1, 1, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [2, 0, 0, 0, 0, 1],
                   [1, 1, 1, 1, 1, 1]])

    world = World(automata, Context(
        blocking_types={"body": ["wall", "body"]},
        touching_types={"wall": ["wall"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[0].name, {}, {"x": 32, "y": 33})],
                links=[((5 * 32, 32, 32, 32), "1", (1 * 32, 32, 32, 32))]
            ),
            "1": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm2,
                        0, 0, 0, 0)
                ],
                initial_automata=[],
                links=[((-1 * 32, 32, 32, 32), "0", (3 * 32, 32, 32, 32))]
            )
        }
    ))
    # print world.spaces["0"].valuations[0][0].parameters
    # print world.spaces["0"].valuations
    # print world.spaces["0"].valuations[0][0].parameters['gravity']
    return world


def load_test_plan():
    automata = []
    automata.append(xml.parse_automaton("resources/rrobot.char.xml"))
    automata.append(xml.parse_automaton(
        "resources/plat_h_activating.char.xml"))
    automata.append(xml.parse_automaton("resources/plat_h.char.xml"))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["goal"])],
                 [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
                  [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]])

    world = World(automata, Context(
        val_limit=1,
        blocking_types={"player": ["wall"]},
        touching_types={"player": ["platform"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[0].name,
                                   {},
                                   {"x": 0,
                                    "y": 64}),
                                  (automata[1].name,
                                   {"r_to_l_x": (7 - 2) * 32,
                                    "l_to_r_x": 3 * 32},
                                   {"x": 3 * 32,
                                    "y": 32}),
                                  (automata[2].name,
                                   {"r_to_l_x": (11 - 2) * 32,
                                    "l_to_r_x": 7 * 32, },
                                   {"x": 7 * 32,
                                    "y": 32})])}))
    # print world.spaces["0"].valuations[0][0].parameters
    # print world.spaces["0"].valuations
    # print world.spaces["0"].valuations[0][0].parameters['gravity']
    return world


def load_test_plan2():
    automata = []
    automata.append(xml.parse_automaton("resources/mario.char.xml"))
    automata.append(xml.parse_automaton(
        "resources/plat_h_activating.char.xml"))
    automata.append(xml.parse_automaton("resources/plat_h.char.xml"))

    tm = TileMap(32, 64, [set(), set(["wall"]), set(["goal"])],
                 [[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]])

    world = World(automata, Context(
        blocking_types={"player": ["wall"]},
        touching_types={"player": ["platform"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[0].name,
                                   {},
                                   {"x": 32,
                                    "y": 64 + 32}),
                                  (automata[1].name,
                                   {"r_to_l_x": (7 - 2) * 32,
                                    "l_to_r_x": 3 * 32},
                                   {"x": 3 * 32,
                                    "y": 64 * 2}),
                                  (automata[2].name,
                                   {"r_to_l_x": (7 - 2) * 32,
                                    "l_to_r_x": 3 * 32, },
                                   {"x": 3 * 32,
                                    "y": 64 * 3})])}))
    # print world.spaces["0"].valuations[0][0].parameters
    # print world.spaces["0"].valuations
    # print world.spaces["0"].valuations[0][0].parameters['gravity']
    return world


def load_test_plan3():
    automata = []
    automata.append(xml.parse_automaton("resources/mario.char.xml"))
    automata.append(xml.parse_automaton(
        "resources/plat_h_activating.char.xml"))
    automata.append(xml.parse_automaton("resources/plat_h.char.xml"))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["goal"])],
                 [[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
                  [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]])

    world = World(automata, Context(
        blocking_types={"player": ["wall"]},
        touching_types={"player": ["platform"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[0].name,
                                   {},
                                   {"x": 32,
                                    "y": 64 + 32}),
                                  # (automata[1].name,
                                  #  {"r_to_l_x": (7 - 2) * 32,
                                  #   "l_to_r_x": 3 * 32},
                                  #  {"x": 3 * 32,
                                  #   "y": 64 * 2}),
                                  # (automata[2].name,
                                  #  {"r_to_l_x": (7 - 2) * 32,
                                  #   "l_to_r_x": 3 * 32, },
                                  #  {"x": 3 * 32,
                                  #   "y": 64 * 3})
                                  ])}))
    # print world.spaces["0"].valuations[0][0].parameters
    # print world.spaces["0"].valuations
    # print world.spaces["0"].valuations[0][0].parameters['gravity']
    return world


def load_zelda():
    automata = []
    automata.extend((xml.parse_automaton("resources/link.char.xml"), xml.parse_automaton("resources/enemy.char.xml"), xml.parse_automaton(
        "resources/key.char.xml"), xml.parse_automaton("resources/enemy_tracker.char.xml"), xml.parse_automaton("resources/door.char.xml")))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"]), set(["goal"])],
                 [[1, 1, 1, 1, 1, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 2],
                  [1, 1, 1, 1, 1, 1]])

    tm2 = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                  [[1, 1, 1, 1, 1, 1],
                   [1, 0, 0, 0, 0, 2],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [2, 0, 0, 0, 0, 1],
                   [1, 1, 1, 1, 2, 1]])
    tm3 = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"]), set(["goal"])],
                  [[1, 1, 1, 1, 2, 1],
                   [1, 0, 0, 0, 3, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 1, 1, 1, 1, 1]])
    tm4 = TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                  [[1, 1, 1, 1, 1, 1],
                   [2, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 0, 0, 0, 0, 1],
                   [1, 1, 1, 1, 1, 1]])

    world = World(automata, Context(
        blocking_types={"body": ["wall", "body"], "enemy_door": [
            "body", "enemy_door"], "door": ["body", "door"]},
        touching_types={"wall": ["wall"], "enemy": ["enemy", "body"], "key": [
            "key", "body"], "door": ["key_got", "door"], "enemy_tracker": ["enemy_tracker", "enemy"],
            "goal": ["body", "goal"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[0].name, {}, {"x": 32, "y": 33})],
                links=[((5 * 32, 32, 32, 32), "1", (1 * 32, 32, 32, 32))]
            ),
            "1": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm2,
                        0, 0, 0, 0)
                ],
                initial_automata=[(automata[1].name,
                                   {},
                                   {"x": 32, "y": 33 * 4}),
                                  (automata[1].name,
                                   {},
                                   {"x": 4 * 32, "y": 32 * 4}),
                                  (automata[1].name,
                                   {},
                                   {"x": 2 * 32, "y": 32 * 3}),
                                  (automata[3].name,
                                   {},
                                   {"x": 32 * 1, "y": 32 * 6}),
                                  (automata[4].name,
                                   {},
                                   {"x": 32 * 4, "y": 32 * 2})],
                links=[((-1 * 32, 32, 32, 32), "0", (3 * 32, 32, 32, 32)),
                       ((4 * 32, -1 * 32, 32, 32), "2",
                        (4 * 32, 6 * 32, 32, 32)),
                       ((5 * 32, 5 * 32, 32, 32), "3", (0 * 32, 5 * 32, 32, 32))]
            ),
            "2": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm3,
                        0, 0, 0, 0)
                ],
                initial_automata=[],
                links=[((4 * 32, 7 * 32, 32, 32), "1", (4 * 32, 0 * 32, 32, 32))]
            ),
            "3": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "teleporter"]),
                        True, True,
                        tm4,
                        0, 0, 0, 0)
                ],
                initial_automata=[
                    (automata[2].name, {}, {"x": 32, "y": 33 * 4})
                ],
                links=[((-1 * 32, 5 * 32, 32, 32), "1", (4 * 32, 5 * 32, 32, 32))]
            )
        }
    ))
    return world


def load_zelda2():
    automata = []
    automata.extend((
        xml.parse_automaton("resources/link.char.xml"),
        xml.parse_automaton("resources/key.char.xml"),
        xml.parse_automaton("resources/door.char.xml")))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["goal"])],
                 [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 1, 0, 3],
                  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]])

    world = World(automata, Context(
        blocking_types={"body": ["wall", "body"], "door": ["body", "door"]},
        touching_types={"wall": ["wall"],
                        "key": ["key", "body"],
                        "door": ["key_got", "door"],
                        "goal": ["body", "goal"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[
                    (automata[0].name, {}, {"x": 32 * 5, "y": 64}),
                    (automata[1].name, {}, {"x": 32, "y": 64}),
                    (automata[2].name, {}, {"x": 32 * 8, "y": 64})
                ],
                links=[]
            )
        }
    ))
    return world


def load_zelda3():
    automata = []
    automata.extend([xml.parse_automaton("resources/link.char.xml")])

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["goal"])],
                 [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
                  [1, 0, 1, 0, 0, 0, 0, 1, 0, 3],
                  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]])

    world = World(automata, Context(
        blocking_types={"body": ["wall", "body"], "door": ["body", "door"]},
        touching_types={"wall": ["wall"],
                        "key": ["key", "body"],
                        "door": ["key_got", "door"],
                        "goal": ["body", "goal"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[
                    (automata[0].name, {}, {"x": 32 * 5, "y": 64})
                ],
                links=[]
            )
        }
    ))
    return world


def platformPlanning1():
    automata = []
    automata.extend((
        xml.parse_automaton("resources/mario.char.xml"),
        xml.parse_automaton("resources/moving_hazard_vert.char.xml"),
        xml.parse_automaton("resources/plat_h.char.xml")))

    tm = TileMap(32, 32, [set(), set(["wall"]), set(["kill"]), set(["goal"])],
                 [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
                  [1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
                      0, 1, 2, 2, 2, 2, 1, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
                  [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
                      0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
                  [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0,
                      0, 1, 1, 1, 1, 1, 1, 0, 0, 1],
                  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 3, 1],
                  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]])

    world = World(automata, Context(
        blocking_types={"body": ["wall", "body"], "kill": ["kill", "body"]},
        touching_types={"wall": ["wall"], "body": ["goal"]},
        spaces={
            "0": ContextSpace(
                static_colliders=[
                    Collider(
                        "map",
                        set(["wall", "kill", "goal"]),
                        True, True,
                        tm,
                        0, 0, 0, 0)
                ],
                initial_automata=[
                    (automata[0].name, {}, {"x": 32, "y": 2 * 32}), (automata[1].name, {}, {
                        "x": 14 * 32, "y": 1 * 32}), (automata[2].name, {}, {"x": 17 * 32, "y": 9 * 32})
                ],
                links=[]
            )
        }
    ))
    # print world.spaces["0"].valuations[0][0].parameters
    # print world.spaces["0"].valuations
    # print world.spaces["0"].valuations[0][0].parameters['gravity']
    return world


def run_test(filename=None, tilename=None, initial=None):
    import time
    import matplotlib.pyplot as plt

    test_world = load_test(filename, tilename, initial)

    dt = 1.0 / 60.0
    history = []

    t = time.time()
    xidx = test_world.var_ordering[0]["x"]
    for steps in [(120, ["right"]), (120, ["left"]), (60, [])]:
        for i in range(steps[0]):
            step(test_world, steps[1], dt)
            history.append(test_world.cvars[0, 0, 0, 0, xidx])
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
