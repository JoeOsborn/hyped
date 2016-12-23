from collections import namedtuple

# TODO: Replace these "value" things with a thing using namedtuple or
# __slots__=[...]?


class Automaton(namedtuple("Automaton",
                           "name parameters variables colliders flows groups provenance")):
    __slots__ = ()

    def make_valuation():
        pass


class Collider(namedtuple("Collider",
                          "types guard shape provenance")):
    __slots__ = ()


class Shape(object):
    __slots__ = ()


class Rect(namedtuple("Rect",
                      "x y w h provenance"),
           Shape):
    __slots__ = ()


class Guard(object):
    __slots__ = ()


class GuardConjunction(namedtuple("GuardConjunction",
                                  "conjuncts provenance"),
                       Guard):
    __slots__ = ()


class GuardInMode(namedtuple("GuardInMode",
                             "character mode provenance"),
                  Guard):
    __slots__ = ()

    
class GuardJointTransition(namedtuple("GuardJointTransition",
                                      "character mode direction provenance"),
                           Guard):
    __slots__ = ()

    
class GuardColliding(namedtuple("GuardColliding",
                                "self_type normal_check other_type provenance"),
                     Guard):
    __slots__ = ()


class GuardButton(namedtuple("GuardButton",
                             "playerID buttonID status provenance"),
                  Guard):
    __slots__ = ()


class GuardTrue(namedtuple("GuardTrue", "provenance"),
                Guard):
    __slots__ = ()


class UnqualifiedGroup(namedtuple("UnqualifiedGroup",
                                  "name modes provenance")):
    __slots__ = ()


class UnqualifiedMode(namedtuple("UnqualifiedMode",
                                 "name is_initial flows edges groups provenance")):
    __slots__ = ()


class UnqualifiedEdge(namedtuple("UnqualifiedEdge",
                                 "target guard updates provenance")):
    __slots__ = ()


class Group(namedtuple("Group",
                       UnqualifiedGroup._fields + ("qualified_name",))):
    __slots__ = ()


class Mode(namedtuple("Mode",
                      UnqualifiedMode._fields + ("qualified_name",))):
    __slots__ = ()


class Edge(namedtuple("Edge",
                      UnqualifiedEdge._fields + ("qualified_target",))):
    __slots__ = ()


# TODO: replace these with real singletons, or at least real parameterized
# singletons... at least at the moment they have value semantics.
class Type(object):
    __slots__ = ()


class RealType_(Type):
    __slots__ = ()


RealType = RealType_()


class PosType_(RealType_):
    __slots__ = ()
    degree = 0


PosType = PosType_()


class VelType_(RealType_):
    __slots__ = ()
    degree = 1


VelType = VelType_()


class AccType_(RealType_):
    __slots__ = ()
    degree = 2


AccType = AccType_()


class TupleType(namedtuple("TupleType", "values"),
                Type):
    __slots__ = ()


class Expr(object):
    __slots__ = ()


class ConstantExpr(namedtuple("ConstantExpr", "value provenance"),
                   Expr):
    __slots__ = ()


class RealConstant(ConstantExpr):
    __slots__ = ()


class Parameter(namedtuple("Parameter",
                           "name type value provenance"),):
    __slots__ = ()


class Variable(namedtuple("Variable",
                          "name type init provenance")):
    __slots__ = ()

    @property
    def degree(self):
        return self.type.degree

    @property
    def primed_name(self):
        if self.degree == 0:
            return self.name
        elif self.degree == 1:
            return self.name + "'"
        elif self.degree == 2:
            return self.name + "''"


class Flow(namedtuple("Flow", "var value provenance")):
    __slots__ = ()

    @property
    def degree(self):
        return self.var.degree


def all_derivs(v, vbls):
    if v.degree == 0:
        return v, vbls[v.name + "'"], vbls[v.name + "''"]
    elif v.degree == 1:
        return vbls[v.name], v, vbls[v.name + "''"]
    elif v.degree == 2:
        return vbls[v.name], vbls[v.name + "'"], v
    else:
        raise ValueError("Non-derivable variable", v)


def flow_conflict(flows, var):
    return flows.get(var.name, None)

# We assume parent and child aren't internally conflicting.
# If child defines any flow over any variable in parent,
# use the one from child instead, clobbering any control
# from the parent.  So whether the parent defines x=5 or x''=5,
# setting x'=5 in the child will set x''=0 and x=x' dt.


def merge_flows(parent, child):
    r = {}
    r.update(parent)
    r.update(child)
    return r


def default_parameters():
    return {"gravity": Parameter("gravity", RealType, RealConstant(0, "default"), "default")}


def default_variables():
    zero = RealConstant(0, "default")
    return {"x": Variable("x", PosType, zero, "default"),
            "x'": Variable("x", VelType, zero, "default"),
            "x''": Variable("x", AccType, zero, "default"),
            "y": Variable("y", PosType, zero, "default"),
            "y'": Variable("y", VelType, zero, "default"),
            "y''": Variable("y", AccType, zero, "default")}


def default_automaton_flows(parameters, variables):
    flows = {}
    flows["y"] = Flow(variables["y''"], parameters["gravity"], "default")
    return flows


# TODO: CMP/LT/ETC?

# TODO: Relative paths. Need group_in/mode_in to include the cwd?


MODE_SEPARATOR = "."


class GroupPath(namedtuple("GroupPath", "parent_mode groupid")):
    __slots__ = ()

    def __str__(self):
        if self.parent_mode is None:
            return str(self.groupid)
        return str(self.parent_mode)+MODE_SEPARATOR+str(self.groupid)

    def __add__(self, modeid):
        return ModePath(self, modeid)

    @property
    def groups(self):
        if self.parent_mode is None:
            return [self.groupid]
        return self.parent_mode.groups + [self.groupid]

    @property
    def modes(self):
        if self.parent_mode is None:
            return []
        return self.parent_mode.modes

    def group_in(self, groups):
        if self.parent_mode is None:
            return groups[self.groupid]
        mode = self.parent_mode.mode_in(groups)
        return mode.groups[self.groupid]

    @property
    def is_rooted(self):
        return True #return not (self.parent_mode is None)


class ModePath(namedtuple("ModePath", "parent_group modeid")):
    __slots__ = ()

    def __str__(self):
        if self.parent_group is None:
            return str(self.modeid)
        return str(self.parent_group)+MODE_SEPARATOR+str(self.modeid)

    def __add__(self, groupid):
        return GroupPath(self, groupid)

    @property
    def modes(self):
        return self.parent_group.modes + [self.modeid]

    @property
    def groups(self):
        return self.parent_group.groups

    @property
    def parent_mode(self):
        if self.parent_group is None:
            return None
        return self.parent_group.parent_mode

    def mode_in(self, groups):
        group = self.parent_group.group_in(groups)
        return group.modes[self.modeid]

    @property
    def is_rooted(self):
        return True  # return not (self.parent_group is None)


def flat_modes(groups, prefix=None):
    here = []
    for gid, g in groups.items():
        here_path = prefix
        if prefix is None:
            here_path = GroupPath(None, gid)
        else:
            here_path = prefix + gid
        assert isinstance(here_path, GroupPath)
        for mid, m in g.modes.items():
            this_path = here_path + mid
            assert isinstance(this_path, ModePath), this_path
            here.append(this_path)
            here.extend(flat_modes(m.groups, this_path))
    return here


def initial_modes(automaton):
    return [m for m in flat_modes(automaton.groups) if m.is_initial]


def find_target_mode(search_prefix, groups, mode_ref):
    if isinstance(mode_ref, ModePath):
        if mode_ref.is_rooted:
            return mode_ref
        return search_prefix + mode_ref
    group = search_prefix.groups[0]
    # Find all modes with name mode_ref
    modes = flat_modes(groups)
    # TODO: use some lookup logic? for now just assume no overlapping
    # names within one top level group.
    matching = [stk for stk in modes
                if stk.groups[0] == group and
                stk.mode_in(groups).name == mode_ref]
    assert len(matching) != 0, "{} must identify a mode from {}".format(
        mode_ref,
        modes
    )
    assert len(matching) == 1, "Must uniquely identify a mode"
    return matching[0]


def find_guard_mode(search_prefix, groups, mode_ref):
    if isinstance(mode_ref, ModePath):
        if mode_ref.is_rooted:
            return mode_ref
        return search_prefix + mode_ref
    # Find all modes with name mode_ref
    modes = flat_modes(groups)
    # TODO: use some lookup logic?
    matching = [stk for stk in modes
                if stk.mode_in(groups).name == mode_ref]
    assert len(matching) != 0, "{} must identify a mode from {}".format(
        mode_ref,
        modes
    )
    assert len(matching) == 1, "Must uniquely identify a mode"
    return matching[0]


def qualify_guard(prefix, all_groups, g):
    assert isinstance(g, Guard)
    if isinstance(g, GuardConjunction):
        return GuardConjunction([qualify_guard(prefix, all_groups, gi)
                                 for gi in g.conjuncts],
                                g.provenance)
    if isinstance(g, GuardInMode):
        return GuardInMode(g.character,
                           find_guard_mode(prefix, all_groups, g.mode),
                           g.provenance)
    # assume GuardJointTransition already qualified
    return g


def qualify_modes(prefix, all_groups, modes):
    ret = {}
    for mid, m in modes.items():
        # print modes, mid, m
        qname = prefix + mid
        edges = []
        for e in m.edges:
            qualified_target = find_target_mode(qname, all_groups, e.target)
            qualified_guard = qualify_guard(qname, all_groups, e.guard)
            edges.append(Edge(e.target,
                              qualified_guard,
                              e.updates,
                              e.provenance,
                              qualified_target))
        groups = qualify_groups(m.groups, all_groups, qname)
        ret[mid] = Mode(mid,
                        m.is_initial,
                        m.flows,
                        edges,
                        groups,
                        m.provenance,
                        qname)
    return ret


def qualify_groups(groups, all_groups, prefix=None):
    ret = {}
    for gid, g in groups.items():
        if prefix is None:
            here = GroupPath(None, gid)
        else:
            here = prefix + gid
        modes = qualify_modes(here, all_groups, g.modes)
        ret[gid] = Group(gid, modes, g.provenance, here)
    return ret

# TODO: push down flows and transitions into leaves, check for conflicts,
# desugar, etc.

# push the flows on the left (root, parent, etc) down through the groups.
# recurse by calling push_flows(my_flows, childGroups)
# rootGroups = push_flows(flows, rootGroups)

# pushing transitions is attractive but probably not possible since we
# want to be able to transition into a parent group and get any parallel
# child groups started up for free.  Either transitions need to be able to
# turn off/on multiple modes at once, or the transition-performing
# function needs to know which modes to turn off and on for a given source
# and target mode.  either way, naively pushing transitions down is not a
# complete answer.

# TODO: timers! Notice if a state has a timer edge out and if so add a
# state_S_timer variable which increases by 1 per second in that state and
# is reset to 0 on that state entry and exit.

# desugaring:
# push default flows and transitions down into the leaves
# error on possibly-conflicting flows in different modes that
#  might be active simultaneously
# error on possibly-conflicting updates in different modes that
#  might be active simultaneously
# then produce a k-hot encoding, where each leaf mode can be active or not,
#   make 0-1 variables multiplied by flow terms, and have one big
#   "state evolution" expression that multiplies the matrix of 0-1 variables
#   by the matrix of dt-multiplied flows.  something like that.
# for guards, we can do something similar to the above once every
# predicate has turned into a 0-1?  but maybe that can be left for later.
