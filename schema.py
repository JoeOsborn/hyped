from value import Value

# TODO: Replace these "value" things with a thing using namedtuple or
# __slots__=[...]?


class Automaton(Value):

    def __init__(self, name, params, variables, colliders, flows, groups):
        pass

    def make_valuation():
        pass


class Collider(Value):

    def __init__(self, types, guard, shape):
        pass


class Shape(Value):
    pass


class Rect(Shape):

    def __init__(self, x, y, w, h):
        pass


class Guard(Value):
    pass


class GuardConjunction(Guard):

    def __init__(self, conjuncts):
        pass


class GuardInMode(Guard):

    def __init__(self, character, mode):
        pass


class GuardColliding(Guard):

    def __init__(self, selfType, normalCheck, otherType):
        pass


class GuardButton(Guard):

    def __init__(self, playerID, buttonID, status):
        pass


class GuardTrue(Guard):
    pass


class Group(Value):

    def __init__(self, name, modes):
        pass


class Mode(Value):

    def __init__(self, name, flows, edges, groups):
        pass


class Edge(Value):

    def __init__(self, target, guard, updates):
        pass


# TODO: replace these with real singletons, or at least real parameterized
# singletons... at least at the moment they have value semantics.
class Type(Value):

    def __init__(self):
        pass


class RealType_(Type):
    pass


RealType = RealType_()


class PosType_(RealType_):
    degree = 0


PosType = PosType_()


class VelType_(RealType_):
    degree = 1


VelType = VelType_()


class AccType_(RealType_):
    degree = 2


AccType = AccType_()


class TupleType(Type):

    def __init__(self, vtypes):
        self.values = [vt for vt in vtypes]


class Expr(Value):
    pass


class ConstantExpr(Expr):

    def __init__(self, value):
        pass


class RealConstant(ConstantExpr):
    pass


class Parameter(Value):

    def __init__(self, name, type, value):
        pass


class Variable(Value):

    def __init__(self, name, type, init):
        pass

    @property
    def degree(self):
        return self.type.degree


class Flow(Value):

    def __init__(self, var, value):
        pass

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
    return {"gravity": Parameter("gravity", RealType, RealConstant(0))}


def default_variables():
    return {"x": Variable("x", PosType, 0),
            "x'": Variable("x", VelType, 0),
            "x''": Variable("x", AccType, 0),
            "y": Variable("y", PosType, 0),
            "y'": Variable("y", VelType, 0),
            "y''": Variable("y", AccType, 0)}


def default_automaton_flows(parameters, variables):
    flows = {}
    flows["y"] = Flow(variables["y''"], parameters["gravity"])
    return flows


# TODO: fully qualify names and references to names, push down flows and
# transitions into leaves, check for conflicts, desugar, etc.

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

# TODO: also might be worth annotating objects with the XML we loaded them
# from?  Maybe later?

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
