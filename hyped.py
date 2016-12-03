import ast
import sys
from value import Value
from defusedxml import ElementTree

# TODO: Replace these "value" things with a thing using namedtuple or __slots__=[...]?

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


# TODO: replace these with real singletons, or at least real parameterized singletons... at least at the moment they have value semantics.
class Type(Value):
    def __init__(self):
        pass


class RealType_(Type):
    pass


RealType = RealType_()


class PosType_(RealType_):
    order = 0


PosType = PosType_()


class VelType_(RealType_):
    order = 1


VelType = VelType_()


class AccType_(RealType_):
    order = 2


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
    def order(self):
        return self.type.order


class Flow(Value):

    def __init__(self, var, value):
        pass

    @property
    def order(self):
        return self.var.order


def parse_expr(expr_str, parameterContext={}, variableContext={}):
    try:
        literal = float(ast.literal_eval(expr_str))
        return RealConstant(literal)
    except (SyntaxError, ValueError):
        # TODO: Handle parameters and variables belonging to other HAs.
        t, v, tb = sys.exc_info()
        if expr_str in parameterContext:
            return parameterContext[expr_str]
        elif expr_str in variableContext:
            return variableContext[expr_str]
        else:
            raise t, v, tb


def all_derivs(v, vbls):
    if v.order == 0:
        return v, vbls[v.name + "'"], vbls[v.name + "''"]
    elif v.order == 1:
        return vbls[v.name], v, vbls[v.name + "''"]
    elif v.order == 2:
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


flappy = ElementTree.parse("resources/flappy.char.xml").getroot()

name = flappy.attrib["name"]
parameter_dict = {}
for parm in flappy.findall("param"):
    if parm.attrib["name"] in parameter_dict:
        raise Exception("Duplicate parameter name", parm.attrib["name"],
                        flappy)
    parameter_dict[parm.attrib["name"]] = Parameter(
        parm.attrib["name"],
        RealType,
        parse_expr(parm.attrib["value"])
    )
    parameter_dict[parm.attrib["name"]].provenance = parm
parameters = {"gravity": Parameter("gravity", RealType, RealConstant(0))}
parameters["gravity"].provenance = None
parameters.update(parameter_dict)

variable_dict = {}
for vbl in flappy.findall("variable"):
    vname = vbl.attrib["name"]
    if vname in variable_dict:
        raise Exception("Duplicate variable name", vname, flappy)
    val = parse_expr(vbl.attrib["value"], parameters, {})
    vtype = (vbl.attrib["type"] or
             (PosType if
              vname[-1] != "'"
              else None) or
             (VelType if
              vname[-1] == "'" and
              vname[-2] != "'"
              else None) or
             (AccType if
              vname[-2] == "'" and
              vname[-1] == "'" and
              vname[-3] != "'"
              else None) or
             val.vtype)
    variable_dict[vname] = Variable(
        vname,
        vtype,
        val
    )
    variable_dict[vname].provenance = vbl
variables = {"x": Variable("x", PosType, 0),
             "x'": Variable("x", VelType, 0),
             "x''": Variable("x", AccType, 0),
             "y": Variable("y", PosType, 0),
             "y'": Variable("y", VelType, 0),
             "y''": Variable("y", AccType, 0)}
for k,v in variables.items():
    v.provenance = None
variables.update(variable_dict)


def parse_guard(guardXML, params, variables):
    if guardXML is None:
        g = GuardTrue()
        g.provenance = guardXML
        return g
    guardType = guardXML.tag
    if guardType == "guard" or guardType == "and":
        g = GuardConjunction(
            [
                parse_guard(g, params, variables) for g in list(guardXML)
            ])
        g.provenance = guardXML
        return g
    elif guardType == "in_mode":
        # TODO: qualify name?
        g = GuardInMode(None, guardXML.attrib["mode"])
        g.provenance = guardXML
        return g
    elif guardType == "button":
        buttonStatus = guardXML.attrib["status"]
        assert buttonStatus in set(["on", "off", "pressed", "released"])
        g = GuardButton(guardXML.attrib.get("player", "p1"),
                           guardXML.attrib["name"],
                           buttonStatus)
        g.provenance = guardXML
        return g
    elif guardType == "colliding":
        myType = guardXML.attrib.get("type", None)
        normal = guardXML.attrib.get("normal", None)
        if normal == "top":
            normal = (0, -1)
        elif normal == "bottom":
            normal = (0, 1)
        elif normal == "right":
            normal = (1, 0)
        elif normal == "left":
            normal = (-1, 0)
        theirType = guardXML.attrib.get("othertype", None)
        g = GuardColliding(myType, normal, theirType)
        g.provenance = guardXML
        return g
    raise NotImplementedError("Unrecognized guard", guardXML)


colliders = []
for col in flappy.findall("collider"):
    types = set([t.attrib["name"] for t in col.findall("type")])
    guard = parse_guard(col.find("guard"), parameters, variables)
    shapeXML = col.find("rect")
    shape = Rect(
        parse_expr(shapeXML.attrib["x"], parameters, variables),
        parse_expr(shapeXML.attrib["y"], parameters, variables),
        parse_expr(shapeXML.attrib["w"], parameters, variables),
        parse_expr(shapeXML.attrib["h"], parameters, variables)
    )
    shape.provenance = shapeXML
    colliders.append(Collider(types, guard, shape))
    colliders[-1].provenance = col


def get_flows(xmlNode, parameters, variables):
    flow_dict = {}
    for flow in xmlNode.findall("flow"):
        var = parse_expr(flow.attrib["var"], {}, variables)
        val = parse_expr(flow.attrib["value"], parameters, variables)
        if var.name in flow_dict:
            raise ValueError("Conflicting flows", var, val,
                             flow_dict[var.name], flappy)
        # order is implicit
        flow_dict[var.name] = Flow(var, val)
        flow_dict[var.name].provenance = flow
    return flow_dict


flow_dict = get_flows(flappy, parameters, variables)
flows = {}
flows["y"] = Flow(variables["y''"], parameters["gravity"])
flows["y"].provenance = None
flows = merge_flows(flows, flow_dict)


def parse_edge(xml, parameters, variables):
    target = xml.attrib["target"]
    # TODO: error if multiple guards
    guard = parse_guard(xml.find("guard"), parameters, variables)
    updates = {}
    for update in xml.findall("update"):
        var = update.attrib["var"]
        if var in updates:
            raise ValueError("Conflicting update", var,
                             update.attrib["val"], updates)
        updates[var] = parse_expr(update.attrib["val"], parameters, variables)
    e = Edge(target, guard, updates)
    e.provenance = xml
    return e


def parse_mode(xml, parameters, variables):
    name = xml.attrib["name"]
    flows = get_flows(xml, parameters, variables)
    edges = [parse_edge(edgeXML, parameters, variables)
             for edgeXML in xml.findall("edge")]
    groups = [parse_group(groupXML, parameters, variables)
              for groupXML in xml.findall("group")]
    m = Mode(name, flows, edges, groups)
    m.provenance = xml
    return m


def parse_group(xml, parameters, variables):
    # parse mode list
    groupName = xml.attrib.get("name", None)
    # TODO: error if no modes
    modes = [parse_mode(modeXML, parameters, variables)
             for modeXML in xml.findall("mode")]
    g = Group(groupName, modes)
    g.provenance = groupXML
    return g

rootGroups = [parse_group(groupXML, parameters, variables)
              for groupXML in flappy.findall("group")]

automaton = Automaton(name, parameters, variables, colliders, flows, rootGroups)
automaton.provenance = flappy


# TODO: fully qualify names and references to names, push down flows and transitions into leaves, check for conflicts, desugar, etc.

# push the flows on the left (root, parent, etc) down through the groups. recurse by calling push_flows(my_flows, childGroups)
#rootGroups = push_flows(flows, rootGroups)

# pushing transitions is attractive but probably not possible since we want to be able to transition into a parent group and get any parallel child groups started up for free.  Either transitions need to be able to turn off/on multiple modes at once, or the transition-performing function needs to know which modes to turn off and on for a given source and target mode.  either way, naively pushing transitions down is not a complete answer.

# TODO: also might be worth annotating objects with the XML we loaded them from?  Maybe later?

# TODO: timers! Notice if a state has a timer edge out and if so add a state_S_timer variable which increases by 1 per second in that state and is reset to 0 on that state entry and exit.

# desugaring:
# push default flows and transitions down into the leaves
# error on possibly-conflicting flows in different modes that might be active simultaneously
# error on possibly-conflicting updates in different modes that might be active simultaneously
# then produce a k-hot encoding, where each leaf mode can be active or not, make 0-1 variables multiplied by flow terms, and have one big "state evolution" expression that multiplies the matrix of 0-1 variables by the matrix of dt-multiplied flows.  something like that.
# for guards, we can do something similar to the above once every
# predicate has turned into a 0-1?  but maybe that can be left for later.
