import ast
import sys
from value import Value
from defusedxml import ElementTree


class Automaton(Value):

    def __init__(self, name, params, variables, colliders, flows, group):
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


class Group(Value):

    def __init__(self, name, modes):
        pass


class Mode(Value):

    def __init__(self, name, flows, edges):
        pass


class Edge(Value):

    def __init__(self, target, guard, updates):
        pass


class RealType_(Value):

    def __init__(self):
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
parameters = {"gravity": Parameter("gravity", RealType, RealConstant(0))}
parameters.update(parameter_dict)

variable_dict = {}
for vbl in flappy.findall("variable"):
    vname = vbl.attrib["name"]
    if vname in variable_dict:
        raise Exception("Duplicate variable name", vname, flappy)
    val = parse_expr(parm.attrib["value"], parameters)
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
    variable_dict[vbl.attrib["name"]] = Variable(
        parm.attrib["name"],
        vtype,
        val
    )
variables = {"x": Variable("x", PosType, 0),
             "x'": Variable("x", VelType, 0),
             "x''": Variable("x", AccType, 0),
             "y": Variable("y", PosType, 0),
             "y'": Variable("y", VelType, 0),
             "y''": Variable("y", AccType, 0)}
variables.update(variable_dict)


def get_flows(xmlNode, parameters, variables):
    flow_dict = {}
    for flow in xmlNode.findall("flow"):
        var = parse_expr(flow.attrib["var"], {}, variables)
        val = parse_expr(flow.attrib["value"], parameters, variables)
        order = var.order
        if var.name in flow_dict:
            raise ValueError("Conflicting flows", var, val,
                             flow_dict[var.name], flappy)
        # order is implicit
        flow_dict[var.name] = Flow(var, val)
    return flow_dict


flow_dict = get_flows(flappy, parameters, variables)
flows = {}
flows["y"] = Flow(variables["y''"], parameters["gravity"])
flows = merge_flows(flows, flow_dict)
# find all the params and variables and make sympy variables or something
# then parse the other expressions (flows, etc) as expressions
# push default flows and transitions down into the leaves
# error on possibly-conflicting flows in different modes that might be active simultaneously
# error on possibly-conflicting updates in different modes that might be active simultaneously
# then produce a k-hot encoding, where each leaf mode can be active or not, make 0-1 variables multiplied by flow terms, and have one big "state evolution" expression that multiplies the matrix of 0-1 variables by the matrix of dt-multiplied flows.  something like that.
# for guards, we can do something similar to the above once every
# predicate has turned into a 0-1?  but maybe that can be left for later.
