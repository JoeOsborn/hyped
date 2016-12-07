import ast
import sys
from defusedxml import ElementTree
import schema as h


def parse_expr(expr_str, parameterContext={}, variableContext={}):
    try:
        literal = float(ast.literal_eval(expr_str))
        return h.RealConstant(literal)
    except (SyntaxError, ValueError):
        # TODO: Handle parameters and variables belonging to other HAs.
        t, v, tb = sys.exc_info()
        if expr_str in parameterContext:
            return parameterContext[expr_str]
        elif expr_str in variableContext:
            return variableContext[expr_str]
        else:
            raise t, v, tb


def parse_parameters(haRoot):
    parameter_dict = {}
    for parm in haRoot.findall("param"):
        if parm.attrib["name"] in parameter_dict:
            raise Exception("Duplicate parameter name", parm.attrib["name"],
                            haRoot)
        parameter_dict[parm.attrib["name"]] = h.Parameter(
            parm.attrib["name"],
            h.RealType,
            parse_expr(parm.attrib["value"])
        )
        parameter_dict[parm.attrib["name"]].provenance = parm
    parameters = h.default_parameters()
    for k, v in parameters.items():
        v.provenance = None
    parameters.update(parameter_dict)
    return parameters


def parse_variables(haRoot, parameters):
    variable_dict = {}
    for vbl in haRoot.findall("variable"):
        vname = vbl.attrib["name"]
        if vname in variable_dict:
            raise Exception("Duplicate variable name", vname, haRoot)
        val = parse_expr(vbl.attrib["value"], parameters, {})
        vtype = (vbl.attrib["type"] or
                 (h.PosType if
                  vname[-1] != "'"
                  else None) or
                 (h.VelType if
                  vname[-1] == "'" and
                  vname[-2] != "'"
                  else None) or
                 (h.AccType if
                  vname[-2] == "'" and
                  vname[-1] == "'" and
                  vname[-3] != "'"
                  else None) or
                 val.vtype)
        variable_dict[vname] = h.Variable(
            vname,
            vtype,
            val
        )
        variable_dict[vname].provenance = vbl
    variables = h.default_variables()
    for k, v in variables.items():
        v.provenance = None
    variables.update(variable_dict)
    return variables


def parse_guard(guardXML, params, variables):
    if guardXML is None:
        g = h.GuardTrue()
        g.provenance = guardXML
        return g
    guardType = guardXML.tag
    if guardType == "guard" or guardType == "and":
        g = h.GuardConjunction(
            [
                parse_guard(gx, params, variables) for gx in list(guardXML)
            ])
        g.provenance = guardXML
        return g
    elif guardType == "in_mode":
        # TODO: qualify name?
        g = h.GuardInMode(None, guardXML.attrib["mode"])
        g.provenance = guardXML
        return g
    elif guardType == "button":
        buttonStatus = guardXML.attrib["status"]
        assert buttonStatus in set(["on", "off", "pressed", "released"])
        g = h.GuardButton(guardXML.attrib.get("player", "p1"),
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
        g = h.GuardColliding(myType, normal, theirType)
        g.provenance = guardXML
        return g
    raise NotImplementedError("Unrecognized guard", guardXML)


def parse_flows(xmlNode, parameters, variables):
    flow_dict = {}
    for flow in xmlNode.findall("flow"):
        var = parse_expr(flow.attrib["var"], {}, variables)
        val = parse_expr(flow.attrib["value"], parameters, variables)
        if var.name in flow_dict:
            raise ValueError("Conflicting flows", var, val,
                             flow_dict[var.name], xmlNode)
        # degree is implicit
        flow_dict[var.name] = h.Flow(var, val)
        flow_dict[var.name].provenance = flow
    return flow_dict


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
    e = h.Edge(target, guard, updates)
    e.provenance = xml
    return e


def parse_mode(xml, parameters, variables):
    name = xml.attrib["name"]
    flows = parse_flows(xml, parameters, variables)
    edges = [parse_edge(edgeXML, parameters, variables)
             for edgeXML in xml.findall("edge")]
    groups = [parse_group(groupXML, parameters, variables)
              for groupXML in xml.findall("group")]
    m = h.Mode(name, flows, edges, groups)
    m.provenance = xml
    return m


def parse_group(xml, parameters, variables):
    # parse mode list
    groupName = xml.attrib.get("name", None)
    # TODO: error if no modes
    modes = [parse_mode(modeXML, parameters, variables)
             for modeXML in xml.findall("mode")]
    g = h.Group(groupName, modes)
    g.provenance = xml
    return g


def parse_automaton(path):
    ha = ElementTree.parse(path).getroot()
    name = ha.attrib["name"]
    parameters = parse_parameters(ha)
    variables = parse_variables(ha, parameters)
    colliders = []
    for col in ha.findall("collider"):
        types = set([t.attrib["name"] for t in col.findall("type")])
        guard = parse_guard(col.find("guard"), parameters, variables)
        shapeXML = col.find("rect")
        shape = h.Rect(
            parse_expr(shapeXML.attrib["x"], parameters, variables),
            parse_expr(shapeXML.attrib["y"], parameters, variables),
            parse_expr(shapeXML.attrib["w"], parameters, variables),
            parse_expr(shapeXML.attrib["h"], parameters, variables)
        )
        shape.provenance = shapeXML
        colliders.append(h.Collider(types, guard, shape))
        colliders[-1].provenance = col
    flow_dict = parse_flows(ha, parameters, variables)
    flows = h.default_automaton_flows(parameters, variables)
    for k, v in flows.items():
        v.provenance = None
    flows = h.merge_flows(flows, flow_dict)
    rootGroups = [parse_group(groupXML, parameters, variables)
                  for groupXML in ha.findall("group")]
    automaton = h.Automaton(name, parameters, variables,
                            colliders, flows, rootGroups)
    automaton.provenance = ha
    return automaton
