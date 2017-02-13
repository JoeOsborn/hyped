import ast
import sys
from defusedxml import ElementTree
import schema as h


def parse_expr(expr_str, parameterContext={}, variableContext={}):
    try:
        literal = float(ast.literal_eval(expr_str))
        return h.RealConstant(literal, expr_str)
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
            parse_expr(parm.attrib["value"]),
            parm
        )
    parameters = h.default_parameters()
    parameters.update(parameter_dict)
    return parameters


def parse_mode_ref(modestr):
    # is it just a name or a path?
    chunks = modestr.split(h.MODE_SEPARATOR)
    if len(chunks) == 1:
        # TODO: return a relative path
        return chunks[0]
    path = h.GroupPath(None, chunks[0])
    for c in chunks[1:]:
        path = path + c
    return path


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
        basename = vname.rstrip("'")
        variable_dict[vname] = h.Variable(
            vname,
            basename,
            vtype,
            val,
            vbl
        )
    variables = h.default_variables()
    variables.update(variable_dict)
    return variables


def parse_guard(guardXML, params, variables):
    if guardXML is None:
        g = h.GuardTrue(guardXML)
        return g
    guardType = guardXML.tag
    if guardType == "guard" or guardType == "and":
        g = h.GuardConjunction(
            [
                parse_guard(gx, params, variables) for gx in list(guardXML)
            ],
            guardXML)
        return g
    elif guardType == "in_mode":
        # TODO: qualify name?
        g = h.GuardInMode(
            None,
            parse_mode_ref(guardXML.attrib["mode"]),
            guardXML)
        return g
    elif guardType == "button":
        buttonStatus = guardXML.attrib["status"]
        assert buttonStatus in set(["on", "off", "pressed", "released"])
        g = h.GuardButton(guardXML.attrib.get("player", "p1"),
                          guardXML.attrib["name"],
                          buttonStatus,
                          guardXML)
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
        g = h.GuardColliding(myType, normal, theirType, guardXML)
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
        flow_dict[var.name] = h.Flow(var, val, flow)
    return flow_dict


def parse_edge(xml, parameters, variables):
    target = parse_mode_ref(xml.attrib["target"])
    # TODO: error if multiple guards
    guard = parse_guard(xml.find("guard"), parameters, variables)
    updates = {}
    for update in xml.findall("update"):
        var = update.attrib["var"]
        if var in updates:
            raise ValueError("Conflicting update", var,
                             update.attrib["val"], updates)
        updates[var] = parse_expr(update.attrib["val"], parameters, variables)
    e = h.UnqualifiedEdge(target, guard, updates, xml)
    return e


def parse_envelope(xml, parameters, variables):
    refl_count = int(xml.attrib["ways"], 10)
    vbls = [parse_expr(v.attrib["var"], {}, variables)
            for v in xml.findall("control")]
    axes = [(ax.attrib.get("player", "p1"),
             ax.attrib["name"])
            for ax in xml.findall("axis")]
    if refl_count <= 2:
        assert len(vbls) == 1
        assert len(axes) == 1
    else:
        assert len(vbls) == 2
        assert len(axes) == 2
    guard = parse_guard(xml.find("guard"), parameters, variables)
    attack = xml.find("attack")
    attack_acc = parse_expr(attack.attrib["acc"], parameters, variables)
    # TODO: instant attack
    # TODO: decay
    # decay = xml.find("decay")
    sustain = xml.find("sustain")
    sustain_rate = parse_expr(sustain.attrib["level"], parameters, variables)
    release = xml.find("release")
    if (release is not None) and "hold" in release.attrib:
        assert "level" not in release.attrib
        assert "acc" not in release.attrib
        release_settings = ("hold")
    elif (release is not None) and "acc" in release.attrib:
        release_settings = ("acc",
                            parse_expr(release.attrib.get("acc"),
                                       parameters,
                                       variables),
                            parse_expr(release.attrib.get("level", "0"),
                                       parameters,
                                       variables))
    else:
        assert (release is None) or "level" in release.attrib
        release_settings = ("set",
                            parse_expr(release.attrib.get("level", "0")
                                       if release is not None else 0,
                                       parameters,
                                       variables))
    return h.Envelope(refl_count,
                      vbls, axes,
                      guard,
                      # TODO hard coded for no real sustain
                      ("acc", attack_acc, "level", sustain_rate),
                      ("acc", 0, "level", sustain_rate),
                      ("level", sustain_rate),
                      release_settings,
                      xml)


def parse_mode(xml, is_initial, parameters, variables):
    name = xml.attrib["name"]
    flows = parse_flows(xml, parameters, variables)
    envelopes = [parse_envelope(envXML, parameters, variables)
                 for envXML in xml.findall("envelope")]
    edges = [parse_edge(edgeXML, parameters, variables)
             for edgeXML in xml.findall("edge")]
    groups = [parse_group(groupXML, parameters, variables)
              for groupXML in xml.findall("group")]
    groupsByName = {g.name: g for g in groups}
    m = h.UnqualifiedMode(name, is_initial,
                          flows, envelopes,
                          edges, groupsByName,
                          xml)
    return m


def parse_group(xml, parameters, variables):
    # parse mode list
    groupName = xml.attrib.get("name", None)
    # TODO: error if no modes
    modes = [parse_mode(modeXML, mi == 0, parameters, variables)
             for mi, modeXML in enumerate(xml.findall("mode"))]
    modesByName = {m.name: m for m in modes}
    g = h.UnqualifiedGroup(groupName, modesByName, xml)
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
            parse_expr(shapeXML.attrib["h"], parameters, variables),
            shapeXML
        )
        colliders.append(h.Collider(types, guard, shape, col))
    flow_dict = parse_flows(ha, parameters, variables)
    flows = h.default_automaton_flows(parameters, variables)
    flows = h.merge_flows(flows, flow_dict)
    rootGroups = [parse_group(groupXML, parameters, variables)
                  for groupXML in ha.findall("group")]
    rootGroupsByName = {g.name: g for g in rootGroups}
    qualifiedRootGroups = h.qualify_groups(rootGroupsByName, rootGroupsByName)
    automaton = h.Automaton(name, parameters, variables,
                            colliders, flows, qualifiedRootGroups,
                            ha)
    return automaton
