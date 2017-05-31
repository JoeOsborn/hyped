import ast
import sys
from lxml import etree as ElementTree
import schema as h
import sympy
import sympy.abc


def parse_expr(expr_str,
               parameterContext={}, variableContext={}, dvariableContext={}):
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
        elif expr_str in dvariableContext:
            return dvariableContext[expr_str]
        else:
            # TODO: parse math expressions here
            return sympy.S(expr_str, sympy.abc._clash)


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
        vtype = (vbl.attrib.get("type", None) or
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


def parse_dvariables(haRoot, parameters):
    variable_dict = {}
    for vbl in haRoot.findall("dvariable"):
        vname = vbl.attrib["name"]
        if vname in variable_dict:
            raise Exception("Duplicate variable name", vname, haRoot)
        val = parse_expr(vbl.attrib["value"], parameters, {})
        vtype = (vbl.attrib.get("type", None) or
                 val.vtype if isinstance(val, h.Parameter) else h.RealType)
        variable_dict[vname] = h.Variable(
            vname,
            vname,
            vtype,
            val,
            vbl
        )
    variables = h.default_dvariables()
    variables.update(variable_dict)
    return variables


def parse_guard(guardXML, params, variables, dvariables):
    if guardXML is None:
        g = h.GuardTrue(guardXML)
        return g
    guardType = guardXML.tag
    if guardType == "guard" or guardType == "and":
        g = h.GuardConjunction(
            [
                parse_guard(gx, params, variables, dvariables) for gx in list(guardXML)
            ],
            guardXML)
        return g
    elif guardType == "or":
        g = h.GuardDisjunction(
            [
                parse_guard(gx, params, variables, dvariables) for gx in list(guardXML)
            ],
            guardXML)
        return g
    elif guardType == "timer":
        g = h.GuardTimer(
            parse_expr(guardXML.attrib["limit"],
                       params, variables, dvariables),
            guardXML
        )
        return g
    elif guardType == "compare":
        g = h.GuardCompare(
            parse_expr(guardXML.attrib["left"], params, variables, dvariables),
            guardXML.attrib["op"],
            parse_expr(guardXML.attrib["right"],
                       params, variables, dvariables),
            guardXML
        )
        return g
    elif guardType == "in_mode":
        # TODO: qualify name?
        g = h.GuardInMode(
            None,
            parse_mode_ref(guardXML.attrib["mode"]),
            guardXML)
        return g
    elif guardType == "joint_transition":
        # TODO: qualify name?
        g = h.GuardJointTransition(
            None,
            guardXML.attrib.get("direction", "enter"),
            parse_mode_ref(guardXML.attrib["mode"]),
            guardXML)
        return g
    elif guardType == "not":
        assert(len(list(guardXML)) == 1)
        g = h.GuardNegation(
            parse_guard(list(guardXML)[0], params, variables, dvariables),
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
            normal = (0, 1)
        elif normal == "bottom":
            normal = (0, -1)
        elif normal == "right":
            normal = (1, 0)
        elif normal == "left":
            normal = (-1, 0)
        theirType = guardXML.attrib.get("othertype", None)
        g = h.GuardColliding(myType, normal, theirType, guardXML)
        return g
    raise NotImplementedError("Unrecognized guard", guardXML)


def parse_flows(xmlNode, parameters, variables, dvariables):
    flow_dict = {}
    for flow in xmlNode.findall("flow"):
        var = parse_expr(flow.attrib["var"],
                         {}, variables, dvariables)
        val = parse_expr(flow.attrib["value"],
                         parameters, variables, dvariables)
        if var.name in flow_dict:
            raise ValueError("Conflicting flows", var, val,
                             flow_dict[var.name], xmlNode)
        # degree is implicit
        flow_dict[var.name] = h.Flow(var, val, flow)
    return flow_dict


def parse_edge(xml, parameters, variables, dvariables):
    target = parse_mode_ref(xml.attrib["target"])
    # TODO: error if multiple guards
    guard = parse_guard(xml.find("guard"),
                        parameters, variables, dvariables)
    updates = {}
    for update in xml.findall("update"):
        var = update.attrib["var"]
        if var in updates:
            raise ValueError("Conflicting update", var,
                             update.attrib["value"], updates)
        updates[var] = parse_expr(update.attrib["value"],
                                  parameters,
                                  variables,
                                  dvariables)
    e = h.UnqualifiedEdge(target, guard, updates, xml)
    return e


def parse_follow_link(xml, parameters, variables, dvariables):
    # TODO: error if multiple guards
    guard = parse_guard(xml.find("guard"),
                        parameters, variables, dvariables)
    updates = {}
    for update in xml.findall("update"):
        var = update.attrib["var"]
        if var in updates:
            raise ValueError("Conflicting update", var,
                             update.attrib["value"], updates)
        updates[var] = parse_expr(update.attrib["value"],
                                  parameters,
                                  variables,
                                  dvariables)
    f = h.FollowLink(guard, updates, xml)
    return f


def parse_envelope(xml, parameters, variables, dvariables):
    # TODO: handle n-way
    refl_count = int(xml.attrib["ways"], 10)
    vbls = [parse_expr(v.attrib["var"],
                       {}, variables, dvariables)
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
    guard = parse_guard(xml.find("guard"),
                        parameters, variables, dvariables)
    attack = xml.find("attack")
    attack_acc = parse_expr(attack.attrib["acc"],
                            parameters, variables, dvariables)
    # TODO: instant attack
    # TODO: decay
    # decay = xml.find("decay")
    sustain = xml.find("sustain")
    sustain_rate = parse_expr(sustain.attrib["level"],
                              parameters, variables, dvariables)
    release = xml.find("release")
    if (release is not None) and "hold" in release.attrib:
        assert "level" not in release.attrib
        assert "acc" not in release.attrib
        release_settings = ("hold",)
    elif (release is not None) and "acc" in release.attrib:
        release_settings = ("acc",
                            parse_expr(release.attrib.get("acc"),
                                       parameters,
                                       variables,
                                       dvariables),
                            parse_expr(release.attrib.get("level", "0"),
                                       parameters,
                                       variables,
                                       dvariables))
    else:
        assert (release is None) or "level" in release.attrib
        release_settings = ("set",
                            parse_expr(release.attrib.get("level", "0")
                                       if release is not None else 0,
                                       parameters,
                                       variables,
                                       dvariables))
    return h.Envelope(refl_count,
                      vbls, axes,
                      guard,
                      # TODO hard coded for no real sustain
                      ("acc", attack_acc, "level", sustain_rate),
                      ("acc", 0, "level", sustain_rate),
                      ("level", sustain_rate),
                      release_settings,
                      xml)


def parse_mode(xml, is_initial, parameters, variables, dvariables):
    name = xml.attrib["name"]
    flows = parse_flows(xml, parameters, variables, dvariables)
    envelopes = [parse_envelope(envXML, parameters, variables, dvariables)
                 for envXML in xml.findall("envelope")]
    edges = [parse_edge(edgeXML, parameters, variables, dvariables)
             for edgeXML in xml.findall("edge")]
    follows = [parse_follow_link(followXML, parameters, variables, dvariables)
               for followXML in xml.findall("follow_link")]
    groups = [parse_group(groupXML, parameters, variables, dvariables)
              for groupXML in xml.findall("group")]
    groupsByName = {g.name: g for g in groups}
    m = h.UnqualifiedMode(name, is_initial,
                          flows, envelopes,
                          edges, follows,
                          groupsByName,
                          xml)
    return m


def parse_group(xml, parameters, variables, dvariables):
    # parse mode list
    groupName = xml.attrib.get("name", None)
    # TODO: error if no modes
    modes = [parse_mode(modeXML, mi == 0, parameters, variables, dvariables)
             for mi, modeXML in enumerate(xml.findall("mode"))]
    modesByName = {m.name: m for m in modes}
    g = h.UnqualifiedGroup(groupName, modesByName, xml)
    return g


def parse_automaton(path):
    schema = ElementTree.RelaxNG(file="resources/schema.rng")
    #print "Parsing", path
    ha = ElementTree.parse(
        path,
        parser=ElementTree.ETCompatXMLParser()).getroot()
    schema.assertValid(ha)
    name = ha.attrib["name"]
    parameters = parse_parameters(ha)
    variables = parse_variables(ha, parameters)
    dvariables = parse_dvariables(ha, parameters)
    colliders = []
    for col in ha.findall("collider"):
        types = set([t.attrib["name"] for t in col.findall("type")])
        guard = parse_guard(col.find("guard"),
                            parameters, variables, dvariables)
        # TODO: ensure no timer or colliding guards
        shapeXML = col.find("rect")
        shape = h.Rect(
            parse_expr(shapeXML.attrib["x"],
                       parameters, variables, dvariables),
            parse_expr(shapeXML.attrib["y"],
                       parameters, variables, dvariables),
            parse_expr(shapeXML.attrib["w"],
                       parameters, variables, dvariables),
            parse_expr(shapeXML.attrib["h"],
                       parameters, variables, dvariables),
            shapeXML
        )
        static = col.attrib.get("static", "false") == "true"
        colliders.append(h.Collider(types, guard, shape, static, col))
    flow_dict = parse_flows(ha, parameters, variables, dvariables)
    flows = {}  # h.default_automaton_flows(parameters, variables)
    flows = h.merge_flows(flows, flow_dict)
    rootGroups = [parse_group(groupXML, parameters, variables, dvariables)
                  for groupXML in ha.findall("group")]
    rootGroupsByName = {g.name: g for g in rootGroups}
    qualifiedRootGroups = h.qualify_groups(rootGroupsByName, rootGroupsByName)
    automaton = h.Automaton(name, parameters, variables, dvariables,
                            colliders, flows, qualifiedRootGroups,
                            ha)
    return automaton
