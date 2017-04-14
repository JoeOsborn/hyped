import z3
import z3.z3util as z3u
import hyped.schema as h
import hyped.xmlparser as xmlparser
import itertools
import copy
import re


def simplify(expr):
    tac = z3.Then(
        z3.Tactic('purify-arith'),
        z3.Tactic('simplify'),
        z3.Tactic('propagate-values'),
        z3.Tactic('propagate-ineqs'),
        # Tactic('sat-preprocess'),
        z3.Tactic('ctx-solver-simplify'),
        # Tactic('split-clause'),
        # Tactic('elim-and'),
        z3.Tactic('solve-eqs'),
        z3.Tactic('propagate-ineqs'),
        z3.Tactic('ctx-solver-simplify')
    )
    simp = tac(expr)
    return simp.as_expr()


def flatten(listOfLists):
    return list(itertools.chain.from_iterable(listOfLists))

# NOTE: because I want to find equations as a result, and not just models,
# it would be better to use z3 than z3.  but I can probably reuse a
# bunch of this code!  and at any rate the stuff below gives a template
# for future symbolic execution stuff.


mario = xmlparser.parse_automaton("resources/mario.char.xml")

# "Flows" now will contain both Flow and Envelope objects


def merge_flows(f1s, f2s, e2s):
    f1s = copy.deepcopy(f1s)
    fkeys2 = {flow.var.basename: flow for vn, flow in f2s.items()}
    ekeys2 = {}
    for e in e2s:
        ekeys2[e.variables[0].basename] = e
        if e.reflections > 2:
            ekeys2[e.variables[1].basename] = e
    f1s.update(fkeys2)
    f1s.update(ekeys2)
    return f1s


def sym_eval(ha, val, param_symbols):
    if isinstance(val, h.Parameter):
        return param_symbols[val.name]
    elif isinstance(val, h.Variable):
        return z3.Real(val.name)
    else:
        return z3.RealVal(val.value)


button_symbols = {
    k: z3.Bool(k)
    for k in ["p1_left",
              "p1_right",
              "p1_up",
              "p1_down",
              "p1_jump",
              "p1_flap"]
}


def Eq(lhs, rhs):
    return Rel(lhs, rhs, "==")


def Ge(lhs, rhs):
    return Rel(lhs, rhs, ">=")


def Le(lhs, rhs):
    return Rel(lhs, rhs, "<=")


def Ne(lhs, rhs):
    return Rel(lhs, rhs, "!=")


def Lt(lhs, rhs):
    return Rel(lhs, rhs, "<")


def Gt(lhs, rhs):
    return Rel(lhs, rhs, "<")


def Rel(lhs, rhs, op):
    if op == "<":
        return lhs < rhs
    elif op == "<=":
        return lhs <= rhs
    elif op == "==":
        return lhs == rhs
    elif op == ">=":
        return lhs >= rhs
    elif op == ">":
        return lhs > rhs
    elif op == "!=":
        return lhs != rhs
    else:
        assert False


def guard_to_z3(ha, guard, t, param_symbols):
    if isinstance(guard, h.GuardTimer):
        return t >= sym_eval(ha, guard.threshold, param_symbols)
    elif isinstance(guard, h.GuardCompare):
        # TODO: handle expressions on LHS, RHS
        lhs = sym_eval(ha, guard.left, param_symbols)
        rhs = sym_eval(ha, guard.right, param_symbols)
        return Rel(lhs, rhs, guard.operator)
    elif isinstance(guard, h.GuardConjunction):
        return z3.And(*[guard_to_z3(ha, g, t, param_symbols)
                        for g in guard.conjuncts])
    elif isinstance(guard, h.GuardDisjunction):
        return z3.Or(*[guard_to_z3(ha, g, t, param_symbols)
                       for g in guard.disjuncts])
    elif isinstance(guard, h.GuardNegation):
        return z3.Not(guard_to_z3(ha, guard.guard, t, param_symbols))
    elif isinstance(guard, h.GuardButton):
        # We can handle buttons specially since they have a boolean in them
        # already
        bsym = button_symbols[str(guard.playerID + "_" + guard.buttonID)]
        return (bsym if guard.status == "on" or guard.status == "pressed"
                else z3.Not(bsym))
    elif isinstance(guard, h.GuardTrue):
        return z3.BoolVal(True)
    elif isinstance(guard, h.GuardFalse):
        return z3.BoolVal(False)
    else:
        # any other guard we just turn into a boolean variable
        return z3.Bool(str(guard))


# Call me with a state and the merged flows for that state.
#  Probably best not to call this on a state that has child states
#  since no effort is made to consider child flows.  Also, any parent
#  guards might constrain the state even more; in fact, in general,
#  because this state might be active with arbitrary other states,
#  this invariant will be an over-approximation.
def invariants(ha, state, flows_and_envelopes):
    param_symbols = {pn: z3.Real(pn) for pn in ha.parameters}
    t = z3.Real("t")
    variable_symbols = {"t": t}
    motion_eqs = {}
    for v in ha.variables.values():
        if v.type != h.VelType:
            continue
        v0 = z3.Real(v.name + "_")
        v1 = z3.Real(v.name)
        param_symbols[v.name + "_"] = v0
        variable_symbols[v.name] = v1

        if v.basename not in flows_and_envelopes:
            continue
        mover = flows_and_envelopes[v.basename]
        if isinstance(mover, h.Flow):
            motion_eqs[str(v1)] = Eq(v0, v1)
            flow_degree = flows_and_envelopes[v.basename].degree
            flow_val_z = sym_eval(
                ha, flows_and_envelopes[v.basename].value, param_symbols)
            if flow_degree == 2:
                motion_eqs[str(v1)] = Eq(v0 + flow_val_z * t, v1)
            elif flow_degree == 1:
                motion_eqs[str(v1)] = Eq(flow_val_z, v1)
            elif flow_degree == 0:
                assert False, "not supported"
            print motion_eqs[str(v1)]
        elif isinstance(mover, h.Envelope):
            # Only support sustain envelopes and ignore attack/decay/release.
            # TODO: support cases where attack goes up higher than sustain
            # or maybe do something appropriate with release or the input axes?
            sustain = sym_eval(ha, mover.sustain[1], param_symbols)
            motion_eqs[str(v1)] = z3.And(Ge(v1, -sustain),
                                         Le(v1, sustain))
        else:
            assert False, str(mover)

    #  We could get tighter invariants if we considered envelopes as well.
    # For instance, if we had an x velocity envelope and a guard that exited
    # if vx exceeded something then we could catch that.

    # NOTE: assumes s1 has no child group

    # inv: conjunction  of invariant bits and bobs
    inv = [Ge(t, 0)]
    edges = state.edges
    for ei, e in enumerate(edges):
        guard = guard_to_z3(ha, e.guard, t, param_symbols)
        print "TC:", guard
        inv.append(z3.Not(guard))
    invariant = z3.And(*inv)
    print "Invariant0:", invariant
    # Let's put all the equations and constraints of motion in, only now we
    # have to also consider that they might arbitrarily be 0 due to collisions
    param_subs = [(param_symbols[p.name], z3.RealVal(p.value.value))
                  for p in ha.parameters.values()]
    print param_subs
    invariant = z3.substitute(invariant, param_subs)
    # TODO: should really work on an instance.
    # Or be in a different function!
    # Param choices can totally change the invariant.

    print "Invariant01:", invariant

    subsed_motion_eqs = {
        k: z3.substitute(me, param_subs)
        for k, me in motion_eqs.items()}

    # If all edges into a state set a variable to a given value, we can
    # replace the v_' with that value; here we assume it for jump_control
    # TODO: do for real
    if state.name == "jump_control":
        subs = [(param_symbols["y'_"],
                 z3.RealVal(200))]
        invariant = z3.substitute(invariant, subs)
        subsed_motion_eqs = {
            k: z3.substitute(me, subs)
            for k, me in subsed_motion_eqs.items()}

    move_eqs = [z3.Or(z3.And(z3.Not(z3.Bool(vbl + "_blocked")),
                             meq),
                      z3.And(z3.Bool(vbl + "_blocked"),
                             Eq(variable_symbols[vbl],
                                z3.RealVal(0))))
                for vbl, meq in subsed_motion_eqs.items()]
    print "Move_eqs:", move_eqs
    move_eqs = z3.And(*move_eqs)
    # If there are collision guards involving something with a normal, we can
    # force them to have the same truth value as the corresponding blocking
    # predicate.
    col_re = re.compile(
        "GuardColliding\(.*normal_check=\((-?[01])\, (-?[01])\).*\)")
    block_eqs = set()
    # for every collision guard
    for col in z3u.get_vars(z3.And(*inv)):
        match = col_re.match(str(col))
        if not match:
            continue
        nx = int(match.group(1))
        ny = int(match.group(2))
        xb = z3.Implies(col, z3.Bool("x'_blocked"))
        yb = z3.Implies(col, z3.Bool("y'_blocked"))
        if nx != 0 and ny != 0:
            block_eqs.add(z3.Or(xb, yb))
        elif nx != 0:
            block_eqs.add(xb)
        elif ny != 0:
            block_eqs.add(yb)
    print "Blocking", block_eqs
    block_eqs = z3.And(*block_eqs)
    invariant = z3.And(move_eqs, block_eqs, invariant)
    print "Invariant1:", invariant

    print "Smeqs:", subsed_motion_eqs
    print "Final", simplify(invariant)

# TODO: another version of above that takes entry variables; maybe that
# will be easier to simplify?


flows = mario.flows
s0 = mario.groups["movement"].modes["air"]
flows = merge_flows(flows, s0.flows, s0.envelopes)
print s0.name
invariants(mario, s0, flows)
print "=======\n"
s1 = s0.groups["aerial"].modes["jump_control"]
print s1.name
flows1 = merge_flows(flows, s1.flows, s1.envelopes)
invariants(mario, s1, flows1)
print "=======\n"
s2 = s0.groups["aerial"].modes["jump_fixed"]
print s2.name
flows2 = merge_flows(flows, s2.flows, s2.envelopes)
invariants(mario, s2, flows2)
print "=======\n"
s3 = s0.groups["aerial"].modes["falling"]
print s3.name
flows3 = merge_flows(flows, s3.flows, s3.envelopes)
invariants(mario, s3, flows3)
print "=======\n"
sg = mario.groups["movement"].modes["ground"]
print sg.name
flowsg = merge_flows(flows, sg.flows, sg.envelopes)
invariants(mario, sg, flowsg)
