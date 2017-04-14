import sympy
import hyped.schema as h
import hyped.xmlparser as xmlparser
import itertools
import copy
import re


def flatten(listOfLists):
    return list(itertools.chain.from_iterable(listOfLists))

# NOTE: because I want to find equations as a result, and not just models,
# it would be better to use sympy than z3.  but I can probably reuse a
# bunch of this code!  and at any rate the stuff below gives a template
# for future symbolic execution stuff.


mario = xmlparser.parse_automaton("resources/mario.char.xml")

# let's just arbitrarily pick movement.aerial.jump_control and movement.aerial.jump_fixed and merge them.
# then merge that with movement.aerial.falling.


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
        return sympy.Symbol(val.name, real=True)
    else:
        return sympy.S(val.value)


button_symbols = {
    k: sympy.Symbol(k)
    for k in ["p1_left",
              "p1_right",
              "p1_up",
              "p1_down",
              "p1_jump",
              "p1_flap"]
}


def guard_to_sympy(ha, guard, t, param_symbols):
    if isinstance(guard, h.GuardTimer):
        return t >= sym_eval(ha, guard.threshold, param_symbols)
    elif isinstance(guard, h.GuardCompare):
        # TODO: handle expressions on LHS, RHS
        lhs = sym_eval(ha, guard.left, param_symbols)
        rhs = sym_eval(ha, guard.right, param_symbols)
        return sympy.Rel(lhs, rhs, guard.operator)
    elif isinstance(guard, h.GuardConjunction):
        return sympy.And(*[guard_to_sympy(ha, g, t, param_symbols)
                           for g in guard.conjuncts])
    elif isinstance(guard, h.GuardDisjunction):
        return sympy.Or(*[guard_to_sympy(ha, g, t, param_symbols)
                          for g in guard.disjuncts])
    elif isinstance(guard, h.GuardNegation):
        return sympy.Not(guard_to_sympy(ha, guard.guard, t, param_symbols))
    elif isinstance(guard, h.GuardButton):
        # We can handle buttons specially since they have a boolean in them
        # already
        bsym = button_symbols[str(guard.playerID + "_" + guard.buttonID)]
        return bsym if guard.status == "on" or guard.status == "pressed" else sympy.Not(bsym)
    elif isinstance(guard, h.GuardTrue):
        return sympy.BooleanTrue
    elif isinstance(guard, h.GuardFalse):
        return sympy.BooleanFalse
    else:
        # any other guard we just turn into a boolean variable
        return sympy.Symbol(str(guard))


# Call me with a state and the merged flows for that state.
#  Probably best not to call this on a state that has child states
#  since no effort is made to consider child flows.  Also, any parent
#  guards might constrain the state even more; in fact, in general,
#  because this state might be active with arbitrary other states,
#  this invariant will be an over-approximation.
def invariants(ha, state, flows_and_envelopes):
    param_symbols = {pn: sympy.Symbol(pn) for pn in ha.parameters}
    t = sympy.Symbol("t", real=True)
    variable_symbols = {"t": t}
    motion_eqs = {}
    for v in ha.variables.values():
        if v.type != h.VelType:
            continue
        v0 = sympy.Symbol(v.name + "_")
        v1 = sympy.Symbol(v.name)
        param_symbols[v.name + "_"] = v0
        variable_symbols[v.name] = v1

        if v.basename not in flows_and_envelopes:
            continue
        mover = flows_and_envelopes[v.basename]
        if isinstance(mover, h.Flow):
            motion_eqs[str(v1)] = sympy.Eq(v0, v1)
            flow_degree = flows_and_envelopes[v.basename].degree
            flow_val_z = sym_eval(ha, flows_and_envelopes[v.basename].value, param_symbols)
            if flow_degree == 2:
                motion_eqs[str(v1)] = sympy.Eq(v0 + flow_val_z * t, v1)
            elif flow_degree == 1:
                motion_eqs[str(v1)] = sympy.Eq(flow_val_z, v1)
            elif flow_degree == 0:
                assert False, "not supported"
            print motion_eqs[str(v1)]
        elif isinstance(mover, h.Envelope):
            # Only support sustain envelopes and ignore attack/decay/release.
            # TODO: support cases where attack goes up higher than sustain
            # or maybe do something appropriate with release or the input axes?
            sustain = sym_eval(ha, mover.sustain[1], param_symbols)
            motion_eqs[str(v1)] = sympy.And(sympy.Ge(v1, -sustain),
                                            sympy.Le(v1, sustain))
        else:
            assert False, str(mover)

    #  We could get tighter invariants if we considered envelopes as well.
    # For instance, if we had an x velocity envelope and a guard that exited
    # if vx exceeded something then we could catch that.

    # NOTE: assumes s1 has no child group

    # inv: conjunctive invariant
    inv = [sympy.Ge(t, 0)]
    edges = state.edges
    for ei, e in enumerate(edges):
        guard = guard_to_sympy(ha, e.guard, t, param_symbols)
        print "TC:", guard
        # Magic to do faux-SMT: sympy.satisfiable(guard, all_models=True) and
        # enumerate
        dnf = sympy.to_dnf(guard, simplify=True)
        guard_symbols = dnf.atoms(sympy.Symbol)
        if not isinstance(dnf, sympy.Or):
            models = [dnf]
        else:
            models = dnf.args
        print "DNF:", dnf
        for m in models:
            print "------\n", "M:", m
            if isinstance(m, sympy.And):
                clauses = list(m.args)
            elif isinstance(m, list):
                clauses = m
            else:
                clauses = [m]
            all_symbols = set(flatten(map(lambda me: me.atoms(sympy.Symbol),
                                          motion_eqs.values()))
                              + list(guard_symbols))
            if len(clauses) == 0:
                continue
            print "Clauses:", clauses + motion_eqs.values()
            # Find t in terms of clauses and equations of motion.  Is there a
            # constraint on t or other variables?
            # t_soln = sympy.solve(
            #     clauses + [motion_eq],
            #     t,
            #     exclude=param_symbols.values())
            # print "Solve:", t_soln
            # if isinstance(t_soln, dict):
            #     t_soln = sympy.And(*[sympy.Eq(k, v) for k, v in t_soln.items()])
            # solved_clauses = [t_soln]
            # if isinstance(t_soln, sympy.And):
            #     solved_clauses = t_soln.args
            solved_clauses = clauses + motion_eqs.values()
            print "Solved:", solved_clauses
            sorted_symbols = [s for s in sympy.ordered(
                all_symbols - set(param_symbols.values())
            )]
            booly_clauses = [s for s in solved_clauses if (isinstance(s, sympy.Not) and isinstance(s.args[0],sympy.Symbol)) or isinstance(s, sympy.Symbol)]
            print "SS:", sorted_symbols
            here_t_constraints = []
            for will_change_constraint in solved_clauses:
                print "CON:", will_change_constraint
                if (isinstance(will_change_constraint, sympy.Not) and
                        isinstance(will_change_constraint.args[0], sympy.Symbol)):
                    print "Skip1",will_change_constraint
                    continue
                if isinstance(will_change_constraint, sympy.Symbol):
                    print "Skip2",will_change_constraint
                    continue
                if not isinstance(will_change_constraint, sympy.Rel):
                    print "Skip3",will_change_constraint
                    continue
                if (will_change_constraint.lhs == sympy.oo or
                    will_change_constraint.lhs == -sympy.oo or
                    will_change_constraint.rhs == sympy.oo or
                        will_change_constraint.rhs == -sympy.oo):
                    # not informative
                    continue
                will_change_constraint = will_change_constraint.canonical
                if will_change_constraint.func == sympy.Ne:
                    assert isinstance(will_change_constraint.lhs, sympy.Symbol)
                    assert will_change_constraint.rhs == sympy.S(0) or will_change_constraint.rhs == sympy.S(1)
                    will_change_constraint = sympy.Eq(
                        will_change_constraint.lhs,
                        sympy.S(0) if will_change_constraint.rhs == sympy.S(1) else sympy.S(1))
                assert will_change_constraint.func != sympy.Ne
                will_change_eq0 = sympy.expand(
                    will_change_constraint.lhs - will_change_constraint.rhs
                )
                print "WCC", will_change_constraint, will_change_eq0
                here_t_constraints.append(will_change_eq0)
            print "HTS:", here_t_constraints
            print sorted_symbols
            root = dict(zip(sorted_symbols, list(sympy.linsolve(
                here_t_constraints,
                *sorted_symbols))[0]))
            print root
            print "Boolys", booly_clauses
            inv = inv + [
                sympy.Lt(k, v) if k == t else sympy.Ne(k, v)
                for k, v in root.items() if k != v
            ] + [sympy.Not(sympy.Or(*booly_clauses))]
    invariant = sympy.And(*inv)
    print "Invariant0:", invariant
    # Let's put all the equations and constraints of motion in, only now we have to also consider that they might arbitrarily be 0 due to collisions
    invariant = invariant.subs({param_symbols[p.name]: p.value.value
                                for p in ha.parameters.values()})
        # TODO: should really work on an instance.
        # Or be in a different function!
        # Param choices can totally change the invariant.
    
    print "Invariant01:",invariant

    subsed_motion_eqs = {
        k: me.subs({param_symbols[p.name]: p.value.value
                     for p in ha.parameters.values()})
        for k, me in motion_eqs.items()}

    # If all edges into a state set a variable to a given value, we can
    # replace the v_' with that value; here we assume it for jump_control
    # TODO: do for real
    if state.name == "jump_control":
        invariant = invariant.subs(param_symbols["y'_"], 200)
        subsed_motion_eqs = {
            k: me.subs(param_symbols["y'_"],
                       200)
            for k, me in subsed_motion_eqs.items()}

    env_eqs = [sympy.Or(sympy.And(sympy.Not(sympy.Symbol(vbl+"_blocked")),meq),
                        sympy.And(sympy.Symbol(vbl+"_blocked"), sympy.Eq(variable_symbols[vbl], sympy.S(0))))
               for vbl, meq in subsed_motion_eqs.items()]
    print "Env_eqs:", env_eqs
    env_eqs = sympy.And(*env_eqs)
    print "SEnv eqs:", env_eqs
    # If there are collision guards involving something with a normal, we can force them to have the same truth value as the corresponding blocking predicate.
    col_re = re.compile("GuardColliding\(.*normal_check=\((-?[01])\, (-?[01])\).*\)")
    block_eqs = set()
    for col in sympy.And(*inv).atoms(sympy.Symbol):
        match = col_re.match(str(col))
        if not match:
            continue
        nx = int(match.group(1))
        ny = int(match.group(2))
        xb = sympy.Implies(col, sympy.Symbol("x'_blocked"))
        yb = sympy.Implies(col, sympy.Symbol("y'_blocked"))
        if nx != 0 and ny != 0:
            block_eqs.add(sympy.Or(xb, yb))
        elif nx != 0:
            block_eqs.add(xb)
        elif ny != 0:
            block_eqs.add(yb)
    print "Blocking", block_eqs
    block_eqs = sympy.And(*block_eqs)
    invariant = sympy.And(env_eqs, block_eqs, invariant)
    print "Invariant1:", invariant

    # Now if we look at the right hand sides of the
    # un-equalities WRT time, we can determine if they should be Gt or Lt.
    # This is safe at this point because all accelerations are constant
    # given the entry parameters.

    print "Smeqs:", subsed_motion_eqs
    #invariant = sympy.simplify(invariant)
    print "With Neqs:", invariant
    neqs = [a for a in invariant.args if isinstance(a, sympy.Ne)]
    for neq in neqs:
        # Another interesting case: buttons.  These should turn into 0/1
        # equalities.
        # Actually, collisions and joint transitions and stuff should also act
        # just like buttons.
        if str(neq.lhs) in subsed_motion_eqs:
            # TODO: do the right thing in more
            # complicated equations or those not varying in t

            # Look at the equation of motion for that variable,
            # take the sign of movement

            # TODO: pick the right one per variable
            meqs = subsed_motion_eqs[str(neq.lhs)].rhs
            if isinstance(meqs, sympy.And):
                assert False
            else:
                acc_sign = meqs.coeff(t)
                if acc_sign < 0:
                    ineq = sympy.Gt(neq.lhs, neq.rhs)
                elif acc_sign > 0:
                    ineq = sympy.Lt(neq.lhs, neq.rhs)
                else:
                    # give up
                    ineq = neq
        elif str(neq.lhs) in variable_symbols:
            ineq = invariant.subs(neq, sympy.Or(sympy.Lt(neq.lhs, neq.rhs),
                                                sympy.Gt(neq.lhs, neq.rhs)))
        elif isinstance(neq.lhs, sympy.Symbol) and (neq.rhs == sympy.S(0) or neq.rhs == sympy.S(1)):
            # no need to look at the direction or anything because I know booleans aren't rootish.
            ineq = sympy.Eq(neq.lhs,
                            sympy.S(1)
                            if neq.rhs == sympy.S(0) else sympy.S(0))
        else:
            ineq = neq
        invariant = invariant.subs(neq, ineq)
    print "Final", sympy.simplify(
        invariant.subs({sympy.Symbol("y_'"):sympy.S(0),
                        sympy.Symbol("x'_"):sympy.S(0)}))

# TODO: another version of above that takes entry variables; maybe that will be easier to simplify?

flows = mario.flows
s0 = mario.groups["movement"].modes["air"]
flows = merge_flows(flows, s0.flows, s0.envelopes)
print s0.name
invariants(mario, s0, flows)
print "=======\n"
s1 = mario.groups["movement"].modes["air"].groups["aerial"].modes["jump_control"]
print s1.name
flows1 = merge_flows(flows, s1.flows, s1.envelopes)
invariants(mario, s1, flows1)
print "=======\n"
s2 = mario.groups["movement"].modes["air"].groups["aerial"].modes["jump_fixed"]
print s2.name
flows2 = merge_flows(flows, s2.flows, s2.envelopes)
invariants(mario, s2, flows2)
print "=======\n"
s3 = mario.groups["movement"].modes["air"].groups["aerial"].modes["falling"]
print s3.name
flows3 = merge_flows(flows, s3.flows, s3.envelopes)
invariants(mario, s3, flows3)
print "=======\n"
sg = mario.groups["movement"].modes["ground"]
print sg.name
flowsg = merge_flows(flows, sg.flows, sg.envelopes)
invariants(mario, sg, flowsg)
