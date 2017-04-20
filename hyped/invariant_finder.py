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
        # z3.Tactic('simplify'),
        z3.Tactic('propagate-values'),
        # z3.Tactic('propagate-ineqs'),
        z3.Tactic('sat-preprocess'),
        # z3.Tactic('ctx-solver-simplify'),
        # Tactic('split-clause'),
        # Tactic('elim-and'),
        # z3.Tactic('solve-eqs'),
        z3.Tactic('propagate-ineqs'),
        # z3.Tactic('ctx-solver-simplify')
    )
    simp = tac(expr)
    return simp.as_expr()


def flatten(listOfLists):
    return list(itertools.chain.from_iterable(listOfLists))

# "Flows" now will contain both Flow and Envelope objects


def merge_flows(f1s, f2s, e2s):
    f1s = copy.deepcopy(f1s)
    # Flows clobber envelopes or whatever else
    fkeys2 = {flow.var.basename: [flow] for vn, flow in f2s.items()}
    f1s.update(fkeys2)
    ekeys2 = {}
    for e in e2s:
        if e.variables[0].basename not in ekeys2:
            # Envelopes beat flows if they're available
            # but must be combined with other envelopes.
            # I'm OK with nested envelopes being treated as conflicts if their
            # guards are not disjoint.
            ekeys2[e.variables[0].basename] = f1s.get(
                e.variables[0].basename, [])
        ekeys2[e.variables[0].basename].append(e)
        if e.reflections > 2:
            if e.variables[1].basename not in ekeys2:
                ekeys2[e.variables[1].basename] = f1s.get(
                    e.variables[1].basename, [])
            ekeys2[e.variables[1].basename].append(e)
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


def to_dnf(z):
    clauses = z3.Then(
        z3.Tactic('simplify'),
        z3.Tactic('tseitin-cnf'),
        z3.Repeat(z3.OrElse(z3.Tactic('split-clause'),
                            z3.Tactic('skip')))
    )(z).as_expr()
    if z3.is_or(clauses):
        return clauses.children()
    return [clauses]


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


def collision_vars_with_normals(zexpr):
    terms = z3u.get_vars(zexpr)
    col_pat = "GuardColliding\(.*self_type='([^']*)'.*normal_check=\((-?[01])\, (-?[01])\).*\)"
    col_re = re.compile(col_pat)
    cols = []
    norms = []
    types = []
    # for every collision guard
    for col in terms:
        match = col_re.match(str(col))
        if not match:
            continue
        type = match.group(1)
        nx = int(match.group(2))
        ny = int(match.group(3))
        cols.append(col)
        norms.append((nx, ny))
        types.append(type)
    return cols, norms, types


def Iff(a, b):
    return z3.And(z3.Implies(a, b), z3.Implies(b, a))

# Call me with a state and the merged flows for that state.
#  Probably best not to call this on a state that has child states
#  since no effort is made to consider child flows.  Also, any parent
#  guards might constrain the state even more; in fact, in general,
#  because this state might be active with arbitrary other states,
#  this invariant will be an over-approximation.


def invariants(ha, state, flows_and_envelopes):
    base_flows = {v.basename: [h.Flow(v, h.RealConstant(0, "inv_finder"), "inv_finder")]
                  for v in ha.variables.values() if v.degree == 1}
    base_flows.update(flows_and_envelopes)
    flows_and_envelopes = base_flows
    param_symbols = {pn: z3.Real(pn) for pn in ha.parameters}
    t = z3.Real("t")
    variable_symbols = {"t": t}
    motion_eqs = {}
    lag_param_symbols = set()
    now_to_lag = {}
    for v in ha.variables.values():
        if v.type != h.VelType:
            continue
        v0 = z3.Real(v.name + "_")
        v1 = z3.Real(v.name)
        param_symbols[v.name + "_"] = v0
        lag_param_symbols.add(v0)
        now_to_lag[v1] = v0
        variable_symbols[v.name] = v1

        if v.basename not in flows_and_envelopes:
            continue
        movers = flows_and_envelopes[v.basename]
        here_motion_eqs = []
        for mover in movers:
            print movers, mover
            if isinstance(mover, h.Flow):
                eq = Eq(v0, v1)
                flow_degree = mover.degree
                flow_val_z = sym_eval(
                    ha, mover.value, param_symbols)
                if flow_degree == 2:
                    eq = Eq(v0 + flow_val_z * t, v1)
                elif flow_degree == 1:
                    eq = Eq(flow_val_z, v1)
                elif flow_degree == 0:
                    assert False, "not supported"
                print eq
            elif isinstance(mover, h.Envelope):
                # Only support sustain envelopes and ignore attack/decay/release.
                # TODO: support cases where attack goes up higher than sustain
                # or maybe do something appropriate with release or the input
                # axes?
                sustain = sym_eval(ha, mover.sustain[1], param_symbols)
                eq = z3.And(Ge(v1, -sustain),
                            Le(v1, sustain))
            else:
                assert False, str(mover)
            here_motion_eqs.append(eq)
        motion_eqs[str(v1)] = (z3.Or(*here_motion_eqs)
                               if len(here_motion_eqs) > 1
                               else here_motion_eqs[0])

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

    propagate_entry_guards = True

    if propagate_entry_guards:
        enter_options = []
        for src, edge in h.modes_entering(ha, state, implicit=True):
            this_option = z3.BoolVal(True)
            clobbered_symbols = set()
            for uk, uv in edge.updates.items():
                # even if we don't know how to use it, it's still clobbered
                if not uk in variable_symbols:
                    # TODO: FIXME: It sets position or something, ignore for
                    # now
                    continue
                clobbered_symbols.add(variable_symbols[uk])
                if isinstance(uv, h.RealConstant):
                    this_option = z3.And(
                        this_option,
                        param_symbols[str(uk) + "_"] == z3.RealVal(uv.value))
                elif isinstance(uv, h.Parameter):
                    this_option = z3.And(
                        this_option,
                        param_symbols[str(uk) + "_"] == param_symbols[uv.name])
            # Propagation from guards is tough.  It's easy enough to
            # find the guard-involved variables which aren't reset by
            # the updates, but it's hard to get an expression for those variables
            # which doesn't depend on e.g. y'__ or t. so we just try out best.
            this_guard = guard_to_z3(ha, edge.guard, t, param_symbols)
            print "GIN", this_guard
            this_guard_options = to_dnf(this_guard)
            print "DNF:", this_guard_options
            guard_options = []
            bad_vars = clobbered_symbols | lag_param_symbols
            # TODO: can "blocked" go into safe vars too? seems like it.  but it's
            # fancier -- blocked_x implies x_' is 0, etc.
            safe_vars = (set(variable_symbols.values()) |
                         set(param_symbols.values())) - bad_vars
            for combination in this_guard_options:
                if z3.is_and(combination):
                    combination = combination.children()
                else:
                    combination = [combination]
                guard_option = []
                print combination
                for clause in combination:
                    used_vars = set(z3u.get_vars(clause))
                    collision_vars, norms, types = collision_vars_with_normals(
                        clause)
                    if used_vars.issubset(safe_vars):
                        print "Can use", clause
                        # NOTE: if blocking vars are used, we shouldn't also
                        # believe that we're blocked in the new state, just that
                        # x'_ or y'_ was 0.
                        guard_option.append(z3.substitute(
                            clause,
                            now_to_lag.items()
                        ))
                        print "Using", guard_option[-1]
                    elif (used_vars - set(collision_vars)).issubset(safe_vars):
                        print "Can use block inference", clause
                        for c, (nx, ny) in zip(collision_vars, norms):
                            if c in used_vars:
                                xblk = Eq(param_symbols["x'_"], z3.RealVal(0))
                                yblk = Eq(param_symbols["y'_"], z3.RealVal(0))
                                if nx == 0 and ny == 0:
                                    guard_option.append(z3.Or(xblk, yblk))
                                elif nx != 0:
                                    guard_option.append(xblk)
                                elif ny != 0:
                                    guard_option.append(yblk)
                                else:
                                    assert False
                        # for each element of used_vars & collision_vars with
                        # a normal:
                        # the corresponding direction is zeroed out for x'_ or
                        # y'_
                        # also, one of the guards on a self collider of this
                        # type is true
                if len(guard_option) > 0:
                    guard_options.append(z3.And(*guard_option))
            if len(guard_options) > 0:
                this_option = z3.And(this_option, z3.Or(*guard_options))
            # Does this_guard give a non-clobbered variable a value?
            print "Net option:", this_option
            if not z3.eq(this_option, z3.BoolVal(True)):
                enter_options.append(this_option)
        print "Enter options", enter_options
    else:
        enter_options = []
    if len(enter_options) > 0:
        invariant = z3.And(invariant, z3.Or(*enter_options))

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
    # We can also force that the guards on at least one of the colliders with the self-types is true
    # and for blocked we can force that the guards on at least one of the
    # colliders with a blocking type is true.
    collisions = zip(*collision_vars_with_normals(z3.And(*inv)))
    block_eqs = set()
    # for every collision guard
    for col, (nx, ny), selftype in collisions:
        xb = z3.Implies(col, z3.Bool("x'_blocked"))
        yb = z3.Implies(col, z3.Bool("y'_blocked"))
        if nx != 0 and ny != 0:
            block_eqs.add(z3.Or(xb, yb))
        elif nx != 0:
            block_eqs.add(xb)
        elif ny != 0:
            block_eqs.add(yb)
        possible_if_col = []
        for c in ha.colliders:
            if (selftype is None or selftype in c.types):
                possible_if_col.append(
                    guard_to_z3(ha,
                                c.guard,
                                t,
                                param_symbols)
                    if c.guard is not None else z3.BoolVal(True))
        block_eqs.add(z3.Implies(
            col,
            z3.Or(*possible_if_col)
        ))
    possible_if_blocked = []
    for c in ha.colliders:
        # If c.types is blocking with anything, then if we are blocked
        # it might be because of c.guard TODO: only do this for
        # BLOCKING ones, which we don't know without a Context.
        possible_if_blocked.append(
            guard_to_z3(ha, c.guard, t, param_symbols)
            if c.guard is not None else z3.BoolVal(True)
        )
    block_eqs.add(z3.Implies(
        z3.Or(z3.Bool("x'_blocked"), z3.Bool("y'_blocked")),
        z3.Or(*possible_if_blocked)
        if len(possible_if_blocked) > 0 else z3.BoolVal(True)
    ))

    print "Blocking", block_eqs
    block_eqs = z3.And(*block_eqs)
    invariant = z3.And(move_eqs, block_eqs, invariant)
    invariant = z3.substitute(invariant, param_subs)

    print "Invariant1:", invariant
    simp = simplify(invariant)
    print "Final", simp
    assert not simp.eq(z3.BoolVal(False))

# TODO: another version of above that takes entry variables; maybe that
# will be easier to simplify?


if __name__ == "__main__":
    mario = xmlparser.parse_automaton("resources/mario.char.xml")
    flows = {v.var.basename: [v] for k, v in mario.flows.items()}
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
    print "=============\n\n\n============\n"
    plat = xmlparser.parse_automaton("resources/plat_h_activating.char.xml")
    flows = {v.var.basename: [v] for k, v in plat.flows.items()}
    s0 = plat.groups["movement"].modes["wait"]
    flows = merge_flows(flows, s0.flows, s0.envelopes)
    print s0.name
    invariants(plat, s0, flows)
    print "=======\n"
    s1 = plat.groups["movement"].modes["right"]
    print s1.name
    flows1 = merge_flows(flows, s1.flows, s1.envelopes)
    invariants(plat, s1, flows1)
    print "=======\n"
    s2 = plat.groups["movement"].modes["left"]
    print s2.name
    flows2 = merge_flows(flows, s2.flows, s2.envelopes)
    invariants(plat, s2, flows2)
    print "=======\n"
