import sympy
import hyped.schema as h
import hyped.xmlparser as xmlparser

# NOTE: because I want to find equations as a result, and not just models,
# it would be better to use sympy than z3.  but I can probably reuse a
# bunch of this code!  and at any rate the stuff below gives a template
# for future symbolic execution stuff.

mario = xmlparser.parse_automaton("resources/mario.char.xml")

# let's just arbitrarily pick movement.aerial.jump_control and movement.aerial.jump_fixed and merge them.
# then merge that with movement.aerial.falling.


def merge_flows(f1s, f2s):
    fkeys1 = {flow.var.basename: flow for vn, flow in f1s.items()}
    fkeys2 = {flow.var.basename: flow for vn, flow in f2s.items()}
    fkeys1.update(fkeys2)
    return fkeys1


flows = mario.flows
s0 = mario.groups["movement"].modes["air"]
flows = merge_flows(flows, s0.flows)
s1 = mario.groups["movement"].modes["air"].groups["aerial"].modes["jump_control"]
flows1 = merge_flows(flows, s1.flows)
s2 = mario.groups["movement"].modes["air"].groups["aerial"].modes["jump_fixed"]
flows2 = merge_flows(flows, s2.flows)
# print s1, "\n", flows1
# print s2, "\n", flows1

# z = z3.Solver()

# t=how long to spend in s1
# vy0=initial value of vy (y assumed = 0 [relative movement planning])
# vy1=final value of vy
# ay assumed constant
t, vy0, vy1 = sympy.symbols("t y_' y'", real=True)
ay = sympy.S(0.0)


param_symbols = {pn: sympy.Symbol(pn) for pn in mario.parameters}
param_symbols["y_'"] = vy0


def sym_eval(ha, val):
    if isinstance(val, h.Parameter):
        return param_symbols[val.name]
    elif isinstance(val, h.Variable):
        return sympy.Symbol(val.name, real=True)
    else:
        return sympy.S(val.value)


flow_type = flows1["y"].var.type
flow_val_z = sym_eval(mario, flows1["y"].value)

motion_eq = sympy.Eq(vy0, vy1)

if flow_type == h.AccType:
    ay = flow_val_z
    motion_eq = sympy.Eq(vy0 + ay * t, vy1)
elif flow_type == h.VelType:
    ay = 0
    pass
else:
    assert False


def guard_to_sympy(ha, guard, t):
    if isinstance(guard, h.GuardTimer):
        return t >= sym_eval(ha, guard.threshold)
    elif isinstance(guard, h.GuardCompare):
        # TODO: handle expressions on LHS, RHS
        lhs = sym_eval(ha, guard.left)
        rhs = sym_eval(ha, guard.right)
        return sympy.Rel(lhs, rhs, guard.operator)
    elif isinstance(guard, h.GuardConjunction):
        return sympy.And(*[guard_to_sympy(ha, g, t)
                           for g in guard.conjuncts])
    elif isinstance(guard, h.GuardDisjunction):
        return sympy.Or(*[guard_to_sympy(ha, g, t)
                          for g in guard.disjuncts])
    elif isinstance(guard, h.GuardNegation):
        return sympy.Not(guard_to_sympy(ha, guard.guard, t))
    elif isinstance(guard, h.GuardButton):
        bsym = sympy.Symbol(str(guard.playerID + "_" + guard.buttonID))
        return bsym if guard.status == "on" else sympy.Not(bsym)
    elif isinstance(guard, h.GuardTrue):
        return sympy.BooleanTrue
    elif isinstance(guard, h.GuardFalse):
        return sympy.BooleanFalse
    else:
        return sympy.Eq(
            sympy.Symbol(str(guard), integer=True, real=False),
            1)


# NOTE: assumes s1 has no child group

# inv: conjunctive invariant
inv = [sympy.Ge(t, 0)]
t_constraints = set()
edges = s1.edges
motion_eq = motion_eq
for ei, e in enumerate(edges):
    guard = guard_to_sympy(mario, e.guard, t)
    print "TC:", guard
    # Magic to do faux-SMT: sympy.satisfiable(guard, all_models=True) and
    # enumerate
    dnf = sympy.to_dnf(guard, simplify=True)
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
        all_symbols = set(motion_eq.atoms(sympy.Symbol))
        if len(clauses) == 0:
            continue
        print "Clauses:", clauses + [motion_eq]
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
        solved_clauses = clauses + [motion_eq]
        sorted_symbols = [s for s in sympy.ordered(
            all_symbols - set(param_symbols.values())
        )]
        print "SS:", sorted_symbols
        here_t_constraints = []
        for will_change_constraint in solved_clauses:
            print "CON:", will_change_constraint
            if not isinstance(will_change_constraint, sympy.Rel):
                continue
            if (will_change_constraint.lhs == sympy.oo or
                will_change_constraint.lhs == -sympy.oo or
                will_change_constraint.rhs == sympy.oo or
                    will_change_constraint.rhs == -sympy.oo):
                # not informative
                continue
            will_change_constraint = will_change_constraint.canonical
            assert will_change_constraint.func != sympy.Ne
            # TODO: hopefully this converts it to linear form
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
        inv = inv + [sympy.Lt(k, v) if k == t else sympy.Ne(k, v)
                     for k, v in root.items() if k != v]
invariant = sympy.simplify(sympy.And(*inv))
print "Invariant:", invariant

# Once we know parameter values, we can substitute those in.  First
# substitute the per-instance parameters:

invariant = sympy.simplify(invariant.subs({param_symbols["jump_gravity"]: -250,
                                           param_symbols["jump_max_hold"]: 0.7}))
print invariant

# If all edges into a state set a variable to a given value, we can
# replace the v_' with that value; here we assume it for jump_control
if s1.name == "jump_control":
    invariant = sympy.simplify(invariant.subs(vy0, 200))
    print invariant

# TODO: now, we enter the entry-state-specific part I think

# Now if we look at the right hand sides of the
# un-equalities WRT time, we can determine if they should be Gt or Lt.
# This is safe at this point because all accelerations are constant
# given the entry parameters.

neqs = [a for a in invariant.args if isinstance(a, sympy.Ne)]
for neq in neqs:
    # For now, we're always accelerating downwards, so we'll just do it like
    # this.  In the future this requires knowing whether lhs_' is bigger or
    # smaller than the RHS.
    invariant = invariant.subs(neq, sympy.Gt(neq.lhs, neq.rhs))
print invariant

#Constraints = Sympy.solve(sympy.Not(t_soln), t, exclude=param_symbols)
# print "Constraints:", constraints
# for each edge out, create a new s1'+s2 state and give it s2's edges and flows in convex union of flows(s1)_upto_t, flows(s2)_from_updates
# print e.target
# print s2.qualified_name
# assert e.target == s2.qualified_name
# z.add(z3.If(guard_to_z3(z, mario, "edge_" + str(ei), e.guard, t),
#             z3.And(*[edge_z if edge_z_i == ei else z3.Not(edge_z)
#                      for edge_z_i, edge_z in enumerate(edge_zs)]),
#             z3.Not(edge_zs[ei])
#             ))
