import copy
import math
import sys
import re
import z3
import z3.z3util as z3u
import invariant_finder as ifind
import schema as sch
import interpreter as itp
import heapq
import random
import itertools

# Local search could work one of several ways:
# 1. Naive (heuristic) search, try every available action at every timestep
# 2. Use invariants to guide search and possibly break symmetries?
# 3. Abstraction refinement: local search in an abstract machine, then turn that into a real low level trajectory
# We don't have the luxury of symmetry breaking by projection onto xy or by making assumptions about dynamics.  So invariants could yield a way to know which source states are in equivalence classes wrt getting to a destination state.  Here it would be something like "find me distinct destination discrete modes/nvariant regions I can get into from my source invariant region".
# It makes sense to try both ways!


def projection(w):
    return (
        tuple(w.theories.input.pressed),
        tuple(w.theories.input.on),
        tuple(w.theories.input.released),
        tuple([
            (id, tuple([
                tuple([
                    (tuple(v.parameters.values()),
                     tuple(v.variables),
                     tuple(v.dvariables.values()),
                     tuple([vt
                            for mi, vt in enumerate(v.timers)
                            if w.automata[
                                v.automaton_index
                            ].ordered_modes[mi].needs_timer]),
                     v.entered,
                     v.exited)
                    for v in aut_vs
                ])
                for aut_vs in ws.valuations
            ]))
            for id, ws in w.spaces.items()
        ])
    )


class hashwrap(object):
    __slots__ = ["projection", "world"]

    def __init__(self, w):
        # TODO: FIXME: sloppy, inefficient
        self.world = w
        self.projection = projection(w)

    def __hash__(self):
        return hash(self.projection)

    def __eq__(self, o):
        if isinstance(o, hashwrap):
            return self.projection == o.projection
        return False


def button_combos(opts):
    option_sets = itertools.product(*opts)
    return map(lambda os: filter(lambda o: o is not None, os), option_sets)


def neighbors(n, log):
    # TODO: smartly look at envelopes and guard conditions of active modes.
    # Do this in terms of transitions, not (just) button changes probably.
    # button_options = [["left", "right", None], ["down", "up", None],
    # ["jump", None], ["flap", None]]
    button_options = [["left", "right", None]]
    button_sets = button_combos(button_options)
    random.shuffle(button_sets)
    neighbs = []
    for bs in button_sets:
        logc = log.clone()
        neighbs.append((bs, itp.step(n.clone(), bs, dt, logc), logc))
    return neighbs


def dijkstra(world, extra, costfn, scorer, dt, node_limit=100000):
    open = []
    log = itp.TransitionLog()
    heapq.heappush(open, ((0, scorer(world, extra)),
                          world, log,
                          extra, None))
    seen = {projection(world): (0, log)}
    found = None
    checked = 0
    while found is None and len(open) > 0 and checked < node_limit:
        checked = checked + 1
        (costs, n, log, nextra, move0) = heapq.heappop(open)
        cost = costs[0]
        if checked % 100 == 0:
            print ("G:", checked, costs, move0,
                   n.spaces["0"].valuations[0][0].get_var("x"))
        for (move, np, nplog) in neighbors(n, log):
            # TODO: can we do something to either figure out if a K-step plan
            # would get us to the solution OR have just one node per distinct
            # k-step plan?  or something?  this is going to start resembling
            # symbolic search more and more.  Another possibility: add the
            # nodes and expand only a certain (randomly sampled) set of their
            # neighbors, and then only a certain set of the remaining once
            # those are exhausted, etc?
            npp = projection(np)
            # TODO: cost + 1 should be only if the mode changed, not
            # necessarily the move.  Right?
            g = costfn(cost, move0, move, nplog)
            if npp not in seen:
                h, npextra = scorer(np, nextra)
                if h < 0:
                    continue
                seen[npp] = (g, (n, nplog))
                if h < 1:
                    found = np
                    break
                # Lexical priority: lowest number of transitions first, then
                # closest to goal
                heapq.heappush(open, ((g, h), np, nplog, npextra, move))
    if found is None:
        return False
    # Get a concrete path and lift it to an abstract path by replaying it and
    # logging
    # path = []
    # here = found
    herep = projection(found)
    return seen[herep][1][1]
    # while seen[herep][1] is not None:
    #     path.append(seen[herep][1][1])
    #     here = seen[herep][1][0]
    #     herep = projection(here)
    # path.reverse()
    # print "Concrete path", path
    # here = world.clone()
    # log = itp.TransitionLog()
    # for pi in path:
    #     itp.step(here, pi, dt, log)
    # return log


def stagger_neighbors(n, log, s, reg, move0):
    levels = 5
    max_gap = 2**(levels + 1)
    neighbs = []
    if reg:
        # TODO: this, smartly, based on current modes and available
        # buttons/axes
        button_options = [["left", "right", None]]
        button_sets = button_combos(button_options)
        for bs in button_sets:
            if bs == move0:
                continue
            logc = log.clone()
            neighbs.append(
                (bs,
                 itp.step(n.clone(), bs, dt, logc),
                 logc,
                 1,
                 0,
                 True))
    if s == 0:
        later = n.clone()
        logc = log.clone()
        for i in range(0, max_gap):
            later = itp.step(later, move0, dt, logc)
        neighbs.append((move0, later, logc, max_gap, 0, True))
    if s < levels:
        later = n.clone()
        logc = log.clone()
        steps = 2**(levels - s)
        neighbs.append((move0, n, log, 0, s + 1, False))
        for i in range(0, steps):  # 32, 16, 8, 4, 2
            later = itp.step(later, move0, dt, logc)
        neighbs.append((move0, later, logc, steps, s + 1, True))
    elif s == levels:
        logc = log.clone()
        neighbs.append(
            (move0,
             itp.step(n.clone(), move0, dt, logc),
             logc,
             1, 6, True))
    return neighbs


def dijkstra_stagger(world, extra, costfn, scorer, dt, node_limit=100000):
    open = []
    log = itp.TransitionLog()
    heapq.heappush(
        open,
        ((0, 0, scorer(world, extra)),
         world, log, extra, True, []))
    seen = {projection(world): (0, log)}
    found = None
    checked = 0
    while found is None and len(open) > 0 and checked < node_limit:
        checked = checked + 1
        (costs, n, log, nextra, r, move0) = heapq.heappop(open)
        cost = costs[0]
        s = costs[1]
        if checked % 1000 == 0:
            print ("G:", checked, costs, r, move0,
                   n.spaces["0"].valuations[0][0].get_var("x"),
                   len(open))
        # a node generates regular neighbors (if it has the regular flag) plus stagger neighbors.
        # stagger=0: now+0*dt @ 1 reg=0, now+32*dt @ 1, now+64*dt @ 0
        # stagger=1: now+0*dt @ 2 reg=0, now+16*dt @ 2
        # stagger=2: now+0*dt @ 3 reg=0, now+8*dt @ 3
        # stagger=3: now+0*dt @ 4 reg=0, now+4*dt @ 4
        # stagger=4: now+0*dt @ 5 reg=0, now+2*dt @ 5
        # stagger=5: now+1*dt @ 6
        for (move, np, nplog, steps, sp, regp) in stagger_neighbors(n, log, s, r, move0):
            # TODO: can we do something to either figure out if a K-step plan
            # would get us to the solution OR have just one node per distinct
            # k-step plan?  or something?  this is going to start resembling
            # symbolic search more and more.  Another possibility: add the
            # nodes and expand only a certain (randomly sampled) set of their
            # neighbors, and then only a certain set of the remaining once
            # those are exhausted, etc?
            npp = projection(np)
            g = costfn(cost, move0, move, nplog)
            if not regp or npp not in seen:
                h, npextra = scorer(np, nextra)
                if h < 0:
                    continue
                if regp:
                    seen[npp] = (g, (n, nplog, steps))
                if h < 1:
                    found = np
                    break
                # Lexical priority: lowest number of transitions first, then
                # closest to goal
                heapq.heappush(
                    open, ((g, sp, h), np, nplog, npextra, regp, move))
    if found is None:
        return False
    herep = projection(found)
    return seen[herep][1][1]


def aut_distance(w, space_aut_vals, space, aut, idx):
    # This heuristic is inadmissible but what are ya gonna do?
    valtarg = space_aut_vals[space][aut][idx]
    val = w.spaces[space].valuations[aut][idx]
    if val.get_var("y") < 0 or val.get_var("x") < 0:
        return -1, None
    delta = (abs(valtarg["x"] - val.get_var("x")) +
             abs(valtarg["y"] - val.get_var("y")))
    # TODO: hack
    if delta < 16:
        return 0, None
    # Could return 1 if you want an uninformative one
    # return 1
    return delta, None


def varname(*parts):
    return "_".join(map(str, parts))


def guard_to_z3(world, sid, auti, vali, mi, guard):
    assert False
    pass


def bmc_initial(world):
    eqs = []
    for sid, ws in world.spaces.items():
        for auti, vals in enumerate(ws.valuations):
            for vali, valu in enumerate(vals):
                for mi, m in enumerate(valu.ordered_modes):
                    eqs.append((z3.Bool(varname(sid, auti, vali,
                                                "mode", mi,
                                                "active", "enter", 0)) ==
                                (valu.active_modes & (1 << mi)) != 0))
                for cvarname in valu.var_names:
                    eqs.append((z3.Real(varname(sid, auti, vali,
                                                cvarname, "enter", 0)) ==
                                z3.RealVal(valu.get_var(cvarname))))
                for dvarname, dvarval in valu.dvariables.items():
                    eqs.append((z3.Real(varname(sid, auti, vali,
                                                dvarname, "enter", 0)) ==
                                z3.RealVal(dvarval)))
    return z3.And(*eqs)


def bmc_final(desc):
    # in terms of enter vars
    eqs = []
    for sid, s in desc.items():
        for auti, vals in enumerate(s):
            for vali, valu in enumerate(vals):
                for var, val in valu.items():
                    eqs.append(
                        (z3.Real(varname(sid, auti, vali, var, "ENTER")) ==
                         z3.RealVal(val)))
    return z3.And(*eqs)


def flow_constraints(sid, auti, vali, val, mi, vbl, flow, guards):
    # if len guards, return nor(guards) => F
    # express F as bounds on vbl, vbl', vbl''
    pass


def env_flows(sid, auti, vali, val, env, vbl):
    # return envelope bounds of controlled degree of vbl expressed as bounds
    # on vbl, vbl', vbl''
    pass


def bmc_flows(sid, auti, vali, mi, m):
    # v_flow = v_enter + something*(t_NEXT-t_NOW)
    flow_constraints = []
    aut = world.automata[auti]
    val = world.spaces[sid].valuations[auti][vali]
    m = val.modes[mi]
    for varbl in aut.variables:
        if varbl.degree != 0:
            continue
        vbl = varbl.basename
        # Envelopes clobber flows
        var_flow_guards = []
        for env in m.envelopes:
            guard = guard_to_z3(world, sid, auti, vali, mi, env.guard)
            var_flow_guards.append(guard)
            flow_constraints.append(z3.Implies(
                guard,
                env_flows(sid, auti, vali, val, env, vbl)
            ))
        if vbl in m.flows:
            flow_constraints.append(
                flow_constraints(sid, auti, vali, val, mi, vbl,
                                 m.flows[vbl], var_flow_guards)
            )
        else:
            flow_constraints.append(flow_constraints(sid, auti, vali, val, mi,
                                                     vbl,
                                                     None, var_flow_guards))
    return z3.And(*flow_constraints)


def bmc_edges(sid, auti, vali, mi, m):
    # guard_true => edge_taken
    assert False
    return z3.Or()


def bmc_update(sid, auti, vali, mi, m, ei, e):
    # updates and new modes in/active
    # updates all discrete variables
    assert False
    return z3.And()


def bmc_null_update(sid, auti, vali):
    # keeps new modes and discrete vars same as old ones
    assert False
    return z3.And()


def bmc_step(world):
    # This one emits time as well.
    # v_t_flow = v_t_enter + flow(tnow-tprev); v_t_exit = update(v_t_flow)
    # enter vars: BLAH_BLAH_BLAH_ENTER space_auti_vali_cdvarname_ENTER, space_auti_vali_mode_i_active_ENTER
    # flow vars: BLAH_BLAH_BLAH_FLOW space_auti_vali_cdvarname_FLOW
    # exit vars: BLAH_BLAH_BLAH_EXIT space_auti_vali_cdvarname_EXIT,  space_auti_vali_mode_i_active_EXIT, space_auti_vali_mode_i_edge_j_taken_EXIT
    # T vars: t_NOW, t_NEXT
    flow_eqns = []
    for sid, ws in world.spaces.items():
        for auti, vals in enumerate(ws.valuations):
            for vali, valu in enumerate(vals):
                for mi, m in enumerate(valu.ordered_modes):
                    flow_eqns.append(
                        z3.Implies(
                            z3.Bool(varname(sid, auti, vali,
                                            "mode", mi,
                                            "active", "ENTER")),
                            z3.And(
                                bmc_flows(sid, auti, vali, mi, m),
                                bmc_edges(sid, auti, vali, mi, m)
                            )
                        )
                    )
    discrete_eqns = []
    all_edge_takens = []
    for sid, ws in world.spaces.items():
        for auti, vals in enumerate(ws.valuations):
            for vali, valu in enumerate(vals):
                for mi, m in enumerate(valu.ordered_modes):
                    for ei, e in enumerate(m.edges):
                        all_edge_takens.append(
                            z3.Bool(varname(sid, auti, vali,
                                            "mode", mi,
                                            "edge", ei,
                                            "taken", "EXIT")))
                        discrete_eqns.append(
                            z3.Implies(
                                z3.And(
                                    z3.Bool(varname(sid, auti, vali,
                                                    "mode", mi,
                                                    "active", "ENTER")),
                                    z3.Bool(varname(sid, auti, vali,
                                                    "mode", mi,
                                                    "edge", ei,
                                                    "taken", "EXIT"))
                                ),
                                bmc_update(sid, auti, vali, mi, m, ei, e)
                            )
                        )
    discrete_eqns.append(
        z3.Implies(z3.Not(z3.Or(*all_edge_takens)),
                   bmc_null_update(sid, auti, vali)
                   ))
    return z3.And(*(flow_eqns + discrete_eqns))

# These functions return lists of (varname, k-ified-name) tuples


def renumber_enter_vars(formula, k):
    # any var ending in ENTER gets renumbered
    vars = z3u.get_vars(formula)
    renums = []
    is_enter = re.compile("(.*)_ENTER$")
    for v in vars:
        match = is_enter.match(v)
        if not match:
            continue
        renums.append((v, z3.Real(varname(match.group(1), "enter", str(k)))))
    return renums


def renumber_flow_vars(formula, k):
    # This one renumbers tnow, tprev also
    # any var ending in FLOW gets renumbered
    vars = z3u.get_vars(formula)
    renums = [("t_NOW", z3.Real(varname("t", str(k)))),
              ("t_NEXT", z3.Real(varname("t", str(k + 1))))]
    is_flow = re.compile("(.*)_FLOW$")
    for v in vars:
        match = is_flow.match(v)
        if not match:
            continue
        renums.append((v, z3.Real(varname(match.group(1), "flow", str(k)))))
    return renums


def renumber_exit_vars(formula, k):
    # any var ending in EXIT gets renumbered to k+1's enter
    vars = z3u.get_vars(formula)
    renums = []
    is_exit = re.compile("(.*)_EXIT$")
    for v in vars:
        match = is_exit.match(v)
        if not match:
            continue
        renums.append(
            (v, z3.Real(varname(match.group(1), "enter", str(k + 1)))))
    return renums


def bmc(world, target, bound):
    # TODO: fix assumptions of flat modes and no envelopes
    # world = smart_flattener.flatten(world)
    solver = z3.Solver()
    initial = bmc_initial(world)
    solver.add(initial)
    step = bmc_step(world)
    steps = [initial]
    final = bmc_final(target)
    for k in range(0, bound):
        stepk = z3.substitute(step, renumber_enter_vars(step, k))
        stepk = z3.substitute(stepk, renumber_flow_vars(step, k))
        stepk = z3.substitute(stepk, renumber_exit_vars(step, k + 1))
        solver.add(stepk)
        steps.append(stepk)
        finalk = z3.substitute(final, renumber_enter_vars(final, k + 1))
        ret = solver.check(finalk)
        if ret == "sat":
            return solver.model()
    return None


def col_distance(world, sid, valuation, collider_lookup):
    # TODO this is not right and needs substantial changes.
    # does the valuation's space's contacts contain appropriate collisions?
    # tm_rect is (tm_rect, idx, subidx) -- but note it's rectangles so I'd have to convert everything first.
    #  probably I have to look for tilemap collisions and then see which rectangles the collided tiles are in.
    # dynamic is (aut, aut_type, vali, colid)
    #   with implicit assumption that is_active
    blocking = collider_lookup[0] == "block"
    if collider_lookup[0] == "touch":
        _touch, c1, c2 = collider_lookup
        normal = None
    elif collider_lookup[0] == "block":
        _block, c1, c2, nx, ny = collider_lookup
        normal = (nx, ny)
    else:
        assert False, "invalid"
    satisfied = False
    # TODO: this stuff.  once it's done I should have an A* search that bails
    # early if collision plan is not satisfied for valuation.
    for con in world.spaces[sid].contacts:
        if blocking != con.blocking:
            continue
        # check a_key belongs to a collider of valuation
        assert False, "notdone"
        # check normals
        assert False, "notdone"
        # then:
        if con_b_key_is_tilemap and c2_is_tilemap:
            # b_key is collider key, xy, 0
            # check that collider key matches collider_lookup's tilemap identifier index
            # and (something else I forgot??)
            # if so, True and break
            assert False, "notdone"
        elif not con_b_key_is_tilemap and not c2_is_tilemap:
            # check b_key matches collider_lookup
            # if so, True and break
            assert False, "notdone"
        else:
            continue
    # TODO: in the future maybe return distance of valuation vs collider_lookup's <normal> side? unless collider_lookup is inactive or all valuation's colliders are inactive?
    #       honestly that's probably no harder than the above
    return 0 if satisfied else 1


def aut_distance_colpath(n, path):
    new_path = []
    hs = []
    for (sid, auti, vali, valpath) in path:
        valu = n.spaces[sid].valuations[auti][vali]
        if len(valpath) == 0:
            continue
        target_cols, target_condition = valpath[0]
        # TODO: WRONG! It's not just _at least these collisions_, it's
        # _EXACTLY_ these collisions involving valuation
        valu_satisfies_here = all([
            colliding(world, sid, valu, col) == (
                True if is_target_col(col, target_cols) else False)
            for col in n.spaces[sid].colliders])
        # TODO: condition
        if len(valpath) == 1 and valu_satisfies_here:
            # we are satisfying the last thing!
            continue
        target_cols, target_condition = valpath[1]
        valu_satisfies_next = all([
            colliding(world, sid, valu, col) == (
                True if is_target_col(col, target_cols) else False)
            for col in n.spaces[sid].colliders])
        # TODO: condition
        if valu_satisfies_next:
            new_path.append((sid, auti, vali, valpath[1:]))
        elif valu_satisfies_here:
            new_path.append((sid, auti, vali, valpath))
        else:
            return -1, path
        target_cols = new_path[-1][-1][0][0]
        nearness = min([col_distance(n, sid, valu, c) for c in target_cols])
        hs.append(nearness)
    if len(path) == 0 or len(new_path) == 0:
        return 0, []


if __name__ == "__main__":
    world = itp.load_test_plan()
    # Local planner does point-to-point planning with the assumption that
    # the points are nearby each other.  Eventually we want this to be a
    # set-to-set planning problem with the sets defined symbolically, but for
    # now we can say that we are looking for a path between two concrete
    # worlds.

    # as a first attempt, let's use a fixed path and see if we can recover it.
    dt = 1.0 / 60.0
    worlds = [world]
    log = itp.TransitionLog()
    for i in range(0, int(math.ceil((1. / dt) * 2. / 3.))):
        worlds.append(itp.step(worlds[-1].clone(), [], dt, log))
    for i in range(0, int(math.ceil((1. / dt) * 7))):
        worlds.append(itp.step(worlds[-1].clone(), ["right"], dt, log))
    worldK = worlds[-1]

    # The "path" is the sequence of transitions (time, [state, edge]) of each automaton in each space:
    # (time, {space:[..., {idx:[(state, edge), ...transitions], vals}, auts], spaces})
    # From that we can recover valuations at any instant as well as button
    # presses, etc.
    print "Target:", log
    print worldK.spaces["0"].valuations[0][0].get_var("x")
    print worldK.spaces["0"].valuations[0][0].get_var("y")
    mode = sys.argv[1] if len(sys.argv) > 1 else "dijkstra"
    costfn = sys.argv[2] if len(sys.argv) > 2 else "transitions"
    cost_fns = {
        "t": lambda g0, _move0, _move, _log: g0 + dt,
        "moves": lambda g0, move0, move, _log: g0 + (1 if move0 != move else 0),
        "transitions": lambda g0, move0, move, log:
        len(filter(lambda pc: (len(pc[1]) > 0 and
                               len(pc[1]["0"][0]) > 0),
                   log.path))
    }
    if mode == "dijkstra":
        bound = 200000
        print dijkstra(
            world, None,
            cost_fns[costfn],
            lambda w, _ignored: aut_distance(
                w,
                {"0": [[{"x": 13 * 32, "y": 48}]]},
                "0",
                0,
                0),
            dt,
            bound)
    elif mode == "dijkstra_stagger":
        bound = 100000
        print dijkstra_stagger(
            world, None,
            cost_fns[costfn],
            lambda w, _ignored: aut_distance(
                w,
                {"0": [[{"x": 13 * 32, "y": 48}]]},
                "0",
                0,
                0),
            dt,
            bound)
    elif mode == "bmc":
        # let's do bounded model checking!
        # The naive way:
        bound = 100
        print bmc(world,
                  {"0": [[{"x": 13 * 32, "y": 48}]]},
                  bound)
    elif mode == "dijkstra_colpath":
        bound = 100
        # The input to this is a symbolic collision path, which we can
        # say might also include mode transitions.  The key question
        # is: am I looking at just one automaton's collisions and
        # modes, or at those of all automata?  for now let's say all
        # automata.
        # HMM, but that's inconvenient and very very timing sensitive in fact
        #
        # we could start from an assumption of independence of every HA
        # and then refine that abstraction over time, until eventually we
        # end up with a situation where we need to have the whole symbolic
        # path.

        # This is essentially planning with a tunnel.
        playid = ("aut", 0, 0, 0)
        plat0id = ("tm_rect", 0, 0)
        plat1id = ("aut", 1, 0, 0)
        plat2id = ("aut", 2, 0, 0)
        plat3id = ("tm_rect", 0, 1)
        goalid = ("tm_rect", 0, 2)
        plat0 = ("block", playid, plat0id, 0, -1)
        plat1 = ("block", playid, plat1id, 0, -1)
        plat2 = ("block", playid, plat2id, 0, -1)
        plat3 = ("block", playid, plat3id, 0, -1)
        goal = ("touch", playid, goalid)
        col_seq = [("0", 0, 0, [([], []),
                                ([plat0], []),
                                ([plat0, plat1], []),
                                ([plat1], []),
                                ([plat1, plat2], []),
                                ([plat2], []),
                                ([plat2, plat3], []),
                                ([plat3], []),
                                ([plat3, goal], [])])]

        abound = 100000
        print dijkstra_stagger(
            world, col_seq,
            aut_distance_colpath,
            dt,
            bound)

        # now let's find a path through mode X position space that
        # ensures the collision constraints.  we could find a path
        # through symbolic mode X position space and try to optimize
        # towards those collision sequences (penalize for not touching
        # on the normals or for colliding with other stuff).  for each
        # step in the col_seq, there are also implicit assumptions
        # like the collision is available and the objects are near
        # each other and not near other objects.
        # so we could combine this with BMC to guide the search a little bit?
        # we could do it with BMC to find constraints on just one HA's mode
        # evolutions and incidentally the values of other HAs at various times.

        # So let's plan on that:
        # * encode a BMC formula of same length as collision sequence, with only flow constraints and invariants placed on one HA's variables and modes
        # * add collision constraints tying together the HA with the colliders, and for only-sometimes-enabled colliders add the guards on those as being true at least in the periods while the collision is happening
        # * don't worry about the objective position and stuff, for now let's just see if I can find a mode sequence that gets me there
        # ** one approach would be to enumerate mode sequences and do symx on each one to try and solve for times that keep everything valid.  because the time horizon is pretty short!
        pass
