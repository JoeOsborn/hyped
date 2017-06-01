import invariant_finder as invf
import copy
import random
import math
import schema as h
import local_planner as lp
import sys
import os
import time
import multiprocessing as mp
from ConfigParser import ConfigParser

try:
    import hyped.interpreter as itp
except ImportError:
    sys.path.append(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))))
    import hyped.interpreter as itp


class RRT(object):
    __slots__ = ["conf", "events", "index", "space", "dt", "size",
                 "test", "goal", "root", "precision", "time_limit", "node_limit",
                 "modes", "world",
                 "nearest", "select", "expand", "local", "resolve",
                 "space_id", "nodes", "queue",
                 "local_node_limit", "local_planner_threshold"]

    def __init__(self, config, num, dt, world, space_id, test=0):
        self.conf = 'RRT%s' % num
        type_dispatcher = {
            'rrt': (self.nearest_rrt, self.select_rrt, self.expand_rrt, self.local_discrete, self.resolve_rrt),
            'rct': (self.nearest_rct, self.select_rrt, self.expand_rrt, self.local_discrete, self.resolve_rct),
            'rgt': (self.nearest_rgt, self.select_rgt, self.expand_rgt, self.local_discrete, self.resolve_rgt),
            'egt': (self.nearest_egt, self.select_egt, self.expand_rgt, self.local_discrete, self.resolve_egt),
            'rrt_astar': (self.nearest_rrt, self.select_rrt_astar, self.expand_rrt, self.local_astar, self.resolve_rrt),
            'rgt_astar': (self.nearest_rgt, self.select_rgt_astar, self.expand_rgt, self.local_astar, self.resolve_rgt)}
        self.index = [int(i) for i in config.get(
            self.conf, 'index').split(' ')]
        self.precision = int(config.get(self.conf, 'precision'))
        self.time_limit = int(config.get('RRT', 'time_limit'))
        self.node_limit = int(config.get('RRT', 'node_limit'))
        self.local_node_limit = int(config.get(
            'RRT', 'local_node_limit') if config.has_option('RRT', 'local_node_limit') else 300)
        self.local_planner_threshold = int(config.get(
            'RRT', 'local_planner_threshold') if config.has_option('RRT', 'local_planner_threshold') else 16**2)
        goals = [int(g) for g in config.get('RRT', 'goal').split(' ')]
        self.goal = []
        for i in range(0, len(goals), 2):
            self.goal.append((goals[i], goals[i + 1]))
        self.test = test
        self.space_id = space_id
        self.world = world.clone()
        self.world.spaces = {space_id: self.world.spaces[space_id]}
        self.space = Space(str(self.index[0]), world)
        self.dt = dt
        (self.nearest,
         self.select,
         self.expand,
         self.local,
         self.resolve) = type_dispatcher[
            config.get(self.conf, 'type').lower()]
        self.size = 1
        self.events = {"Start:": (time.time(), self.size)}
        self.modes = {}
        self.queue = []
        self.root = Node(self.index, None, lp.itp.step(self.world.clone(), [], self.dt),
                         space_id, ["init"])
        self.get_available(self.root)
        self.calc_r(self.root)
        self.queue.append(self.root)

    def get_available(self, node):
        active = node.val.active_modes
        if str(active) in self.modes:
            node.available = self.modes[str(active)][:]
            node.m = len(node.available)
        else:
            available = []
            mi = 0
            modes = node.state.automata[self.index[0]].ordered_modes
            mode_count = len(modes)
            while mi < mode_count:
                if active & (1 << mi):
                    hor_move = False
                    vert_move = False
                    mode = modes[mi]
                    for e in mode.envelopes:
                        if e.axes[0][1] == 'x':
                            hor_move = True
                            available.append(["left"])
                            available.append(["wait"])
                            available.append(["right"])
                        elif e.axes[0][1] == 'y':
                            vert_move = True
                            available.append(["up"])
                            available.append(["wait"])
                            available.append(["down"])
                    for e in mode.edges:
                        if isinstance(e.guard.conjuncts[0], lp.itp.h.GuardButton):
                            button = e.guard.conjuncts[0].buttonID
                            if not hor_move and not vert_move:
                                try:
                                    available.index(["wait"])
                                except ValueError:
                                    available.append(["wait"])
                                available.append([button])
                            elif hor_move and vert_move:
                                available.append([button, "left"])
                                available.append([button])
                                available.append([button, "right"])
                                available.append([button, "up"])
                                available.append([button])
                                available.append([button, "down"])
                            elif hor_move:
                                available.append([button, "left"])
                                available.append([button])
                                available.append([button, "right"])
                            elif vert_move:
                                available.append([button, "up"])
                                available.append([button])
                                available.append([button, "down"])
                            else:
                                print "Some Error"
                mi += 1
            self.modes[str(active)] = available
            node.available = available[:]
            node.m = len(available)

    def get_hash_str(self, action):
        hashable_string = ""
        for input in action:
            hashable_string += input
        return hashable_string

    def test_goal(self, node):
        nx, ny = node.val.get_var('x'), node.val.get_var('y')
        gx, gy = self.goal[self.test][0], self.goal[self.test][1]
        dist = math.sqrt((nx - gx)**2 + (ny - gy)**2)
        if dist < 16:
            return True
        return False

    def calc_r(self, node):
        for action in node.available:
            state = node.state.clone()
            for i in range(0, self.precision):
                lp.itp.step(state, action, self.dt)
            node.r[self.get_hash_str(action)] = action, state

    def update_cvf(self, node):
        curr = node
        m = curr.m
        k = 1
        while curr:
            curr.cvf += 1.0 / (m**k)
            k += 1
            curr = curr.parent
        return

    def nearest_rrt(self, s2):
        curr = None
        dist = None
        for node in self.queue:
            if len(node.available) > 0:
                new_dist = self.space.get_dist(node.state, s2)
                # print new_dist
                if not dist or new_dist < dist:
                    curr = node
                    dist = new_dist
            else:
                self.queue.remove(node)
        return curr, None

    def nearest_rct(self, s2):
        curr = None
        dist = None
        for node in self.queue:
            if len(node.available) > 0:
                if node.cvf < random.random():
                    new_dist = self.space.get_dist(node.state, s2)
                    if not dist or new_dist < dist:
                        curr = node
                        dist = new_dist
            else:
                self.queue.remove(node)
        return curr, None

    def nearest_rgt(self, s2):
        curr = None
        action = None
        dist = None
        for node in self.queue:
            # print "Node: {!s}".format(node)
            # print "Curr: {!s} Action: {!s} Dist: {!s}".format(curr, action,
            # dist)
            if len(node.available) > 0:
                new_dist = self.space.get_dist(node.state, s2)
                new_action = None
                rdist = None
                for k, v in node.r.iteritems():
                    new_rdist = self.space.get_dist(v[1], s2)
                    if not rdist or new_rdist < rdist:
                        new_action = v[0]
                        rdist = new_rdist
                        # print "New rdist: {!s} New Action:
                        # {!s}".format(rdist, k)
                if (not dist and rdist < new_dist) or rdist < new_dist < dist:
                    curr = node
                    action = new_action
                    dist = new_dist

                    # print "New Dist: {!s} New Action: {!s}".format(new_dist,
                    # action)
            else:
                self.queue.remove(node)
        # print "Chosen: {!s} Action: {!s} Dist: {!s} Rdist: {!s}".format(curr,
        # action, dist, rdist)
        return curr, action

    def nearest_egt(self, s2):
        curr = None
        action = None
        dist = None
        for node in self.queue:
            # print "Node: {!s}".format(node)
            # print "Curr: {!s} Action: {!s} Dist: {!s}".format(curr, action,
            # dist)
            if len(node.available) > 0:
                if node.cvf < random.random():
                    new_dist = self.space.get_dist(node.state, s2)
                    new_action = None
                    rdist = None
                    for k, v in node.r.iteritems():
                        new_rdist = self.space.get_dist(v[1], s2)
                        if not rdist or new_rdist < rdist:
                            new_action = v[0]
                            rdist = new_rdist
                            # print "New rdist: {!s} New Action:
                            # {!s}".format(rdist, k)
                    if (not dist and rdist < new_dist) or rdist < new_dist < dist:
                        curr = node
                        action = new_action
                        dist = new_dist

                        # print "New Dist: {!s} New Action:
                        # {!s}".format(new_dist, action)
            else:
                self.queue.remove(node)
        # print "Chosen: {!s} Action: {!s} Dist: {!s} Rdist: {!s}".format(curr,
        # action, dist, rdist)
        return curr, action

    def select_rrt(self, node, action, target):
        choice = random.randint(0, len(node.available) - 1)
        input = node.available[choice]
        del node.available[choice]
        return Node(self.index, node, node.state.clone(), self.space_id, input)

    def select_rrt_astar(self, node, action, target):
        return Node(self.index, node, node.state.clone(), self.space_id, [])

    def select_rgt(self, node, action, target):
        if not node or not action:
            return None
        hash_str = self.get_hash_str(action)
        if self.space.check_bounds(node.r[hash_str][1]) and node.r[hash_str][0] in node.available:
            node.available.remove(action)
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]) and v[0] in node.available:
                    new_dist = self.space.get_dist(v[1], target)
                    if not dist or new_dist < dist:
                        new_action = v[0]
                        dist = new_dist
            if not new_action and not dist:
                node.available = []
                return None
            else:
                node.available.remove(new_action)
                return Node(self.index, node, node.state.clone(), self.space_id, new_action)

    def select_rgt_astar(self, node, action, target):
        if not node or not action:
            return None
        hash_str = self.get_hash_str(action)
        if self.space.check_bounds(node.r[hash_str][1]) and node.r[hash_str][0] in node.available:
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]) and v[0] in node.available:
                    new_dist = self.space.get_dist(v[1], target)
                    if not dist or new_dist < dist:
                        new_action = v[0]
                        dist = new_dist
            if not new_action and not dist:
                node.available = []
                return None
            else:
                return Node(self.index, node, node.state.clone(), self.space_id, new_action)

    def select_egt(self, node, action, target):
        if not node or not action:
            return None
        hash_str = self.get_hash_str(action)
        if self.space.check_bounds(node.r[hash_str][1]) and node.r[hash_str][0] in node.available:
            self.update_cvf(node)
            node.available.remove(action)
            node.r.pop(hash_str)
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            self.update_cvf(node)
            node.r.pop(hash_str)
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]) and v[0] in node.available:
                    new_dist = self.space.get_dist(v[1], target)
                    if not dist or new_dist < dist:
                        new_action = v[0]
                        dist = new_dist
            if not new_action and not dist:
                node.r = {}
                node.available = []
                return None
            else:
                node.available.remove(new_action)
                node.r.pop(self.get_hash_str(new_action))
                return Node(self.index, node, node.state.clone(), self.space_id, new_action)

    def expand_rrt(self, node, target):
        return self.local(node, target)

    def expand_rgt(self, node, target):
        steps = 0
        if node:
            steps = self.local(node, target)
            self.get_available(node)
            self.calc_r(node)
        return steps

    def local_discrete(self, node, _target):
        steps = 0
        while self.space.check_bounds(node.state) and steps < self.precision:
            # print "step"
            lp.itp.step(node.state, node.action, self.dt)
            steps += 1
        return steps

    def local_astar_distance(self, w, target):
        dist = self.space.get_dist(w, target)
        if not self.space.check_bounds(w):
            return -1, None
        # FIXME: magic number
        if dist < self.local_planner_threshold:
            return 0, None
        return dist, None

    def local_astar(self, node, target):
        """Steps means something different here."""
        success, astar_node, path = lp.dijkstra(
            node.state, None,
            lambda g0, h, _move0, _move, log: log.t + h,
            lambda w, _ignore: self.local_astar_distance(w, target),
            self.dt,
            self.local_node_limit,
            self.precision
        )
        node.state = astar_node
        node.action = path
        if success:
            return self.precision + 1
        else:
            # Future: maybe return precision * 1-(closest_node_distance/initial
            # distance from target)
            return self.precision

    def resolve_rrt(self, new_node):
        del new_node

    def resolve_rct(self, new_node):
        self.update_cvf(new_node.parent)
        del new_node

    def resolve_rgt(self, new_node):
        if new_node:
            del new_node

    def resolve_egt(self, new_node):
        if new_node:
            self.update_cvf(new_node.parent)
            del new_node

    def grow(self, id=0, queue=None, results=None):
        skips = 0
        fails = 0
        while (0 == self.time_limit or time.time() - self.events["Start:"][0] < self.time_limit) and \
                (0 == self.node_limit or self.size < self.node_limit):
            # print "Tree Size: %s" % self.size
            # Get random goal state and best state
            target = self.space.get_sample()

            if random.random() <= 0.05:
                target[self.index[0]][self.index[1]][
                    "variables"]["x"] = self.goal[self.test][0]
                target[self.index[0]][self.index[1]][
                    "variables"]["y"] = self.goal[self.test][1]
            assert len(self.queue) > 0
            # Select best state by some algorithm
            node, action = self.nearest(target)

            # Create a new node from random available choices of found node
            if node:
                # print node, action
                # Select input to expand by some algorithm
                new_node = self.select(node, action, target)

                # print "Parent: {!s} Child: {!s}".format(node.get_origin(), new_node.get_origin())
                # Expand input by some algorithm
                steps = self.expand(new_node, target)

                # Resolve changes by some algorithm
                if steps >= self.precision:
                    # Increase tree size and insert into tree
                    # print node.val.get_var("x"), node.val.get_var("y")
                    # print new_node.val.get_var("x"),
                    # new_node.val.get_var("y")
                    self.size += 1
                    self.get_available(new_node)
                    node.children.append(new_node)
                    # print "OK", steps, self.precision

                    # Add to tree and append to queue for visualization
                    self.queue.append(new_node)
                    if queue:
                        queue.put(node.state)
                        queue.put(new_node.state)

                    # Check if goal reached
                    if self.test_goal(node) and "Goal Reached:" not in self.events:
                        self.events["Goal Reached:"] = (
                            time.time() - self.events["Start:"][0], self.size)
                else:
                    # print "NOK'", steps, self.precision
                    self.resolve(new_node)
                    fails += 1
            else:
                skips += 1
                pass
        print "\t%s exiting (%s skips, %s fails)..." % (self.conf, skips, fails)
        self.events["Terminated:"] = (
            time.time() - self.events["Start:"][0], self.size)
        # for e in self.events:
        #     print "\t" + e + " " + str(self.events[e])
        if results:
            results.put(self.events)

    def profile_grow(self, i, queue, results):
        import cProfile
        prof = cProfile.Profile()
        prof.runcall(self.grow, i, queue, results)
        prof.dump_stats('prof%d.out' % i)

    def get_path(self, node):
        curr = node
        result = ""
        while curr.parent:
            result = str(curr.action) + ";\n" + result
            curr = curr.parent
        result = str(curr.action) + ";\n" + result
        print result


class Node(object):
    __slots__ = ["state", "val", "action", "available",
                 "parent", "children", "r", "m", "cvf"]

    def __init__(self, index, parent, state, space_id, action):
        self.state = state
        self.val = self.state.spaces[space_id].valuations[index[0]][index[1]]
        self.action = action[:]
        self.available = []
        self.parent = parent
        self.children = []
        self.r = {}
        self.m = -1
        self.cvf = 0

    def get_origin(self):
        return [self.val.get_var('x'), self.val.get_var('y'), 0.6]


class Intervals(object):
    __slots__ = ["ivs", "options"]

    @classmethod
    def Unit(cls, val):
        return cls([(val, val)])

    def __init__(self, ivs):
        self.ivs = sorted(ivs)
        self._recalculate_options()

    def __str__(self):
        return str(self.ivs)

    def __repr__(self):
        return "Intervals(" + str(self.ivs) + ")"

    def __eq__(self, other):
        return self.ivs == other.ivs

    def __ne__(self, other):
        return not self.__eq__(other)

    def _recalculate_options(self):
        self.options = []
        for iv in self.ivs:
            assert not math.isinf(iv[0])
            assert not math.isinf(iv[1])
            self.options += range(int(iv[0]), int(iv[1]) + 1, 1)

    @property
    def lower(self):
        return self.options[0]

    @property
    def upper(self):
        return self.options[-1]

    def always_below(self, val):
        return self.upper <= val

    def always_above(self, val):
        return self.lower >= val

    def interval_overlap(self, iv1, iv2):
        # Either endpoint of ivA is between endpoints of ivB.
        return (
            (iv2[0] <= iv1[0] <= iv2[1]) or
            (iv2[0] <= iv1[1] <= iv2[1]) or
            (iv1[0] <= iv2[0] <= iv1[0]) or
            (iv1[0] <= iv2[1] <= iv1[0])
        )

    def interval_merge(self, iv1, iv2):
        return (min(iv1[0], iv2[0]), max(iv1[1], iv2[1]))

    def append_interval(self, lst, next_one):
        if len(lst) == 0:
            lst.append(next_one)
            return
        if self.interval_overlap(lst[-1], next_one):
            lst[-1] = self.interval_merge(lst[-1], next_one)
        else:
            lst.append(next_one)

    def merge(self, other):
        ivs = copy.copy(self.ivs)
        oivs = copy.copy(other.ivs)
        ivi = 0
        ovi = 0
        result = []
        # merge sorted lists by popping from whichever has earlier thing
        while ivi < len(ivs) or ovi < len(oivs):
            next_one = None
            if ivi == len(ivs):
                next_one = oivs[ovi]
                ovi += 1
            elif ovi == len(oivs):
                next_one = ivs[ivi]
                ivi += 1
            elif self.interval_overlap(ivs[ivi], oivs[ovi]):
                next_one = self.interval_merge(ivs[ivi], oivs[ovi])
                ivi += 1
                ovi += 1
            elif ivs[ivi][0] < oivs[ovi][0]:
                next_one = ivs[ivi]
                ivi += 1
            else:
                next_one = oivs[ovi]
                ovi += 1
            assert next_one is not None
            self.append_interval(result, next_one)
        self.ivs = result
        self._recalculate_options()

    def sample(self):
        return random.choice(self.options)

    def contains(self, val):
        for iv in self.ivs:
            if iv[0] <= val <= iv[1]:
                return True
        return False


def get_combination_data(aut, groups):
    mode_mask = 0
    edges_out = []
    edges_in = []
    modes = []
    flows = invf.default_automaton_flows(aut.parameters,
                                         aut.variables)
    for group in groups:
        for mode in group[1]:
            ordered_mode = aut.ordered_modes[
                aut.ordering[mode.qualified_name]
            ]
            edges_out += ordered_mode.edges
            edges_in += invf.ordered_modes_entering(
                aut,
                ordered_mode,
                implicit=True)
            flows = invf.merge_flows(flows,
                                     ordered_mode.flows,
                                     ordered_mode.envelopes)
            mode_mask |= 1 << ordered_mode.index
            modes.append(ordered_mode)
    return modes, mode_mask, flows, edges_out, edges_in


def get_flow_bounds(world, val, flows):
    bounds = {}
    for flow_var, vflows in flows.items():
        ivs = []
        var = None
        for flow in vflows:
            # print flow_var, flow
            if isinstance(flow, lp.itp.h.Envelope):
                refl = flow.reflections
                sust = lp.itp.eval_value(flow.sustain[1],
                                         world,
                                         val)
                var = (flow.variables[0]
                       if flow.variables[0].basename == flow_var
                       else flow.variables[1])
                if refl == 0:
                    flow_vals = [
                        (0, sust) if sust > 0 else (sust, 0)]
                else:
                    # TODO: -max, 0, max?
                    flow_vals = [
                        (-abs(sust),
                         abs(sust))
                    ]
            else:
                var = flow.var
                flow_val = lp.itp.eval_value(
                    flow.value, world, val)
                flow_vals = [(flow_val, flow_val)]
                # TODO: if some collider is non-static
                if not world.automata[
                        val.automaton_index].colliders[0].is_static:
                    flow_vals.append((0, 0))
            ivs += flow_vals
        bounds[var.name] = Intervals(ivs)
        if var.degree == 0:
            bounds[var.name + "'"] = Intervals([(0, 0)])
            bounds[var.name + "''"] = Intervals([(0, 0)])
        elif var.degree == 1:
            bounds[var.name + "'"] = Intervals([(0, 0)])
        elif var.degree == 2:
            pass
        else:
            assert False
    return bounds


class Space(object):
    __slots__ = ["index", "vars", "bounds"]

    def __init__(self, index, world):
        self.index = index
        self.bounds = []
        refine_bounds = True
        valuations = world.spaces[index].valuations
        for i in range(0, len(valuations)):
            aut = world.automata[i]
            mode_combinations = list(lp.itp.h.mode_combinations(
                aut
            ))
            aut_bounds = []
            self.bounds.append(aut_bounds)
            for val in valuations[i]:
                vbounds = {}
                aut_bounds.append(vbounds)
                # for individual combinations, use invariants
                # and then see if the union of all combinations has some invariant as well.
                # here we're looking to see if e.g. y' is always 0 or
                # something.
                shared_bounds = {
                    "variables": {var.name: Intervals.Unit(lp.itp.eval_value(var, world, val))
                                  for var in aut.variables.values()},
                    "dvariables": {var.name: Intervals.Unit(lp.itp.eval_value(var, world, val))
                                   for var in aut.dvariables.values()},
                    "timers": {t: Intervals([(0, 0)]) for t in range(len(val.timers))}
                }
                if refine_bounds:
                    for groups in mode_combinations:
                        (modes,
                         _mask,
                         flows,
                         edges_in,
                         edges_out) = get_combination_data(aut, groups)
                        flow_constraints = get_flow_bounds(world, val, flows)
                        for fv, fint in flow_constraints.items():
                            shared_bounds["variables"][fv].merge(fint)
                            # print fv, fint
                    for e in edges_in:
                        for uk, uv in e.updates.items():
                            # TODO: what about updates that refer to
                            # non-constants?
                            shared_bounds["variables"][uk].merge(
                                Intervals.Unit(
                                    lp.itp.eval_value(uv, world, val)))
                    # TODO: for e in edges_out, if guard constraints any value
                    # use that info.
                    for v in [v for v in aut.variables.values() if v.degree == 2]:
                        # if any acceleration, velocity might be arbitrary
                        # (later, consider guards and updates too)
                        here = shared_bounds["variables"][v.name]
                        lo = shared_bounds["variables"][v.name[:-1]]
                        if here == Intervals.Unit(0):
                            pass
                        elif here.always_below(0):
                            lo.merge(Intervals([(-1000, lo.upper)]))
                        elif here.always_above(0):
                            lo.merge(Intervals([(lo.lower, 1000)]))
                        else:
                            lo.merge(Intervals([(-1000, 1000)]))
                    for v in [v for v in aut.variables.values() if v.degree == 1]:
                        # if any acceleration or velocity, position might be
                        # arbitrary (later, consider guards and updates too)
                        here = shared_bounds["variables"][v.name]
                        lo = shared_bounds["variables"][v.name[:-1]]
                        if here == Intervals.Unit(0):
                            pass
                        elif here.always_below(0):
                            lo.merge(Intervals([(0, lo.upper)]))
                        elif here.always_above(0):
                            lo.merge(Intervals([(lo.lower, 640)]))
                        else:
                            lo.merge(Intervals([(0, 640)]))
                else:
                    for vn in shared_bounds["variables"]:
                        if vn.endswith("'"):
                            shared_bounds["variables"][vn] = Intervals(
                                [(-1000, 1000)])
                        else:
                            shared_bounds["variables"][vn] = Intervals(
                                [(0, 640)])
                    for vn in shared_bounds["dvariables"]:
                        shared_bounds["dvariables"][vn] = Intervals([(0, 128)])
                    for vn in shared_bounds["timers"]:
                        shared_bounds["timers"][vn] = Intervals([(0, 10)])
                print aut.name, "shared bounds", shared_bounds
                for groups in mode_combinations:
                    (modes,
                     mode_mask,
                     flows,
                     edges_in,
                     edges_out) = get_combination_data(aut, groups)
                    # print "found mask", mode_mask
                    mode_bounds = copy.deepcopy(shared_bounds)
                    for t, _ in enumerate(val.timers):
                        # FIXME use invariants/interesting intervals
                        # use the max interesting value of this timer to
                        # bound?
                        # This should give (0,0) for timers associated with
                        # inactive modes in this combined-mode
                        mode_bounds["timers"][t] = Intervals(
                            [(0, 10.0)]
                            if ((1 << t) & mode_mask)
                            else [(0, 0)])
                    if refine_bounds:
                        flow_constraints = get_flow_bounds(world, val, flows)
                        mode_bounds["variables"].update(flow_constraints)
                        for e in edges_in:
                            for uk, uv in e.updates.items():
                                # TODO: what about updates that refer to
                                # non-constants?
                                mode_bounds["variables"][uk].merge(
                                    Intervals.Unit(
                                        lp.itp.eval_value(uv, world, val)))

                    print aut.name, "Bound", mode_mask, mode_bounds
                    vbounds[mode_mask] = mode_bounds

    def get_sample(self):
        result = []
        for i in range(0, len(self.bounds)):
            result.append([])
            for a in range(0, len(self.bounds[i])):
                vals = {
                    "active_modes": 0,
                    "variables": {},
                    "dvariables": {},
                    "timers": {}
                }
                result[i].append(vals)
                # start by picking a discrete mode
                vbounds = self.bounds[i][a]
                mode = random.choice(vbounds.keys())
                mbounds = vbounds[mode]
                vals["active_modes"] = mode
                for vk, vv in mbounds["variables"].items():
                    vals["variables"][vk] = vv.sample()
                for vk, vv in mbounds["dvariables"].items():
                    vals["dvariables"][vk] = vv.sample()
                for vk, vv in mbounds["timers"].items():
                    vals["timers"][vk] = vv.sample()
        return result

    def get_dist(self, s1, s2):
        sqrsum = 0
        # Distance over all things
        # but we could try task distance of just player x,y.
        for i, aut in enumerate(s1.spaces[self.index].valuations):
            s2i = s2[i]
            for a, val in enumerate(aut):
                s2ia = s2i[a]
                if val.active_modes != s2ia["active_modes"]:
                    sqrsum += 10 ** 2
                # TODO: could speed this up with canonical var ordering
                vars = s2ia["variables"]
                for v in vars:
                    sqrsum += (val.get_var(v) - vars[v]) ** 2
                # dvars = s2ia["dvariables"]
                # for v in dvars:
                #     sqrsum += (val.get_dvar(v) - dvars[v]) ** 2
                # timers = s2ia["timers"]
                # for v in s2ia["timers"]:
                #     sqrsum += (val.timers[v] - timers[v]) ** 2
        return sqrsum

    def check_bounds(self, s1):
        # by definition this will be in configuration space, so
        # just check for out of bounds.
        for i in range(0, len(s1.spaces[self.index].valuations)):
            vals = s1.spaces[self.index].valuations[i]
            for a in range(0, len(vals)):
                active_modes = vals[a].active_modes
                for m in range(0, len(s1.automata[i].ordered_modes)):
                    if active_modes & (1 << m) and s1.automata[i].ordered_modes[m].name == "dead":
                        print "Dead"
                        return False
                x = vals[a].get_var("x")
                if x < 0 or x > 640:
                    return False
                y = vals[a].get_var("y")
                if y < 0 or y > 640:
                    return False
        return True


def test_all():
    config = ConfigParser()
    config.read("settings.ini")
    test_num = 0
    iterations = int(config.get('RRT', 'iterations'))
    results = {}
    result_queue = []
    for i in range(0, int(config.get('RRT', 'trees'))):
        result_queue.append(mp.Queue())

    for test in [lp.itp.load_test_plan,
                 lp.itp.load_test_plan2,
                 lp.itp.load_test_plan3,
                 lp.itp.platformPlanning1
                 ]:
        curr_test = "Test " + str(test_num)
        print curr_test
        for n in range(0, iterations):
            print "--------------------------------------------------------------------------------------"
            print "\tIteration " + str(n)
            procs = []
            node = test()
            running = True

            for i in range(0, int(config.get('RRT', 'trees'))):
                print "\tLoading Tree %s" % i
                tree = RRT(config, i, 1.0 / 60.0, node.clone(), "0", test_num)
                search = mp.Process(
                    target=tree.grow, args=(i, None, result_queue[i]))
                procs.append(search)
                search.start()

            print "\n"

            while running:
                running = False
                for proc in procs:
                    if proc.is_alive():
                        running = True
                        time.sleep(1)

        i = 0
        finals = {}
        for q in result_queue:
            tree = "Tree " + str(i)
            finals[tree] = {"Terminated:": [0, 0],
                            "Goal Reached:": [0, 0],
                            "Success Rate:": [0, 0]}
            while not q.empty():
                e = q.get()
                # print "Events: {!s}".format(e)

                for k, v in e.iteritems():
                    if k != "Start:":
                        # print "KVP: {!s}, {!s}".format(k, v)
                        finals[tree][k][0] += v[0]
                        finals[tree][k][1] += v[1]
                    if k == "Goal Reached:":
                        finals[tree]["Success Rate:"][0] += 1
                        finals[tree]["Success Rate:"][1] += 1
            i += 1

        for tree in finals:
            for k, v in finals[tree].iteritems():
                # print "Value: {!s}".format(v)
                if k != "Success Rate:":
                    for num in range(0, len(v)):
                        v[num] /= iterations
                else:
                    v[0] /= float(iterations)
        print "\nFinals: {!s}\n".format(finals)
        results[curr_test] = finals
        test_num += 1

    print "--------------------\nTest Results:\n--------------------"
    for k, v in results.iteritems():
        print "{!s}:".format(k)
        for k, v in v.iteritems():
            print "\t{!s}".format(k)
            print "\t\t{!s}".format(v)
        print ""


if __name__ == "__main__":
    test_all()
