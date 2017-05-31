import heapq
import invariant_finder as invf
import interpreter as itp
import random
import math
import hyped.schema as h
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
    __slots__ = ["conf_num", "events", "index", "space", "dt", "size",
                 "goal", "root", "precision", "time_limit", "node_limit",
                 "modes", "world",
                 "nearest", "select", "expand", "local", "resolve",
                 "space_id", "nodes", "queue",
                 "local_node_limit", "local_planner_threshold"]

    def __init__(self, config, num, dt, world, space_id):
        self.conf_num = 'RRT%s' % num
        type_dispatcher = {
            'rrt': (self.nearest_rrt, self.select_rrt, self.expand_rrt, self.local_discrete, self.resolve_rrt),
            'rct': (self.nearest_rct, self.select_rrt, self.expand_rrt, self.local_discrete, self.resolve_rct),
            'rgt': (self.nearest_rgt, self.select_rgt, self.expand_rgt, self.local_discrete, self.resolve_rgt),
            'egt': (self.nearest_egt, self.select_egt, self.expand_rgt, self.local_discrete, self.resolve_egt),
            'rrt_astar': (self.nearest_rrt, self.select_rrt_astar, self.expand_rrt, self.local_astar, self.resolve_rrt),
            'rgt_astar': (self.nearest_rgt, self.select_rgt_astar, self.expand_rgt, self.local_astar, self.resolve_rgt)}
        self.index = [int(i) for i in config.get(
            self.conf_num, 'index').split(' ')]
        self.precision = int(config.get(self.conf_num, 'precision'))
        self.time_limit = int(config.get('RRT', 'time_limit'))
        self.node_limit = int(config.get('RRT', 'node_limit'))
        self.local_node_limit = int(config.get(
            'RRT', 'local_node_limit') if config.has_option('RRT', 'local_node_limit') else 300)
        self.local_planner_threshold = int(config.get(
            'RRT', 'local_planner_threshold') if config.has_option('RRT', 'local_planner_threshold') else 16**2)
        self.goal = [int(v) for v in config.get('RRT', 'goal').split(' ')]
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
            config.get(self.conf_num, 'type').lower()]
        self.size = 1
        self.events = {"Start:": (time.time(), self.size)}
        self.modes = {}
        self.queue = []
        self.root = Node(self.index, None, self.world.clone(),
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
                        if isinstance(e.guard.conjuncts[0], h.GuardButton):
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
        gx, gy = self.goal[0], self.goal[1]
        dist = math.sqrt((nx - gx)**2 + (ny - gy)**2)
        if dist < 16:
            return True
        return False

    def calc_r(self, node):
        for action in node.available:
            state = node.state.clone()
            for i in range(0, self.precision):
                lp.itp.step(state, action, 1.0 / 60.0)
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
        if self.space.check_bounds(node.r[hash_str][1]):
            node.available.remove(action)
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            node.available.remove(action)
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]):
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
        if self.space.check_bounds(node.r[hash_str][1]):
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]):
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
        if not node:
            return None
        hash_str = self.get_hash_str(action)
        if self.space.check_bounds(node.r[hash_str][1]):
            self.update_cvf(node)
            node.available.remove(action)
            node.r.pop(hash_str)
            return Node(self.index, node, node.state.clone(), self.space_id, action)
        else:
            self.update_cvf(node)
            node.available.remove(action)
            node.r.pop(hash_str)
            new_action = None
            dist = None
            for k, v in node.r.iteritems():
                if self.space.check_bounds(v[1]):
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
            lp.itp.step(node.state, node.action, 1.0 / 60.0)
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
            self.local_node_limit
        )
        node.state = astar_node
        node.action = path
        if success:
            return self.precision
        else:
            # Future: maybe return precision * 1-(closest_node_distance/initial
            # distance from target)
            return 0

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

    def grow(self, queue=None):
        while (0 == self.time_limit or time.time() - self.events["Start:"][0] < self.time_limit) and \
                (0 == self.node_limit or self.size < self.node_limit):
            # Get random goal state and best state
            target = self.space.get_sample()

            # Select best state by some algorithm
            node, action = self.nearest(target)

            # Create a new node from random available choices of found node
            if node:
                # Select input to expand by some algorithm
                new_node = self.select(node, action, target)

                # Expand input by some algorithm
                steps = self.expand(new_node, target)

                # Resolve changes by some algorithm
                if steps >= self.precision:
                    # Increase tree size and insert into tree
                    self.size += 1
                    self.get_available(new_node)
                    node.children.append(new_node)

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
                    self.resolve(new_node)
            else:
                pass
        print "%s exiting..." % self.conf_num
        self.events["Terminated:"] = (
            time.time() - self.events["Start:"][0], self.size)
        for e in self.events:
            print e + " " + str(self.events[e])

    @staticmethod
    def get_path(node):
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

    def __init__(self, ivs):
        self.ivs = sorted(ivs)
        self.options = []
        for iv in self.ivs:
            assert not math.isinf(iv[0])
            assert not math.isinf(iv[1])
            self.options += range(int(iv[0]), int(iv[1]) + 1, 1)

    def sample(self):
        return random.choice(self.options)

    def contains(self, val):
        for iv in self.ivs:
            if iv[0] <= val <= iv[1]:
                return True
        return False


class Space(object):
    __slots__ = ["index", "vars", "bounds"]

    def __init__(self, index, world):
        self.index = index
        self.bounds = []
        valuations = world.spaces[index].valuations
        for i in range(0, len(valuations)):
            aut = world.automata[i]
            mode_combinations = h.mode_combinations(
                aut
            )
            aut_bounds = []
            self.bounds.append(aut_bounds)
            for val in valuations[i]:
                vbounds = {}
                aut_bounds.append(vbounds)
                for groups in mode_combinations:
                    # print aut.name, i, "start group group"
                    mode_mask = 0
                    modes = []
                    for group in groups:
                        # print "inner group"
                        for mode in group[1]:
                            ordered_mode = aut.ordered_modes[
                                aut.ordering[mode.qualified_name]
                            ]
                            # print "mode in", ordered_mode.name, (1 <<
                            # ordered_mode.index)
                            modes.append(ordered_mode)
                            mode_mask |= 1 << ordered_mode.index
                    # print "found mask", mode_mask
                    mode_bounds = {
                        "variables": {},
                        "dvariables": {},
                        "timers": {}
                    }
                    flows = {}
                    for m in modes:
                        invf.merge_flows(flows, m.flows, m.envelopes)
                    for val in valuations[i]:
                        #                        flows =
                        # pick arbitrary values for all variables in ranges (later get these from invariants)
                        # then refine those picks like so:
                        # iterate through flows and pick values for accs or velocities (fixed or flow vel means pick acc = 0, fixed pos for some reason means set vel and acc to 0)
                        # (don't iterate through aut.variables.values at all)
                        for var in aut.variables.values():

                            # if the variable is positional, use information about world, colliders, etc too
                            # if the mode has a flow on this variable, use the flow
                            # if the mode has an envelope on this variable, use the envelope bounds
                            # if the mode has an update leading into it that sets this variable...
                            # FIXME
                            if var.degree == 0:
                                mode_bounds["variables"][var.name] = Intervals(
                                    [(0, 640)])
                            else:
                                mode_bounds["variables"][var.name] = Intervals(
                                    [(-1000, 1000)])
                            # if var.degree == 0:
                            #     mode_bounds["variables"][var.name] = (0, 640) if var.name == "x" else (
                            #         0,
                            #         val.get_var("y")
                            #     )
                            #     if i > 0 and var.name == "y":
                            #         mode_bounds["variables"][var.name] = (
                            #             val.get_var("y"), val.get_var("y"))
                            #     if i == 1 and var.name == "x":
                            #         mode_bounds["variables"][var.name] = (
                            #             3 * 32 - 1, 5 * 32 + 1)
                            #     elif i == 2 and var.name == "x":
                            #         mode_bounds["variables"][var.name] = (
                            #             7 * 32 - 1, 9 * 32 + 1)
                            # else:
                            #     if var.name == "y''" and i == 0:
                            #         mode_bounds["variables"][var.name] = (
                            #             -1000, 0
                            #         )
                            #     elif (var.name == "y'" or var.name == "y''") and i > 0:
                            #         mode_bounds["variables"][var.name] = (0, 0)
                            #     elif var.name == "y'" and i == 0:
                            #         mode_bounds["variables"][var.name] = (
                            #             -256, 0)
                            #     elif var.name == "x''":
                            #         mode_bounds["variables"][var.name] = (0, 0)
                            #     elif var.name == "x'" and i == 0:
                            #         mode_bounds["variables"][var.name] = (
                            #             -60, 60)
                            #     elif var.name == "x'" and i > 0:
                            #         mode_bounds["variables"][var.name] = (
                            #             -30, 30)
                            #     else:
                            #         mode_bounds["variables"][var.name] = (
                            #             -1000,
                            #             1000
                            #         )
                        for dvar in aut.dvariables.values():
                            # if the mode has an udpate leading into
                            # it that changes this dvar, use that
                            # update (if it's constant or whatever)
                            # FIXME
                            mode_bounds["dvariables"][dvar.name] = Intervals(
                                [(-128, 128)])
                        for t, _ in enumerate(val.timers):
                            # FIXME
                            # use the max interesting value of this timer to
                            # bound?
                            # This should give (0,0) for timers associated with
                            # inactive modes in this combined-mode
                            mode_bounds["timers"][t] = Intervals(
                                [(0, 10.0)] if ((1 << t) & mode_mask)
                                else [(0, 0)])
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
        for i in range(0, len(s1.spaces[self.index].valuations)):
            for a in range(0, len(s1.spaces[self.index].valuations[i])):
                if s1.spaces[self.index[0]].valuations[i][a].active_modes != s2[i][a]["active_modes"]:
                    sqrsum += 10 ** 2
                for v in s2[i][a]["variables"]:
                    sqrsum += (s1.spaces[self.index].valuations[i][a].get_var(v) -
                               s2[i][a]["variables"][v]) ** 2
                for v in s2[i][a]["dvariables"]:
                    sqrsum += (s1.spaces[self.index].valuations[i][a].get_dvar(v) -
                               s2[i][a]["dvariables"][v]) ** 2
                for v in s2[i][a]["timers"]:
                    sqrsum += (s1.spaces[self.index].valuations[i][a].timers[v] -
                               s2[i][a]["timers"][v]) ** 2
        return sqrsum

    def check_bounds(self, s1):
        for i in range(0, len(s1.spaces[self.index].valuations)):
            for a in range(0, len(s1.spaces[self.index].valuations[i])):
                active_modes = s1.spaces[
                    self.index].valuations[i][a].active_modes
                for v in self.bounds[i][a][active_modes]["variables"]:
                    vv = self.bounds[i][a][active_modes]["variables"][v]
                    val = s1.spaces[self.index].valuations[i][a].get_var(v)
                    if not vv.contains(val):
                        # print v, vl, val, vh
                        return False
        return True


class SpatialHash(object):
    __slots__ = ["cell_size", "contents"]

    def __init__(self, cell_size):
        self.cell_size = cell_size
        self.contents = {}

    def _hash(self, point):
        return int(point[0] / self.cell_size), int(point[1] / self.cell_size)

    def append(self, node):
        self.contents.setdefault(self._hash(
            node.get_origin()), []).append(node)

    def query(self, point):
        bucket = self.contents.get(self._hash(point))
        if bucket:
            return [(0, bucket)]
        else:
            return None

    def query_nearest(self, point):
        dist = 0
        bucket = None
        queue = []
        for b in self.contents:
            center = (b[0] * self.cell_size + 0.5 * self.cell_size,
                      b[1] * self.cell_size + 0.5 * self.cell_size)
            sqrsum = (point[0] - b[0]) ** 2
            sqrsum += (point[1] - b[1]) ** 2
            heapq.heappush(queue, (sqrsum, self.contents[b]))
        return queue

    def print_table(self):
        print self.contents
        for b in self.contents:
            print b


def test_all():
    config = ConfigParser()
    config.read("settings.ini")
    iterations = 0

    for test in [lp.itp.load_test_plan, lp.itp.load_test_plan2, lp.itp.load_test_plan3]:
        print "Test %s:" % iterations
        procs = []
        node = test()
        running = True

        for i in range(0, int(config.get('RRT', 'trees'))):
            print "Loading Tree %s" % i
            tree = RRT(config, i, 1.0 / 60.0, node.clone(), "0")
            search = mp.Process(target=tree.grow)
            procs.append(search)
            search.start()

        while running:
            running = False
            for proc in procs:
                if proc.is_alive():
                    running = True

        print ""
        iterations += 1


if __name__ == "__main__":
    test_all()
