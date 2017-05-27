import heapq

import schema as schema
import interpreter as itp
import local_planner as lp
import random
import invariant_finder as invf


def get_nearest_hash(self, target):
    #target = self.space.get_sample()
    queue = self.nodes.query((target['x'], target['y']))
    if not queue:
        queue = self.nodes.queryNearest((target['x'], target['y']))
    # print queue
    for bucket in queue:
        for node in bucket[1]:
            if len(node.available) > 0:
                # print node, target
                return node
    return None


def dijkstra(self, queue):
    for i in range(0, self.constraint):
        # Get random goal state and nearest node
        goal = self.space.get_sample()
        node = None
        if len(self.queue) > 0:
            node = self.queue.pop()

        # Create a new node from random available choices of found node
        if node:
            #choice = random.randint(0, len(node.available)-1)
            new_node = Node(self.index, node, node.state.clone(),
                            self.space_id,
                            ["planner"])
            steps = 0

            # Step until precision is reached, too long idle, or OOB
            state = lp.dijkstra_stagger(node.state, None, lambda g0, h, _move0, _move, log: log.t + h,
                                        lambda w, _ignored: lp.aut_distance(
                                            w, {"0": [[goal]]}, "0", 0, 0),
                                        self.dt, 5, self.append_path)

            if isinstance(state, itp.World):
                new_node.state = state.clone()
            # if self.space.check_bounds(new_node):
                self.get_available(new_node)
                node.children.append(new_node)
                self.queue.append(new_node)
                queue.put(node.state)
                queue.put(new_node.state)
                #self.append_path(node.state, new_node.state)
                #del node.available[choice]
            # Else clear node
            else:
                pass
                #del node.available[choice]
        else:
            pass
            # print "Node has no moves"
        self.goal['x'] = -1
        self.goal['y'] = -1


class RRT(object):
    __slots__ = ["index", "space", "dt", "size",
                 "root", "precision",
                 "modes", "world", "nearest", "select", "expand", "resolve",
                 "space_id", "nodes", "queue"]

    def __init__(self, config, num, dt, world, space_id):
        conf_num = 'RRT%s' % num
        type_dispatcher = {'rrt': (self.nearest_rrt, self.select_rrt, self.expand_rrt, self.resolve_rrt),
                           'rct': (self.nearest_rct, self.select_rrt, self.expand_rrt, self.resolve_rct)}
        self.index = [int(i) for i in config.get(conf_num, 'index').split(' ')]
        self.space_id = space_id
        self.world = world.clone()
        self.world.spaces = {space_id: self.world.spaces[space_id]}
        self.space = Space(str(self.index[0]), world)
        self.dt = dt
        self.nearest, self.select, self.expand, self.resolve = type_dispatcher[config.get(conf_num, 'type').lower()]
        # self.nearest = self.nearest_rrt
        # self.select = self.select_rrt
        # self.expand = self.expand_rrt
        # self.resolve = self.resolve_rrt
        self.size = 1
        self.modes = {}
        self.queue = []
        self.root = Node(self.index, None, self.world.clone(),
                         space_id, ["init"])
        self.get_available(self.root)
        # self.nodes.append(self.root)
        self.queue.append(self.root)
        self.precision = int(config.get(conf_num, 'precision'))

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
                        if isinstance(e.guard.conjuncts[0], schema.GuardButton):
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
        return curr

    def nearest_rct(self, s2):
        curr = None
        dist = None
        for node in self.queue:
            if len(node.available) > 0:
                r = random.random()
                if r > node.cvf:
                    new_dist = self.space.get_dist(node.state, s2)
                    if not dist or new_dist < dist:
                        curr = node
                        dist = new_dist
            else:
                self.queue.remove(node)
        return curr

    def select_rrt(self, node):
        choice = random.randint(0, len(node.available) - 1)
        action = node.available[choice]
        del node.available[choice]
        return Node(self.index, node, node.state.clone(), self.space_id, action)

    def expand_rrt(self, node):
        steps = 0
        # Step until precision is reached, too long idle, or OOB
        while self.space.check_bounds(node.state) and steps < self.precision:
            itp.step(node.state, node.action, 1.0 / 60.0)
            steps += 1
        return steps

    @staticmethod
    def resolve_rrt(new_node):
        del new_node

    @staticmethod
    def resolve_rct(new_node):
        curr = new_node.parent
        del new_node
        m = curr.m
        k = 1
        while curr:
            curr.cvf += 1.0/(m**k)
            k += 1
            curr = curr.parent
        return

    def grow(self, queue):
        while True:
            # Get random goal state and best state
            target = self.space.get_sample()

            # Select best state by some algorithm
            node = self.nearest(target)

            # Create a new node from random available choices of found node
            if node:
                # Select input to expand by some algorithm
                new_node = self.select(node)

                # Expand input by some algorithm
                steps = self.expand(new_node)

                # Resolve changes by some algorithm
                if steps >= self.precision:
                    # Increase tree size and insert into tree
                    self.size += 1
                    self.get_available(new_node)
                    node.children.append(new_node)

                    # Add to tree and append to queue for visualization
                    self.queue.append(new_node)
                    queue.put(node.state)
                    queue.put(new_node.state)
                else:
                    self.resolve(new_node)
            else:
                pass
                # print "Tree dead"
                # exit(0)

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
                 "parent", "children", "m", "cvf"]

    def __init__(self, index, parent, state, space_id, action):
        self.state = state
        self.val = self.state.spaces[space_id].valuations[index[0]][index[1]]
        self.action = action[:]
        self.available = []
        self.parent = parent
        self.children = []
        self.m = -1
        self.cvf = 0

    def get_origin(self):
        return [self.val.get_var('x'), self.val.get_var('y'), 0.6]


class Space(object):
    __slots__ = ["index", "vars", "bounds"]

    def __init__(self, index, world):
        self.index = index
        self.bounds = []
        valuations = world.spaces[index].valuations
        for i in range(0, len(valuations)):
            aut = world.automata[i]
            mode_combinations = schema.mode_combinations(
                aut
            )
            aut_bounds = []
            self.bounds.append(aut_bounds)
            for val in valuations[i]:
                vbounds = {}
                aut_bounds.append(vbounds)
                for groups in mode_combinations:
                    mode_mask = 0
                    for group in groups:
                        for mode in group[1]:
                            ordered_mode = aut.ordered_modes[
                                aut.ordering[mode.qualified_name]
                            ]
                            mode_mask |= 1 << ordered_mode.index
                    mode_bounds = {
                        "variables": {},
                        "dvariables": {},
                        "timers": {}
                    }
                    for val in valuations[i]:
                        for var in aut.variables.values():
                            # if the variable is positional, use information about world, colliders, etc too
                            # if the mode has a flow on this variable, use the flow
                            # if the mode has an envelope on this variable, use the envelope bounds
                            # if the mode has an update leading into it that sets this variable...
                            # FIXME
                            if var.degree == 0:
                                mode_bounds["variables"][var.name] = (0, 640)
                            else:
                                mode_bounds["variables"][var.name] = (
                                    -1000, 1000)
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
                            # if the mode has an udpate leading into it that changes this dvar, use that update (if it's constant or whatever)
                            # FIXME
                            mode_bounds["dvariables"][dvar.name] = (-128, 128)
                        for t, _ in enumerate(val.timers):
                            # FIXME
                            # use the max interesting value of this timer to
                            # bound?
                            # This should give (0,0) for timers associated with
                            # inactive modes in this combined-mode
                            mode_bounds["timers"][t] = (0, 10.0)
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
                    vals["variables"][vk] = random.uniform(vv[0], vv[1])
                for vk, vv in mbounds["dvariables"].items():
                    vals["dvariables"][vk] = random.uniform(vv[0], vv[1])
                for vk, vv in mbounds["timers"].items():
                    vals["timers"][vk] = random.uniform(vv[0], vv[1])
        return result

    def get_dist(self, s1, s2):
        sqrsum = 0
        # Distance over all things
        # but we could try task distance of just player x,y.
        for i in range(0, len(s1.spaces[self.index].valuations)):
            for a in range(0, len(s1.spaces[self.index].valuations[i])):
                if s1.spaces[self.index[0]].valuations[i][a].active_modes != s2[i][a]["active_modes"]:
                    sqrsum += 1
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
                active_modes = s1.spaces[self.index].valuations[i][a].active_modes
                for v in self.bounds[i][a][active_modes]["variables"]:
                    vl, vh = self.bounds[i][a][active_modes]["variables"][v]
                    val = s1.spaces[self.index].valuations[i][a].get_var(v)
                    if not vl <= val <= vh:
                        #
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


def main():
    pass


if __name__ == "__main__":
    main()
