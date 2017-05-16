import heapq

import schema as schema
import interpreter as interpreter
import local_planner as lp
import random


def linear_distance(space, s1, s2):
    for var in space.vars:
        return (s1.spaces[space.index[0]].valuations[space.index[1]][space.index[2]].get_var(var) - s2[var]) ** 2


def quad_distance(space, s1, s2):
    sqrsum = 0
    for var in space.vars:
        sqrsum += (s1.spaces[space.index[0]].valuations[space.index[1]][space.index[2]].get_var(var) - s2[var]) ** 2
    return sqrsum


dist_dispatcher = {'linear': linear_distance,
                   'quadratic': quad_distance}


def get_nearest_traversal(self, goal):
    if self.goal['x'] >= 0 and self.goal['y'] >= 0:
        target = {'x': self.goal['x'],
                  'y': self.goal['y']}
    else:
        target = self.space.get_sample()
    curr = None
    dist = None
    for node in self.queue:
        if len(node.available) > 0:
            new_dist = self.space.get_dist(node.state, target)
            if not dist or (new_dist < dist and len(node.available) > 0):
                curr = node
    return curr, target


def get_nearest_hash(self, goal):
    if self.goal['x'] >= 0 and self.goal['y'] >= 0:
        target = (self.goal['x'], self.goal['y'])
    else:
        goal = self.space.get_sample()
    queue = self.nodes.query((goal['x'], goal['y']))
    if not queue:
        queue = self.nodes.queryNearest((goal['x'], goal['y']))
    #print queue
    for bucket in queue:
        for node in bucket[1]:
            if len(node.available) > 0:
                #print node, target
                return node
    return None


def dijkstra(self):
    for i in range(0, self.constraint):
        # Get random goal state and nearest node
        if self.goal['x'] >= 0 and self.goal['y'] >= 0:
            goal = self.goal
        else:
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
                                        lambda w, _ignored: lp.aut_distance(w, {"0": [[goal]]}, "0", 0, 0),
                                        self.dt, 5, self.append_path)

            if isinstance(state, interpreter.World):
                new_node.state = state.clone()
            #if self.space.check_bounds(new_node):
                self.get_available(new_node)
                node.children.append(new_node)
                self.queue.append(new_node)
                self.append_path(node.state, new_node.state)
                #del node.available[choice]
            # Else clear node
            else:
                pass
                #del node.available[choice]
        else:
            pass
            #print "Node has no moves"
        self.goal['x'] = -1
        self.goal['y'] = -1


def grow(self):
    for i in range(0, self.constraint):
        # Get random goal state and nearest node
        if self.goal['x'] >= 0 and self.goal['y'] >= 0:
            target = self.goal
        else:
            target = self.space.get_sample()
        node = self.get_nearest(target)

        # Create a new node from random available choices of found node
        if node:
            choice = random.randint(0, len(node.available)-1)
            new_node = Node(self.index, node, node.state.clone(),
                            self.space_id,
                            node.available[choice])
            steps = 0

            # Step until precision is reached, too long idle, or OOB
            while self.space.check_bounds(new_node) and steps < self.precision:
                interpreter.step(new_node.state, new_node.action, 1.0/60.0)
                steps += 1

            # If still valid state, append node to tree
            if self.space.check_bounds(new_node):
                self.get_available(new_node)
                node.children.append(new_node)
                self.nodes.append(new_node)
                self.queue.append(new_node)
                self.append_path(node.state, new_node.state)
                del node.available[choice]
            # Else clear node
            else:
                del new_node
                del node.available[choice]
        else:
            pass
            print "Tree dead"


def make_grow(self, choose, grow, add):
    def grow_function(self):
        # Choose node
        node, goal = choose(self)
        if node:
            # Grow node
            new_node = grow(self, node, goal)
            # Add node
            add(self, node.state, new_node.state)
        else:
            pass
    return grow_function


grow_dispatcher = {'rrt': (grow, get_nearest_hash),
                   'dijkstra': (dijkstra, get_nearest_traversal)}


class RRT(object):
    __slots__ = ["index", "space", "dt", "size", "root", "precision", "constraint",
                 "modes", "_grow_func", "_near_func", "append_path", "goal", "world",
                 "space_id", "nodes", "queue"]

    def __init__(self, config, dt, world, space_id):
        self.index = [int(i) for i in config.get('RRT', 'index').split(' ')]
        vars = config.get('RRT', 'vars').split(' ')
        rng = config.get('RRT', 'bounds').split(' ')
        bounds = {}
        for v in range(0, len(rng), 3):
            bounds[rng[v]] = (int(rng[v+1]), int(rng[v+2]))
        del rng
        self.space = Space(('0', 0, 0), vars, bounds, quad_distance)
        self.dt = dt
        self.modes = {}
        self.size = 1
        self.world = world.clone()
        self.world.spaces = {space_id: self.world.spaces[space_id]}
        self.space_id = space_id
        self.append_path = lambda parent, child: None
        self._grow_func, self._near_func = grow_dispatcher[config.get('RRT', 'type').lower()]
        self.nodes = SpatialHash(32)
        self.queue = []
        self.goal = {'x': -1, 'y': -1, 'z': 0.6}
        self.root = Node(self.index, None, self.world.clone(), space_id, ["init"])
        self.get_available(self.root)
        self.nodes.append(self.root)
        self.queue.append(self.root)
        self.precision = int(config.get('RRT', 'precision'))
        self.constraint = int(config.get('RRT', 'constraint'))

    def get_available(self, node):
        active = node.val.active_modes
        if str(active) in self.modes:
            node.available = self.modes[str(active)][:]
        else:
            available = []
            mi = 0
            modes = node.state.automata[self.index[0]].ordered_modes
            mode_count = len(modes)
            active = node.val.active_modes
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

    def grow(self):
        self._grow_func(self)

    def get_nearest(self, goal):
        return self._near_func(self, goal)

    def add_children(self, node):
        for action in node.available:
            new_node = Node(self.index, node.state.clone(), self.space_id,
                            action)
            new_node.parent = node
            node.children.append(new_node)
            heapq.heappush(self.queue, new_node)
        node.available = []

    @staticmethod
    def get_path(node):
        curr = node
        result = ""
        while curr.parent:
            result = str(curr.action) + ";\n" + result
            curr = curr.parent
        result = str(curr.action) + ";\n" + result
        print result


class SpatialHash(object):
    __slots__ = ["cell_size", "contents"]

    def __init__(self, cell_size):
        self.cell_size = cell_size
        self.contents = {}

    def _hash(self, point):
        return int(point[0]/self.cell_size), int(point[1]/self.cell_size)

    def append(self, node):
        self.contents.setdefault(self._hash(node.get_origin()), []).append(node)

    def query(self, point):
        bucket = self.contents.get(self._hash(point))
        if bucket:
            return [(0, bucket)]
        else:
            return None

    def queryNearest(self, point):
        dist = 0
        bucket = None
        queue = []
        for b in self.contents:
            center = (b[0]*self.cell_size+0.5*self.cell_size, b[1]*self.cell_size+0.5*self.cell_size)
            sqrsum = (point[0] - b[0]) ** 2
            sqrsum += (point[1] - b[1]) ** 2
            heapq.heappush(queue, (sqrsum, self.contents[b]))
            # if not bucket or sqrsum < dist:
            #     dist = sqrsum
            #     bucket = b
        return queue

    def print_table(self):
        print self.contents
        for b in self.contents:
            print b


class Node(object):
    __slots__ = ["state", "space_id", "val", "action", "available",
                 "parent", "children", "dist"]

    def __init__(self, index, parent, state, space_id, action):
        self.state = state
        self.val = self.state.spaces[space_id].valuations[index[0]][index[1]]
        self.action = action[:]
        self.available = []
        self.parent = parent
        self.children = []
        self.dist = -1

    def __cmp__(self, node):
        assert isinstance(node, Node)
        return cmp(self.dist, node.dist)

    def get_origin(self):
        return [self.val.get_var('x'), self.val.get_var('y'), 0.6]


class Space(object):
    __slots__ = ["index", "vars", "bounds", "_dist_func"]

    def __init__(self, index, vars, bounds, dist_func):
        self.index = index
        self.vars = vars
        self.bounds = bounds
        self._dist_func = dist_func

    def get_sample(self):
        result = {}
        for v in self.vars:
            result[v] = random.randrange(self.bounds[v][0], self.bounds[v][1])
        return result

    def get_dist(self, state, goal):
        return self._dist_func(self, state, goal)

    def check_bounds(self, node):
        for v in self.bounds.keys():
            if not self.bounds[v][0] <= node.val.get_var(v) <= self.bounds[v][1]:
                return False
        return True

    def set_vars(self, node):
        for v in self.vars:
            node.vars[v] = node.val.get_var(v)


def main():
    pass

if __name__ == "__main__":
    main()
