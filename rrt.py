import schema
import interpreter
import copy
import random
import Queue
import matplotlib.pyplot as plt
from math import sqrt


def linear_distance(s1, s2):
    v = []
    for k in s2.keys():
        v.append(s1.vars[k])
        v.append(s2[k])
    return abs(v[0] - v[1])


def quad_distance(s1, s2):
    v = []
    for k in s2.keys():
        v.append(s1.vars[k])
        v.append(s2[k])
    return sqrt((v[0] - v[1])**2 + (v[2] - v[3])**2)


class RRT(object):
    __slots__ = ["index", "root", "space", "precision", "constraint", "paths", "goal"]

    def __init__(self, index, start, space, func, precision=5, constraint=5):
        self.index = index
        self.space = space
        self.root = Node(self.index, copy.deepcopy(start), self.space.vars, ["init"], func)
        self.precision = precision
        self.constraint = constraint
        self.paths = []
        self.goal = None

    def get_nearest(self, goal):
        curr = self.root
        if self.goal:
            target = self.goal
        else:
            target = goal
        while len(curr.children) > 0:
            index = None
            dist = curr.children[0].get_dist(target)
            for c in range(1, len(curr.children)):
                new_dist = curr.children[c].get_dist(target)
                if new_dist < dist and len(curr.children[c].available) > 0:
                    index = c
                    dist = new_dist
            if index:
                curr = curr.children[index]
            else:
                return curr
        return curr

    def grow(self):
        for i in range(0, self.constraint):
            goal = self.space.get_random()
            node = self.get_nearest(goal)
            new_node = Node(self.index, copy.deepcopy(node.state), self.space.vars, None, node.dist_func)
            node.children.append(new_node)
            if len(node.available) > 0:
                choice = random.randint(0, len(node.available)-1)
                new_node.action = node.available[choice]
                for p in range(0, self.precision):
                    interpreter.step(new_node.state, new_node.action, 1.0/60.0)
                new_node.set_vars()
                if self.space.check_bounds(new_node) and node.get_dist(new_node.vars) > 0:
                    print new_node.action
                    new_node.get_available()
                    new_node.set_origin()
                    self.paths.append([node.origin, new_node.origin])
                    del node.available[choice]
                else:
                    del new_node
                    del node.available[choice]

    def bfs(self):
        queue = Queue.Queue()
        queue.put(self.root)
        paths = []
        i = 0
        while not queue.empty():
            curr = queue.get()
            paths.append([])
            paths[i].append(curr.origin)
            paths[i].append([])
            for c in curr.children:
                paths[i][1].append(c.origin)
                queue.put(c)
            i += 1
        return paths


class Node(object):
    __slots__ = ["index", "state", "val", "vars", "origin", "action", "available", "children", "dist_func"]

    def __init__(self, index, state, vars, action, func):
        self.index = index
        self.state = state
        self.val = self.state.valuations[self.index[0]][self.index[1]]
        self.vars = {}
        for v in vars:
            self.vars[v] = 0
        self.set_vars()
        self.origin = [0, 0]
        self.set_origin()
        self.action = action
        self.available = []
        self.get_available()
        self.children = []
        self.dist_func = func

    def set_vars(self):
        for v in self.vars:
            try:
                self.vars[v] = self.val.get_var(v)
            except ValueError:
                return

    def set_origin(self):
        self.origin = [self.val.get_var('x'), self.val.get_var('y'), 0.6]

    def get_available(self):
        self.available = [["wait"]]
        mi = 0
        modes = self.state.automata[self.val.automaton_index].ordered_modes
        mode_count = len(modes)
        active = self.val.active_modes
        while mi < mode_count:
            if active & (1 << mi):
                hor_move = False
                vert_move = False
                mode = modes[mi]
                for e in mode.envelopes:
                    if e.axes[0][1] == 'x':
                        hor_move = True
                        self.available.append(["left"])
                        self.available.append(["right"])
                    elif e.axes[0][1] == 'y':
                        vert_move = True
                        self.available.append(["up"])
                        self.available.append(["down"])
                for e in mode.edges:
                    if isinstance(e.guard.conjuncts[0], schema.GuardButton):
                        button = e.guard.conjuncts[0].buttonID
                        self.available.append([button])
                        if hor_move:
                            self.available.append([button, "left"])
                            self.available.append([button, "right"])
                        if vert_move:
                            self.available.append([button, "up"])
                            self.available.append([button, "down"])
                        break
            mi += 1

    def get_dist(self, goal):
        return self.dist_func(self, goal)


class Space(object):
    __slots__ = ["vars", "bounds"]

    def __init__(self, vars, bounds):
        self.vars = vars
        self.bounds = bounds

    def get_random(self):
        result = {}
        for v in self.vars:
            result[v] = random.randrange(self.bounds[v][0], self.bounds[v][1])
        return result

    def check_bounds(self, node):
        for v in self.vars:
            if node.vars[v] < self.bounds[v][0] or node.vars[v] > self.bounds[v][1]:
                return False
        return True

if __name__ == "__main__":
    i = (0, 0)
    w = interpreter.load_test()
    s = Space(['x', 'y'], {'x': (0, 500), 'y': (0, 500)})
    t = RRT(i, w, s, quad_distance, constraint=100)
    t.grow()


