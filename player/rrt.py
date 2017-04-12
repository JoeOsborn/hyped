import hyped.schema as schema
import hyped.interpreter as interpreter
import copy
import random
import Queue


def linear_distance(s1, s2):
    for k in s1.vars.keys():
        return abs(s1.vars[k] - s2[k])


def quad_distance(s1, s2):
    sqrsum = 0
    for k in s1.vars.keys():
        sqrsum += (s1.vars[k] - s2[k]) ** 2
    return sqrsum


dispatcher = {'linear': linear_distance,
              'quadratic': quad_distance}


class RRT(object):
    __slots__ = ["index", "size", "root", "space", "precision", "constraint",
                 "nodes", "paths", "modes", "queue", "goal", "world",
                 "space_id"]

    def __init__(self, config, world, space_id):
        self.index = [int(i) for i in config.get('RRT', 'index').split(' ')]
        vars = config.get('RRT', 'vars').split(' ')
        rng = config.get('RRT', 'bounds').split(' ')
        bounds = {}
        for v in range(0, len(vars)):
            bounds[vars[v]] = (int(rng[v*2]), int(rng[v*2+1]))
        del rng
        self.space = Space(vars, bounds)
        self.modes = {}
        self.size = 1
        self.world = copy.deepcopy(world)
        self.world.spaces = {space_id: self.world.spaces[space_id]}
        self.space_id = space_id
        self.root = Node(self.index, copy.deepcopy(self.world), space_id,
                         self.space.vars, ["init"],
                         dispatcher[config.get('RRT', 'dist').lower()])
        self.get_available(self.root)
        #print self.root.available
        self.precision = int(config.get('RRT', 'precision'))
        self.constraint = int(config.get('RRT', 'constraint'))
        self.nodes = {str([int(self.root.origin[0]), int(self.root.origin[1])]): self.root}
        self.paths = []
        self.queue = []
        self.goal = {'x': -1, 'y': -1, 'z': 0.6}

    def get_nearest(self, goal):
        curr = self.root
        if self.goal['x'] >= 0 and self.goal['y'] >= 0:
            target = self.goal
        else:
            target = goal
        while len(curr.children) > 0:
            index = -1
            dist = curr.get_dist(target)
            available = len(curr.available)
            for c in range(0, len(curr.children)):
                new_dist = curr.children[c].get_dist(target)
                new_available = len(curr.children[c].available)
                new_children = len(curr.children[c].children)
                if available < 1 or new_dist < dist:
                    if new_children > 0 or new_available > 0:
                        index = c
                        dist = new_dist
                        available = new_available
            if index < 0:
                break
            elif index >= 0:
                curr = curr.children[index]
            else:
                pass
                # print "Error"
        if len(curr.available) > 0:
            return curr
        else:
            return None

    def get_available(self, node):
        active = node.val.active_modes
        if str(active) in self.modes:
            # print self.modes[str(active)]
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
                            #print button
                            if not hor_move and not vert_move:
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
            # print self.modes[str(active)]
            node.available = available[:]

    def grow(self):
        for i in range(0, self.constraint):
            goal = self.space.get_random()
            node = self.get_nearest(goal)
            if node:
                choice = random.randint(0, len(node.available)-1)
                new_node = Node(self.index, copy.deepcopy(node.state),
                                self.space_id, self.space.vars,
                                node.available[choice],
                                node.dist_func)
                lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")
                idle = 0
                steps = 0
                while self.space.check_bounds(new_node) and steps < self.precision and idle < 5:
                    interpreter.step(new_node.state, new_node.action, 1.0/60.0)
                    new_node.set_vars()
                    steps += 1
                    if new_node.val.get_var("x") == lastx and new_node.val.get_var("y") == lasty or \
                       new_node.val.get_var("x'") == 0 and new_node.val.get_var("y'") == 0:
                        idle += 1
                        #print "Testing idle... " + str(idle)
                    lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")
                if self.space.check_bounds(new_node) and idle < 5:
                    #print new_node.action
                    node.children.append(new_node)
                    new_node.set_origin()
                    self.get_available(new_node)
                    self.nodes[str([int(new_node.origin[0]), int(new_node.origin[1])])] = new_node
                    self.paths.append([node.origin, new_node.origin])
                    del node.available[choice]
                else:
                    del new_node
                    del node.available[choice]
            else:
                pass
                #print "Node has no moves"

    def grow_test(self, node, action, count=9999):
        idle = 0
        steps = 0
        #print "Testing " + str(a)
        new_node = Node(self.index, copy.deepcopy(node.state), self.space_id,
                        self.space.vars, node.available[action],
                        node.dist_func)
        mode = new_node.val.active_modes
        lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")
        while self.space.check_bounds(new_node) and new_node.val.active_modes == mode and idle < 5 and steps < count:
            interpreter.step(new_node.state, new_node.action, 1.0/60.0)
            new_node.set_vars()
            if steps < 1 and new_node.val.active_modes != mode:
                mode = new_node.val.active_modes
            steps += 1
            if (new_node.val.get_var("x'") == 0 and new_node.val.get_var("y'") == 0) or \
               (new_node.val.get_var("x") == lastx and new_node.val.get_var("y") == lasty):
                idle += 1
                print "Idle = " + str(idle)
            lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")
        if self.space.check_bounds(new_node) and idle < 5:
            new_node.set_origin()
            self.get_available(new_node)
            self.nodes[str([int(new_node.origin[0]), int(new_node.origin[1])])] = new_node
            self.paths.append([node.origin, new_node.origin])
            node.children.append(new_node)
            return new_node, new_node.val.active_modes, steps
        else:
            del new_node
            del node.available[action]
            print "OOB or Idle"
            return None, None, None

    def branch_test(self):
        for i in range(0, self.constraint):
            #node = self.bfs()
            goal = self.space.get_random()
            node = self.get_nearest(goal)
            branches = []
            modes = []
            count = []
            print "Root: " + str(node.action)
            if node:
                action = random.randint(0, len(node.available)-1)
                new_node, mode, steps = self.grow_test(node, action)
                if new_node:
                    branches.append(new_node)
                    modes.append(mode)
                    count.append(steps)
            # for a in node.available:
            #     print a
            #     new_node, mode, steps = self.grow_test(node, a)
            #     if new_node:
            #         branches.append(new_node)
            #         modes.append(mode)
            #         count.append(steps)
            #node.available = []
            #print set(modes)
            # if len(set(modes)) > 1:
            #     for b in range(0, len(branches)):
            #         if modes[b] != modes[b+1]:
            #             c_node, mode, steps = self.grow_test(node, branches[b].action, count[b]/2)
            #             node.children.append(c_node)
            #             c_node.children.append(branches[b])
            #             d_node, mode, steps = self.grow_test(c_node, branches[b+1].action, count[b+1]/2)
            #             c_node.children.append(d_node)


    def bfs(self):
        queue = Queue.Queue()
        queue.put(self.root)
        while not queue.empty():
            curr = queue.get()
            #print curr.action
            #print curr.children
            #print curr.available
            if len(curr.children) <= 0 < len(curr.available):
                return curr
            else:
                for c in curr.children:
                    queue.put(c)
        return None


class Node(object):
    __slots__ = ["state", "space_id", "val", "vars", "origin", "action",
                 "available", "children", "dist_func"]

    def __init__(self, index, state, space_id, vars, action, func):
        self.state = state
        self.val = self.state.spaces[space_id].valuations[index[0]][index[1]]
        self.vars = {}
        for v in vars:
            self.vars[v] = 0
        self.set_vars()
        self.origin = [0, 0]
        self.set_origin()
        self.action = action
        self.available = []
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


def main():
    i = (0, 0)
    w = interpreter.load_test()
    s = Space(['x', 'y'], {'x': (0, 500), 'y': (0, 500)})
    t = RRT(i, w, s, quad_distance, constraint=100)
    t.grow()

if __name__ == "__main__":
    main()


