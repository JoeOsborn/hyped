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
        self.world = world.clone()
        self.world.spaces = {space_id: self.world.spaces[space_id]}
        self.space_id = space_id
        self.root = Node(self.index, self.world.clone(), space_id,
                         self.space.vars, ["init"],
                         dispatcher[config.get('RRT', 'dist').lower()])
        self.get_available(self.root)
        self.precision = int(config.get('RRT', 'precision'))
        self.constraint = int(config.get('RRT', 'constraint'))
        self.nodes = SpatialHash(32)
        self.nodes.insert(self.root)
        self.paths = []
        self.queue = None
        self.goal = {'x': -1, 'y': -1, 'z': 0.6}

    def get_nearest(self, goal):
        if self.goal['x'] >= 0 and self.goal['y'] >= 0:
            target = (self.goal['x'], self.goal['y'])
        else:
            target = (goal['x'], goal['y'])
        bucket = self.nodes.query((target[0], target[1]))
        if not bucket:
            bucket = self.nodes.queryNearest((target[0], target[1]))
        for node in bucket:
            if len(node.available) > 0:
                return node
        return None

    def get_nearest_bk(self, goal):
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
            #print self.modes[str(active)]
            node.available = available[:]

    def grow(self):
        for i in range(0, self.constraint):
            # Get random goal state and nearest node
            goal = self.space.get_random()
            node = self.get_nearest(goal)

            # Create a new node from random available choices of found node
            if node:
                choice = random.randint(0, len(node.available)-1)
                new_node = Node(self.index, node.state.clone(),
                                self.space_id, self.space.vars,
                                node.available[choice],
                                node.dist_func)
                lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")
                idle = 0
                steps = 0

                # Step until precision is reached, too long idle, or OOB
                while self.space.check_bounds(new_node) and steps < self.precision and idle < 5:
                    interpreter.step(new_node.state, new_node.action, 1.0/60.0)
                    new_node.set_vars()
                    steps += 1
                    if new_node.val.get_var("x") == lastx and new_node.val.get_var("y") == lasty or \
                       new_node.val.get_var("x'") == 0 and new_node.val.get_var("y'") == 0:
                        idle += 1
                    lastx, lasty = new_node.val.get_var("x"), new_node.val.get_var("y")

                # If still valid state, append node to tree
                if self.space.check_bounds(new_node) and idle < 5:
                    node.children.append(new_node)
                    new_node.set_origin()
                    self.get_available(new_node)
                    self.nodes.insert(new_node)
                    self.paths.append([node.origin, new_node.origin])
                    del node.available[choice]
                # Else clear node
                else:
                    del new_node
                    del node.available[choice]
            else:
                pass
                #print "Node has no moves"

    def grow_test(self):
        # Get random goal and nearest node
        goal = self.space.get_random()
        node = self.get_nearest(goal)

        # Make random choice
        if node:
            #print "Action: " + str(node.action)
            #print "Available: " + str(node.available)
            choice = random.randint(0, len(node.available) - 1)
            idle = 0
            steps = 0
            new_node = Node(self.index, node.state.clone(), self.space_id,
                            self.space.vars, node.available[choice],
                            node.dist_func)
            #print new_node.action

            # Record initial mode and velocities
            mode = new_node.val.active_modes
            contacts = set(c.b_types for c in new_node.state.spaces.values()[0].contacts)


            # Loop while in bounds with idle check
            while self.space.check_bounds(new_node) and idle < 20:
                #print steps
                interpreter.step(new_node.state, new_node.action, 1.0 / 60.0)
                new_node.set_vars()
                new_node.set_origin()
                steps += 1

                new_contacts = set(c.b_types for c in new_node.state.spaces.values()[0].contacts)
                if len(contacts) != len(new_contacts) or contacts != new_contacts:
                    #print new_node.action
                    new_node.action.append("Contact Change")
                    #print new_node.action
                    idle = 21

                if new_node.val.get_var("x'") == 0 and new_node.val.get_var("y'") == 0:
                    idle += 1
                    #print "Idle = " + str(idle)

            # If valid, append
            if self.space.check_bounds(new_node):
                new_node.action.append("Steps: " + str(steps))
                new_node.parent = node
                self.get_available(new_node)
                self.nodes.insert(new_node)
                self.paths.append([node.origin, new_node.origin])
                node.children.append(new_node)
                del node.available[choice]
                #self.fork_test(node, "wait", new_node.action, steps)
            else:
                del node.available[choice]

    def fork_test(self, node, a, b, count):
        newA = Node(self.index, node.state.clone(), self.space_id,
                    self.space.vars, a,
                    node.dist_func)
        steps = 0
        # Record initial mode and velocities
        while self.space.check_bounds(newA) and steps < count/2:
            interpreter.step(newA.state, newA.action, 1.0 / 60.0)
            newA.set_vars()
            newA.set_origin()
            steps += 1
        newB = Node(self.index, node.state.clone(), self.space_id,
                    self.space.vars, b,
                    node.dist_func)
        steps = 0
        while self.space.check_bounds(newB) and steps < count/2:
            interpreter.step(newB.state, newB.action, 1.0 / 60.0)
            newB.set_vars()
            newB.set_origin()
            steps += 1

        # Append Nodes
        newA.parent = node
        self.get_available(newA)
        self.nodes.insert(newA)
        self.paths.append([node.origin, newA.origin])
        node.children.append(newA)
        newB.parent = newA
        self.get_available(newB)
        self.nodes.insert(newB)
        self.paths.append([newA.origin, newB.origin])
        newA.children.append(newB)

    def get_path(self, node):
        curr = node
        result = ""
        while not curr.action[0] == "init":
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

    def insert(self, node):
        self.contents.setdefault(self._hash(node.origin), []).append(node)

    def query(self, point):
        return self.contents.get(self._hash(point))

    def queryNearest(self, point):
        dist = 0
        bucket = None
        for b in self.contents:
            center = (b[0]*self.cell_size+0.5*self.cell_size, b[1]*self.cell_size+0.5*self.cell_size)
            sqrsum = (point[0] - b[0]) ** 2
            sqrsum += (point[1] - b[1]) ** 2
            if not bucket or sqrsum < dist:
                dist = sqrsum
                bucket = b
        return self.contents[bucket]

    def printTable(self):
        print self.contents
        for b in self.contents:
            print b


class Node(object):
    __slots__ = ["state", "space_id", "val", "vars", "origin", "action",
                 "available", "parent", "children", "dist_func"]

    def __init__(self, index, state, space_id, vars, action, func):
        self.state = state
        self.val = self.state.spaces[space_id].valuations[index[0]][index[1]]
        self.vars = {}
        for v in vars:
            self.vars[v] = 0
        self.set_vars()
        self.origin = [0, 0]
        self.set_origin()
        self.action = action[:]
        self.available = []
        self.parent = None
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