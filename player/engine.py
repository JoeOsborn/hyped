from ConfigParser import ConfigParser
from OpenGL.GLUT import *
import multiprocessing as mp

try:
    import hyped.interpreter as itp
except ImportError:
    sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    import hyped.interpreter as itp
import hyped.rrt as rrt

import data
import graphics
import input
import random


class Engine(object):
    __slots__ = ["id", "dt", "pause", "data", "queue", "procs",
                 "graphics", "input", "rrt", "time"]

    def __init__(self, queue, procs, ini="settings.ini"):
        config = ConfigParser()
        config.read(ini)
        self.id = 0
        n, d = config.get('Engine', 'dt').split()
        self.dt = float(n) / float(d)
        self.pause = False
        self.data = data.Data(config)
        self.input = input.Input(config)
        # if config.get('Engine', 'rrt').lower() == "true":
        #     self.rrt = rrt.RRT(config, self.dt,
        #                        self.data.world,
        #                        # TODO: a particular space, not some arbitrary one?
        #                        self.data.world.spaces.keys()[0])
        # else: self.rrt = None
        self.graphics = graphics.Graphics(config)
        self.time = 0
        self.procs = procs
        self.queue = queue
        for proc in procs:
            pathcolor = (random.randint(20, 100)/100.0, random.randint(20, 100)/100.0, random.randint(20, 100)/100.0, 0.3)
            nodecolor = (random.randint(20, 100)/100.0, random.randint(20, 100)/100.0, random.randint(20, 100)/100.0, 0.5)
            self.graphics.trees.append(graphics.PathTree(pathcolor, nodecolor))

    def engine_keys(self):
        # p: pause game
        if self.input.keys[112]:
            self.pause = not self.pause
            # If game is un-paused, allow history overwrite
            if not self.pause:
                self.data.clip_history(self.data.frame)
            self.input.keys[112] = False
        if self.input.keys[113]:
            for proc in self.procs:
                proc.terminate()
            for q in range(0, len(self.queue)):
                self.queue[q].close()
                self.queue[q] = mp.Queue()
        # ESC: exit
        if self.input.keys[27]:
            exit(0)
        # PAUSED + Arrow Left: Scrub through playback, if + CTRL then fast scrub
        if self.input.skeys[100]:
            if self.pause:
                self.data.frame -= 1
            if self.input.skeys[114]:
                self.data.frame -= 5
            if self.data.frame < 0:
                self.data.frame = 0
        # PAUSED + Arrow Right: Scrub through playback, if + CTRL then fast scrub
        if self.input.skeys[102]:
            if self.pause:
                self.data.frame += 1
                if self.input.skeys[114]:
                    self.data.frame += 5
        # CTRL + S: Save Game
        if self.input.keys[19]:
            self.pause = True
            self.data.save_state()
            self.input.clear_all()
        # CTRL + L: Load Game
        if self.input.keys[12]:
            self.pause = True
            self.data.load_state()
            self.input.clear_all()
            self.graphics.draw_scene(self.data.frame_history[self.data.frame])
        # CTRL + R: Reset Playback
        if self.input.keys[18]:
            self.data.frame = 0
            self.data.clip_history(0)
            self.input.keys[18] = False
        # Left Click: Close Menu
        if self.input.mouse[0]:
            # if self.rrt:
            #     node = self.graphics.pathtree.check(self.input.x, self.graphics.height - self.input.y)
            #     #print self.input.x, self.graphics.height - self.input.y
            #     print node
            #     if node:
            #         self.rrt.get_path(node)
            #     self.rrt.goal['x'] = -1
            #     self.rrt.goal['y'] = -1
            # x, y = self.input.x, self.graphics.height - self.input.y
            # if not self.graphics.menu.check(x, y):
            #     self.graphics.menu.active = False
            # else:
            #     pass
            self.input.mouse[0] = False

        # Right Click: Open Menu
        if self.input.mouse[2]:
            # self.rrt.goal['x'] = self.input.x
            # self.rrt.goal['y'] = self.graphics.height - self.input.y
            # print self.input.x, self.graphics.height - self.input.y
            # self.graphics.menu.active = True
            # if self.graphics.menu.active:
            #     self.graphics.menu.origin = [self.input.x, self.graphics.height - self.input.y]
            self.input.mouse[2] = False

    def step(self):
        # Add init values as "0" Frame, ensure frame is in history bounds
        if self.data.frame == -1:
            self.data.frame = 0
            self.data.input_history.append(self.input.in_queue[:])
            self.data.frame_history.append(self.data.world.clone())
        elif self.data.frame <= 0:
            self.data.frame = 0

        # Check engine function input
        self.engine_keys()

        # Calculate frame and cache
        if not self.pause:
            self.data.frame += 1
            self.input.game_keys()
            itp.step(self.data.world, self.input.in_queue, self.dt)
            self.data.input_history.append(self.input.in_queue)
            self.data.frame_history.append(self.data.world.clone())
        elif self.data.frame >= len(self.data.frame_history):
            iterations = self.data.frame - len(self.data.frame_history) + 1
            for i in range(iterations):
                itp.step(self.data.world, self.input.in_queue, self.dt)
                self.data.input_history.append(self.input.in_queue)
                self.data.frame_history.append(self.data.world.clone())

        # Clear inputs
        self.input.in_queue = []

    def display(self):
        """
        Drawing Calls go here
        :return:
        """
        self.graphics.draw_scene(self.data.frame_history[self.data.frame])

    def game_loop(self):
        """
        Main Loop function, three cases arise:
            1. If Frame == -1, instance is uninitialized so set history[0] to initial values and increment frame
            2. If Frame >= len(history)-1, we've reached the most recent frame, so calculate next step and add to history
            3. Else Frame is already in history, just play back
        :return: None
        """

        # Process Logics
        self.step()

        # if self.rrt:
        #     self.rrt.grow()
        #print len(self.queue)
        for q in range(0, len(self.queue)):
            if not self.queue[q].empty():
                parent = self.queue[q].get()
                child = self.queue[q].get()
                self.graphics.trees[q].append_path(parent, child)
            else:
                self.procs[q].terminate()
                self.queue[q].close()
                self.queue[q] = mp.Queue()
                #print "Queue %s Empty. Terminating..." % (q,)


        # Queue Redisplay
        glutPostRedisplay()


def run_engine(q, p):
    e = Engine(q, p)
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)

    # Initialize starting state and run
    e.step()
    glutMainLoop()


def test(q):
    while True:
        if not q.empty():
            return


if __name__ == "__main__":
    procs = []
    queue = [mp.Queue(), mp.Queue()]
    node = None
    config = ConfigParser()
    config.read("settings.ini")

    for i in range(0, 2):
        node = itp.load_test_plan()
        tree = rrt.RRT(config, i, 1.0/60.0, node, "0")
        search = mp.Process(target=tree.grow, args=(queue[i],))
        search.daemon = True
        procs.append(search)
        search.start()

    run_engine(queue, procs)



# self.rrt = rrt.RRT(config, self.dt,
#                    self.data.world,
#                    # TODO: a particular space, not some arbitrary one?
#                    self.data.world.spaces.keys()[0])