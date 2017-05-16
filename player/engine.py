from ConfigParser import ConfigParser

from OpenGL.GLUT import *

import data
import graphics
import hyped.interpreter as interpreter
import hyped.local_planner as lp
import hyped.rrt as rrt
import input



class Engine(object):
    __slots__ = ["id", "dt", "pause", "data",
                 "graphics", "input", "rrt", "time"]

    def __init__(self, ini="settings.ini"):
        config = ConfigParser()
        config.read(ini)
        self.id = 0
        n, d = config.get('Engine', 'dt').split()
        self.dt = float(n) / float(d)
        self.pause = False
        self.data = data.Data(config)
        self.input = input.Input(config)
        if config.get('Engine', 'rrt').lower() == "true":
            self.rrt = rrt.RRT(config, self.dt,
                               self.data.world,
                               # TODO: a particular space, not some arbitrary one?
                               self.data.world.spaces.keys()[0])
        else: self.rrt = None
        self.graphics = graphics.Graphics(config, self.rrt)
        self.time = 0

    def engine_keys(self):
        # p: pause game
        if self.input.keys[112]:
            self.pause = not self.pause
            # If game is un-paused, allow history overwrite
            if not self.pause:
                self.data.clip_history(self.data.frame)
            self.input.keys[112] = False
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
            if self.rrt:
                node = self.graphics.pathtree.check(self.input.x, self.graphics.height - self.input.y)
                #print self.input.x, self.graphics.height - self.input.y
                print node
                if node:
                    self.rrt.get_path(node)
                self.rrt.goal['x'] = -1
                self.rrt.goal['y'] = -1
            # x, y = self.input.x, self.graphics.height - self.input.y
            # if not self.graphics.menu.check(x, y):
            #     self.graphics.menu.active = False
            # else:
            #     pass
            self.input.mouse[0] = False

        # Right Click: Open Menu
        if self.input.mouse[2]:
            self.rrt.goal['x'] = self.input.x
            self.rrt.goal['y'] = self.graphics.height - self.input.y
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
            interpreter.step(self.data.world, self.input.in_queue, self.dt)
            self.data.input_history.append(self.input.in_queue)
            self.data.frame_history.append(self.data.world.clone())
        elif self.data.frame >= len(self.data.frame_history):
            iterations = self.data.frame - len(self.data.frame_history) + 1
            for i in range(iterations):
                interpreter.step(self.data.world, self.input.in_queue, self.dt)
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
        #con = self.data.world.spaces.values()[0].contacts
        #if con: print con[0].b_types
        #con = [c.b_types for c in self.data.world.spaces.values()[0].contacts]
        #print con
        # Process Logics
        self.step()

        if self.rrt:
            self.rrt.grow()

        # Queue Redisplay
        glutPostRedisplay()


def main():
    """
    Currently for testing purposes: Load test data and initialize
    :return:
    """

    e = Engine()
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)

    # Initialize starting state and run
    e.step()
    glutMainLoop()


def test():
    e = Engine()
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)
    lp.dijkstra_stagger(e.data.world, None, lambda g0, h, _move0, _move, log: log.t + h,
                        lambda w, _ignored: lp.aut_distance(w, {"0": [[{"x": 13 * 32, "y": 48}]]}, "0", 0, 0),
                        e.dt, 100000, e.graphics.pathtree.append_path)

    #print len(e.graphics.pathtree.paths)
    # Initialize starting state and run
    e.step()
    glutMainLoop()


if __name__ == "__main__":
    main()
