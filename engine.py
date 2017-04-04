import copy
from OpenGL.GLUT import *
from ConfigParser import ConfigParser

import interpreter
import data
import graphics
import input
import rrt
from vglc_translator import vglc_tilemap


class Engine(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "dt", "pause", "data", "graphics", "input", "rrt", "time"]

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
            self.rrt = rrt.RRT(config, self.data.world)
        else:
            self.rrt = None
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
            self.graphics.pathtree.check(self.input.x, self.graphics.height - self.input.y)
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
            #self.data.world.valuations[0][0].parameters['gravity'] = -9000.0
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
            self.data.frame_history.append(copy.deepcopy(self.data.world))
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
            self.data.frame_history.append(copy.deepcopy(self.data.world))
        elif self.data.frame >= len(self.data.frame_history):
            iterations = self.data.frame - len(self.data.frame_history) + 1
            for i in range(iterations):
                interpreter.step(self.data.world, self.input.in_queue, self.dt)
                self.data.input_history.append(self.input.in_queue)
                self.data.frame_history.append(copy.deepcopy(self.data.world))

        # Update alpha values of active modes
        for h in self.graphics.hud:
            for i in range(len(self.data.world.automata[h.index[0]].ordered_modes)):
                if self.data.world.valuations[h.index[0]][h.index[1]].active_modes & (1 << i):
                    h.colors[i][3] = 1.0
                else:
                    h.colors[i][3] -= 0.01
                    if h.colors[i][3] < 0.0:
                        h.colors[i][3] = 0.0

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

        if self.rrt:
            self.rrt.grow()
            #self.rrt.branch_test()

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
    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)

    for i in range(10):
        e.rrt.grow_test()
        print len(e.graphics.pathtree.tree.paths)
        print e.graphics.pathtree.tree.size
        print e.graphics.pathtree.tree.paths

    for i in range(1000):
        e.step()


if __name__ == "__main__":
    main()
