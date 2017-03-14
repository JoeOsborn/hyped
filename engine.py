import copy
from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *
from ConfigParser import ConfigParser
import time

import schema
import interpreter
import graphics
import input
import data

import pstats
import profile
import logging

logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')


def get_available(world, val):
        available = []
        mi = 0
        modes = world.automata[val.automaton_index].ordered_modes
        mode_count = len(modes)
        active = val.active_modes
        while mi < mode_count:
            if active & (1 << mi):
                mode = modes[mi]
                for e in mode.envelopes:
                    if e.axes[0][1] == 'x':
                        available.append("left")
                        available.append("right")
                    elif e.axes[0][1] == 'y':
                        available.append("up")
                        available.append("down")
                for e in mode.edges:
                    if isinstance(e.guard.conjuncts[0], schema.GuardButton):
                        available.append(e.guard.conjuncts[0].buttonID)
                    if interpreter.eval_guard(e.guard, world, val):
                        available.append(e.target)
                        break
            mi += 1
        return available


class Engine(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "dt", "automata", "pause", "data", "graphics", "input", "time"]

    def __init__(self, ini="settings.ini"):
        config = ConfigParser()
        config.read(ini)
        self.id = 0
        n, d = config.get('Engine', 'dt').split()
        self.dt = float(n) / float(d)
        self.automata = []
        for a in config.get('Engine', 'automata').split(' '):
            self.automata.append(a)
        self.pause = False
        self.input = input.Input(config)
        self.data = data.Data(config)
        self.data.world = interpreter.load_test(self.automata)
        if config.get('Engine', 'rrt').lower() == "true":
            prec, cons = int(config.get('Engine', 'precision')), int(config.get('Engine', 'constraint'))
            self.graphics = graphics.Graphics(config, self.data.world, prec, cons)
        else:
            self.graphics = graphics.Graphics(config)
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
            x, y = self.input.x, self.graphics.height - self.input.y
            if x < self.graphics.menu.origin[0] or x > self.graphics.menu.origin[0] + self.graphics.menu.width or \
               y > self.graphics.menu.origin[1] or y < self.graphics.menu.origin[1] - self.graphics.menu.height:
                self.graphics.menu.active = False
            else:
                pass
            self.input.mouse[0] = False

        # Right Click: Open Menu
        if self.input.mouse[2]:
            '''
            print self.input.x, self.graphics.height - self.input.y
            self.graphics.menu.active = True
            self.graphics.paths.tree.goal = {'x': self.input.x, 'y': self.graphics.height - self.input.y}
            if self.graphics.menu.active:
                self.graphics.menu.origin = [self.input.x, self.graphics.height - self.input.y]
            self.input.mouse[2] = False
        '''

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
            for i in range(0, iterations):
                interpreter.step(self.data.world, self.input.in_queue, self.dt)
                self.data.input_history.append(self.input.in_queue)
                self.data.frame_history.append(copy.deepcopy(self.data.world))
        # Update alpha values of active modes
        for h in self.graphics.hud:
            for i in range(0, len(self.data.world.automata[h.index[0]].ordered_modes)):
                if self.data.world.valuations[h.index[0]][h.index[1]].active_modes & (1 << i):
                    h.colors[i][3] = 1.0
                else:
                    h.colors[i][3] -= 0.01
                    if h.colors[i][3] < 0.0:
                        h.colors[i][3] = 0.0
        self.input.in_queue = []
        #self.graphics.draw_scene(self.data.frame_history[self.data.frame])

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

        # Queue Redisplay
        glutPostRedisplay()


from vglc_translator import vglc_tilemap

def main():
    """
    Currently for testing purposes: Load test data and initialize
    :return:
    """
    e = Engine()
    e.data.world = interpreter.load_test(e.automata,
            vglc_tilemap(16, 16, "./resources/VGLC/SampleRoom.txt", "./resources/VGLC/smb.json", "./resources/VGLC/mario_1_1.json"))
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)
    e.step()
    glutMainLoop()


def test():
    e = Engine()
    e.data.world = interpreter.load_test(e.automata)
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    glutDisplayFunc(e.display)
    glutIdleFunc(e.game_loop)

    for i in range(0, 1000):
        e.step()
        e.display()


if __name__ == "__main__":
    main()

