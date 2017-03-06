import copy
from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *
from ConfigParser import ConfigParser

import interpreter
import broad_phase
import graphics
import input
import data

import logging

logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

e = None
char = 'flappy'


class Engine(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "dt", "pause", "data", "graphics", "input"]

    def __init__(self, ini="settings.ini"):
        config = ConfigParser()
        config.read(ini)
        self.id = 0
        n, d = config.get('Engine', 'dt').split()
        self.dt = float(n) / float(d)
        self.pause = False
        self.input = input.Input(config)
        self.data = data.Data(config)
        self.graphics = graphics.Graphics(config)

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
            print self.input.x, self.graphics.height - self.input.y
            self.graphics.menu.active = True
            if self.graphics.menu.active:
                self.graphics.menu.origin = [self.input.x, self.graphics.height - self.input.y]
            self.input.mouse[2] = False

    def game_loop(self):
        """
        Main Loop function, three cases arise:
            1. If Frame == -1, instance is uninitialized so set history[0] to initial values and increment frame
            2. If Frame >= len(history)-1, we've reached the most recent frame, so calculate next step and add to history
            3. Else Frame is already in history, just play back
        :return: None
        """

        # Add init values as "0" Frame, ensure frame is in history bounds
        if self.data.frame == -1:
            self.data.frame = 0
            self.data.input_history.append(self.input.in_queue)
            self.data.frame_history.append(copy.deepcopy(self.data.world))
            self.graphics.draw_scene(self.data.frame_history[self.data.frame])
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

        # Draw and clear input queue
        self.graphics.draw_scene(self.data.frame_history[self.data.frame])
        print interpreter.determine_available_transitions(self.data.world, self.data.world.valuations[0][0])
        self.input.in_queue = []


def main():
    """
    Currently for testing purposes: Load test data and initialize
    :return:
    """
    global e
    global char
    e = Engine()
    char = 'flappy'
    e.data.world = interpreter.load_test(char)
    e.graphics.init_graphics(e.data.world)
    e.input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(e.game_loop)
    glutIdleFunc(e.game_loop)
    glutMainLoop()


if __name__ == "__main__":
    main()
