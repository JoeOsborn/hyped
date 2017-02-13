from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

import interpreter
import input

import sys
import random

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

# Set windows and timestep
window = 0
dt = 1.0/60.0

# Data Arrays
ents = []
inputs = []
history = []

# State Variables
frame = -1 # Start uninitialized
pause = False

 
def init_GL(width, height):
    """
    Function to initialize OpenGL parameters
    :param width: width of window, unimplemented
    :param height: height of window, unimplemented
    :return: None
    """

    # Set Default BG Color and Depth Tests
    glClearColor(0.0, 0.0, 0.0, 0.0)
    glEnable(GL_DEPTH_TEST)
    glDepthFunc(GL_LESS)

    # Set Viewing Parameters
    glShadeModel(GL_FLAT)
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    glOrtho(0.0, 640.0, 0.0, 480.0, -1.0, 1.0)

    # Set to MV Matrix
    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()


def keyboard_input():
    """
    Function for defining how keys should be
    :return: None
    """

    global pause
    global frame

    # TODO: Implement decorator functions to differentiate inputs that should only fire once per button hold
    # TODO: Change from hard-coding to xml implementation
    # Handlers for standard ASCII keys

    # Spacebar: send "flap" signal
    if input.keys[32]:
        inputs.append("flap")
        input.keys[32] = False

    # c: change color randomly
    if input.keys[99]:
        ents[0].colors = [(random.randint(0, 10)/10.0,
                           random.randint(0, 10)/10.0,
                           random.randint(0, 10)/10.0)]
        input.keys[99] = False

    # p: pause game
    if input.keys[112]:
        pause = not pause
        input.keys[112] = False
    if input.keys[27]:
        exit(0)

    # Handlers for special function keys
    if input.skeys[0] and frame > 0:
        frame -= 1
    if input.skeys[2] and frame < len(history)-1:
        frame += 1

    # Handler for mouse input
    if input.mouse[0] and pause:
        pass


def draw_GLscene():
    """
    Main Loop function, three cases arise:
        1. If Frame == -1, instance is uninitialized so set history[0] to initial values and increment frame
        2. If Frame >= len(history)-1, we've reached the most recent frame, so calculate next step and add to history
        3. Else Frame is already in history, just play back
    :return: None
    """

    global inputs
    global frame
    global history

    # Handle keyboard inputs
    keyboard_input()

    # Add init values as "0" Frame
    if frame == -1:
        history.append(ents[0].origin)
        frame += 1

    # If not paused, then either new step or replay from history
    if not pause:
        if frame >= len(history)-1:
            frame += 1
            interpreter.step(interpreter.world, inputs, dt)
            history.append([interpreter.world.valuations[0][0].get_var("x"),
                            interpreter.world.valuations[0][0].get_var("y"),
                            0])
        else:
            frame += 1

    # Origin is (X, Y, Z) value in history array at frame
    ents[0].origin = history[frame]

    # Clear buffer and draw
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
    for e in ents:
        e.draw()

    # Clear inputs and swap buffers
    inputs = []
    glutSwapBuffers()


def load_ents(world):
    """
    Function to load entities (ents) into ents array. For each ent i, rect for each collider j is loaded and added to
    instance of Entity class
    :param world: World instance from interpreter.py from which to load definitions
    :return: None
    """

    # For each automata, create an Entity instance of id 0 - len(ents), and initial origin for automata
    for i in range(0, len(world.automata)):
        new_ent = Entity()
        new_ent.id = len(ents)
        new_ent.origin = [world.valuations[0][i].get_var('x'), world.valuations[0][i].get_var('y'), 0]

        # For each collider, append one list of [X, Y, Z] to Entity.verts and one list of [R, G, B] to Entity.colors
        for j in range(0, len(world.automata[i][3])):
            x = world.automata[i][3][j].shape[0].value
            y = world.automata[i][3][j].shape[1].value
            w = world.automata[i][3][j].shape[2].value / 2
            h = world.automata[i][3][j].shape[3].value / 2
            new_ent.verts.append([(x-w, y-h, 0.0),
                                  (x-w, y+h, 0.0),
                                  (x+w, y+h, 0.0),
                                  (x+w, y-h, 0.0)])
            new_ent.colors.append([random.randint(0, 10)/10.0,
                                   random.randint(0, 10)/10.0,
                                   random.randint(0, 10)/10.0])

        # Initialize animation values to 0 and append to ents array
        new_ent.rotation = 0.0
        new_ent.translation = (0, 0, 0)
        ents.append(new_ent)


def init_graphics(world):
    """
    Initialize graphics for engine
    :param world: World instance from interpreter.py from which to load definitions
    :return: None
    """

    global window
    global frame

    # Initialize Display, window, and render types
    glutInit(sys.argv)
    glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE | GLUT_DEPTH)
    glutInitWindowSize(640, 480)
    glutInitWindowPosition(200, 200)
    window = glutCreateWindow('HyPED')
    if world:
        load_ents(world)
    init_GL(640, 480)

    # Register input callbacks
    glutMouseFunc(input.mouse_listener)
    glutKeyboardFunc(input.key_down_listener)
    glutKeyboardUpFunc(input.key_up_listener)
    glutSpecialFunc(input.skey_down_listener)
    glutSpecialUpFunc(input.skey_up_listener)
    glutIgnoreKeyRepeat(True)

    # Register function callbacks
    glutDisplayFunc(draw_GLscene)
    glutIdleFunc(draw_GLscene)

    # Draw frame 0 (Initial positions and states) and then start loop
    draw_GLscene()
    glutMainLoop()


def main():
    """
    Currently for testing purposes: Load test data and initialize
    :return:
    """

    interpreter.load_test()
    init_graphics(interpreter.world)


class Entity(object):
    """
    Describes graphical objects in the engine
    """

    def __init__(self):
        self.id = None
        self.name = None
        self.origin = [0, 0, 0]
        self.verts = []
        self.colors = []
        self.rotation = 0.0
        self.translation = [0, 0, 0]

    # TODO: Currently using deprecated drawing, implement vertex arrays and buffers
    def draw(self):
        if self.verts:
            glMatrixMode(GL_MODELVIEW)
            glLoadIdentity()

            glTranslate(*self.origin)
            # glTranslate(*self.translation)
            glRotate(self.rotation, 0, 0, 1)
            if self.rotation == 360 or self.rotation == -360:
                self.rotation = 0

            glBegin(GL_QUADS)
            for i in range(0, len(self.colors)):
                glColor3f(*self.colors[i])
                for v in self.verts[i]:
                    glVertex3f(*v)
            glEnd()
        else:
            # print "Error: No graphic definition"
            pass


if __name__ == "__main__":
        main()
