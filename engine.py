from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

import interpreter
import graphics
import input
import data

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

# Set windows and timestep
window = 0
dt = 1.0/60.0

# State Variables
pause = False


def keyboard_input():
    """
    Function for defining how keys should be handled
    :return: None
    """
    global pause

    # TODO: Implement decorator functions to differentiate inputs that should only fire once per button hold
    # TODO: Change from hard-coding to xml implementation

    # Handlers for standard ASCII keys
    # Spacebar: send "flap" signal
    if input.keys[32]:
        input.in_queue.append("flap")
        input.keys[32] = False
    if input.keys[97]:
        input.in_queue.append('left')
    if input.keys[100]:
        input.in_queue.append('right')
    # p: pause game
    if input.keys[112]:
        #logging.debug(data.input_history)
        pause = not pause
        # If game is un-paused, allow history overwrite
        if not pause:
            data.clip_history(data.frame)
        input.keys[112] = False
    # r: reset game
    if input.keys[114]:
        data.clip_history(0)
        data.frame = 0
        input.keys[114] = False
    # ESC: exit
    if input.keys[27]:
        exit(0)

    # Handlers for special function keys
    if input.skeys[100]:
        if pause:
            data.frame -= 1
        else:
            input.in_queue.append("left")
    if input.skeys[102]:
        if pause:
            data.frame += 1
        else:
            input.in_queue.append("right")

    # Handler for mouse input
    if input.mouse[0] and pause:
        pass

    # Special ASCII CTRL Codes
    # CTRL + S
    if input.keys[19]:
        pause = True
        data.save_state()
        pause = False
    # CTRL + L
    if input.keys[12]:
        pause = True
        data.load_state()


def game_loop():
    """
    Main Loop function, three cases arise:
        1. If Frame == -1, instance is uninitialized so set history[0] to initial values and increment frame
        2. If Frame >= len(history)-1, we've reached the most recent frame, so calculate next step and add to history
        3. Else Frame is already in history, just play back
    :return: None
    """

    # Add init values as "0" Frame, ensure frame is in history bounds
    if data.frame == -1:
        data.append()
    elif data.frame <= 0:
        data.frame = 0

    # Check key input
    keyboard_input()

    # Calculate frame and cache
    interpreter.step(data.world, input.in_queue, dt)
    data.append()
    if not pause:
        data.frame += 1

    if data.frame >= len(data.frame_history)-1:
        data.frame = len(data.frame_history)-1

    # Draw and clear input queue
    graphics.draw_scene(data.frame_history[data.frame])
    input.in_queue = []


def main():
    """
    Currently for testing purposes: Load test data and initialize
    :return:
    """
    data.world = interpreter.load_test()
    graphics.init_graphics(data.world)
    input.register_funcs()

    # Register function callbacks and run
    glutDisplayFunc(game_loop)
    glutIdleFunc(game_loop)
    glutMainLoop()


if __name__ == "__main__":
        main()
