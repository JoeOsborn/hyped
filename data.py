import copy
import os
import input
import graphics
import dill

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

# Data Arrays
frame_history = []
input_history = []

# State Variables
world = None
frame = -1


def clip_history(index):
    global world

    world = copy.deepcopy(frame_history[index])
    del frame_history[index+1:]
    del input_history[index+1:]


def append():
    frame_history.append(copy.deepcopy(world))
    input_history.append(input.in_queue)


def overwrite():
    frame_history[frame] = copy.deepcopy(world)
    input_history[frame] = input.in_queue


def save_state():
    logging.debug("Saving file...")
    save = open('save.pkl', 'wb')
    dill.dump((frame_history, input_history, world, frame), save)
    save.close()
    logging.debug("Save complete.")
    input.clear_all()


def load_state():
    global frame_history
    global input_history
    global world
    global frame

    world = None
    logging.debug("Loading file...")
    if os.path.exists("save.pkl"):
        logging.debug("File exists")
        save = open('save.pkl', 'rb')
        frame_history, input_history, world, frame = dill.load(save)
        save.close()
        logging.debug("Load complete.")
        input.clear_all()
        graphics.draw_scene(frame_history[frame])
    else:
        logging.debug("No Save File Found")
