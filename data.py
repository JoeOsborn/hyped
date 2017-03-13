import copy
import os
import dill

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')


class Data(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["frame_history", "input_history", "world", "frame"]

    def __init__(self, config):
        self.frame_history = []
        self.input_history = []
        self.world = 0
        self.frame = -1

    def clip_history(self, index):
        self.world = copy.deepcopy(self.frame_history[index])
        del self.frame_history[index+1:]
        del self.input_history[index+1:]

    def save_state(self):
        logging.debug("Saving file...")
        save = open('save.pkl', 'wb')
        dill.dump((self.frame_history, self.input_history, self.world, self.frame), save)
        save.close()
        logging.debug("Save complete.")

    def load_state(self):
        logging.debug("Loading file...")
        if os.path.exists("save.pkl"):
            logging.debug("File exists")
            save = open('save.pkl', 'rb')
            self.frame_history, self.input_history, self.world, self.frame = dill.load(save)
            save.close()
            logging.debug("Load complete.")
        else:
            logging.debug("No Save File Found")