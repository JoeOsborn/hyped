import copy
import os
import dill

import hyped.interpreter as interpreter
from hyped.vglc_translator import vglc_tilemap


class Data(object):
    __slots__ = ["frame", "frame_history", "input_history", "world"]

    def __init__(self, config):
        self.frame = -1
        self.frame_history = []
        self.input_history = []
        if ((config.has_option('Data', 'link_test') and
             config.getboolean('Data', 'link_test'))):
            self.world = interpreter.load_test2()
        elif ((config.has_option('Data', 'plan_test') and
               config.getboolean('Data', 'plan_test'))):
            self.world = interpreter.load_test_plan()
        else:
            automata = []
            for a in config.get('Data', 'automata').split(' '):
                automata.append(a)
            initial = self.get_init(config, automata)
            tz = int(config.get('Data', 'tilesize'))
            tilemap = vglc_tilemap(tz, tz,
                                   *config.get('Data', 'tilemap').split(' '))
            self.world = interpreter.load_test(automata, tilemap, initial)

    def get_init(self, config, automata):
        initial = []
        name = None
        params = {}
        origin = {'x': -1, 'y': -1}
        for i in config.get('Data', 'initial').split(' '):
            if i.isdigit():
                if origin['x'] < 0:
                    origin['x'] = int(i)
                elif origin['y'] < 0:
                    origin['y'] = int(i)
                else:
                    print "Some Error"
            else:
                string = i.split('=')
                if len(string) > 1:
                    params[string[0]] = float(string[1])
                elif i + ".char.xml" in automata:
                    name = i
                else:
                    print "Some Error"
            if name and not origin['x'] < 0 and not origin['y'] < 0:
                initial.append((name, params, origin))
                name, params, origin = None, {}, {'x': -1, 'y': -1}
        if not initial:
            return None
        return initial

    def clip_history(self, index):
        self.world = copy.deepcopy(self.frame_history[index])
        del self.frame_history[index + 1:]
        del self.input_history[index + 1:]

    def save_state(self):
        # logging.debug("Saving file...")
        save = open('save.pkl', 'wb')
        dill.dump((self.frame_history, self.input_history,
                   self.world, self.frame),
                  save)
        save.close()
        # logging.debug("Save complete.")

    def load_state(self):
        # logging.debug("Loading file...")
        if os.path.exists("save.pkl"):
            # logging.debug("File exists")
            save = open('save.pkl', 'rb')
            (self.frame_history,
             self.input_history,
             self.world,
             self.frame) = dill.load(save)
            save.close()
            # logging.debug("Load complete.")
        else:
            pass
            # logging.debug("No Save File Found")
