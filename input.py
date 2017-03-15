import bitarray
from OpenGL.GLUT import *

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')


class Input(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["in_queue", "handlers", "keys", "skeys", "mouse", "x", "y", "dx", "dy"]

    def __init__(self, config):
        self.in_queue = []
        self.handlers = self.generate_handlers(config)
        self.keys = bitarray.bitarray(255)
        self.keys.setall(False)
        self.skeys = bitarray.bitarray(128)
        self.skeys.setall(False)
        self.mouse = bitarray.bitarray(5)
        self.mouse.setall(False)
        self.x = 0.0
        self.y = 0.0
        self.dx = 0.0
        self.dy = 0.0

    def clear_all(self):
        self.in_queue = []
        self.keys.setall(False)
        self.skeys.setall(False)
        self.mouse.setall(False)

    # Handlers for ASCII keys, translates to keycode and flips bit
    def key_down_listener(self, key, x, y):
        keycode = ord(key)
        #logging.debug(keycode)
        self.keys[keycode] = True
        return

    def key_up_listener(self, key, x, y):
        keycode = ord(key)
        # logging.debug(keycode)
        self.keys[keycode] = False
        return

    # Handlers for special keys
    def skey_down_listener(self, key, x, y):
        #logging.debug(key)
        self.skeys[key] = True
        return

    def skey_up_listener(self, key, x, y):
        # logging.debug(keycode)
        self.skeys[key] = False
        return

    # Handler for mouse click
    def mouse_listener(self, button, state, x, y):
        #logging.debug("Button: " + str(button) + " State: " + str(state) + " x: " + str(x) + " y: " + str(y))
        self.mouse[button] = not state
        self.dx = x - self.x
        self.dy = y - self.y
        self.x = x
        self.y = y
        return

    # Handler for mouse motion
    def motion_listener(self, x, y):
        self.dx = x - self.x
        self.dy = y - self.y
        self.x = x
        self.y = y
        return

    def register_funcs(self):
        """
        Register function callbacks to glut
        :return:
        """
        # Register input callbacks
        glutMouseFunc(self.mouse_listener)
        #glutPassiveMotionFunc(self.motion_listener)
        glutKeyboardFunc(self.key_down_listener)
        glutKeyboardUpFunc(self.key_up_listener)
        glutSpecialFunc(self.skey_down_listener)
        glutSpecialUpFunc(self.skey_up_listener)
        glutIgnoreKeyRepeat(True)

    def game_keys(self):
        for h in self.handlers:
            h()

    def generate_handlers(self, config):
        handlers = []

        def make_key_handler(key_in, key_t, keycode, repeat):
            def key_wrapper():
                def key_handler():
                    if getattr(self, key_t)[keycode]:
                        self.in_queue.append(key_in)
                    return
                key_handler()
                if not repeat:
                    getattr(self, key_t)[keycode] = False
            return key_wrapper

        for i in config.items('Input'):
            key_in = i[0]
            args = i[1].split()
            for a in range(0, len(args), 3):
                if args[a+2].lower() == "true":
                    repeat = True
                else:
                    repeat = False
                handlers.append(make_key_handler(key_in, args[a], int(args[a+1]), repeat))
        return handlers

    def menu(self, entry):
        if entry == 0:
            print self.x, self.y, self.dx, self.dy
