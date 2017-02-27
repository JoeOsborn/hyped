import bitarray
from OpenGL.GLUT import *
# from defusedxml import ElementTree as et

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

in_queue = []

# Keys is a 255 bitarray representing all ASCII keys, 1 is on, 0 is off
keys = bitarray.bitarray(255)
keys.setall(False)

# Skeys is bitarray representing special keys like arrow keys and function keys
skeys = bitarray.bitarray(128)
skeys.setall(False)

# Mouse is bitarray representing mouse button states
mouse = bitarray.bitarray(5)
mouse.setall(False)

# Mouse variables saving mouse position
mouse_x = 0.0
mouse_y = 0.0
mouse_d = 0.0


def clear_all():
    in_queue = []
    keys.setall(False)
    skeys.setall(False)
    mouse.setall(False)


# Handlers for ASCII keys, translates to keycode and flips bit
def key_down_listener(key, x, y):
    global keys
    keycode = ord(key)
    #logging.debug(keycode)
    keys[keycode] = True
    return


def key_up_listener(key, x, y):
    global keys
    keycode = ord(key)
    # logging.debug(keycode)
    keys[keycode] = False
    return


# Handlers for special keys
def skey_down_listener(key, x, y):
    global skeys
    #logging.debug(key)
    skeys[key] = True
    return


def skey_up_listener(key, x, y):
    global skeys
    # logging.debug(keycode)
    skeys[key] = False
    return


# Handler for mouse click
def mouse_listener(button, state, x, y):
    global mouse
    # logging.debug("Button: " + str(button) + " State: " + str(state))
    mouse[button] = not state
    # logging.debug(mouse)
    return

def register_funcs():
    """
    Register function callbacks to glut
    :return:
    """
    # Register input callbacks
    glutMouseFunc(mouse_listener)
    glutKeyboardFunc(key_down_listener)
    glutKeyboardUpFunc(key_up_listener)
    glutSpecialFunc(skey_down_listener)
    glutSpecialUpFunc(skey_up_listener)
    glutIgnoreKeyRepeat(True)

"""
# Dict to dispatch to correct array
types = {"keys": keys,
         "skeys": skeys,
         "mouse": mouse}

# functions = {transform}

def make_key_handler(key_t, keycode, repeat):
    def wrapper():
        types[key_t][keycode] = True
        logging.debug(types[key_t][keycode])
    return wrapper


def repeat_false(function):
    def wrapper():
        function(key_t, keycode)
        types[key_t][keycode] = False
        logging.debug(types[key_t][keycode])
    return wrapper



def key_handler(key_t, keycode):
    types[key_t][keycode] = True
    logging.debug(types[key_t][keycode])
    return


def xml_input_parse(filename):
    pass


def main():
    func = repeat_false(key_handler("keys", 0))
    func()
    return

if __name__ == "__main__":
    main()

"""