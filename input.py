import bitarray
import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')

# Keys is a 255 bitarray representing all ASCII keys, 1 is on, 0 is off
keys = bitarray.bitarray(255)
keys.setall(False)

# Skeys is bitarray representing special keys like arrow keys and function keys
skeys = bitarray.bitarray(4)
skeys.setall(False)

# Mouse is bitarray representing mouse button states
mouse = bitarray.bitarray(5)
mouse.setall(False)

# Mouse variables saving mouse position
mouse_x = 0.0
mouse_y = 0.0
mouse_d = 0.0


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
    #logging.debug(keycode)
    keys[keycode] = False
    return

# Handlers for special keys, 0 is left arrow, 1 is up, 2 is right, 3 is left
def skey_down_listener(key, x, y):
    global skeys
    keycode = key % 100
    #logging.debug(keycode)
    skeys[keycode] = True
    return


def skey_up_listener(key, x, y):
    global skeys
    keycode = key % 100
    #logging.debug(keycode)
    skeys[keycode] = False
    return


# Handler for mouse click
def mouse_listener(button, state, x, y):
    global mouse
    #logging.debug("Button: " + str(button) + " State: " + str(state))
    mouse[button] = not state
    #logging.debug(mouse)
    return
