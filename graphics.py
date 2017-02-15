from OpenGL.GL import *
from OpenGL.GLUT import *
import random

ents = []
tilemaps = []


def init_gl(width, height):
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


def draw_scene(frame):
    """
    Given a specific frame to draw, draw the scene and swap buffers
    :param frame: frame to draw
    :return:
    """

    if frame != -1:
        # Origin is (X, Y, Z) value in history array at frame
        ents[0].origin = [frame.valuations[0][0].get_var("x"),
                          frame.valuations[0][0].get_var("y"),
                          0]

    # Clear buffer and draw
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
    for t in tilemaps:
        t.draw()
    for e in ents:
        e.draw()

    # Clear inputs and swap buffers
    glutSwapBuffers()


def load_ents(world):
    """
    For each ent i, rect for each collider j is loaded and added to instance of Entity class
    :param world: World instance from interpreter to load from
    :return:
    """
    # For each automata, create an Entity instance of id 0 - len(ents), and initial origin for automata
    for a in range(0, len(world.automata)):
        new_ent = Entity()
        new_ent.id = len(ents)
        new_ent.origin = [world.valuations[0][a].get_var('x'), world.valuations[0][a].get_var('y'), 0]

        # For each collider, append one list of [X, Y, Z] to Entity.verts and one list of [R, G, B] to Entity.colors
        for c in range(0, len(world.automata[a][3])):
            x = world.automata[a][3][c].shape[0].value
            y = world.automata[a][3][c].shape[1].value
            w = world.automata[a][3][c].shape[2].value / 2
            h = world.automata[a][3][c].shape[3].value / 2
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


def load_tilemap(world):
    """
    For each tilemap (tm) i, calculate tiles as individual rects and load into Entity class
    :param world: World instance from interpreter to load from
    :return:
    """
    new_tm = Entity()
    new_tm.id = len(ents)
    for t in world.context.static_colliders:
        color = [random.randint(0, 10)/10.0,
                 random.randint(0, 10)/10.0,
                 random.randint(0, 10)/10.0]
        width = t.shape.tile_width/2
        height = t.shape.tile_height/2
        for i in range(0, len(t.shape.tiles)):
            for j in range(0, len(t.shape.tiles[i])):
                if t.shape.tiles[i][j] == 1:
                    new_tm.verts.append([(width*j, height * i, 0.0),
                                         (width*j + width, height * i, 0.0),
                                         (width*j + width, height * i + height, 0.0),
                                         (width*j, height * i + height, 0.0)])
                    new_tm.colors.append(color)
        tilemaps.append(new_tm)


def init_graphics(world):
    """
    Initialize graphics for engine
    :param world: World instance from interpreter.py from which to load definitions
    :return: None
    """
    global window

    # Initialize Display, window, and render types
    glutInit(sys.argv)
    glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE | GLUT_DEPTH)
    glutInitWindowSize(640, 480)
    glutInitWindowPosition(200, 200)
    window = glutCreateWindow('HyPED')
    if world:
        load_ents(world)
        load_tilemap(world)
    init_gl(640, 480)


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
