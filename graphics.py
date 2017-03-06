from OpenGL.GL import *
from OpenGL.GLUT import *
import random
import copy


class Graphics(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["window", "fullscreen", "width", "height", "ents", "tilemaps", "hud", "menu"]

    def __init__(self, config):
        self.window = None
        self.fullscreen = False
        if config.get('Graphics', 'fullscreen') == 'True':
            self.fullscreen = True
        self.width = int(config.get('Graphics', 'width'))
        self.height = int(config.get('Graphics', 'height'))
        self.ents = []
        self.tilemaps = []
        self.hud = []
        self.menu = None

    def init_gl(self):
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
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)

        # Set Viewing Parameters
        glShadeModel(GL_SMOOTH)
        glMatrixMode(GL_PROJECTION)
        glLoadIdentity()
        glOrtho(0.0, self.width, 0.0, self.height, -10.0, 10.0)

        # Set to MV Matrix
        glMatrixMode(GL_MODELVIEW)
        glLoadIdentity()

    def draw_scene(self, frame):
        """
        Given a specific frame to draw, draw the scene and swap buffers
        :param frame: frame to draw
        :return:
        """
        # Clear buffer and draw
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
        for t in self.tilemaps:
            t.draw()

        for a in range(0, len(self.ents)):
            for i in range(0, len(self.ents[a])):
                self.ents[a][i].origin = [frame.valuations[a][i].get_var("x"),
                                          frame.valuations[a][i].get_var("y"),
                                          0]
                self.ents[a][i].draw()

        for h in self.hud:
            h.draw()

        if self.menu.active:
            self.menu.draw()

        # Swap buffers
        glutSwapBuffers()

    def load_hud(self, world, a, i, color):
        h = Hud(a, i)

        for j in range(0, len(world.automata[a].ordered_modes)):
            h.text.append(world.automata[a].ordered_modes[j].name)
            new_color = copy.deepcopy(color)
            if world.valuations[a][i].active_modes & (1 << j) > 0:
                new_color[3] = 1.0
            else:
                new_color[3] = 0.0
            h.colors.append(new_color)
        self.hud.append(h)

    def load_ents(self, world):
        """
        For each ent i, rect for each collider j is loaded and added to instance of Entity class
        :param world: World instance from interpreter to load from
        :return:
        """
        id = -1
        # For each automata, create an Entity instance with initial origin for automata
        for a in range(0, len(world.valuations)):
            self.ents.append([])
            for i in range(0, len(world.valuations[a])):
                id += 1
                new_ent = Entity()
                new_ent.origin = [world.valuations[a][i].get_var('x'), world.valuations[a][i].get_var('y'), 0]
                new_ent.id = id

                # For each collider, append one list of [X, Y, Z] to Entity.verts and one list of [R, G, B] to Entity.colors
                for c in range(0, len(world.automata[a][3])):
                    x = world.automata[a][3][c].shape[0].value
                    y = world.automata[a][3][c].shape[1].value
                    w = world.automata[a][3][c].shape[2].value
                    h = world.automata[a][3][c].shape[3].value
                    new_ent.verts.append([(x, y, 0.5),
                                          (x+w, y, 0.5),
                                          (x+w, y-h, 0.5),
                                          (x, y-h, 0.5)])
                    new_ent.colors.append([random.randint(3, 10)/10.0,
                                           random.randint(3, 10)/10.0,
                                           random.randint(3, 10)/10.0,
                                           1.0])
                self.load_hud(world, a, i, new_ent.colors[0])
                self.ents[a].append(new_ent)

        for i in range(0, len(self.hud)):
            self.hud[i].origin = [(self.width - 100) - i*100, self.height - 30]

    def load_tilemap(self, world):
        """
        For each tilemap (tm) i, calculate tiles as individual rects and load into Entity class
        :param world: World instance from interpreter to load from
        :return:
        """
        new_tm = Entity()
        new_tm.id = len(self.ents)
        for t in world.context.static_colliders:
            color = [random.randint(3, 10)/10.0,
                     random.randint(3, 10)/10.0,
                     random.randint(3, 10)/10.0,
                     1.0]

            tile_w = t.shape.tile_width
            tile_h = t.shape.tile_height
            map_h = len(t.shape.tiles)*tile_h
            for i in range(0, len(t.shape.tiles)):
                for j in range(0, len(t.shape.tiles[i])):
                    if t.shape.tiles[i][j] == 1:
                        new_tm.verts.append([(tile_w*j, map_h - tile_h*i, 0.5),
                                             (tile_w*j + tile_w, map_h - tile_h*i, 0.5),
                                             (tile_w*j + tile_w, map_h - (tile_h*i + tile_h), 0.5),
                                             (tile_w*j, map_h - (tile_h*i + tile_h), 0.5)])
                        new_tm.colors.append(color)
            self.tilemaps.append(new_tm)

    def init_graphics(self, world):
        """
        Initialize graphics for engine
        :param world: World instance from interpreter.py from which to load definitions
        :return: None
        """
        # Initialize Display, window, and render types
        glutInit(sys.argv)
        glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE | GLUT_DEPTH)
        glutInitWindowSize(self.width, self.height)
        glutInitWindowPosition(0, 0)
        self.window = glutCreateWindow('HyPED')
        self.menu = Menu([])
        if self.fullscreen:
            glutFullScreen()
        if world:
            self.load_ents(world)
            self.load_tilemap(world)
        self.init_gl()


class Entity(object):
    """
    Describes graphical objects in the engine
    """
    __slots__ = ["id", "name", "origin", "verts", "colors"]

    def __init__(self):
        self.id = None
        self.name = None
        self.origin = [0, 0, 0]
        self.verts = []
        self.colors = []

    # TODO: Currently using deprecated drawing, implement vertex arrays and buffers
    def draw(self):
        assert self.verts
        glMatrixMode(GL_MODELVIEW)
        glTranslate(*self.origin)

        glBegin(GL_QUADS)
        for i in range(0, len(self.colors)):
            glColor4f(*self.colors[i])
            for v in self.verts[i]:
                glVertex3f(*v)
        glEnd()
        glLoadIdentity()


class Hud(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "index", "origin", "spacing", "font", "text", "colors"]

    def __init__(self, a, i, x=None, y=None):
        self.id = None
        self.index = [a, i]
        self.origin = [x, y]
        self.font = fonts.GLUT_BITMAP_HELVETICA_18
        self.spacing = glutBitmapHeight(self.font)
        self.text = []
        self.colors = []

    # TODO: Currently using deprecated drawing, implement vertex arrays and buffers
    def draw(self):
        for i in range(0, len(self.text)):
            glColor4f(*self.colors[i])
            glRasterPos2f(self.origin[0], self.origin[1]-(i*self.spacing))
            for str in self.text[i]:
                glutBitmapString(self.font, str)


class Menu(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "active", "origin", "font", "content", "width", "height"]

    def __init__(self, content, font=None):
        self.id = None
        self.active = False
        self.origin = [0, 0]
        self.font = font
        if not self.font:
            self.font = fonts.GLUT_BITMAP_HELVETICA_12
        self.content = content
        if self.content:
            self.height = glutBitmapHeight(self.font)*len(content)
            max_w = self.content[0].width
            for c in self.content:
                if c.width > max_w:
                    max_w = c.width
            self.width = max_w

        else:
            self.width = 100
            self.height = 100

    def draw(self):
        glColor4f(0.5, 0.5, 0.5, 0.5)
        glBegin(GL_QUADS)
        glVertex3f(self.origin[0], self.origin[1], 0.6)
        glVertex3f(self.origin[0]+self.width, self.origin[1], 0.6)
        glVertex3f(self.origin[0]+self.width, self.origin[1]-100.0, 0.6)
        glVertex3f(self.origin[0], self.origin[1]-100.0, 0.6)
        glEnd()
        '''
        for i in range(0, len(self.content)):
            glRasterPos2f(self.content[i].origin[0], self.content[i].origin[1]+(i*self.height))
            self.content[i].draw()
            '''


class SubMenu(Menu):
    def __init__(self, content):
        Menu.__init__(self)
        self.content = content
        self.width = glutBitmapLength(self.font)

    def draw(self):
        glutBitmapString(self.font, self.content)



