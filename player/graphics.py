from OpenGL.GL import *
from OpenGL.GLUT import *
import ctypes
import random


class Graphics(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["window", "fullscreen", "width", "height",
                 "ents", "ent_count",
                 "tilemaps", "hud", "pathtree", "menu"]

    def __init__(self, config, rrt):
        self.window = None
        self.fullscreen = False
        if config.get('Graphics', 'fullscreen').lower == "true":
            self.fullscreen = True
        self.width = int(config.get('Graphics', 'width'))
        self.height = int(config.get('Graphics', 'height'))
        self.ents = {}
        self.ent_count = 0
        self.tilemaps = {}
        self.hud = []
        if rrt:
            self.pathtree = PathTree(rrt)
        else:
            self.pathtree = None
        self.menu = None

    def init_gl(self):
        """
        Function to initialize OpenGL parameters
        :return: None
        """
        # Set Default BG Color and Depth Tests
        glClearColor(0.0, 0.0, 0.0, 0.0)
        glEnable(GL_DEPTH_TEST)
        glDepthFunc(GL_LESS)
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        glDisable(GL_LIGHTING)

        self.menu = Menu([SubMenu("Set Goal")])

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
        top = 0
        left = 0
        max_x = 0
        max_y = 0
        for sid, ents in sorted(self.ents.items()):
            glMatrixMode(GL_MODELVIEW)
            glPushMatrix()
            glTranslate(left, top, 0)
            for t in self.tilemaps[sid]:
                sx, sy = t.get_dims()
                max_x = max(max_x, t.origin[0]+sx)
                max_y = max(max_y, t.origin[1]+sy)
                t.draw()
            for a in range(0, len(ents)):
                for i in range(0, len(ents[a])):
                    ent = self.ents[sid][a][i] 
                    ent.origin = [
                        frame.spaces[sid].valuations[a][i].get_var("x"),
                        frame.spaces[sid].valuations[a][i].get_var("y"),
                        0]
                    sx, sy = ent.get_dims()
                    max_x = max(max_x, ent.origin[0]+sx)
                    max_y = max(max_y, ent.origin[1]+sy)
                    ent.draw()
            left += max_x
            max_x = 0
            if left >= self.width:
                left = 0
                top += max_y
            glMatrixMode(GL_MODELVIEW)
            glPopMatrix()

        if self.pathtree:
            self.pathtree.draw()

        for h in self.hud:
            # Update alpha values of active modes
            space = frame.spaces[h.index[0]]
            for i in range(len(frame.automata[h.index[1]].ordered_modes)):
                if space.valuations[h.index[1]][h.index[2]].active_modes & (1 << i):
                    h.colors[i][3] = 1.0
                else:
                    h.colors[i][3] -= 0.01
                    if h.colors[i][3] < 0.0:
                        h.colors[i][3] = 0.0

            h.draw()

        if self.menu.active:
            self.menu.draw()

        # Swap buffers
        glutSwapBuffers()

    def load_hud(self, world, s, a, i, color):
        h = Hud(s, a, i)

        for j in range(0, len(world.automata[a].ordered_modes)):
            h.text.append(world.automata[a].ordered_modes[j].name)
            new_color = color[:]
            if world.spaces[s].valuations[a][i].active_modes & (1 << j) > 0:
                new_color[3] = 1.0
            else:
                new_color[3] = 0.0
            h.colors.append(new_color)
        self.hud.append(h)

    def load_ents(self, world, space_id):
        """
        For each ent i, rect for each collider j is loaded and added to
        instance of Entity class.
        :param world: World instance from interpreter to load from
        :return:
        """
        # For each automata, create an Entity instance with initial origin for
        # automata
        space = world.spaces[space_id]
        if space_id not in self.ents:
            self.ents[space_id] = []
        for a in range(0, len(space.valuations)):
            self.ents[space_id].append([])
            for i in range(0, len(space.valuations[a])):
                new_ent = Entity()
                new_ent.origin = [
                    space.valuations[a][i].get_var('x'),
                    space.valuations[a][i].get_var('y'),
                    0
                ]
                new_ent.id = self.ent_count
                self.ent_count += 1

                # For each collider, append one list of [X, Y, Z] and one list
                # of [R, G, B] to Entity.colors
                for c in range(0, len(world.automata[a][3])):
                    x = world.automata[a][3][c].shape[0].value
                    y = world.automata[a][3][c].shape[1].value
                    w = world.automata[a][3][c].shape[2].value
                    h = world.automata[a][3][c].shape[3].value
                    new_ent.verts.append([(x, y, 0.5),
                                          (x + w, y, 0.5),
                                          (x + w, y - h, 0.5),
                                          (x, y - h, 0.5)])
                    new_ent.colors.append([random.randint(3, 10) / 10.0,
                                           random.randint(3, 10) / 10.0,
                                           random.randint(3, 10) / 10.0,
                                           1.0])
                self.load_hud(world, space_id, a, i, new_ent.colors[0])
                self.ents[space_id][a].append(new_ent)

        for i in range(0, len(self.hud)):
            self.hud[i].origin = [
                (self.width - 100) - i * 100,
                self.height - 30]

    def load_tilemap(self, world, space_id):
        """
        For each tilemap (tm) i, calculate tiles as individual rects and load into Entity class
        :param world: World instance from interpreter to load from
        :return:
        """
        new_tm = Entity()
        new_tm.id = self.ent_count
        self.ent_count += 1
        space = world.spaces[space_id]
        if space_id not in self.tilemaps:
            self.tilemaps[space_id] = []
        for t in space.static_colliders:
            color = [random.randint(3, 10) / 10.0,
                     random.randint(3, 10) / 10.0,
                     random.randint(3, 10) / 10.0,
                     1.0]
            tile_w = t.shape.tile_width
            tile_h = t.shape.tile_height
            map_h = len(t.shape.tiles) * tile_h
            for i in range(0, len(t.shape.tiles)):
                for j in range(0, len(t.shape.tiles[i])):
                    if t.shape.tiles[i][j] is not 0:
                        new_tm.verts.append([(tile_w * j, map_h - tile_h * i, 0.5),
                                             (tile_w * j + tile_w,
                                              map_h - tile_h * i, 0.5),
                                             (tile_w * j + tile_w, map_h -
                                              (tile_h * i + tile_h), 0.5),
                                             (tile_w * j, map_h - (tile_h * i + tile_h), 0.5)])
                        new_tm.colors.append(color)
            self.tilemaps[space_id].append(new_tm)

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
            for s in world.spaces.keys():
                self.load_ents(world, s)
                self.load_tilemap(world, s)
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


    def get_dims(self):
        max_x = 0
        max_y = 0
        for i in range(0, len(self.colors)):
            for v in self.verts[i]:
                max_x = max(max_x, v[0])
                max_y = max(max_y, v[1])
        return (max_x, max_y)


    # TODO: Currently using deprecated drawing, implement vertex arrays and
    # buffers
    def draw(self):
        assert self.verts
        glMatrixMode(GL_MODELVIEW)
        glPushMatrix()
        glTranslate(*self.origin)

        glBegin(GL_QUADS)
        for i in range(0, len(self.colors)):
            glColor4f(*self.colors[i])
            for v in self.verts[i]:
                glVertex3f(*v)
        glEnd()
        glPopMatrix()


class Hud(object):
    """
    Describes HUD object in the engine
    """
    __slots__ = ["id", "index", "origin", "spacing", "font", "text", "colors"]

    def __init__(self, s, a, i, x=None, y=None):
        self.id = None
        self.index = [s, a, i]
        self.origin = [x, y]
        self.font = fonts.GLUT_BITMAP_HELVETICA_18
        self.spacing = 12  # glutBitmapHeight(self.font)
        self.text = []
        self.colors = []

    # TODO: Currently using deprecated drawing, implement vertex arrays and
    # buffers
    def draw(self):
        for i in range(0, len(self.text)):
            glColor4f(*self.colors[i])
            glRasterPos3f(self.origin[0],
                          self.origin[1] - (i * self.spacing), 0.7)
            for str in self.text[i]:
                for char in str:
                    glutBitmapCharacter(self.font, ord(char))


class PathTree(object):
    __slots__ = ["color", "width", "paths", "tree", "ptsize", "node"]

    def __init__(self, tree, pathcolor=(1.0, 0.0, 0.0, 0.5), width=2.5,
                 goalcolor=(0.0, 1.0, 0.0, 0.5), ptsize=10.0):
        self.color = [pathcolor, goalcolor]
        self.width = width
        self.tree = tree
        self.ptsize = ptsize
        self.node = []

    def check(self, x, y):
        for dx in range(-5, 5):
            for dy in range(-5, 5):
                pos = str([x + dx, y + dy])
                if pos in self.tree.nodes:
                    # print "True"
                    # print self.tree.nodes
                    node = self.tree.nodes[pos]
                    origin = [node.origin[0], node.origin[1], 0.8]
                    action = str(node.action)
                    self.node = [origin, action]

    def draw(self):
        for p in self.tree.paths:
            glColor4f(*self.color[0])
            glLineWidth(self.width)
            glBegin(GL_LINES)
            glVertex3f(*p[0])
            glVertex3f(*p[1])
            glEnd()

            glColor4f(*self.color[1])
            glPointSize(self.ptsize)
            glBegin(GL_POINTS)
            glVertex3f(*p[0])
            glVertex3f(*p[1])
            glEnd()

        if self.tree.goal['x'] > -1 and self.tree.goal['y'] > -1:
            glColor4f(*self.color[1])
            glPointSize(self.ptsize)
            glBegin(GL_POINTS)
            glVertex3f(self.tree.goal['x'],
                       self.tree.goal['y'], self.tree.goal['z'])
            glEnd()

        if self.node:
            glColor4f(1.0, 1.0, 1.0, 1.0)
            glRasterPos3f(*self.node[0])
            for c in self.node[1]:
                glutBitmapCharacter(fonts.GLUT_BITMAP_HELVETICA_12, ord(c))

        glLoadIdentity()


class Menu(object):
    __slots__ = ["id", "active", "origin", "spacing",
                 "font", "content", "width", "height"]

    def __init__(self, content=None, font=fonts.GLUT_BITMAP_HELVETICA_12):
        self.id = None
        self.active = False
        self.origin = [0, 0]
        self.font = font
        self.content = content
        self.spacing = 12  # glutBitmapHeight(self.font)
        if self.content:
            self.height = self.spacing * len(content)
            max_w = 100
            for c in self.content:
                if c.width > max_w:
                    max_w = c.width
            self.width = max_w
        else:
            self.width = 100
            self.height = 100

    def create_SubMenu(self, content):
        pass

    def check(self, x, y):
        if self.origin[0] <= x <= self.origin[0] + self.width and \
           self.origin[1] - self.height <= y <= self.origin[1]:
            return True
        return False

    def draw(self):
        glColor4f(1.0, 1.0, 1.0, 1.0)
        for i in range(0, len(self.content)):
            glRasterPos3f(
                self.origin[0], self.origin[1] - ((i + 1) * self.height), 0.8)
            self.content[i].draw()
        glColor4f(0.5, 0.5, 0.5, 0.8)
        glBegin(GL_QUADS)
        glVertex3f(self.origin[0], self.origin[1], 0.7)
        glVertex3f(self.origin[0] + self.width, self.origin[1], 0.7)
        glVertex3f(self.origin[0] + self.width, self.origin[1] - 100.0, 0.7)
        glVertex3f(self.origin[0], self.origin[1] - 100.0, 0.6)
        glEnd()


class SubMenu(Menu):
    def __init__(self, content):
        Menu.__init__(self)
        self.content = content
        self.width = glutBitmapLength(
            self.font, (ctypes.c_ubyte * len(content)).from_buffer_copy(content))

    def draw(self):
        for c in self.content:
            glutBitmapCharacter(self.font, ord(c))
