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
                 "tilemaps", "hud", "trees", "menu"]

    def __init__(self, config):
        self.window = None
        self.fullscreen = False
        if config.get('Graphics', 'fullscreen').lower() == "true":
            self.fullscreen = True
        self.width = int(config.get('Graphics', 'width'))
        self.height = int(config.get('Graphics', 'height'))
        self.ents = {}
        self.ent_count = 0
        self.tilemaps = {}
        self.hud = []
        self.trees = []
        #if rrt: rrt.append_path = self.pathtree.append_path
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
                max_x = max(max_x, t.origin[0] + sx)
                max_y = max(max_y, t.origin[1] + sy)
                t.draw()
            for a in range(0, len(ents)):
                for vi in range(frame.context.val_limit):
                    ent = self.ents[sid][a][vi]
                    old_active = ent.is_active
                    new_active = frame.is_active_entity(
                        frame.space_ordering[sid], a, vi)
                    if new_active and not old_active:
                        self.load_hud(frame, sid, a, vi, ent.colors[0])
                    elif old_active and not new_active:
                        self.remove_hud(sid, a, vi)
                    if new_active:
                        ent.origin = [
                            frame.get_val_var(sid, a, vi, "x"),
                            frame.get_val_var(sid, a, vi, "y"),
                            0
                        ]
                        sx, sy = ent.get_dims()
                        max_x = max(max_x, ent.origin[0] + sx)
                        max_y = max(max_y, ent.origin[1] + sy)
                        ent.draw()
                    self.ents[sid][a][vi].is_active = new_active
            left += max_x
            max_x = 0
            if left >= self.width:
                left = 0
                top += max_y
            glMatrixMode(GL_MODELVIEW)
            glPopMatrix()

        for tree in self.trees:
            tree.draw()

        self.reposition_hud()

        for h in self.hud:
            # Update alpha values of active modes
            for i in range(len(frame.automata[h.index[1]].ordered_modes)):
                if frame.get_val_active_modes(h.index[0], h.index[1], h.index[2]) & (1 << i):
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
        h = Hud(world.automata[a].name, s, a, i)

        for j in range(len(world.automata[a].ordered_modes)):
            h.text.append(world.automata[a].ordered_modes[j].name)
            new_color = color[:]
            if world.get_val_active_modes(s, a, i) & (1 << j) > 0:
                new_color[3] = 1.0
            else:
                new_color[3] = 0.0
            h.colors.append(new_color)
        self.hud.append(h)

    def remove_hud(self, s, a, i):
        for idx in range(0, len(self.hud)):
            if self.hud[idx].index == (s, a, i):
                del self.hud[idx]
                return

    def load_ent(self, world, sid, a, i):
        new_ent = Entity()
        new_ent.origin = [
            world.get_val_var(sid, a, i, "x"),
            world.get_val_var(sid, a, i, "y"),
            0
        ]
        new_ent.id = self.ent_count
        self.ent_count += 1

        # For each collider, append one list of [X, Y, Z] and one list
        # of [R, G, B] to Entity.colors
        for c in range(len(world.automata[a].colliders)):
            x = world.automata[a].colliders[c].shape[0].value
            y = world.automata[a].colliders[c].shape[1].value
            w = world.automata[a].colliders[c].shape[2].value
            h = world.automata[a].colliders[c].shape[3].value
            new_ent.verts.append([(x, y, 0.5),
                                  (x + w, y, 0.5),
                                  (x + w, y - h, 0.5),
                                  (x, y - h, 0.5)])
            new_ent.colors.append([random.randint(3, 10) / 10.0,
                                   random.randint(3, 10) / 10.0,
                                   random.randint(3, 10) / 10.0,
                                   1.0])
        self.ents[sid][a][i] = new_ent
        if world.is_active_entity(world.space_ordering[sid], a, i):
            new_ent.is_active = True
            self.load_hud(world, sid, a, i, new_ent.colors[0])
        return new_ent

    def load_ents(self, world, space_id):
        """
        For each ent i, rect for each collider j is loaded and added to
        instance of Entity class.
        :param world: World instance from interpreter to load from
        :return:
        """
        # For each automata, create an Entity instance with initial origin for
        # automata
        self.ents[space_id] = []
        for a in range(len(world.automata)):
            self.ents[space_id].append([None] * world.context.val_limit)
            for i in range(world.context.val_limit):
                self.load_ent(world, space_id, a, i)
        self.reposition_hud()

    def reposition_hud(self):
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
        new_tm.is_active = True
        new_tm.id = self.ent_count
        self.ent_count += 1
        if space_id not in self.tilemaps:
            self.tilemaps[space_id] = []
        for t in world.static_colliders[world.space_ordering[space_id]]:
            colors = []
            for val in {x for x in t.shape.tile_defs}:
                colors.append([random.randint(3, 10) / 10.0,
                               random.randint(3, 10) / 10.0,
                               random.randint(3, 10) / 10.0,
                               1.0])
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
                        new_tm.colors.append(colors[t.shape.tiles[i][j]])
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
            for s in world.space_ordering.keys():
                self.load_ents(world, s)
                self.load_tilemap(world, s)
        self.init_gl()


class Entity(object):
    """
    Describes graphical objects in the engine
    """
    __slots__ = ["id", "name", "origin", "verts", "colors", "is_active"]

    def __init__(self):
        self.id = None
        self.name = None
        self.origin = [0, 0, 0]
        self.verts = []
        self.colors = []
        self.is_active = False

    def get_dims(self):
        max_x = 0
        max_y = 0
        for i in range(0, len(self.colors)):
            for v in self.verts[i]:
                max_x = max(max_x, v[0])
                max_y = max(max_y, v[1])
        return (max_x, max_y)

    def draw(self):
        if not self.is_active:
            return
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

    def __init__(self, id, s, a, i, x=None, y=None):
        self.id = "[" + str(a) + "," + str(i) + "]"
        self.index = (s, a, i)
        self.origin = [x, y]
        self.font = fonts.GLUT_BITMAP_HELVETICA_18
        self.spacing = 20  # glutBitmapHeight(self.font)
        self.text = []
        self.colors = []

    # TODO: Currently using deprecated drawing, implement vertex arrays and
    # buffers
    def draw(self):
        glColor4f(self.colors[0][0], self.colors[0][1], self.colors[0][2], 1.0)
        glRasterPos3f(self.origin[0],
                      self.origin[1], 0.7)
        for str in self.id:
            for char in str:
                glutBitmapCharacter(self.font, ord(char))

        for i in range(0, len(self.text)):
            glColor4f(*self.colors[i])
            glRasterPos3f(self.origin[0],
                          self.origin[1] - ((i + 1) * self.spacing), 0.7)
            for str in self.text[i]:
                for char in str:
                    glutBitmapCharacter(self.font, ord(char))


def draw_line(self, p):
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


def calc_curve(t, n1, c, n2):
    u = 1.0 - t
    u2 = float(u**2)
    t2 = float(t**2)

    px = u2 * n1[0] + 2 * u * t * c[0] + t2 * n2[0]
    py = u2 * n1[1] + 2 * u * t * c[1] + t2 * n2[1]

    return px, py, 0.6


class PathTree(object):
    __slots__ = ["color", "width", "paths", "curves", "ptsize", "node"]

    def __init__(self, pathcolor=(1.0, 0.0, 0.0, 0.3), nodecolor=(0.0, 1.0, 0.0, 0.5),
                 width=2.5, ptsize=8.0):
        self.color = [pathcolor, nodecolor]
        self.paths = [[], []]
        self.curves = []
        self.width = width
        self.ptsize = ptsize
        self.node = []

    def check(self, x, y):
        for dx in range(-5, 5):
            for dy in range(-5, 5):
                #bucket = self.tree.nodes.query((x, y))
                bucket = None
                if bucket:
                    print bucket
                    node = bucket[0][1][0]
                    origin = node.get_origin()
                    origin[2] = 0.8
                    action = str(node.action)
                    self.node = [origin, action]
                    return node
                else:
                    self.node = []
                    return None

    def append_path(self, parent, child):
        parent_origin = (parent.spaces.values()[0].valuations[0][0].get_var("x"),
                         parent.spaces.values()[0].valuations[0][0].get_var("y"), 0.6)
        child_origin = (child.spaces.values()[0].valuations[0][0].get_var("x"),
                        child.spaces.values()[0].valuations[0][0].get_var("y"), 0.6)
        c = [(parent_origin[0] + child_origin[0]) / 2.0,
             (parent_origin[1] + child_origin[1]) / 2.0]
        if (child_origin[0] - parent_origin[0])**2 > (child_origin[1] - parent_origin[1])**2:
            c[1] += random.randint(-25, 25)
        else:
            c[0] += random.randint(-25, 25)
        points = [parent_origin]
        for t in [0.25, 0.5, 0.75]:
            points.append(calc_curve(t, parent_origin, c, child_origin))
        points.append(child_origin)
        for p in [parent_origin[0], child_origin[0]]:
            self.paths[0].append(p)
        for p in [parent_origin[1], child_origin[1]]:
            self.paths[1].append(p)
        self.curves.append(tuple(points))
        #self.paths.append((parent_origin, c, child_origin))

    def draw_curve(self, path):
        # points = [path[0]]
        # for t in [0.25, 0.5, 0.75]:
        #     points.append(calc_curve(t, *path))
        # points.append(path[2])

        glLineWidth(self.width)
        for ind in range(0, len(path) - 1):
            glColor4f(*(x + ind * 0.1 for x in self.color[0]))
            glBegin(GL_LINES)
            glVertex3f(*path[ind])
            glVertex3f(*path[ind + 1])
            glEnd()

        glColor4f(*self.color[1])
        glPointSize(self.ptsize)
        glBegin(GL_POINTS)
        glVertex3f(*path[0])
        glVertex3f(*path[4])
        glEnd()

    def draw(self):
        for p in self.curves:
            self.draw_curve(p)

        # if self.tree and self.tree.goal['x'] > -1 and self.tree.goal['y'] > -1:
        #     glColor4f(*self.color[1])
        #     glPointSize(self.ptsize)
        #     glBegin(GL_POINTS)
        #     glVertex3f(self.tree.goal['x'],
        #                self.tree.goal['y'], self.tree.goal['z'])
        #     glEnd()

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
