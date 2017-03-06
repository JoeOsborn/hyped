from interpreter import Collider, Rect


class QuadTree(object):
    __slots__ = ["node_capacity", "boundary", "colliders", "nw", "ne", "sw", "se"]

    def __init__(self, node_capacity, boundary):
        self.node_capacity = node_capacity
        self.boundary = boundary
        self.colliders = []
        self.nw = None
        self.ne = None
        self.sw = None
        self.se = None

    def insert(self, collider):
        assert isinstance(collider.shape, Rect)
        if not self.boundary.contains(collider):
            return False
        if len(self.colliders) < self.node_capacity and not self.nw:
            self.colliders.append(collider)
            return True
        if not self.nw:
            self.subdivide()
            self.insert(collider)
        elif self.nw.insert(collider) or self.ne.insert(collider) or \
                self.sw.insert(collider) or self.se.insert(collider):
            return True
        else:
            return False

    def subdivide(self):
        hw, hh = int(self.boundary.shape.w / 2.0), int(self.boundary.shape.h / 2.0)
        x1, y1 = self.boundary.nx, self.boundary.ny
        x2, y2 = x1 + hw, y1 - hh
        self.nw = QuadTree(self.node_capacity, Collider(shape=Rect(hw, hh), nx=x1, ny=y1))
        self.ne = QuadTree(self.node_capacity, Collider(shape=Rect(hw, hh), nx=x2, ny=y1))
        self.sw = QuadTree(self.node_capacity, Collider(shape=Rect(hw, hh), nx=x1, ny=y2))
        self.se = QuadTree(self.node_capacity, Collider(shape=Rect(hw, hh), nx=x2, ny=y2))
        while len(self.colliders) > 0:
            if self.nw.insert(self.colliders[0]) or self.ne.insert(self.colliders[0]) or \
               self.sw.insert(self.colliders[0]) or self.se.insert(self.colliders[0]):
                del self.colliders[0]
            else:
                print "Subdivision Insert Error."
                return
        self.colliders = []

    def update(self):
        for c in self.colliders:
            if not self.boundary.contains(c):
                pass

    def __str__(self):
        x, y = self.boundary.nx, self.boundary.ny
        w, h = self.boundary.shape.w, self.boundary.shape.h
        res = "(" + str(x) + "," + str(y) + ")"
        res += ": (" + str(x+w) + "," + str(y-h) + ")\n"
        for c in self.colliders:
            res += "\t\t(" + str(c.nx) + ", " + str(c.ny) + ") : Rect(" + str(c.shape.w) + ", " + str(c.shape.h) + ")"
        if self.nw:
            res += "\n\t" + str(self.nw)
            res += "\n\t" + str(self.ne)
            res += "\n\t" + str(self.sw)
            res += "\n\t" + str(self.se)
        return res

if __name__ == "__main__":
    a = Collider(shape=Rect(1, 1), nx=1, ny=1)
    b = Collider(shape=Rect(2, 2), nx=6, ny=8)
    c = Collider(shape=Rect(3, 3), nx=6, ny=4)
    q = QuadTree(2, Collider(shape=Rect(10, 10), nx=0, ny=10))
    q.insert(a)
    q.insert(b)
    q.insert(c)
    print q
    c.ny = 8
    print q
