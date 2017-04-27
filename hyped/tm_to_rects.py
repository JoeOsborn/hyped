import interpreter as itp
import numpy as np


def aggregate_rect(tm, x, y, marked):
    h, w = marked.shape
    types = tm.tile_types(x, y)
    # expand rightwards while xi < w and types same
    # then expand downwards while every x in x0...xmax in that row has same
    # type
    rw = 0
    rh = 0
    while x + rw < w and tm.tile_types(x + rw, y) == types:
        marked[y, x + rw] = 1
        rw += 1
    row_ok = True
    while y + rh < h and row_ok:
        for xi in range(x, x + rw):
            if tm.tile_types(xi, y + rh) != types:
                row_ok = False
        if row_ok:
            marked[y + rh, x:x + rw] = 1
            rh += 1
    return (x, y, rw, rh, types)


def tm_to_rects(tm):
    # Flood fill rectangles for each contiguous block of the same _collider_
    # types.  Bias towards wider, shorter rects.
    w = len(tm.tiles[0])
    h = len(tm.tiles)
    x = 0
    y = 0
    rects = []
    marked = np.zeros(shape=(h, w))
    while y < h:
        x = 0
        while x < w:
            print x, y, w, h
            if marked[y, x]:
                x += 1
                continue
            rects.append(aggregate_rect(tm, x, y, marked))
            print "Found rect:", rects[-1]
            x += rects[-1][2]
        y += 1
    return filter(lambda r: r[-1] != 0, rects)


if __name__ == "__main__":
    world = itp.load_test_plan()
    print tm_to_rects(world.spaces["0"].static_colliders[0].shape)
