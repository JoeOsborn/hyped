import schema as h
import interpreter as itp
import numpy as np
import random
import time
import math
import pomp.structures.nearestneighbors as neighb
import pomp.spaces.metric as metrics
import pomp.spaces.configurationspace as consp
import pomp.spaces.controlspace as ctrlsp

# Goal: Fast single threaded performance with lots of node expansions
# Aiming for at least 4K nodes/s

world = itp.load_test_plan()

# sample a config c in config space
# find nearest neighbor n to c
# sample a control for n (and remember we did this control for n already)
# apply control to n for n'
# if n' is not valid, continue
# else put n' into tree
# if n' is at the goal, finish

t0 = time.time()
t = t0
nc = 0


def sample(world, cont, disc):
    # TODO: use bounds analysis (simple and complex)
    cont[:] = np.random.uniform(0, 1000, size=cont.size)
    # TODO: use mode_combinations to preconfigure this
    disc[:] = disc
    return cont, disc


def sample_control(world):
    return random.choice([
        [],
        ["left"],
        ["right"],
        ["jump"],
        ["left", "jump"],
        ["right", "jump"]
    ])


def invalid(world):
    # TODO: fixme assumes player is val 0 in aut 0 in space 0
    # TODO: dead mode
    #modes = world.get_val_active_modes("0", 0, 0)
    posx = world.get_val_var("0", 0, 0, "x")
    posy = world.get_val_var("0", 0, 0, "y")
    return posx < 0 or posx > 640 or posy < 30 or posy > 640  # or modes contains dead


def at_goal(world):
    posx = world.get_val_var("0", 0, 0, "x")
    return posx > 400


nn = neighb.NearestNeighbors(
    metric=lambda a, b: metrics.L1Metric(a, b),
    # + metrics.L1Metric(a[1], b[1])
    method='sqrtforce'
)
s0 = world.store_to_hybrid_space()
nn.add(s0[0], s0)

dt = 1.0 / 60.0
config_templ_c, config_templ_d = (
    np.zeros_like(s0[0], dtype=np.float32),
    np.zeros_like(s0[1], dtype=np.int64)
)
pos_c = world.cvars.size / 3
limit = 20
goal = False
#cfgs = [s0]
maxx = 0
maxy = 0
steps = 10
while (t - t0) < limit:
    sample(world, config_templ_c[:pos_c], config_templ_d[:])
    if random.random() < 0.1:
        config_templ_c[0] = 400
    _nearest_proj, nearest = nn.nearest(config_templ_c[:pos_c])
    world.load_from_hybrid_space(np.copy(nearest[0]),
                                 np.copy(nearest[1]))
    ctrl = sample_control(world)
    for i in range(steps):
        itp.step(world, ctrl, dt)
    nc += 1
    if invalid(world):
        pass
    else:
        nextn = world.store_to_hybrid_space()
        nn.add(nextn[0][:pos_c], nextn)
        posx = world.get_val_var("0", 0, 0, "x")
        posy = world.get_val_var("0", 0, 0, "y")
        maxx = max(posx, maxx)
        maxy = max(posy, maxy)
        if not goal and at_goal(world):
            goal = True
            print("Reached goal at", t - t0, "nc", nc)
    t = time.time()

print nc, 'nodes', nc // (t - t0), "per second", "reach:", maxx, maxy

import matplotlib
import matplotlib.pyplot as plt
positions = map(lambda n: n[0][:2], nn.nodes)
xs, ys = zip(*positions)
print xs[0], ys[0]
plt.plot(xs, ys, '.')
plt.savefig("out.png")


# class HypedContinuousSpace(consp.GeodesicSpace):
#     pass

# class HypedDiscreteSpace(consp.ConfigurationSpace):
#     def __init__(self, world):
#         pass

#     def dimension(self):
#         """Returns the number of entries of a configuration"""
#         return self.world.modes.size

#     def intrinsicDimension(self):
#         """Returns the number of true degrees of freedom, which may be
#         less than dimension() if the representation is redundant."""
#         return self.dimension()

#     def sample(self):
#         """Sample a random configuration from the space"""
#         raise NotImplementedError("Do this")

#     def sampleNeighborhood(self,x,r):
#         # TODO: return up to r steps away in transition diagram??
#         return x

#     def feasible(self,x):
#         """Return true if the configuration is feasible"""
#         # TODO: return player is alive
#         return True

#     def contains(self,x):
#         return self.feasible(x)

#     def distance(self,a,b):
#         """A distance metric. Default uses euclidean distance"""
#         # TODO: use transition system distance
#         return metrics.L1Metric(a,b)

#     def interpolator(self,x,y):
#         raise NotImplementedError("Nonsense??")


# class HypedConfigurationSpace(consp.MultiConfigurationSpace):
#     def __init__(self, world):
#         super(HypedContinuousSpace(world), HypedDiscreteSpace(world))


# class HypedControlSpace (ctrlsp.ControlSpace):
#     """The control is u=(dt,ubase).  The integration duration dt is sampled from
#     the range [0,dtmax]."""
#     def __init__(self,cspace,dt=1./60.,dtmax=10./60.):
#         self.cspace = cspace
#         self.world = self.cspace.world
#         self.dt = dt
#         self.dtmax = dtmax
#     def configurationSpace(self):
#         return self.cspace
#     def controlSet(self,x):
#         # TODO: this one
#         available_controls = self.dspace.controlSet(x)
#         return consp.MultiSet(
#             consp.TimeBiasSet(self.dtmax,
#                               available_controls),
#             available_controls)
#     def trajectory(self,x,u):
#         duration = u[0]
#         ub = u[1:]
#         path = [x]
#         t = 0.0
#         self.world.load_from_hybrid_space(*x.components)
#         while t < duration:
#             dt = min(self.dt,duration-t)
#             itp.step(self.world,ub,dt)
#             path.append(self.world.store_to_hybrid_space())
#             t = min(t+self.dt,duration)
#         return path
#     def nextState(self,x,u):
#         return self.trajectory(x,u)[-1]
#     def interpolator(self,x,u):
#         raise NotImplementedError()
#     def connection(self,x,y):
#         return None


# confspace = HypedConfigurationSpace(world)
# contrspace = HypedControlSpace(confspace)

# First try: not using pomp except for nearestneighbors with compound L1 metric
