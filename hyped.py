import xmlparser as xml
import schema as h
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


automaton = xml.parse_automaton("resources/flappy.char.xml")


OK = "ok"


def ok_mode(m):
    if len(m.groups) > 1:
        return "Too many groups in a non-root mode for now!"
    assert isinstance(m, h.Mode)
    for e in m.edges:
        assert isinstance(e, h.Edge)
    return OK


def ok_automaton(aut):
    for gid, g in aut.groups.items():
        assert isinstance(g, h.Group)
        for mid, m in g.modes.items():
            status = ok_mode(m)
            if status != OK:
                return (g, m, status)
    return OK


assert ok_automaton(automaton) == OK


# Now, we could transform automaton into some more efficiently
# executable formalism, or we could try to interpret it directly, or
# we could translate it to C, or whatever.

# The object-oriented interpreter is a bit obvious but also makes it
# tedious to ensure certain invariants, and it requires lots of
# recursions and centralized control.  So it's a lot of ceremony.  For
# this interpreter, I'd like to explore an approach that would
# translate more easily to C or maybe take advantage of numpy.

# A valuation is a set of assignments to parameters and variables
# (which we will optimize later), along with an active set.  The obvious
# implementation of the active set would be as a set or a dict mapping
# qualified mode names to runtime data, or perhaps a tree of active
# groups and modes.  This requires lots of pointer chasing and
# reorganizing data structures, which is unnecessary given that the
# number of modes and groups in an automaton is small, fixed, and
# known a priori.  So we 


# TODO: new tree thing based on path -> whatever mapping.
# TODO: maybe make paths a class of a list, rather than
# grouppath/modepath classes with pointers.


class Valuation(object):
    __slots__ = ["active", "parameters", "variables"]

    def __init__(self, active, parameters, variables):
        self.active = active
        self.parameters = parameters
        self.variables = variables

    def enter_modes(self, ordered_modes):
        for om in ordered_modes:
            # do om's on-entry, then...
            self.active.enter_modes(ordered_modes)


valuation = Valuation(ActiveGroups(),
                      {pn: p.value.value
                       for pn, p in automaton.parameters.items()},
                      {vn: v.init.value
                       for vn, v in automaton.variables.items()})

valuation.enter_modes(h.initial_modes(automaton))

theories = {"input": {"pressed": set(),
                      "on": set(),
                      "released": set()},
            "collision": {}}


def input_theory_update(aut, val, theories, dt, buttons):
    inth = theories["input"]
    # update on, off, pressed, released accordingly
    buttons = set(buttons)
    # clear pressed and released
    inth["pressed"].clear()
    inth["released"].clear()
    # move ON to RELEASED if not in buttons
    for b in inth["on"]:
        if not (b in buttons):
            inth["released"].add(b)
    for b in inth["released"]:
        inth["on"].remove(b)
    # put new buttons into PRESSED and ON
    for b in buttons:
        inth["pressed"].add(b)
        inth["on"].add(b)


def all_active_modes(aut, tree):
    r = [t[0] for t in tree]
    for group in tree:
        r.extend(all_active_modes(aut, group[1]))
    return r


def get_mode(aut, stack):
    rootGroup, rootMode = stack[0]
    cur = aut.groups[rootGroup].modes[rootMode]
    for groupidx, modeidx in stack[1:]:
        cur = cur.groups[groupidx].modes[modeidx]
    return cur


def collision_theory_update(aut, val, theories, dt):
    pass


def eval_guard(aut, val, theories, guard):
    # TODO: Dispatch on guard type. for now say colliding is false but
    # do button and inmode for real.
    return False


def group_tree_drop(aut, gtree, group):
    # assuming only parallelism at the top level
    for gi, g in enumerate(gtree):
        # a group tree entry is a tuple of stack, child-entries
        # so we want to know if the GROUP of the BOTTOM of the
        # the STACK == group.  So, [0][0][0].
        if g[0][0][0] == group:
            del gtree[gi]
            return True
    return False


def group_tree_init(aut, gtree, new_stack, prefix=[]):
    # Assuming one group per non-root level.
    if len(new_stack) > len(prefix):
        prefix = prefix + [(new_stack[len(prefix)])]
        gtree.append((prefix, []))
        group_tree_init(aut, gtree[-1][1], new_stack, prefix)
    else:
        m = get_mode(aut, new_stack)
        gtree.extend(initial_group_tree(m.groups, prefix))


def discrete_step(aut, val, theories):
    available_edges = {}
    for stack in all_active_modes(aut, val.group_tree):
        rootGroup, _rootMode = stack[0]
        # transition each root group separately.  we have prior knowledge
        #  that groups are only at the top level for now.  so we can
        #  write a simpler discrete step function.
        if rootGroup in available_edges:
            # higher-up groups take precedence
            continue
        mode_def = get_mode(aut, stack)
        for e in mode_def.edges:
            ret = eval_guard(aut, val, theories, e.guard)
            if ret:
                update = {uk: eval_expr(aut, val, theories, uv) for
                          uk, uv in e.updates.items()}
                target = e.qualified_target
                available_edges[rootGroup] = (stack, ret, target, update)
                break
    for group, (stack, guard_ret, target, update) in available_edges.items():
        # drop all modes with stack as prefix from group tree (find
        # the parent and drop this child). then insert the new stack
        # at the right spot (find the parent and insert). note that
        # this may also close off parents of the original stack
        # entry...
        # so it would be better to just drop the whole group for now
        #  and remake it, given the assumption of only root
        #  parallelism above.
        print "TRANSITION", val.group_tree, group, target
        assert group_tree_drop(aut, val.group_tree, group)
        print "DROPPED", val.group_tree
        group_tree_init(aut, val.group_tree, target)
        print "ADDED", val.group_tree
        for uk, uv in update.items():
            val.variables[uk] = uv
        # TODO: joint transitions, etc


def eval_expr(aut, autval, val):
    if isinstance(val, h.ConstantExpr):
        return val.value
    elif isinstance(val, h.Parameter):
        return eval_expr(aut, autval, val.value)
    elif isinstance():
        pass


def continuous_step(aut, val, theories, dt):
    active_modes = all_active_modes(aut, val.group_tree)
    print "Active modes:", [get_mode(aut, stack).name for stack in active_modes]
    all_flows = {}
    for f in aut.flows.values():
        fvar = f.var
        fvalexpr = f.value
        fval = eval_expr(aut, val, fvalexpr)
        print "Default flow",fvar,fval
        all_flows[fvar.name] = ([], fvar, fval)
    for stack in active_modes:
        mode = get_mode(aut, stack)
        for f in mode.flows.values():
            fvar = f.var
            fvalexpr = f.value
            fval = eval_expr(aut, val, fvalexpr)
            if fvar.name in all_flows:
                print "Flow", (mode.name,fvar,fval), "clobbering",all_flows[fvar.name],"from",(get_mode(aut,all_flows[fvar.name][0]).name
                                                                           if
                                                                           len(all_flows[fvar.name][0])
                                                                           else "root")
            all_flows[fvar.name] = (stack, fvar, fval)
    #  update variables by flows (assuming no conflicts)
    # for each posn variable, ....
    vbls = aut.variables
    pos_vbls = [v for v in vbls.values() if v.degree == 0]
    for pos in pos_vbls:
        (_, vel, acc) = h.all_derivs(pos, vbls)
        val_pos = val.variables[pos.primed_name]
        val_vel = val.variables[vel.primed_name]
        val_acc = val.variables[acc.primed_name]
        # see if it's in the flow dict.
        if pos.name in all_flows:
            #  If so, update its vel or acc according to the flow, set any
            #  higher degrees to 0, and update lower degrees as above
            #  (acc->vel, vel->pos).
            (stack, fvar, fval) = all_flows[pos.name]
            if fvar.degree == 2:
                val_acc = fval
                val_vel = val_vel + val_acc * dt
                val_pos = val_pos + val_vel * dt
            elif fvar.degree == 1:
                val_acc = 0
                val_vel = fval
                val_pos = val_pos + val_vel * dt
            else:
                val_acc = 0
                val_vel = 0
                val_pos = fval
        else:
            #  If not, update its vel according to its acc and its pos
            #  according to its vel.
            # val_acc = val_acc
            val_vel = val_vel + val_acc * dt
            val_pos = val_pos + val_vel * dt
        # Note that implicit flows as above have a different semantics
        # to default flows like "y'' = gravity"!
        val.variables[pos.primed_name] = val_pos
        val.variables[vel.primed_name] = val_vel
        val.variables[acc.primed_name] = val_acc


# The below defines a discrete, fixed time step semantics.
# It would also be helpful to define an "event driven" semantics that
# calculates the next time any transition happens and do nothing until
# then.  Maybe do that with Z3?

dt = 1.0/60.0
history = []
for step in [(5, []), (5, ["flap"]), (5, [])]:
    for i in range(step[0]):
        input_theory_update(automaton,
                            valuation,
                            theories,
                            dt,
                            step[1])
        discrete_step(automaton, valuation, theories)
        continuous_step(automaton, valuation, theories, dt)
        collision_theory_update(automaton,
                                valuation,
                                theories,
                                dt)
        history.append(valuation.variables["y"])
# collect positions and graph
plt.plot(history)
plt.gca().invert_yaxis()
plt.savefig('ys')
print history
