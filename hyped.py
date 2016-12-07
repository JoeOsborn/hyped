import xmlparser as xml
import schema as h

automaton = xml.parse_automaton("resources/flappy.char.xml")

# Now, we could transform automaton into some more efficiently
# executable formalism, or we could try to interpret it directly, or
# we could translate it to C, or whatever.  Let's just do some
# experiments with flappy bird simulation in the absence of
# collisions.


def initial_group_tree(groups, stack=[]):
    t = []
    # for each group, start with its first thing
    for i, g in enumerate(groups) or []:
        stackHere = stack + [i]
        t.append((stackHere,
                  initial_group_tree(g.modes[0].groups, stackHere)))
    return t


valuation = {"groupTree": initial_group_tree(automaton.groups),
             "parameters": {p.name: p.value.value
                            for p in automaton.parameters},
             "variables": {v.name: v.init.value
                           for v in automaton.variables}}

theories = {"input": {"pressed": set(),
                      "on": set(),
                      "released": set()},
            "collision": {}}



def input_theory_update(aut, val, theories, buttons):
    inth = theories["input"]
    # update on, off, pressed, released accordingly
    buttons = set(buttons)
    # clear pressed and released
    inth["pressed"].clear()
    inth["released"].clear()
    # move ON to RELEASED if not in buttons
    for b in inth["on"]:
        if not (b in buttons):
            inth["on"].remove(b)
            inth["released"].add(b)
    # put new buttons into PRESSED and ON
    for b in buttons:
        inth["pressed"].add(b)
        inth["on"].add(b)


def collision_theory_update(aut, val, theories):
    pass


def discrete_step(aut, val, theories):
    pass


def continuous_step(aut, val, theories):
    pass


for step in [(5, []), (5, ["flap"]), (5, [])]:
    for i in range(step[0]):
        input_theory_update(automaton,
                            valuation,
                            theories,
                            step[1])
        discrete_step(automaton, valuation, theories)
        continuous_step(automaton, valuation, theories)
        collision_theory_update(automaton,
                                valuation,
                                theories)
    # collect positions and graph
