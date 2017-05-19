import hyped.interpreter as interpreter
import hyped.local_planner as lp
import hyped.rrt as rrt


class Planner(object):
    __slots__ = ["goal", "nodes"]

    def __init__(self, config):
        x, y = config.get('Planner', 'goal')
        self.goal = {'x': x, 'y': y, 'z': 0.6}
        self.nodes = []

    def plan(self):
        # Choose a node to grow

        # Grow node according to algorithm

        # Append node
        pass

    def choose(self):
        # Select node from nodes according to type

        # Return selected node
        pass

    def append(self, node):
        # Take node and append to nodes according to type
        pass

