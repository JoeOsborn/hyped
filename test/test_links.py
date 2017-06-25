import hyped.interpreter as itp
import hyped.xmlparser as xml
import unittest


class TestLinks(unittest.TestCase):

    def test_follow_basic(self):
        automata = [xml.parse_automaton("resources/mario.char.xml")]
        tm = itp.TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                         [[1, 1, 1, 1, 1, 1],
                          [1, 0, 0, 0, 0, 1],
                          [1, 0, 0, 0, 0, 1],
                          [1, 0, 0, 0, 0, 1],
                          [1, 0, 0, 0, 0, 1],
                          [1, 0, 0, 0, 0, 2],
                          [1, 1, 1, 1, 1, 1]])

        tm2 = itp.TileMap(32, 32, [set(), set(["wall"]), set(["teleporter"])],
                          [[1, 1, 1, 1, 1, 1],
                           [1, 1, 0, 0, 0, 1],
                           [1, 1, 0, 0, 0, 1],
                           [1, 1, 0, 0, 0, 1],
                           [1, 1, 0, 0, 0, 1],
                           [2, 0, 0, 0, 0, 1],
                           [1, 1, 1, 1, 1, 1]])
        w = itp.World(automata, itp.Context(
            blocking_types={"body": ["wall", "body"]},
            touching_types={"wall": ["wall"]},
            spaces={
                "0": itp.ContextSpace(
                    static_colliders=[
                        itp.Collider(
                            "map",
                            set(["wall", "teleporter"]),
                            True, True,
                            tm,
                            0, 0, 0, 0)
                    ],
                    initial_automata=[(automata[0].name, {},
                                       {"x": 5 * 32 - 1, "y": 64})],
                    links=[((5 * 32, 32, 32, 32), "1", (1 * 32, 32, 32, 32))]
                ),
                "1": itp.ContextSpace(
                    static_colliders=[
                        itp.Collider(
                            "map",
                            set(["wall", "teleporter"]),
                            True, True,
                            tm2,
                            0, 0, 0, 0)
                    ],
                    initial_automata=[],
                    links=[((0 * 32, 32, 32, 32), "0", (4 * 32, 32, 32, 32))]
                )
            }
        ))
        # assert mario goes right into space1 then back left into space0
        dt = 1.0 / 60.0
        self.assertTrue(w.is_active_entity(0, 0, 0))
        self.assertFalse(w.is_active_entity(1, 0, 0))
        for i in range(0, 5):
            itp.step(w, ["right"], dt)
        self.assertFalse(w.is_active_entity(0, 0, 0))
        self.assertTrue(w.is_active_entity(1, 0, 0))
        for i in range(0, 5):
            itp.step(w, ["right"], dt)
        self.assertFalse(w.is_active_entity(0, 0, 0))
        self.assertTrue(w.is_active_entity(1, 0, 0))
        for i in range(0, 25):
            itp.step(w, ["left"], dt)
        self.assertTrue(w.is_active_entity(0, 0, 0))
        self.assertFalse(w.is_active_entity(1, 0, 0))


if __name__ == '__main__':
    unittest.main()
