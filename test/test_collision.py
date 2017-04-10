import hyped.interpreter as itp
import unittest


class TestCollisions(unittest.TestCase):

    def test_ha_ha(self):
        tmax = 360
        x0 = 16.0
        y0 = 200
        w = itp.load_test(["mario.char.xml", "moving_platform_vert.char.xml"],
                          None,
                          [("mario", {}, {"x": x0,
                                          "y": y0}),
                           ("moving_platform_vert",
                            {"down_to_up_y": y0 - 100,
                             "up_to_down_y": y0 + 0},
                            {"x": 0,
                             "y": y0 - 34})])
        # assert mario goes down for a while then up for a while and
        # then down for a while and x stays the same
        dt = 1.0 / 60.0
        state = "downwards"
        yp = y0
        space = w.spaces["0"]
        for t in range(0, tmax):
            itp.step(w, [], dt)
            self.assertEqual(space.valuations[0][0].get_var("x"), x0)
            y = space.valuations[0][0].get_var("y")
            plat_y = space.valuations[1][0].get_var("y")
            if y > yp and state == "downwards":
                self.assertLessEqual(
                    plat_y,
                    space.valuations[1][0].get_param("down_to_up_y") + 1
                )
                state = "upwards"
            if y < yp and state == "upwards":
                self.assertGreaterEqual(
                    plat_y,
                    space.valuations[1][0].get_param("up_to_down_y") - 1
                )
                state = "downwards"
            if state == "downwards":
                self.assertLessEqual(y, yp)
            if state == "upwards":
                self.assertGreaterEqual(y, yp)
            # fudge the threshold a little bit to simplify
            # the test; Mario starts a couple pixels above the platform.
            self.assertLessEqual(abs(y - plat_y), 32 + 3)
            yp = y

    def test_mario_grounding(self):
        tmax = 30
        x0 = 16.0
        y0 = 200
        w = itp.load_test(["mario.char.xml", "moving_platform_vert.char.xml"],
                          None,
                          [("mario", {}, {"x": x0,
                                          "y": y0}),
                           ("moving_platform_vert",
                            {"down_to_up_y": y0 - 100,
                             "up_to_down_y": y0 + 0},
                            {"x": 0,
                             "y": y0 - 34})])
        space = w.spaces["0"]
        # assert mario goes down for a while then up for a while and
        # then down for a while and x stays the same
        dt = 1.0 / 60.0
        state = "not_touched"  # or touched
        print w.automata[0].ordered_modes[4].name
        groundMask = 1 << 4
        for t in range(0, tmax):
            itp.step(w, [], dt)
            self.assertEqual(space.valuations[0][0].get_var("x"), x0)
            if state == "touched":
                self.assertEqual(len(space.contacts), 1)
                self.assertTrue(space.valuations[0][0].active_modes & groundMask)
            if len(space.contacts) >= 1:
                state = "touched"


if __name__ == '__main__':
    unittest.main()
