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
        for t in range(0, tmax):
            itp.step(w, [], dt)
            self.assertEqual(w.get_val_var("0", 0, 0, "x"), x0)
            y = w.get_val_var("0", 0, 0, "y")
            plat_y = w.get_val_var("0", 1, 0, "y")
            if y > yp and state == "downwards":
                self.assertLessEqual(
                    plat_y,
                    w.get_val_param("0", 1, 0, "down_to_up_y") + 1
                )
                state = "upwards"
            if y < yp and state == "upwards":
                self.assertGreaterEqual(
                    plat_y,
                    w.get_val_param("0", 1, 0, "up_to_down_y") - 1
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
        # assert mario goes down for a while then up for a while and
        # then down for a while and x stays the same
        dt = 1.0 / 60.0
        state = "not_touched"  # or touched
        ground_mode = [
            m
            for m in w.automata[0].ordered_modes
            if m.name == "ground"][0]
        ground_mask = 1 << ground_mode.index
        for t in range(0, tmax):
            itp.step(w, [], dt)
            self.assertEqual(w.get_val_var("0", 0, 0, "x"), x0)
            if state == "touched":
                self.assertEqual(len(w.contacts[0]), 1)
                self.assertTrue(
                    w.get_val_active_modes("0", 0, 0) & ground_mask
                )
            if len(w.contacts[0]) >= 1:
                state = "touched"

    def test_zelda_door(self):
        dt = 1.0 / 60.0
        w = itp.load_zelda()
        self.assertTrue(w.theories.collision.touching_typesets(
            w.colliders[1][0].types,
            w.colliders[1][1].types))
        self.assertTrue(len(w.contacts[1]) > 0)
        log = itp.TransitionLog()
        itp.step(w, [], dt, log)
        self.assertEqual(len(log.path[-1][1]), 0)

    def test_mario_instant_death(self):
        dt = 1.0 / 60.0
        w = itp.platformPlanning1()
        log = itp.TransitionLog()
        itp.step(w, [], dt, log)
        self.assertEqual(len(log.path[-1][1]), 0)
        itp.step(w, [], dt, log)
        self.assertEqual(len(log.path[-1][1]), 1)
        itp.step(w, [], dt, log)
        self.assertEqual(len(log.path[-1][1]), 0)


if __name__ == '__main__':
    unittest.main()
