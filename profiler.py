import pstats
import profile
import cProfile
import engine

import logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(funcName)s: %(message)s')


def run_profile():
    profile.run("engine.test()", "hyped.stats")
    stats = pstats.Stats("hyped.stats")
    stats.sort_stats('tottime')
    stats.print_stats()


def run_cprofile():
    cProfile.run("engine.test()", "hyped.pstat")
    stats = pstats.Stats("hyped.pstat")
    stats.strip_dirs()
    stats.sort_stats('tottime')
    stats.print_stats()

if __name__ == "__main__":
    #run_profile()
    run_cprofile()
