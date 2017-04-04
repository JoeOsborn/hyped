import os
from setuptools import setup

# Utility function to read the README file.
# Used for the long_description.  It's nice, because now 1) we have a top level
# README file and 2) it's easier to type in the README file than to put a raw
# string in below ...


def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()


setup(
    name="HyPED",
    version="0.0.2",
    author="Joseph Osborn, Brian Lambrigger, Calvin Walantus",
    author_email="jcosborn@ucsc.edu",
    description=("Hybrid automata-based game character modeling"),
    license="MIT",
    # keywords="example documentation tutorial",
    url="https://github.com/JoeOsborn/hyped",
    packages=['hyped'],
    install_requires=[
        'numpy',
        'scipy',
        'sympy',
        'pyopengl',
        'PyOpenGL_accelerate',
        'vectormath',
        'defusedxml',
        'matplotlib'
    ],
    long_description=read('README'),
    classifiers=[
        "Development Status :: 3 - Alpha",
        # "Topic :: Utilities",
        "License :: OSI Approved :: MIT License",
    ],
)
