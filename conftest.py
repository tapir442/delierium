"""Doctests of the modules (testpaths src/delierium): the optional
visualization module only with matplotlib installed (pip install
delierium[plot])."""

import importlib.util

collect_ignore = (
    [] if importlib.util.find_spec("matplotlib") else ["src/delierium/visualization.py"]
)
