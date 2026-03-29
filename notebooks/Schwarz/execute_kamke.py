import sys
sys.path.append("../../")
from sympy import *
from sympy.core.backend import *

from delierium.Infinitesimals import overdeterminedSystemODE, Janet_Basis_from_ODE
from delierium.helpers import ltf
from delierium.matrix_order import Mgrevlex, Mgrlex, Mlex

import pathlib
import importlib


init_printing()

p = pathlib.Path("../../kamke-test-suite")

def execute_kamke(chapter, equation, path=pathlib.Path("/home/tapir/research-disk/delierium/kamke-test-suite"), sort_order=Mgrevlex):
    sys.path.insert(0, path.absolute())
    import test_kamke
    x = Symbol('x')
    y = Function('y')(x)
    ode = (getattr(test_kamke.Kamke, chapter))[equation]
    ode = ode.xreplace({test_kamke.x: x, test_kamke.y(x): y})
    print(f"{ode=}")
    inf =  {x:r"\xi", y:r"\eta"}
    infs = overdeterminedSystemODE(ode, y, x, infinitesimals=inf)
    print("Determining equations")
    for _ in infs:
        ltf(_, [y], [x])
    k = Janet_Basis_from_ODE(ode, y, x, sort_order=sort_order, infinitesimals=inf)
    print("Janet Basis")
    for _ in k:
        print(_.show())
    for _ in k: 
        print(_.Lterm())