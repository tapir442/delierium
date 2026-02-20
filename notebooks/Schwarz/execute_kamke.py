import sys
import sympy as sp

from delierium.Infinitesimals import overdeterminedSystemODE, Janet_Basis_from_ODE
from delierium.helpers import ltf
from delierium.matrix_order import Mgrevlex, Mgrlex, Mlex

def execute_kamke(chapter, equation, path="../../kamke_test_suite", sort_order=Mgrevlex):
    sys.path.append(path)
    import test_kamke
    x = sp.Symbol('x')
    y = sp.Function('y')(x)
    ode = (getattr(test_kamke.Kamke, chapter))[equation]
    ode = ode.xreplace({test_kamke.x: x, test_kamke.y(x): y})
    infs = overdeterminedSystemODE(ode, [y], [x], infinitesimals={x:r"\xi", y:r"\eta"})
    for _ in infs:
        ltf(_, [y], [x])
    k = Janet_Basis_from_ODE(ode, [y], [x], sort_order=sort_order, infinitesimals={x:r"\xi", y:r"\eta"})
    for _ in k:
        ltf(_, [y], [x])