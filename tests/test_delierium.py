from sympy import *

from delierium.helpers import is_derivative

def testDelieriumFunction():
    x = symbols('x')
    u = Function ("u")(x)
    d = diff(u,x)
    assert is_derivative(d)
    assert not is_derivative(u)
