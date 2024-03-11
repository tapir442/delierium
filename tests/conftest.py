import pytest
import sys
sys.path.insert (0, "../delierium")
import delierium.matrix_order as M
from sage.all import *

@pytest.fixture
def context_x_y_w_z ():
    var ("x y")
    w = function ("w")(x,y)
    z = function ("z")(x,y)
    ctx = M.Context ((w, z), (x,y))
    return ctx

@pytest.fixture
def context_x_y_z_u_v_w ():
    var ("x y z")
    u = function ("u")(x,y,z)
    v = function ("v")(x,y,z)
    w = function ("w")(x,y,z)
    ctx = M.Context ((u,v,w), (x,y,z))
    return ctx

@pytest.fixture
def system_2_24():
    vars = var ("x y")
    z = function("z")(x,y)
    w = function("w")(x,y)
    f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
    f2 = diff(z,x,y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
    f3 = diff(w, x,y) - 2*x*diff(z, x,2)/y - x*diff(w,x)/y**2
    f4 = diff(w, x,y) + diff(z, x,y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
    f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)
    return vars, [w,z], [f4,f2,f1,f5,f3]
