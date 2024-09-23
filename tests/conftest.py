import sys

import pytest

import delierium.MatrixOrder as M
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
def context_x_y_w_z_mlex ():
    var ("x y")
    w = function ("w")(x,y)
    z = function ("z")(x,y)
    ctx = M.Context ((w, z), (x,y),  M.Mlex)
    return ctx

@pytest.fixture
def context_x_y_z_u_v_w_mlex ():
    var ("x y z")
    u = function ("u")(x,y,z)
    v = function ("v")(x,y,z)
    w = function ("w")(x,y,z)
    ctx = M.Context ((u,v,w), (x,y,z), M.Mlex)
    return ctx


@pytest.fixture
def context_x_y_w_z_mgrlex ():
    var ("x y")
    w = function ("w")(x,y)
    z = function ("z")(x,y)
    ctx = M.Context ((w, z), (x,y),  M.Mgrlex)
    return ctx

@pytest.fixture
def context_x_y_z_u_v_w_mgrlex ():
    var ("x y z")
    u = function ("u")(x,y,z)
    v = function ("v")(x,y,z)
    w = function ("w")(x,y,z)
    ctx = M.Context ((u,v,w), (x,y,z), M.Mgrlex)
    return ctx
