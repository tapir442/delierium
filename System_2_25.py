#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Dec 14 14:10:23 2021

@author: tapir
"""

import sage.all
from sage.calculus.var import var, function
from sage.calculus.functional import diff

from delierium.JanetBasis import (
    Autoreduce, Differential_Polynomial, Reorder, CompleteSystem, derivative_to_vec,multipliers
    , reduceS)
from delierium.MatrixOrder import Context, Mgrlex, Mgrevlex, Mlex


vars = var ("x y")
z = function("z")(*vars)
w = function("w")(*vars)
# ctx: items are in descending order
ctx = Context((w,z), vars, Mgrevlex)

g1 = diff(z, y,y) + diff(z,y)/(2*y)
g2 = diff(w,x,x) + 4*diff(w,y)*y**2 - 8*(y**2) * diff(z,x) - 8*w*y
g3 = diff(w,x,y) - diff(z,x,x)/2 - diff(w,x)/(2*y) - 6* (y**2) * diff(z,y)
g4 = diff(w,y,y) - 2*diff(z,x,y) - diff(w,y)/(2*y) + w/(2*y**2)

system_2_25 = [g2,g3,g4,g1]
