#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Dec 14 14:10:23 2021

@author: tapir
"""
import sage.all
from sage.calculus.var import var, function
from sage.calculus.functional import diff

from delierium.MatrixOrder import Context, Mgrlex, Mgrevlex, Mlex


vars = var ("x y")
z = function("z")(*vars)
w = function("w")(*vars)
# ctx: items are in descending order
ctx_grevlex_f = Context((w,z), vars, Mgrevlex)
ctx_grlex_f   = Context((w,z), vars, Mgrlex)
ctx_lex_f     = Context((w,z), vars, Mlex)

f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
f2 = diff(z,x,y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
f3 = diff(w, x,y) - 2*x*diff(z, x,2)/y - x*diff(w,x)/y**2
f4 = diff(w, x,y) + diff(z, x,y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)

system_2_24 = [f1,f2,f3,f4,f5]
