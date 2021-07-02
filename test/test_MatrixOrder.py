#%display latex
import sys
sys.path.insert (0, "../pylie")
import helpers
import MatrixOrder as M
import JanetBasis as JB
from collections.abc import Iterable
import functools
from operator import mul, sub
from pprint import pprint


from sage.all import *

var ("x y")
w = function ("w")(x,y)
z = function ("z")(x,y)

ctx = M.Context ((w, z), (x,y))

j = JB.DTerm (w(x,y), ctx)

#dp = JB.Differential_Polynomial(x, ctx)
#print ("only variable", dp._p)

dp = JB.Differential_Polynomial(w (x,y), ctx)
print ("only function", dp._p)

dp = JB.Differential_Polynomial(diff(w, x,y), ctx)
print ("only derivative", dp._p)
var("x, y, t")
w = function("w")(x,y,t)
z = function("z")(x,y,t)
u = function("u")(x,y,t)

ctx = M.Context ((u,w,z), (x,y,t))

flist = [diff(w,x,x,t), 
         diff(w, x,y), 
         diff(w,y,y),
         diff (w,y,t,t), 
         diff(w,x),  w(x,y,t),
     z(x,y,t), diff(z,x,t), diff(z, x,y), diff (z,y), diff(z,x), diff (z,y,y), diff(z,y,y,y),
        u(x,y,t), diff(u,x,x,t), diff(u, x,y), diff (u,y), diff(u,x), diff (u,y,y), diff(u,y,y,y)]

print ("********************** Mlex *******************")
l = [JB.Differential_Polynomial (_, ctx) for _ in flist]
for _ in sorted (l):
    print (_)

print ("********************** Mgrlex *******************")
ctx = M.Context ((u,w,z), (x,y,t), M.Mgrlex)
l = [JB.Differential_Polynomial (_, ctx) for _ in flist]


for _ in sorted (l):
    print (_)

print ("********************** Mgrevlex *******************")
ctx = M.Context ((u,w,z), (x,y,t), M.Mgrevlex)
l = [JB.Differential_Polynomial (_, ctx) for _ in flist]


for _ in sorted(l):
    print (_)
