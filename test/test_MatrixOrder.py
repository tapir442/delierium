#%display latex
import sys
sys.path.insert (0, "../pylie")
import pylie.pylie
import pylie.MatrixOrder as M
import pylie.JanetBasis as JB
from collections.abc import Iterable
import functools
from operator import mul, sub
from pprint import pprint


from sage.all import *

var ("x y")
w = function ("w")(x,y)
z = function ("z")(x,y)

ctx = M.Context ((w, z), (x,y))

dp = JB.Differential_Polynomial(x, ctx)
print ("only variable", dp._p)

dp = JB.Differential_Polynomial(w (x,y), ctx)
print ("only function", dp._p)

dp = JB.Differential_Polynomial(diff(w, x,y), ctx)
print ("only derivative", dp._p)
var("x, y")
w = function("w")(x,y)
z = function("z")(x,y)

ctx = M.Context ((w,z), (x,y))

#Differential_Polynomial(w(x,y), ctx)

flist = [diff(w,x,x), diff(w, x,y), diff (w,y), diff(w,x), diff (w,y,y), w(x,y),
     z(x,y), diff(z,x,x), diff(z, x,y), diff (z,y), diff(z,x), diff (z,y,y)]

l = [JB.Differential_Polynomial (_, ctx) for _ in flist]

l1 = sorted(l,key=functools.cmp_to_key(
                  lambda item1, item2:
                     M.sorter (item1._d, item2._d , ctx)
))
########################################
ctx = M.Context ((w,z), (x,y), M.grlex)
l = [JB.Differential_Polynomial (_, ctx) for _ in flist]

l2 = sorted(l,
            key=functools.cmp_to_key(
                  lambda item1, item2:
                     M.sorter (item1._d, item2._d, ctx)
))
ctx = M.Context ((w,z), (x,y), M.grevlex)
l = [JB.Differential_Polynomial (_, ctx) for _ in flist]

l3 = sorted(l,key=functools.cmp_to_key(
                  lambda item1, item2:
                     M.sorter (item1._d, item2._d , ctx)
))
