import sage.all
import sage.symbolic.operators
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff
from IPython.core.debugger import set_trace
try:
    from delierium.helpers import is_derivative, is_function
except ImportError:
    from helpers import is_derivative, is_function
import functools
from operator import mul
import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff
try :
    from delierium.helpers import (is_derivative, is_function, eq,
                               order_of_derivative)
    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                               order_of_derivative)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex

import functools
from operator import mul
from IPython.core.debugger import set_trace
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, combinations, islice
from sage.matrix.constructor import Matrix


x = var('x')
u = function('u')

f = function('f')

xi = function('xi')
phi = function('phi')

vf = xi(x, u(x))*diff(f(x), x) + phi(x, u(x))*diff(f(x), u)
