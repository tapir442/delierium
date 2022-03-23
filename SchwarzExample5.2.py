import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff


from sage.symbolic.relation import solve

from delierium.Infinitesimals import prolongationODE
from delierium.JanetBasis import Janet_Basis
y = function('y')
x = var('x')
#ode=4*diff(y(x),x,x)*y(x) - 3* diff(y(x),x)**2-12*y(x)**3
#p=prolongationODE(ode, y, x)[0].expand()
#p.show()
#s1=solve(ode==0, diff(y(x),x,x))
#s1=s1[0];s1.show();s1.lhs().show();s1.rhs().show()
#ode1=p.subs({s1.lhs() : s1.rhs()}).simplify()
#ode1.expand().show()
#r1=ode1.expand().collect(diff(y(x),x)**3);r1.show()
#r2=r1.collect(diff(y(x),x)**2);r2.show()
#r3=r2.collect(diff(y(x),x)); r3.show()
#r4=r3.collect(y(x)); r4.show()
from IPython.core.debugger import set_trace
function('xi phi')
def infinitesimalsODE (ode, dependent, independent):
    def order(ode, dep, indep):
        return 3
    prolongation = prolongationODE(ode, dependent, independent)[0]
    from pprint import pprint
    print ("PROLONGATION")
    prolongation.show()
    l = []
    def collect(prol, d):
        res = 0
        s = prol.operands()
        for _s in s:
            locs = _s.operands()
            if d in locs:
                res += _s/d
        return res
    for o in range (order(ode, y, x),0,-1):
        d = diff(dependent(independent), independent)**o
        c = collect(prolongation, d)
        l.append(c.expand())
        prolongation  = prolongation - c*d
    l.append (prolongation.expand())
    janet = Janet_Basis(l, [xi, phi], [x, y])
    return janet

ode = 4*diff(y(x),x,x)*y(x) - 3* diff(y(x),x)**2-12*y(x)**3
inf = infinitesimalsODE(ode, y ,x)
inf.show()
