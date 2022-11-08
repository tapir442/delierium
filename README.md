# delierium
<b>D</b>ifferential <b>E</b>quations' <b>LIE</b> symmetries <b>R</b>esearch <b>I</b>nstr<b>UM</b>ent

Searching for symmetries in ODEs using Python/SageMath/sympy

# Status

* still playing around with Janet bases
* Lie ouput form a alpha

## Release 0.0.1.dev1

* Just constructing a Janet basis from a list of homogenuous linear PDEs (for grevlex and degrevlex order,
lex is dubious)


# Literature (and inspiration):
* Werner M. Seiler: Involution. The Formal Theory of Differential Equations and its Applications in Computer Algebra, Spinger Berlin 2010, ISBN 978-3-642-26135-0.
* Gerd Baumann: Symmetry Analysis of Differential Equations with Mathematica, Springer New York Berlin Heidelberg 2000, ISBN 0-387-98552-2.
* Fritz Schwarz: Algorithmic Lie Theory for Solving Ordinary Differential Equations, CRC Press 2008, ISBN 978-1-58488-889-5
* Fritz Schwarz: Loewy Decomposition of Linear Differential Equations, Springer Wien 2012, ISBN 978-3-7091-1687-6
* Daniel J. Arrigo: Symmetry Analysis of Differential Equations, Wiley Hoboken/New Jersey 2015, ISBN 978-1-118-72140-7
* John Starrett: Solving differential equations by Symmetry Groups  (e.g https://www.researchgate.net/publication/233653257_Solving_Differential_Equations_by_Symmetry_Groups)
* Alexey A. Kasatkin, Aliya A. Gainetdinova: Symbolic and Numerical Methods for Searching Symmetries of Ordinary Differential Equations with a Small Parameter and Reducing Its Order, https://link.springer.com/chapter/10.1007%2F978-3-030-26831-2_19 (if you are able and willing to pay the 27 bucks)
* Vishwas Khare, M.G. Timol: New Algorithm In SageMath To Check Symmetry Of Ode Of First Order, https://www.researchgate.net/publication/338388495_New_Algorithm_In_SageMath_To_Check_Symmetry_Of_Ode_Of_First_Order

# Goals:

* Short term:
    * All kinda stuff for symmetry analysis of ODE/PDE , doing is step by step, whatver comes to my mind
* Mid term:
    * Make it a valuable package
* Long term:
    * Maybe integration into SciPy|SymPy|SageMath



# Documentation(work in progress)

## How to use

### Get the determining equations for the symmetry of an third order ODE:

    >>> from delierium.Infinitesimals import infinitesimalsODE
    >>> from sage.calculus.var import var, function
    >>> from sage.calculus.functional import diff
    >>> x   = var('x')
    >>> y   = function('y')
    >>> ode = diff(y(x), x, 3) + y(x) * diff(y(x), x, 2)
    >>> inf = infinitesimalsODE(ode, y, x)
    >>> print("determining system:")
    >>> for _ in inf:
    >>>     print(_)
    >>> -3*D[0](xi)(y(x), x)
    >>> -6*D[0, 0](xi)(y(x), x)
    >>> y(x)*D[0](xi)(y(x), x) + 3*D[0, 0](phi)(y(x), x) - 9*D[0, 1](xi)(y(x), x)
    >>> y(x)*D[1](xi)(y(x), x) + phi(y(x), x) + 3*D[0, 1](phi)(y(x), x) - 3*D[1, 1](xi)(y(x), x)
    >>> -D[0, 0, 0](xi)(y(x), x)
    >>> -y(x)*D[0, 0](xi)(y(x), x) + D[0, 0, 0](phi)(y(x), x) - 3*D[0, 0, 1](xi)(y(x), x)
    >>> y(x)*D[0, 0](phi)(y(x), x) - 2*y(x)*D[0, 1](xi)(y(x), x) + 3*D[0, 0, 1](phi)(y(x), x) - 3*D[0, 1, 1](xi)(y(x), x)
    >>> 2*y(x)*D[0, 1](phi)(y(x), x) - y(x)*D[1, 1](xi)(y(x), x) + 3*D[0, 1, 1](phi)(y(x), x) - D[1, 1, 1](xi)(y(x), x)
    >>> y(x)*D[1, 1](phi)(y(x), x) + D[1, 1, 1](phi)(y(x), x)    
    
If you are using JupyterLab, you can print the results in a more human readable way:


`from IPython.display import Math`

`from delierium.helpers import latexer`

`from delierium.helpers import latexer`

`from delierium.helpers import latexer`

`x   = var('x')`

`y   = function('y')`

`ode = diff(y(x), x, 3) + y(x) * diff(y(x), x, 2)`

`display(Math(latexer(ode)))`

`inf = infinitesimalsODE(ode, y, x)`

`print("determining system:")`

`for _ in inf:`

`    display(Math(latexer(_)))`
    
In this mode a derivative like `d^2y/dx^2` is shown as `y_x`(superscript x)
    
### Janet Basis

    >>> import sage.all
    >>> from delierium.JanetBasis import Janet_Basis
    >>> from sage.calculus.var import var, function
    >>> from sage.calculus.functional import diff
    >>> vars = var ("x y")
    >>> z = function("z")(*vars)
    >>> w = function("w")(*vars)
    >>> f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
    >>> f2 = diff(z, x, y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
    >>> f3 = diff(w, x, y) - 2*x*diff(z, x, 2)/y - x*diff(w,x)/y**2
    >>> f4 = diff(w, x, y) + diff(z, x, y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
    >>> f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)
    >>> system_2_24 = [f1,f2,f3,f4,f5]
    >>> jb=Janet_Basis(system_2_24, (w,z), vars)
    >>> jb.show()
    >>> diff(z(x, y), y)
    >>> diff(z(x, y), x) + (1/2/y) * w(x, y)
    >>> diff(w(x, y), y) + (-1/y) * w(x, y)
    >>> diff(w(x, y), x)
