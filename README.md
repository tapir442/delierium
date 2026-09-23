# delierium
<span style="font-size:30px;"><b>D</b>ifferential <b>E</b>quations' <b>LIE</b> symmetries <b>R</b>esearch <b>I</b>nstr<b>UM</b>ent</span>

Searching for symmetries in ODEs and PDEs using Python/SymPy

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

# Release History
## Release 0.1.0

offers

* the determining equations of the Lie point symmetries of an ODE, a system of ODEs or a
  scalar PDE: `overdetermined_system_ode`, `overdetermined_system_odes`,
  `overdetermined_system_pde`,
* Janet bases of linear systems of PDEs (`JanetBasis`), in particular of these determining
  equations (`janet_basis_from_ode`, `janet_basis_from_odes`), and checks against published
  bases (`is_janet_basis_of`, `is_janet_basis_of_ode`, `is_janet_basis_of_odes`).

Solving the determining equations for the infinitesimals themselves is not part of this
release.



# Documentation(work in progress)

## How to use

### Get the determining equations for the symmetry of a third order ODE:

    >>> from collections import OrderedDict
    >>> from sympy import Symbol, Function, diff
    >>> from delierium.infinitesimals import overdetermined_system_ode
    >>> from delierium.helpers import make_infinitesimal
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> ode = diff(y, x, 3) + y * diff(y, x, 2)
    >>> infinitesimals = OrderedDict({x: make_infinitesimal(x, x, y, name='X'),
    ...                               y: make_infinitesimal(y, x, y, name='Y')})
    >>> inf = overdetermined_system_ode(ode, [y], [x], infinitesimals=infinitesimals)
    >>> for _ in inf:
    ...     print(_)
    y(x)*Derivative(Y(x, y(x)), (x, 2)) + Derivative(Y(x, y(x)), (x, 3))
    y(x)*Derivative(X(x, y(x)), y(x)) + 3*Derivative(Y(x, y(x)), (y(x), 2)) - 9*Derivative(X(x, y(x)), x, y(x))
    ...

The raw output is hard to read. `ltf` prints derivatives in index notation, so `d^2 X/dx dy` becomes `X_{xy}`:

    >>> from delierium.helpers import ltf
    >>> for _ in inf:
    ...     print(ltf(_, [infinitesimals[y]], [infinitesimals[x]], printer=False))
    Y_{xxx} + Y_{xx}*y
    -9*X_{xy} + X_{y}*y + 3*Y_{yy}
    -3*X_{xyy} - X_{yy}*y + Y_{yyy}
    -X_{xxx} - X_{xx}*y + 3*Y_{xxy} + 2*Y_{xy}*y
    -3*X_{xxy} - 2*X_{xy}*y + 3*Y_{xyy} + Y_{yy}*y
    -3*X_{xx} + X_{x}*y + Y + 3*Y_{xy}
    -3*X_{y}
    -6*X_{yy}
    -X_{yyy}

In JupyterLab, drop `printer=False` to render the result as LaTeX.

For a scalar PDE use `overdetermined_system_pde` the same way. Its docstring has the heat equation as an example.

### Janet Basis

    >>> from sympy import symbols, Function, diff
    >>> from delierium.janet_basis import JanetBasis
    >>> x, y = symbols("x y")
    >>> z = Function("z")(x, y)
    >>> w = Function("w")(x, y)
    >>> f1 = diff(w, y) + x*diff(z, y)/(2*y*(x**2+y)) - w/y
    >>> f2 = diff(z, x, y) + y*diff(w, y)/x + 2*y*diff(z, x)/x
    >>> f3 = diff(w, x, y) - 2*x*diff(z, x, 2)/y - x*diff(w, x)/y**2
    >>> f4 = diff(w, x, y) + diff(z, x, y) + diff(w, y)/(2*y) - diff(w, x)/y + x*diff(z, y)/y - w/(2*y**2)
    >>> f5 = diff(w, y, y) + diff(z, x, y) - diff(w, y)/y + w/(y**2)
    >>> system_2_24 = [f1, f2, f3, f4, f5]
    >>> jb = JanetBasis(system_2_24, (w, z), (x, y))
    >>> for _ in jb.S:
    ...     print(_)
    D(z(x, y), y)
    D(z(x, y), x) + (1/(2*y)) * w(x, y)
    D(w(x, y), y) + (-1/y) * w(x, y)
    D(w(x, y), x)
