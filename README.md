# delierium
<span style="font-size:30px;"><b>D</b>ifferential <b>E</b>quations' <b>LIE</b> symmetries <b>R</b>esearch <b>I</b>nstr<b>UM</b>ent</span>

Lie point symmetries of ordinary and partial differential equations with Python and SymPy,
using Janet bases.

# Release 1.0.0

Had a hard time debugging and profiling (a Janet base is, after all, a Gröbner base, with all
its implications during computation), and claude was of great help to find and fix all the
next-to-last bugs.

delierium computes

* the **determining equations** of the Lie point symmetries of an ODE, a system of ODEs or a
  scalar PDE,
* **Janet bases** of linear systems of PDEs, in particular of these determining equations,
  fraction free, with the conditions they assume (factors assumed nonzero, special cases of
  the parameters),
* from a Janet basis its **rank** (the dimension of the solution space, for determining
  equations the dimension of the Lie algebra of point symmetries), its **parametric** and
  **principal derivatives** and its type,
* the **structure of the symmetry algebra** and its type, from the Janet basis of the
  determining equations without solving them, or from given generators,
* **checks** of given generators, and **scaling symmetries** without the determining
  equations,
* **group classifications** and the algebraic **Thomas decomposition**,
* **pictures**: the staircase of a Janet basis, symmetry generators as vector fields with
  solution curves, their flows as animations.

A catalogue of about 660 equations with known symmetries from the literature checks it
(see *Tests*). Solving the determining equations for the infinitesimals themselves is not
part of this release.

# Release notes

Details are in the issues referenced.

### Not released yet

* `symmetry_algebra` and `LieAlgebra.from_janet_basis`: the Lie algebra of the point
  symmetries from the Janet basis, without solving the determining equations ([#11](https://github.com/tapir442/delierium/issues/11)).
* `LieAlgebra.type()`: the type of an algebra of dimension up to 4 in Lie's classification,
  with Schwarz's names ([#11](https://github.com/tapir442/delierium/issues/11)); `LieAlgebra.from_structure_constants`.
* `determining_janet_basis`: the Janet basis of the determining equations; its `rank()` is
  the dimension of the symmetry algebra ([#3](https://github.com/tapir442/delierium/issues/3)).
* `verify_symmetry`, `verify_symmetries`: check generators against the determining
  equations ([#4](https://github.com/tapir442/delierium/issues/4)).
* `scaling_symmetries`: scaling symmetries by linear algebra on the exponents ([#48](https://github.com/tapir442/delierium/issues/48)).
* A benchmark against SymPy and sympy-extras, `benchmarks/sympy_symmetries.py`, with its
  report ([#6](https://github.com/tapir442/delierium/issues/6)).
* Fixed: equations with complex coefficients lost their complex symmetries ([#6](https://github.com/tapir442/delierium/issues/6)).
* Fixed: `adjoint_frechet_derivative` returned the Fréchet derivative itself ([#50](https://github.com/tapir442/delierium/issues/50)).
* Catalogue: the examples and exercises of Hydon, Bluman and Anco, Bluman and Kumei ([#50](https://github.com/tapir442/delierium/issues/50));
  27 first order ODEs with a finite algebra ([#28](https://github.com/tapir442/delierium/issues/28)).

### 2.1.0

* `thomas_decomposition`: the algebraic Thomas decomposition into simple systems ([#58](https://github.com/tapir442/delierium/issues/58)).
* `group_classification` and `classify` use it: their cases are disjoint ([#58](https://github.com/tapir442/delierium/issues/58)).

### 2.0.0

Incompatible changes:

* `LHDP.p` is now `LHDP.terms`; unused methods of `LHDP` are gone.
* `frechet_derivative` and `adjoint_frechet_derivative` take `dependent`, `independent` and
  `test_functions`.
* `Context.divisors` is gone (see `LHDP.assumptions`); `find_integrable_conditions` and
  `matrix_order.insert_row` are no longer exported.

New:

* `group_classification` and `classify`: the cases of an equation or a linear system with
  parameters ([#16](https://github.com/tapir442/delierium/issues/16)).
* `LHDP.assumptions` and `JanetBasis.assumed_nonzero()`: the factors assumed nonzero ([#31](https://github.com/tapir442/delierium/issues/31)).
* `LieAlgebra`: the structure of the algebra of given generators ([#11](https://github.com/tapir442/delierium/issues/11)).
* Janet bases are minimal and reduced ([#54](https://github.com/tapir442/delierium/issues/54)); `JanetBasis.order` is an alias of `rank`.
* About twice as fast: the slow test suite takes 106 s instead of 217 s.

Fixed:

* Exponents with a parameter in a denominator ([#69](https://github.com/tapir442/delierium/issues/69)); trigonometric identities in the
  coefficients ([#61](https://github.com/tapir442/delierium/issues/61)); a term with two unknowns raises `ValueError`.

### 1.1.1

* `delierium.__version__`, read from the package metadata.
* Fixed: floats in equations ([#37](https://github.com/tapir442/delierium/issues/37)), arbitrary functions of expressions ([#36](https://github.com/tapir442/delierium/issues/36)), `Abs` and
  `sign` ([#51](https://github.com/tapir442/delierium/issues/51)), hyperbolic functions next to mixed derivatives ([#52](https://github.com/tapir442/delierium/issues/52)).
* Equations not polynomial in the derivatives ([#5](https://github.com/tapir442/delierium/issues/5)); every catalogue entry passes now.

### 1.1.0

* Fixed: symbolic powers of derivatives ([#39](https://github.com/tapir442/delierium/issues/39)), determining equations that vanish only after
  `simplify()` ([#38](https://github.com/tapir442/delierium/issues/38)), results that depended on the hash seed ([#40](https://github.com/tapir442/delierium/issues/40)).
* Catalogue: Baumann's worked examples ([#27](https://github.com/tapir442/delierium/issues/27)), the group classifications of the CRC
  Handbook, Vol. 1, and of papers with symbolic powers, and the equations of PDEBench,
  APEBench, Gabel et al., ODEBench, Ko et al., EqWorld, Kahlmeyer et al., PINNacle,
  PDE-FIND, Yang et al. and The Well.

### 1.0.2

* A coefficient field of its own for every Janet basis, about 20 % faster ([#30](https://github.com/tapir442/delierium/issues/30)).
* pylint and mypy are blocking in CI ([#8](https://github.com/tapir442/delierium/issues/8)); releases are published by trusted publishing
  ([#7](https://github.com/tapir442/delierium/issues/7)).
* `delierium.higher_infinitesimals` is removed (`overdetermined_system_pde` does it).

### 1.0.1

* `import delierium` no longer patches SymPy's `Derivative`.
* Catalogue: Kamke 1.535, a first order ODE with a finite symmetry algebra ([#28](https://github.com/tapir442/delierium/issues/28)).
* `kamke.ipynb` is removed ([#2](https://github.com/tapir442/delierium/issues/2)).

# Installation

    pip install delierium            # the package, needs Python 3.12 or newer
    pip install "delierium[plot]"    # with matplotlib, for delierium.visualization

delierium runs on Python 3.12, 3.13 and 3.14; the whole test suite passes on each of them.
With uv, choose the version with `--python`, e.g. `uv sync --python 3.12` for the
environment of the project, or, without touching it,

    uv run --isolated --python 3.13 --group test pytest

From the sources, with [uv](https://docs.astral.sh/uv/):

    git clone https://github.com/tapir442/delierium.git
    cd delierium
    uv sync                          # the package and the development tools
    uv sync --group notebooks        # also JupyterLab and matplotlib, for the notebooks

# How to use

### The determining equations of an ODE

The Blasius equation `y''' + y y'' = 0`. `lie_derivative_printer` writes them in the notation
of Lie: `X_xy` is the second derivative of the infinitesimal `X` by `x` and `y`.

    >>> from sympy import Function, Symbol, diff
    >>> from delierium import lie_derivative_printer, overdetermined_system_ode
    >>> x = Symbol("x")
    >>> y = Function("y")(x)
    >>> ode = diff(y, x, 3) + y * diff(y, x, 2)
    >>> determining = overdetermined_system_ode(ode, [y], [x])
    >>> for e in lie_derivative_printer(determining, [y], [x], output="text"):
    ...     print(e)
    Y_xx*y + Y_xxx
    -9*X_xy + X_y*y + 3*Y_yy
    -3*X_xyy - X_yy*y + Y_yyy
    -X_xx*y - X_xxx + 3*Y_xxy + 2*Y_xy*y
    -3*X_xxy - 2*X_xy*y + 3*Y_xyy + Y_yy*y
    X_x*y - 3*X_xx + Y + 3*Y_xy
    X_y
    X_yy
    X_yyy

In JupyterLab, `lie_derivative_printer` without `output` renders them as formulas, and `ltf`
does so for a single expression. `overdetermined_system_odes` and `overdetermined_system_pde`
work the same way for systems of ODEs and for scalar PDEs.

### Their Janet basis

    >>> from delierium import janet_basis_from_ode
    >>> for e in janet_basis_from_ode(ode, y, x):
    ...     print(e)
    D(X(y(x), x), x) + (1/y(x)) * Y(y(x), x)
    D(X(y(x), x), y(x))
    D(Y(y(x), x), x)
    D(Y(y(x), x), y(x)) + (-1/y(x)) * Y(y(x), x)

Every derivative of `X` and `Y` is determined by these four equations, only the values of
`X` and `Y` themselves are free: the Blasius equation has a two-dimensional Lie algebra of
point symmetries, `d/dx` and `x d/dx - y d/dy`.

### The dimension and structure of the symmetry algebra

`determining_janet_basis` gives the Janet basis of the determining equations as a
`JanetBasis` (for an ODE, a system of ODEs or a scalar PDE); its `rank()` is the dimension of
the symmetry algebra. `symmetry_algebra` computes the structure of the algebra from it,
without solving for the generators:

    >>> from delierium import determining_janet_basis, symmetry_algebra
    >>> determining_janet_basis(ode, y, x).rank()
    2
    >>> algebra = symmetry_algebra(ode, y, x)
    >>> algebra.derived_series(), algebra.is_abelian()
    ([2, 1, 0], False)
    >>> print(algebra.type())
    l2,1

`l2,1` is the non-abelian two-dimensional algebra, `[X1, X2] = X1`, in the names of Schwarz.
A first-order ODE always has infinitely many symmetries:

    >>> determining_janet_basis(diff(y, x) - y**2, y, x).rank()
    oo

### Janet bases of linear systems

`JanetBasis` takes a list of linear homogeneous PDEs, the unknown functions and the
variables (highest first), and optionally a ranking (`Mgrevlex`, the default, `Mgrlex`,
`Mlex`). Schwarz's system (2.25):

    >>> from sympy import symbols
    >>> from delierium import JanetBasis
    >>> x, y = symbols("x y")
    >>> z = Function("z")(x, y)
    >>> w = Function("w")(x, y)
    >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
    >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * y**2 * diff(z, x) - 8 * w * y
    >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * y**2 * diff(z, y)
    >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
    >>> janet = JanetBasis([g2, g3, g4, g1], (w, z), (x, y))
    >>> for e in janet.S:
    ...     print(e)
    D(z(x, y), y)
    D(z(x, y), x) + (1/(2*y)) * w(x, y)
    D(w(x, y), y) + (-1/y) * w(x, y)
    D(w(x, y), x)
    >>> janet.rank()
    2
    >>> print(janet.parametric_derivatives())
    [w(x, y), z(x, y)]
    >>> print(janet.principal_derivatives(1))
    [Derivative(w(x, y), x), Derivative(w(x, y), y), Derivative(z(x, y), x), Derivative(z(x, y), y)]

`rank()` is `oo` if there are infinitely many parametric derivatives. `assumed_nonzero()`
lists the factors the computation divided by: where one of them vanishes, for special
values of parameters or on singular lines, the Janet basis may differ.
`parameter_conditions()` gives these special cases of the parameters.

### Pictures

`delierium.visualization` needs matplotlib (`delierium[plot]`) and is not imported by
`import delierium`:

    from delierium.visualization import staircase, vector_fields, ode_solutions, animate_flow

    staircase(janet)                                  # leading, principal, parametric derivatives
    curves = ode_solutions(ode, y)                    # solution curves of an ODE
    vector_fields([("1", "0"), ("x", "-y")], symbols("x y"), curves)
    animate_flow(("x", "-y"), symbols("x y"), curves) # in Jupyter: HTML(_.to_jshtml())

A generator is a tuple of its components, the independent variables first: `("x", "-y")` is
`x d/dx - y d/dy`.

# The package

The public interface is what `delierium` exports; `help(delierium)` lists it:

* determining equations: `overdetermined_system_ode`, `overdetermined_system_odes`,
  `overdetermined_system_pde`, `prolongation`, `make_infinitesimal`, `create_infinitesimals`,
  `determining_janet_basis`; checks: `verify_symmetry`, `verify_symmetries`
* symmetry algebras: `symmetry_algebra`, `LieAlgebra` (`type()`, ...), `scaling_symmetries`
* group classification: `group_classification`, `classify`; `thomas_decomposition`
* Janet bases: `JanetBasis` (with `rank`, `parametric_derivatives`, `principal_derivatives`,
  `type`, `assumed_nonzero`, `parameter_conditions`, `representation`),
  `janet_basis_from_ode`, `janet_basis_from_odes`, `integrability_conditions`, and checks
  against published bases: `is_janet_basis_of`, `is_janet_basis_of_ode`,
  `is_janet_basis_of_odes`
* rankings: `Context`, `Mgrevlex`, `Mgrlex`, `Mlex`
* the notation of Lie: `lie_form`, `ltf`, `lie_derivative_printer`
* operators: `euler_operator`, `frechet_derivative`, `adjoint_frechet_derivative`,
  `variational_derivative`
* pictures: the module `delierium.visualization`

### Tests and the symmetry catalogue

`tests/symmetry_catalog.py` is a catalogue of about 660 ODEs, systems of ODEs and PDEs with
their known symmetries: Kamke's collection, the examples and exercises of textbooks
(Arrigo, Schwarz, Hydon, Baumann, Bluman and others), group classifications and benchmark
data sets. For each, the listed generators have to solve the determining equations and the
rank of their Janet basis has to be the dimension of the symmetry algebra.
`tests/test_schwarz_examples.py` checks the Janet bases printed in Schwarz's book, coefficients
included.

    uv run pytest                    # the fast tests, including the doctests of this README
    uv run pytest -m slow -n 3       # the whole catalogue, about 6 min with 3 workers

### Notebooks

* `notebooks/Catalogue_template.ipynb`: pick an equation of the catalogue by name; its
  Janet basis and pictures.
* `notebooks/Arrigo`, `Baumann`, `Schwarz`, `Khare-Timol`: the examples of these books and
  papers, in their order, built the same way.
* `notebooks/Backlund`: Bäcklund transformations (sine-Gordon, Liouville, Burgers, KdV), and
  the symmetries of their equations.

# Open problems

Equations delierium cannot handle yet are tests in `tests/test_open_problems.py`, each
documented in its module docstring: what is asked, what delierium does, why it fails, what
is known, and ways forward. They are skipped by default; run them with

    uv run pytest -m too_slow --run-too-slow

1. The symmetries of `2 (K(u) u')' + x u' = 0` for an arbitrary `K(u)` (the
   Boltzmann-reduced nonlinear diffusion equation, a group classification problem): the
   Janet basis does not finish, as every differentiation brings in the next derivative of
   `K` as a new generator of the coefficients.
2. The determining equation of the general second order ODE `u'' = F(x, u, u')` with an
   arbitrary `F`: splitting the symmetry condition fails, as `F` is an arbitrary function of
   the jet variable `u'`.
3. Kamke 6.171 and 6.219 with symbolic parameters: the Janet basis does not finish in
   reasonable time. The catalogue checks them at random parameter values, which give the
   generic dimension.

# Literature

* Werner M. Seiler: Involution. The Formal Theory of Differential Equations and its
  Applications in Computer Algebra, Springer Berlin 2010, ISBN 978-3-642-26135-0.
* Fritz Schwarz: Algorithmic Lie Theory for Solving Ordinary Differential Equations, CRC
  Press 2008, ISBN 978-1-58488-889-5.
* Fritz Schwarz: Loewy Decomposition of Linear Differential Equations, Springer Wien 2012,
  ISBN 978-3-7091-1687-6.
* Daniel J. Arrigo: Symmetry Analysis of Differential Equations, Wiley Hoboken/New Jersey
  2015, ISBN 978-1-118-72140-7.
* Gerd Baumann: Symmetry Analysis of Differential Equations with Mathematica, Springer New
  York Berlin Heidelberg 2000, ISBN 0-387-98552-2.
* Peter E. Hydon: Symmetry Methods for Differential Equations, Cambridge University Press
  2000.
* Erich Kamke: Differentialgleichungen. Lösungsmethoden und Lösungen.
* John Starrett: Solving Differential Equations by Symmetry Groups,
  https://www.researchgate.net/publication/233653257_Solving_Differential_Equations_by_Symmetry_Groups
* Alexey A. Kasatkin, Aliya A. Gainetdinova: Symbolic and Numerical Methods for Searching
  Symmetries of Ordinary Differential Equations with a Small Parameter and Reducing Its
  Order, https://link.springer.com/chapter/10.1007%2F978-3-030-26831-2_19
* Vishwas Khare, M. G. Timol: New Algorithm In SageMath To Check Symmetry Of Ode Of First
  Order,
  https://www.researchgate.net/publication/338388495_New_Algorithm_In_SageMath_To_Check_Symmetry_Of_Ode_Of_First_Order

# License

MIT, see `LICENSE`.
