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
* the **structure of the symmetry algebra** (structure constants, derived and lower central
  series, solvability, center, Killing form) from the Janet basis of the determining
  equations, without solving them, or from given generators,
* **pictures**: the staircase of a Janet basis, symmetry generators as vector fields with
  solution curves, their flows as animations.

A catalogue of about 580 equations with known symmetries from the literature checks it
(see *Tests*). Solving the determining equations for the infinitesimals themselves is not
part of this release.

# Release notes

### Not released yet

New:

* **The symmetry algebra without its generators** (#11): `symmetry_algebra(eq, u, [x, t])`
  and `LieAlgebra.from_janet_basis(janet)` compute the structure constants of the Lie
  algebra of point symmetries from the Janet basis of the determining equations alone.
  A solution is determined by its parametric derivatives at a regular point; the normal
  forms of the higher derivatives give the derivatives of a commutator there, and so its
  coordinates (Lie's relations, Schwarz 3.17-3.19). Checked on the 225 catalogue entries
  with a complete list of generators: the same derived and lower central series, center
  and Killing form rank as the algebra of the generators. `y'' = y'**2/y` gives sl(3),
  Burgers' equation a perfect 5-dimensional algebra.
* `LieAlgebra.from_structure_constants(c)`: an abstract Lie algebra.
* `determining_janet_basis(equations, dependent, independent)`: the Janet basis of the
  determining equations of an ODE, a system of ODEs or a scalar PDE as a `JanetBasis`, its
  `rank()` the dimension of the symmetry algebra (#3); the catalogue test uses it.
  `symmetry_algebra` takes systems of ODEs as well.
* `verify_symmetry(equations, dependent, independent, generator)` (and `verify_symmetries` for
  several): a given generator, as a tuple of components (independent variables first),
  substituted into the determining equations; a `VerificationResult` with the residues (0
  where shown to vanish, also for symbolic powers that `simplify` misses) and the
  assumptions (the initials of the equations nonzero), true if all residues vanish (#4).
  The catalogue test and the benchmark use it instead of three private copies.
* `scaling_symmetries(equations, dependent, independent)`: the scaling symmetries
  `x -> l**a x, u -> l**b u` without the determining equations, by linear algebra on the
  exponents: every term has to scale with the same power of `l` (#48; dimensional analysis
  is the special case of physical dimensions). KdV: `x d/dx + 3 t d/dt - 2 u d/du`; symbolic
  exponents are taken for generic values. On the catalogue: 358 of 579 entries have
  scalings, all verified as symmetries, and the 264 listed generators that are scalings lie
  in their span.
* Fixed: an equation with complex coefficients (Kamke 1.743: `y' + I (x**4 + ...)/(32 y)`)
  got its determining equations split into real and imaginary parts, as if its symmetries
  were real; correct complex generators were rejected. Only the `I` of trigonometric
  functions written as exponentials is split off now. `verify_symmetry` also counts a
  residue as 0 where it vanishes for positive variables and parameters (symmetries are
  local: `y' = sqrt(|y|)`, `y'**n = f(x) g(y)`). Both found by the SymPy benchmark (#6).
* `benchmarks/sympy_symmetries.py` and its report `benchmarks/sympy_symmetries.md`:
  delierium against SymPy's `infinitesimals` and sympy-extras on Kamke's first order ODEs
  and on the catalogue, with cross checks of the generators each tool finds (#6).
* Catalogue: Hydon's worked examples and the exercises with answers (35 new entries) and
  Bluman and Anco's examples and exercises (19 entries, among them the biharmonic equation
  and three wave speeds of the classification of u_tt = c(x)**2 u_xx) and 8 PDEs from Bluman
  and Kumei's exercises (heat and Laplace equations in space, u_tt = c(u)**2 u_xx, the
  stream function equation, ...) (#50). Three slips in Bluman and Anco are noted at their
  entries.
* Fixed: `adjoint_frechet_derivative` was a placeholder returning the Frechet derivative
  itself; it now computes the adjoint (Baumann (3.22)). Tests of the derivative operators
  with Baumann's explicit results of chapter 3 (#50).
* `LieAlgebra.type()`: the type of an algebra of dimension at most 4 in Lie's classification
  of the complex Lie algebras, with Schwarz's names (section 3.4: `l1`, `l2,1`, ...,
  `l4,17`) and parameters, e.g. `l3,2(c = -1)` for the Euclidean algebra e(2). Decided by
  invariants (derived series, nilpotency, center, Killing form, the Jordan form of `ad X`
  on the derived algebra), checked on every listed type in random bases and on the
  catalogue: the Janet basis and the generators give the same type for all 154 entries of
  dimension at most 4. Two corrections of the listing: `l4,7` has a derived algebra of
  dimension 3, and `l4,9` with `a = 1` is `l4,14`.

### 2.1.0

New:

* **Algebraic Thomas decomposition** (#58, stage 2): `thomas_decomposition(equations,
  inequations, variables)` splits a system of polynomial equations and inequations into
  disjoint simple systems (`SimpleSystem`: triangular, nonvanishing initials,
  square-free), which together have exactly its solutions (Bächler, Gerdt,
  Lange-Hegermann, Robertz, J. Symb. Comput. 2012, Algorithms 2.6-2.25). By default
  polynomials are factored and the systems split on their factors. Deviations from the
  paper and from SymPy, documented in the code: subresultants as exact Sylvester
  determinants (SymPy's `subresultants()` is wrong for defective sequences),
  `ResSplitDivide` keeps the original inequation (the paper's version lost cases), and a
  workaround for SymPy 1.14's `PolyElement.pquo`. The output is in a compact normal form
  (reduced modulo a Groebner basis of the lower equations, monic where possible). Checked
  on the paper's examples and by a seeded fuzz test of the partition property.
* `group_classification` and `classify` solve their parameter conditions with it, so the
  cases are disjoint also where roots coincide (`a**2 = b`: `a = +-sqrt(b)` with
  `b != 0`, and `a = b = 0`). The existing classifications are unchanged.

### 2.0.0

Incompatible changes (of the public interface; the major version follows them):

* `LHDP.p`, the list of an equation's terms, is now `LHDP.terms`; the unused methods
  `LHDP.terms()`, `derivatives()`, `coefficients()`, `atoms()`, `xreplace()` and `__le__`
  are gone.
* `frechet_derivative` and `adjoint_frechet_derivative` take `dependent`, `independent` and
  `test_functions` instead of `dependVar`, `independVar` and `testfunction`.
  `frechet_derivative` gives one column per unknown also when there are more or fewer
  equations than unknowns.
* `Context.divisors` is gone: every `LHDP` carries its own `assumptions` (see below).
* `delierium.janet_basis.find_integrable_conditions` is no longer exported (it is
  `_integrability_conditions_of_function`); `matrix_order.insert_row` is gone.

New:

* **Group classification** (#16, the linear first stage of the Thomas decomposition #58):
  `group_classification(eq, u, [x, t])` splits the Lie point symmetries of a scalar
  differential equation with parameters into disjoint cases, each with its Janet basis and
  rank, instead of assuming the parameter conditions nonzero; `classify` does the same for
  a linear system with parameters. Each case is computed from the equation itself; the
  cases branch on the parameter conditions of the Janet basis, on the initial of the
  equation and on the parameter values where two powers of jet variables coincide.
  Conditions are solved as in an algebraic Thomas decomposition (`a*b = 0`: `b = 0`, or
  `a = 0` with `b != 0`). Checked against the classical results: `u_t = (u**sigma u_x)_x`
  (4 symmetries, 5 for `sigma = -4/3`), with a source `a u**n` (3; 4 for `n = 1`; 5 for
  `sigma = -4/3` with `n = 1` or `n = -1/3`), and `u_t = (u_x**n)_x`, where `n = -1`
  (linearizable) has infinitely many.
* `LHDP.assumptions`: the factors an equation's derivation assumed nonzero (#31);
  `JanetBasis.assumed_nonzero()` collects them explicitly instead of through a side
  channel, with the same results.
* `JanetBasis.order` is an alias of `rank` (Schwarz's name); a `Matrix` of equations is
  taken as several equations, not as one.
* `LieAlgebra`: the Lie algebra spanned by given generators (vector fields on the
  independent and dependent variables), with structure constants, commutator table,
  derived and lower central series, solvability, nilpotency, center and Killing form;
  `NotClosedError` if a commutator is not a constant linear combination of the generators
  (#11). The generators can come from anywhere, e.g. the literature.
* The catalogue checks that each of its 228 complete lists of generators of a finite
  algebra is closed under commutators.
* Janet bases are the minimal reduced ones: distinct leading derivatives, no redundant
  element, reduced tails (#54). `reduce_by_system` stopped too early (it did not try the
  earlier elements again after a reduction), so integrability conditions that reduce to
  zero could be kept; the results were correct but not minimal. Checked against CoCoA 5's
  `JanetBasis` on 207 systems with constant coefficients: all equal.
* Faster: the numerators of the determining equations are computed in SymPy's sparse
  field of rational functions instead of with `cancel()` (the apoptosis model of
  ODEBench: 51 s -> 20 s), and a reduction normalizes only its result, not every
  intermediate step (Stokes' creeping flow: 129 s -> 58 s). The prolongation is computed in
  jet coordinates, with the characteristic and each total derivative once (4th order PDEs in
  two space variables: 17 s -> 3 s). The generators of the coefficient field are in a fixed
  order: the variable order of its polynomial ring, and with it the time of a Janet basis,
  depended on the hash seed (PINNacle Heat2D_LongTime: 7 s to 450 s, now 7 s). The results
  are the same; the slow test suite takes 106 s instead of 217 s.

Fixed:

* Wrong determining equations when an exponent has a parameter in a denominator
  (`u_x**(p - 1)` with `p = 6 - 8/q`): powers of one jet variable were split as independent,
  giving too many equations and too small a rank (#69).
* Trigonometric identities in the coefficients (#61): the Janet basis divided by
  `2 sin(x) cos(x) - sin(2 x)`, which is zero. `tan`, `cot`, `sec`, `csc` (and the hyperbolic
  ones) are written in `sin` and `cos`, multiples of an argument in one base, and the zero
  test reduces modulo `cos**2 + sin**2 - 1`.
* A term with two unknowns (`f*g`) in a linear equation raises `ValueError` instead of
  losing one of them silently.
* Code cleanup: dead code removed, internal helpers replaced by SymPy's own, clearer names;
  the hashes of terms and equations no longer depend on how they print (they could
  disagree with `==` since #61, and the order of results varied between runs).

### 1.1.1

* `delierium.__version__`, read from the package metadata: the version is written only in
  `pyproject.toml` (`uv version --bump patch` updates it and `uv.lock` together).
* Floats in an equation are taken for the decimals they print as (0.5 -> 1/2) before the
  determining equations are computed; `solve()` had turned all numbers into floats, so one
  root appeared in two forms (#37).
* An arbitrary function of an expression, e.g. y' = x F(y/x) + y/x, no longer fails in
  `finish_substitution`: the derivative F'(y/x) stays a `Subs` (#36).
* `Abs(e)` and `sign(e)` are replaced by s*e and s with a constant sign s (symmetries are
  local); SymPy had differentiated Abs of a complex symbol into re, im and sign (#51).
* `LHDP` simplifies with the derivatives replaced by symbols: SymPy's `simplify()` failed
  on hyperbolic functions next to mixed derivatives ("Improve MV Derivative support in
  collect", sinh-Gordon) (#52).
* Equations not polynomial in the derivatives (#5): functions of jet variables are split
  as independent generators - transcendental functions (log, atan, ...) and arbitrary
  functions F(p) with their derivatives (the generic case), trigonometric and hyperbolic
  functions as exponentials (real and imaginary parts), fractional powers and roots as
  algebraic generators modulo their relation. An equation not polynomial in its highest
  derivative is solved for it when the solution is unique (u_t = atan(u_xx)); with one
  square root of it (Kamke 1.558) the condition is taken on the whole equation.
* Catalogue: Baumann's KdV with slowly varying coefficients, ODEBench 44 and EqWorld's
  sinh-Gordon equation pass now; with #5 every entry of the catalogue does: no
  expected failures are left.

### 1.1.0

* Symbolic powers of derivatives give the right determining equations (#39): powers of one
  jet variable whose symbolic exponents are rational multiples of each other, such as
  u_x**n and u_x**(-n) after solving for a derivative, are split as powers of one
  generator. The filtration equation v_t = v_x**n v_xx has its 5 symmetries now.
* Catalogue: 13 equations with symbolic powers of derivatives from the group
  classifications of Cherniha, King, Kovalenko (2015), AIMS Mathematics (2026) and
  Anco et al. (2016), all with the published dimensions and generators.
* Determining equations that vanish only after `simplify()` no longer stop the Janet
  basis (#38): `LHDP` accepts them as empty, and `JanetBasis`, `integrability_conditions`
  and `is_janet_basis_of` drop them. Twelve catalogue entries with symbolic powers
  (CRC Vol. 1, 10.2-11.6; EqWorld 1.2.1-1.2.6) get their dimension now.
* The determining equations no longer depend on Python's hash seed (#40): of several
  highest derivatives, the equation is solved for one it is linear in with a coefficient
  free of jet variables, ties broken by SymPy's canonical order. Four CRC entries that
  failed for some seeds pass now.
* Catalogue: 29 worked examples of Baumann (#27), from section 4.4 (ODEs of order 1 to 4)
  and the scalar PDEs of 5.6 (flux line, KdV family, Kadomtsev-Petviashvili, Stokes flow,
  Fokker-Planck, molecular beam epitaxy). delierium reproduces the dimension and all
  generators of 27 of them; Kamke 7.13 needs #5, the KdV with slowly varying coefficients
  #36.
* Catalogue: 73 equations from the group classifications of the CRC Handbook, Vol. 1,
  chapters 10, 11 and 12.1-12.4 (diffusion, filtration, anisotropic and hyperbolic heat
  equations, transfer, Hopf and KdV-Burgers type equations, linear and nonlinear wave
  equations). All pass (the last 8 needed #5). Eight generators
  are misprinted in the book and corrected in the entries.
* Catalogue: the scalar equations of the PDEBench datasets (advection, Fisher-KPP,
  diffusion-sorption); the systems among them need #21.
* Catalogue: the scalar physical scenarios of APEBench with their default
  coefficients, 27 equations in 1D and 2D (linear, Burgers, KdV and Kuramoto-Sivashinsky
  variants, Fisher-KPP, Swift-Hohenberg, anisotropic and mixed diffusion and
  dispersion). They replace the book versions of the heat, Burgers and Fisher equations
  (Arrigo; CRC Handbook, Vol. 1, 10.1).
* Catalogue: 24 evolution equations of Gabel, Quax, Gavves (2024), the training set of a
  neural symmetry detector. Three of their generators are misprinted and corrected; three
  equations replace the CRC Handbook's entries (Vol. 1, 10.2, 10.3, 11.6).
* Catalogue: the 63 autonomous systems of ODEBench (ODEFormer, ICLR 2024), 58 entries with
  symbolic constants, with their affine symmetries; the driven pendulum with quadratic
  damping (Abs) fails the dimension check.
* Catalogue: the PDEs of Ko, Kim, Lee (2024) with their full algebras: KdV (replaces
  Arrigo's entry), Burgers with viscosity nu, KdV after a nonlinear time change (a
  misprinted generator corrected) and the cylindrical KdV shifted to t + 1.
* Catalogue: 56 nonlinear PDEs of EqWorld (heat, Klein-Gordon, wave, elliptic,
  transonic flow, Monge-Ampere, KdV and boundary layer equations) with their dimensions
  and generators; the Boussinesq equation replaces Arrigo's. Sinh-Gordon fails in SymPy's
  collect().
* Catalogue: the 12 ODE systems of Kahlmeyer, Merk, Giesen (AAAI 2025) with the
  generators found by their symbolic regression.
* Catalogue: the 12 scalar problems of PINNacle (NeurIPS 2024) with their default
  coefficients (Burgers, Poisson and Helmholtz with sources, heat and wave equations, also
  in 5D, Kuramoto-Sivashinsky); Poisson2D_Classic replaces Arrigo's Laplace equation.
* Catalogue: the scalar real PDEs of PDE-FIND (Rudy et al. 2017): KdV, Burgers and the
  diffusion equation of a random walk.
* Catalogue: the ODE systems of Yang et al., Symmetry-Informed Governing Equation Discovery
  (NeurIPS 2024), with the symmetries the paper uses.
* Catalogue: the scalar equations of The Well (NeurIPS 2024), the Helmholtz and wave
  equations of the Helmholtz staircase; its other 15 data sets are systems (#21).

### 1.0.2

* Every Janet basis computes in a coefficient field of its own (`coefficients.fresh_field`)
  instead of one field shared by the whole process, which grew with every computation
  (#30). The symmetry catalogue runs about 20 % faster (90 s to 70 s in one process),
  results are unchanged.
* Internal change: the code is clean under pylint and mypy, which are now blocking in CI
  (#8). No change in behaviour.
* Internal change: every function has type hints, and mypy requires them for new code.
* Internal change: a version tag publishes the release to PyPI from GitHub Actions, by
  trusted publishing instead of an API token (#7).
* `delierium.higher_infinitesimals` (and its command line tool) removed: a second, limited
  implementation (one function of x and t, order up to 3) of what `overdetermined_system_pde`
  does for any scalar PDE.

### 1.0.1

* `import delierium` no longer replaces SymPy's `Derivative.__new__` with a trimmed copy.
  The patch changed `diff` for all SymPy code in the process (no sign normalisation, no
  canonical form) and depended on SymPy internals. delierium now differentiates with plain
  SymPy, with `simplify=False` where it matters. Results are unchanged; the symmetry
  catalogue runs about 10 % slower, mostly on PDEs.
* New catalogue entry Kamke 1.535, `8 x y'^3 - 12 y y'^2 + 9 y = 0`: cubic in `y'`, so
  unlike `y' = h(x, y)` it has a finite symmetry algebra, of dimension 3. Besides
  `x d/dx + y d/dy` the generators are algebraic: with `u = 3 x ± sqrt(9 x^2 - 4 y^2)`,
  `u^(2/3) d/dx + 3 y u^(-1/3) d/dy`, valid for `x > 0` between the singular solutions
  `y = ±3 x/2`. The dimension was checked independently of the Janet basis.
* `kamke.ipynb` removed from the top directory (#2): an early notebook, superseded by
  `notebooks/Catalogue_template.ipynb`.

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
  `overdetermined_system_pde`, `prolongation`, `make_infinitesimal`, `create_infinitesimals`
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

`tests/symmetry_catalog.py` is a catalogue of about 260 ODEs, systems of ODEs and PDEs with
their known symmetries: Kamke's collection (as classified in Schwarz's Appendix E), the
examples and exercises of Arrigo, Schwarz, Hydon, Baumann and others, and classical
equations. For each, the listed generators have to solve the determining equations and the
rank of their Janet basis has to be the dimension of the symmetry algebra.
`tests/test_schwarz_examples.py` checks the Janet bases printed in Schwarz's book, coefficients
included.

    uv run pytest                    # the fast tests, including the doctests of this README
    uv run pytest -m slow -n auto    # the whole catalogue, about 15 s

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
