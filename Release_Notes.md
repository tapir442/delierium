# Release notes

Details are in the issues referenced.

### 2.7.0

* Faster Janet bases (`determining_janet_basis` over the catalogue about 112 s → 102 s) and
  assumptions: `assumed_nonzero` factors by python-flint (Kamke 6.87, 6.219, 6.171 and
  EqWorld 2.2.5 took over 120 s each, now at most 2.2 s); results unchanged. Janet basis,
  `assumed_nonzero`, `parameter_conditions` and `singular_loci` together: Kamke 6.87
  1619 s → 0.5 s, Kamke 6.219 638 s → 1.7 s.
* `janet_basis_from_ode` on 338 scalar ODEs: 304.2 s in 1.0.0, 15.1 s now (median entry
  6.5x faster; 1.6x faster than 2.6.0):

  | | 1.0.0 | 2.6.0 | 2.6.1 | 2.7.0 |
  |---|---|---|---|---|
  | total | 304.2 s | 334.4 s | 16.5 s | 15.1 s |
  | without Kamke 6.219 | 88.4 s | 28.0 s | 15.0 s | 14.0 s |
  | median entry | 0.202 s | 0.053 s | 0.031 s | 0.030 s |
* Janet bases with large coefficients: `primitive` and large products by python-flint, and
  the reduction divides the two multipliers by their gcd; results unchanged on all 786
  catalogue entries. EqWorld ODE 3.32 about 190 s → 8.4 s, Painlevé V (over 300 s) 47 s;
  the catalogue 116 s → 105 s (flint), then 187 s → 158 s (gcd; with 3.32 and Painlevé V,
  2 processes at a time).
* Python 3.15.1 against 3.14.4, catalogue Janet bases (786 entries, the same bases): median
  entry 1.12x faster, total 155.5 s → 150.1 s; Painlevé V and EqWorld 3.32 slower (46.0 s →
  48.9 s, 8.3 s → 10.0 s), probably python-flint's generic abi3 wheel on 3.15.
* `delierium.multipliers`: the multipliers and nonmultipliers of the Janet division, moved
  out of `janet_basis`.
* Solver: new steps `solve_algebraic` and `integrate_known`, exponentials from characteristic
  equations in the ansatz; fixed spurious conditions from `exp(a*log(y))` next to `y**a`,
  `sin**2 + cos**2`, and `re`/`im` of symbolic roots.
  Complete generators for 525 of the 611 finite catalogue entries (was 511), none lost.
* `integrate_ode`: rational quadratures with symbolic denominators of high degree stay
  integrals (they exhausted the memory); random points with derivatives of arbitrary
  functions. 121 of the 176 catalogue ODEs with generators solved (was 115), none lost.
* Catalogue: EqWorld's ODEs 3.1-3.51, 5.1 and Painlevé I-V (56 entries), cross-checked with
  BLAD and REDUCE's LIEPDE where possible.
* Python 3.15 supported (CI tests 3.12-3.15).

### 2.6.1

* Faster determining equations and Janet bases; results unchanged. python-flint is a new
  dependency (gcd of the coefficients in the Janet basis).
* `determining_janet_basis` over the whole catalogue (730 entries, one process each):
  921 s in 2.6.0, 148 s with the python-flint gcd, 114 s in 2.6.1 (fewer `expand()` and
  `cancel()`: numerators and coefficients in sparse polynomial rings, no `cancel()` of the
  equations of a Janet basis, cheaper comparisons of the unknowns). Kamke 6.171 (over 600 s
  in 2.6.0) takes 3 s, EqWorld 2.2.5 457 s → 4 s, Kamke 6.219 307 s → 1.6 s.
* `janet_basis_from_ode` on the 342 scalar ODEs of the catalogue, the 338 that all three
  versions finish (1.0.0 fails on four, 2.6.0 on Kamke 6.171):

  | | 1.0.0 | 2.6.0 | 2.6.1 |
  |---|---|---|---|
  | total | 304.2 s | 334.4 s | 16.5 s |
  | without Kamke 6.219 | 88.4 s | 28.0 s | 15.0 s |
  | median entry | 0.202 s | 0.053 s | 0.031 s |

  Per entry (median) 2.6.1 is 6.4x faster than 1.0.0 and 1.6x faster than 2.6.0; the Janet
  bases equal those of 2.6.0 on all 338 entries. AMD Ryzen 9 7900X, Linux 7.0, Python
  3.14.4, SymPy 1.14.0, python-flint 0.9.0; 3 processes at a time, nice 19.

### 2.6.0

* `integrate_ode`: ODEs solved by quadratures along a solvable symmetry algebra, and
  `reduce_order` by one generator ([#43](https://github.com/tapir442/delierium/issues/43),
  [#14](https://github.com/tapir442/delierium/issues/14)).

### 2.5.0

* Experimental: `optimal_system`, one-dimensional optimal systems of a Lie algebra under the
  adjoint action, and `adjoint_matrix`, `adjoint_invariants` ([#44](https://github.com/tapir442/delierium/issues/44)).
* Faster determining equations and Janet bases (median 2.2x over the catalogue; polynomial
  equations in one polynomial ring).

### 2.4.0

* `invariants`, `canonical_coordinates`, `differential_invariants` of a given generator
  ([#42](https://github.com/tapir442/delierium/issues/42)).
* `similarity_reduction`: a PDE by a given generator in one independent variable less
  ([#15](https://github.com/tapir442/delierium/issues/15)).
* Every function has a doctest; the module doctests run with the tests.
* Fixed: derivatives of constants in the equations (a parameter set to 0 in (k u**-4 u_x)_x).

### 2.3.0

* `lie_symmetries`: determining equations, Janet basis, dimension, algebra and generators in
  one call ([#10](https://github.com/tapir442/delierium/issues/10)).
* `delierium.solve`: generators by an extensible solver, a list of steps, user steps
  included ([#9](https://github.com/tapir442/delierium/issues/9)); 410 of the 499 finite catalogue entries complete.
* Fixed: `group_classification` with roots of the parameters ([#83](https://github.com/tapir442/delierium/issues/83)); determining
  equations when the highest derivative is inside an arbitrary function ([#84](https://github.com/tapir442/delierium/issues/84)).
* The public functions check their arguments; `euler_operator(dependent, independent)`
  (`depend`, `independ` deprecated).

### 2.2.0

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
* `verify_symmetry` uses the identities of the Lambert W function ([#77](https://github.com/tapir442/delierium/issues/77)).
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

### 1.0.0

Had a hard time debugging and profiling (a Janet base is, after all, a Gröbner base, with all
its implications during computation), and claude was of great help to find and fix all the
next-to-last bugs.

The determining equations of ODEs, systems of ODEs and scalar PDEs, their Janet bases and
rank, and pictures; solving the determining equations for the infinitesimals is not part of
this release.
