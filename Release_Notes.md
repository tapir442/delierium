# Release notes

Details are in the issues referenced.

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
