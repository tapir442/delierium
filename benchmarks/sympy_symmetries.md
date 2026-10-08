# delierium, SymPy and sympy-extras: Lie point symmetries (benchmark #6)

Produced by `benchmarks/sympy_symmetries.py` (see its docstring for the tools and the
method): every task in its own process with a timeout of 60 s and a memory limit.
SymPy 1.14.0, sympy-extras 0.0.2, delierium at the state of PR "complex coefficients"
(after 2.1.0). SymPy's and sympy-extras' Kamke results are from the run of 2026-09-30
(both unchanged since); delierium's tools and all cross checks were rerun on
2026-10-08, the catalogue (579 entries) completely, at 3 processes.

## Summary

- **SymPy** (`infinitesimals`) handles first order ODEs only; on Kamke's first order
  equations its default hint succeeds on 570 of 988, `hint="all"` on 359 (timeouts and
  exceptions in the heuristics). On the catalogue it finds generators for 43 of 579
  entries (first order ODEs and some systems).
- **delierium** gives the determining equations for 966 and the Janet basis for 947 of
  the 988; 13 (Kamke 1.553 - 1.576) are not implemented: transcendental in `y'` and not
  solvable for it (`y' + sin(y') = x`, arbitrary functions of `y'`, `a y'**m + b y'**n`).
  On the 355 equations where all tools succeed, its medians are 0.10 s (determining
  equations) and 0.16 s (Janet basis) against 0.28 s for SymPy's default hint and 2.6 s
  for `hint="all"`; in total 38 s and 67 s against 1193 s and 2833 s. On the catalogue its
  dimension agrees with the literature for all 579 entries except 3 PDEs over the time
  limit, and it confirms all 1254 published generators (1 timeout).
- **sympy-extras** (polynomial ansatz of degree 2) is fast and finds explicit
  generators, but only polynomial ones: fewer than the dimension for many ODEs; for 67 PDEs
  with parameters or arbitrary functions it reports more generators than the literature
  dimension, i.e. it treats them not generically. 63 of the published generators are
  rejected by its own check.

Cross checks of SymPy's generators against delierium's determining equations, and what
they found:

- **A bug in delierium, fixed:** for equations with complex coefficients (Kamke 1.743,
  1.759, 1.769, 1.885, 1.894) the determining equations were split into real and imaginary
  parts, which assumes real infinitesimals; SymPy's complex generators were rejected
  although the textbook condition for `y' = F` holds.
- **Simplification in `verify_symmetry`, improved:** `y' = sqrt(|y|)` (1.57) and
  `y'**n = f(x) g(y)` (1.552) have residues that vanish for positive variables; they count
  now (symmetries are local). For Kamke 1.192 this means a symmetry for `a > 0`, where
  SymPy's check (for all `a`) says no. Kamke 1.565 needs a Lambert W identity: #77.
- **SymPy's check fails** on its own `Piecewise` generators for 1.59 and 1.76; delierium
  confirms them (the residue vanishes for `a != 0` and has a factor `a**2`).
- **Equations nonlinear in `y'`** (Kamke 1.374 - 1.549, e.g. 1.442 and 1.481 factor into
  two first order ODEs): SymPy's and sympy-extras' generators are symmetries of one branch
  only, not of the whole equation, which delierium rejects correctly (#72 is about the
  branches). Such equations can have a finite algebra (delierium ranks 3, 1 or 0 for 30 of
  them, #28).

# Results

Runs (the equations of a run cut short by its time budget are a random sample):

- sympy_symmetries-2026-09-30.jsonl: kamke 1414 of 1435 equations, catalog 257 of 263 equations, time budget 120 min, 14 processes; tools cross_deli, cross_sympy, deli_det, deli_gens, deli_janet, sympy_all, sympy_best, sympy_default, sympy_gens
- sympy_extras-2026-09-30.jsonl: kamke 1435 of 1435 equations, catalog 263 of 263 equations, time budget 10 min, 14 processes; tools cross_extras, extras, extras_gens
- deli-kamke-2026-10-08.jsonl: kamke 1435 of 1435 equations, 3 processes; tools cross_deli, cross_extras, deli_det, deli_janet
- catalog-2026-10-08.jsonl: catalog 579 of 579 equations, 3 processes; tools deli_gens, deli_janet, extras, extras_gens, sympy_all, sympy_gens

## A. First order ODEs: Kamke chapters 1 and 2 (988 equations)

Orders of all equations in the two chapters: {1: 988, 2: 447}; only the first order ones are counted below.

Timeout 60 s per task, one fresh process per task.

| tool | ok | timeout | not implemented | error | memory/crash |
|---|---|---|---|---|---|
| sympy_default | 570 | 269 | 96 | 39 | 0 |
| sympy_all | 359 | 426 | 97 | 92 | 0 |
| sympy_best | 447 | 426 | 101 | 0 | 0 |
| deli_det | 966 | 9 | 13 | 0 | 0 |
| deli_janet | 947 | 28 | 13 | 0 | 0 |
| extras | 961 | 13 | 13 | 0 | 1 |

Run times of the successful runs (seconds):

| tool | n | total | median | 90% | max |
|---|---|---|---|---|---|
| sympy_default | 570 | 1589.0 | 0.285 | 7.641 | 58.07 |
| sympy_all | 359 | 2976.8 | 2.654 | 26.378 | 58.26 |
| sympy_best | 447 | 3657.7 | 2.622 | 24.893 | 59.83 |
| deli_det | 966 | 297.2 | 0.115 | 0.240 | 47.67 |
| deli_janet | 947 | 468.3 | 0.193 | 0.551 | 47.05 |
| extras | 961 | 814.3 | 0.207 | 0.999 | 59.72 |

On the 355 equations where all 6 succeed:

| tool | n | total | median | 90% | max |
|---|---|---|---|---|---|
| sympy_default | 355 | 1192.8 | 0.278 | 10.356 | 44.19 |
| sympy_all | 355 | 2832.7 | 2.626 | 25.874 | 58.26 |
| sympy_best | 355 | 2834.5 | 2.800 | 23.914 | 57.99 |
| deli_det | 355 | 38.0 | 0.103 | 0.138 | 0.24 |
| deli_janet | 355 | 66.5 | 0.157 | 0.276 | 1.64 |
| extras | 355 | 73.7 | 0.166 | 0.327 | 2.23 |

delierium ranks (expected oo for every first order ODE): {'oo': 917, '3': 14, '1': 12, '0': 4}

SymPy generators found per equation (sympy_best): {1: 237, 2: 135, 3: 57, 4: 12, 5: 1, 6: 5}

SymPy's exceptions (hint default/all stop at the first heuristic that raises):

- 63 × sympy_all: TypeError: argument of type 'Mul' is not a container or iterable
- 34 × sympy_default: TypeError: argument of type 'Mul' is not a container or iterable
- 12 × sympy_all: KeyError: C_
- 7 × sympy_all: TypeError: 'NoneType' object is not subscriptable
- 4 × sympy_all: TypeError: argument of type 'Pow' is not a container or iterable
- 3 × sympy_all: UnboundLocalError: cannot access local variable 'polyy' where it is not associated with a 
- 2 × sympy_default: TypeError: argument of type 'Pow' is not a container or iterable
- 1 × sympy_all: TypeError: argument of type 'Zero' is not a container or iterable
- 1 × sympy_default: RecursionError: maximum recursion depth exceeded
- 1 × sympy_all: RecursionError: maximum recursion depth exceeded
- 1 × sympy_default: PolynomialDivisionFailed: couldn't reduce degree in a polynomial division algorithm when d
- 1 × sympy_all: PolynomialDivisionFailed: couldn't reduce degree in a polynomial division algorithm when d
- 1 × sympy_default: TypeError: 'NoneType' object is not subscriptable

| heuristic | found generators on | raised an exception on |
|---|---|---|
| abaco1_simple | 109 | 0 |
| abaco1_product | 105 | 0 |
| abaco2_similar | 164 | 19 |
| abaco2_unique_unknown | 29 | 0 |
| abaco2_unique_general | 0 | 68 |
| linear | 146 | 0 |
| function_sum | 11 | 0 |
| bivariate | 221 | 7 |
| chi | 36 | 0 |

### Cross check of SymPy's generators

- equations: 447
- generators: 761
- sympy ok / delierium ok: 680
- sympy FAIL / delierium FAIL: 25
- sympy ok / delierium FAIL: 53
- sympy FAIL / delierium ok: 3
- disagreeing equations: 1.192, 1.374, 1.382, 1.389, 1.391, 1.393, 1.396, 1.438, 1.439, 1.440, 1.441, 1.442, 1.445, 1.449, 1.471, 1.481, 1.505, 1.523, 1.525, 1.536, 1.539, 1.540, 1.549, 1.565, 1.59, 1.76

| check | n | total | median | 90% | max |
|---|---|---|---|---|---|
| cross_sympy | 447 | 56.0 | 0.104 | 0.174 | 2.20 |
| cross_deli | 447 | 73.5 | 0.109 | 0.247 | 3.49 |

### sympy-extras on the first order ODEs

Generators found per equation (polynomial ansatz of degree 2; a first order ODE has infinitely many): {0: 527, 1: 325, 2: 62, 3: 19, 4: 25, 9: 3}

- generators confirmed by delierium: 577
- generators rejected by delierium: 55
- check did not finish (timeout): 1
- equations with rejected generators: 1.391, 1.396, 1.438, 1.439, 1.440, 1.442, 1.445, 1.449, 1.471, 1.481, 1.505, 1.526, 1.527, 1.539, 1.540

## B. delierium catalogue (579 entries)

| kind | entries | SymPy finds generators | delierium dimension right | wrong | no reference | delierium failed | delierium median s | max s |
|---|---|---|---|---|---|---|---|---|
| ode, order 1 | 33 | 23 | 33 | 0 | 0 | 0 | 0.13 | 0.5 |
| ode, order 2 | 162 | 0 | 162 | 0 | 0 | 0 | 0.19 | 5.1 |
| ode, order 3 | 72 | 0 | 72 | 0 | 0 | 0 | 0.28 | 1.2 |
| ode, order 4 | 2 | 0 | 2 | 0 | 0 | 0 | 0.38 | 0.4 |
| odes | 58 | 20 | 58 | 0 | 0 | 0 | 0.28 | 18.8 |
| pde | 252 | 0 | 249 | 0 | 0 | 3 | 0.30 | 16.0 |
- delierium timeout: Baumann p. 270: Karpman-Belashov (u_t + 6 u u_x - mu u_xx - epsilon u_xxx - lambda u_xxxxx)_x - u_yy = 0
- delierium timeout: EqWorld 2.2.5: w_tt = [a (x + b)**n w_x]_x + f(w)
- delierium timeout: Baumann p. 305: Stokes' creeping flow

### sympy-extras: generators found compared with the dimension

| kind | entries | = dimension | fewer | more | infinite dimension | no reference | failed | median s |
|---|---|---|---|---|---|---|---|---|
| ode, order 1 | 33 | 0 | 1 | 0 | 32 | 0 | 0 | 0.13 |
| ode, order 2 | 162 | 109 | 51 | 1 | 0 | 0 | 1 | 0.12 |
| ode, order 3 | 72 | 18 | 54 | 0 | 0 | 0 | 0 | 0.13 |
| ode, order 4 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 0.10 |
| odes | 58 | 3 | 1 | 0 | 49 | 0 | 5 | 0.20 |
| pde | 252 | 107 | 16 | 67 | 62 | 0 | 0 | 0.20 |
- more generators than the dimension: Arrigo Exercises 2.6, 3: sympy-extras 12, literature 3
- more generators than the dimension: nonlinear diffusion u_t = (u**(-4/3) u_x)_x: sympy-extras 11, literature 5
- more generators than the dimension: nonlinear diffusion u_t = (u**2 u_x)_x: sympy-extras 11, literature 4
- more generators than the dimension: nonlinear diffusion in the plane: sympy-extras 27, literature 6
- more generators than the dimension: EqWorld 1.2.6: w_t = a (w**n w_x)_x + b w + c1 w**m + c2 w**k: sympy-extras 6, literature 2
- more generators than the dimension: CRC 1, 12.4: nonlinear wave equation u_tt = (k u**(-4/3) u_x)_x: sympy-extras 13, literature 5
- more generators than the dimension: CRC 1, 10.8: anisotropic u_t = (u**s1 u_x)_x + (u**s2 u_y)_y: sympy-extras 27, literature 5
- more generators than the dimension: CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**(-2) u_x)_x: sympy-extras 9, literature 4
- more generators than the dimension: CRC 1, 12.4: nonlinear wave equation u_tt = (k u**sigma u_x)_x: sympy-extras 13, literature 4
- more generators than the dimension: CRC 1, 11.6: generalized Hopf equation u_t + u u_x = (u**(2 m) u_x)_x: sympy-extras 4, literature 3
- more generators than the dimension: AIMS 2026 II-(2): u_t = (exp(u) u_x**n)_x + e2 exp(u) - e3: sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.7: u_t = div(u**(-4/5) grad u) in space: sympy-extras 54, literature 12
- more generators than the dimension: CRC 1, 10.8: anisotropic u_t = (exp(a1 u) u_x)_x + (exp(a2 u) u_y)_y: sympy-extras 27, literature 5
- more generators than the dimension: EqWorld 1.2.9: w_t = [f(w) w_x]_x. Nonlinear heat equation of general form: sympy-extras 11, literature 3
- more generators than the dimension: CRC 1, 10.5: u_t = (exp(u) u_x)_x + d: sympy-extras 11, literature 4
- more generators than the dimension: Gabel et al. 10: u_t = (exp(u) u_x)_x - exp(u): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 12.4: nonlinear wave equation u_tt = (exp(u) u_x)_x: sympy-extras 13, literature 4
- more generators than the dimension: AIMS 2026 I-(5): u_t = (u**(1 - n) u_x**n)_x + e2 u: sympy-extras 6, literature 4
- more generators than the dimension: Gabel et al. 13: u_t = (exp(u) u_x)_x - 1: sympy-extras 11, literature 4
- more generators than the dimension: EqWorld 1.2.3: w_t = a (w**m w_x)_x + b w**(m + 1): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + a u**n: sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (k(u) u_x)_x: sympy-extras 9, literature 2
- more generators than the dimension: AIMS 2026 II-(1): u_t = (exp(u) u_x**n)_x + e2 exp(q u): sympy-extras 6, literature 3
- more generators than the dimension: Gabel et al. 12: u_t = (exp(u) u_x)_x + 1: sympy-extras 11, literature 4
- more generators than the dimension: CRC 1, 10.5: u_t = (u**sigma u_x)_x + a u**n: sympy-extras 6, literature 3
- more generators than the dimension: AIMS 2026 I-(4): u_t = (u**m u_x**n)_x + e2 u: sympy-extras 6, literature 4
- more generators than the dimension: EqWorld 2.2.1: w_tt = a (w w_x)_x: sympy-extras 13, literature 4
- more generators than the dimension: Gabel et al. 8: u_t = (exp(u) u_x)_x + exp(-2u): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.8: anisotropic u_t = (k1(u) u_x)_x + (k2(u) u_y)_y: sympy-extras 27, literature 4
- more generators than the dimension: CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam exp(nu u) u_x)_x: sympy-extras 9, literature 3
- more generators than the dimension: AIMS 2026 I-(1): u_t = (u**m u_x**n)_x + e u**r: sympy-extras 6, literature 3
- more generators than the dimension: Gabel et al. 9: u_t = (exp(u) u_x)_x + exp(-u): sympy-extras 6, literature 3
- more generators than the dimension: EqWorld 1.3.4: w_t = [f(w)(w_x)**n]_x + g(w): sympy-extras 6, literature 2
- more generators than the dimension: CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + a u**(-1/3): sympy-extras 6, literature 5
- more generators than the dimension: EqWorld 2.2.3: w_tt = a (exp(lam w) w_x)_x: sympy-extras 13, literature 4
- more generators than the dimension: Gabel et al. 11: u_t = (exp(u) u_x)_x - exp(2u): sympy-extras 6, literature 3
- more generators than the dimension: EqWorld 1.2.4: w_t = a (w**m w_x)_x + b w**(1 - m): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.7: u_t = div(u**sigma grad u) in the plane: sympy-extras 27, literature 6
- more generators than the dimension: EqWorld 6.1.1: w_tt + (w w_x)_x + w_xxxx = 0. Boussinesq equation: sympy-extras 8, literature 3
- more generators than the dimension: AIMS 2026 I-(3): u_t = (u**(1 - n) u_x**n)_x + e2 u log(u): sympy-extras 6, literature 3
- more generators than the dimension: EqWorld 1.2.1: w_t = a (w**m w_x)_x. Heat equation with a power-law nonlinearity: sympy-extras 11, literature 4
- more generators than the dimension: Gabel et al. 4: u_t = (exp(u) u_x)_x: sympy-extras 11, literature 4
- more generators than the dimension: AIMS 2026 I-(2): u_t = (u**m u_x**n)_x + e2 u**(m + n) - e3 u/(m + n - 1): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**(-4/3) u_x)_x: sympy-extras 9, literature 4
- more generators than the dimension: CRC 1, 10.5: u_t = (exp(u) u_x)_x + a exp(m u): sympy-extras 6, literature 3
- more generators than the dimension: EqWorld 1.2.5: w_t = a (w**(2n) w_x)_x + b w**(1 - n): sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.2: nonlinear heat equation u_t = (k(u) u_x)_x: sympy-extras 11, literature 3
- more generators than the dimension: CRC 1, 12.4: nonlinear wave equation u_tt = (k u**(-4) u_x)_x: sympy-extras 13, literature 5
- more generators than the dimension: CRC 1, 10.7: u_t = div(exp(u) grad u) in the plane: sympy-extras 27, literature 6
- more generators than the dimension: Gabel et al. 24: u_t = (exp(u) u_x)_x - u u_x: sympy-extras 4, literature 3
- more generators than the dimension: CRC 1, 10.5: u_t = (u**sigma u_x)_x + d u: sympy-extras 6, literature 4
- more generators than the dimension: EqWorld 1.2.7: w_t = a (exp(lam w) w_x)_x. Heat equation with a exponential nonlinearity: sympy-extras 11, literature 4
- more generators than the dimension: CRC 1, 10.7: u_t = div(k(u) grad u) in the plane: sympy-extras 27, literature 5
- more generators than the dimension: EqWorld 3.3.1: w_xx + [(al w + be) w_y]_y = 0. Stationary Khokhlov-Zabolotskaya equation: sympy-extras 13, literature 4
- more generators than the dimension: EqWorld 1.2.10: w_t = [f(w) w_x]_x + g(w). Nonlinear heat equation with a source of general form: sympy-extras 6, literature 2
- more generators than the dimension: CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + d u: sympy-extras 6, literature 5
- more generators than the dimension: CRC 1, 11.6: generalized Hopf equation u_t + u u_x = (k(u) u_x)_x: sympy-extras 4, literature 2
- more generators than the dimension: EqWorld 2.2.7: w_tt = [f(w) w_x]_x: sympy-extras 13, literature 3
- more generators than the dimension: EqWorld 3.3.3: [f(w) w_x]_x + [g(w) w_y]_y = 0. Anisotropic heat (diffusion) equation: sympy-extras 30, literature 3
- more generators than the dimension: EqWorld 1.2.8: w_t = a (exp(lam w) w_x)_x + b + c1 exp(be w) + c2 exp(sig w): sympy-extras 6, literature 2
- more generators than the dimension: CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**nu u_x)_x: sympy-extras 9, literature 3
- more generators than the dimension: EqWorld 2.2.2: w_tt = a (w**n w_x)_x + b w**k: sympy-extras 6, literature 3
- more generators than the dimension: CRC 1, 10.7: u_t = div(k(u) grad u) + q(u) in the plane: sympy-extras 18, literature 4
- more generators than the dimension: CRC 1, 10.2: nonlinear heat equation u_t = (u**sigma u_x)_x: sympy-extras 11, literature 4
- more generators than the dimension: EqWorld 3.3.2: w_xx + (a exp(be w) w_y)_y = 0. Anisotropic heat (diffusion) equation: sympy-extras 13, literature 4
- more generators than the dimension: CRC 1, 10.5: heat equation with a source u_t = (k(u) u_x)_x + q(u): sympy-extras 6, literature 2
- more generators than the dimension: CRC 1, 12.4: nonlinear wave equation u_tt = (phi(u) u_x)_x: sympy-extras 13, literature 3
- more generators than the dimension: EqWorld 1.2.2: w_t = a (w**m w_x)_x + b w: sympy-extras 6, literature 4
- 6 × sympy-extras timeout: 

SymPy's answers where it found nothing:

- 252 × error: ValueError: ODE's have only one independent variable
- 240 × notimpl: Infinitesimals for only first order ODE's have been implemented
- 15 × error: KeyError: C_
- 12 × notimpl: Infinitesimals could not be found for the given ODE
- 10 × error: TypeError: 'NoneType' object is not subscriptable
- 4 × timeout: 
- 2 × error: UnboundLocalError: cannot access local variable 'polyy' where it is not associated with a 
- 1 × error: TypeError: argument of type 'Mul' is not a container or iterable

### Published generators

- deli_gens: {'confirmed': 1254, 'rejected': 0, 'timeout': 1}; median 0.199 s
- sympy_gens: {'confirmed': 39, 'rejected': 0}; median 0.080 s
- extras_gens: {'confirmed': 1197, 'rejected': 63}; median 0.047 s
