# delierium compared with other tools

How delierium 2.7.0 compares with other programs for Lie point symmetries, Janet bases and
Lie algebras, on the 786 equations of its catalogue (`tests/symmetry_catalog.py`: 398 ODEs,
59 ODE systems, 329 PDEs from textbooks, handbooks, EqWorld and machine-learning
benchmarks, each with the dimension of its symmetry algebra and the published generators,
1790 in all; 611 entries have a finite algebra).

Every difference between a tool and delierium was checked against delierium's determining
equations: a generator is a symmetry if and only if it satisfies them, and the dimension is
that of the Janet basis. Where a tool and delierium disagreed, delierium was right. For
each catalogue entry where a tool differs there is a paragraph below: the
equation, the dimension, what the tool returned, the generators it got wrong or missed, and
the cause. The dimension given is the catalogue's, the same as delierium's; *rejected*
generators fail delierium's determining equations (no symmetries); *missing* are published
generators outside the span of the tool's generators; *not closed*: the tool's generators are
not closed under commutators. The sources of the equations are in `tests/symmetry_catalog.py`;
the Kamke equations of chapters 1 and 2 are those of SymPy's test suite.

**Setup.** 2026-10-28; AMD Ryzen 9 7900X (12 cores, 24 threads), 29 GB, Linux 7.0;
Python 3.14.4, SymPy 1.14.0, python-flint 0.9.0; delierium 2.7.0.
Every entry in its own process with a time limit (60 to 300 s, given per tool) and a memory
limit, at most 3 processes at a time, nice 19. The scripts are in `benchmarks/`, the raw
results in `benchmarks/tool-comparison/`; tools that may not be redistributed (MathLie,
ReLie, DIMSYM) are not included, nor their output.

"Not compared" covers what a tool cannot take (first order ODEs for MathLie, equations not
solved for a derivative, arbitrary functions of expressions for some), its timeouts, and
comparisons over the limits; such entries are counted in each tool's table but get no
paragraph.


## Summary

| tool | computes | entries compared | same as delierium | differ |
|---|---|---|---|---|
| SymPy 1.14 | some generators of first order ODEs | first order ODEs only | see below | see below |
| sympy-extras 0.0.2 | generators, polynomial ansatz of degree ≤ 2 | 608 | 363 | 72 wrong; fewer by design |
| LIEPDE (REDUCE) | generators (CRACK) | 723 | 689 | 34 |
| ReLie 3.0 (REDUCE) | generators (CRACK) | 715 | 691 | 24 |
| DIMSYM 2.3 (REDUCE) | generators | 714 | 713 | 1 |
| SPDE 1986 (REDUCE) | generators | 644 | 492 | 152 |
| MathLie 3.0 (Mathematica 15.0) | generators | 559 | 523 | 36 |
| symmgrp2020 (Maxima) | determining equations | 694 | 676 | 18 |
| BLAD (DifferentialAlgebra) | Rosenfeld-Groebner, dimension | 539 | 539 | 0 |
| CoCoA 5.4, Singular 4 | Janet bases of polynomial ideals | 207 systems | 207 | 0 |
| Singular Plural | Groebner bases in the Weyl algebra | 199 systems | 199 | 0 |
| GAP 4 | Lie algebra invariants | 376 algebras | 376 | 0 |


---

<div style="page-break-before: always"></div>

## SymPy

SymPy 1.14.0 (`infinitesimals`, `checkinfsol`): some generators of first order ODEs by heuristics; everything else raises NotImplementedError (`benchmarks/sympy_symmetries.py`, 60 s per task).

Catalogue (786 entries), `infinitesimals(hint="all")`:

| result | entries |
|---|---|
| error | 363 |
| notimpl | 344 |
| ok | 53 |
| timeout | 26 |

Kamke chapters 1 and 2: SymPy's generators of the first order ODEs (every heuristic separately), checked by delierium 2.7.0: 761 generators, 76 rejected. Every rejection was checked independently of delierium (the textbook condition for y' = F, or the branches); delierium was right in all of them.

### Entries that differ (39)

#### One branch of y' (26)

The ODE is of degree ≥ 2 in y'; SymPy solves it for y' and uses one root, so its generators are symmetries of one branch only, not of the equation (sympy/sympy#30643). delierium works with the equation as given.

[^zoo]: SymPy's ComplexInfinity: a division by zero inside its heuristics.

| entry | equation | generators | rejected |
|---|---|---|---|
| Kamke 1.374 | -y<sup>2</sup> + y'<sup>2</sup> - 2 y' = 0 | 2 | (0, √(y<sup>2</sup> + 1) - 1) |
| Kamke 1.375 | a y' + b x + y'<sup>2</sup> = 0 | 3 | (e<sup>-b Piecewise((log(a + √(a<sup>2</sup> - 4 b x))/b, Ne(b, 0)), (x/((-a/2 - √(a<sup>2</sup>)/2) √(a<sup>2</sup>)), True))</sup>, 0) |
| Kamke 1.376 | a y' + b y + y'<sup>2</sup> = 0 | 2 | (0, e<sup>b Piecewise((log(a + √(a<sup>2</sup> - 4 b y))/b, Ne(b, 0)), (y/((-a/2 - √(a<sup>2</sup>)/2) √(a<sup>2</sup>)), True))</sup>) |
| Kamke 1.382 | a x y' - b x<sup>2</sup> - c + y'<sup>2</sup> = 0 | 2 | (1/(a x + √(a<sup>2</sup> x<sup>2</sup> + 4 b x<sup>2</sup> + 4 c)), 0) |
| Kamke 1.389 | y (4 y + 1) + y'<sup>2</sup> - y' (4 y + 1) = 0 | 2 | (0, -4 y + √(4 y + 1) - 1) |
| Kamke 1.391 | a b x y + y'<sup>2</sup> + y' (a y + b x) = 0 | 3 | (0, e<sup>-a x</sup>), (0, y), (1, 0) |
| Kamke 1.393 | -y<sup>2</sup> + 2 y y' cot(x) + y'<sup>2</sup> = 0 | 3 | (0, e<sup>Integral(√(sin(x)<sup>-2</sup>) - cot(x), x)</sup>), (1/(√(sin(x)<sup>-2</sup>) - cot(x)), 0) |
| Kamke 1.396 | -x y<sup>3</sup> + y y' (-x + y) + y'<sup>2</sup> = 0 | 4 | (0, e<sup>x<sup>2</sup>/2</sup>), (0, y), (1/x, 0) ... |
| Kamke 1.403 | a y'<sup>2</sup> + b y' - y = 0 | 2 | (0, e<sup>-2 a Piecewise((-log(b + √(4 a y + b<sup>2</sup>))/(2 a), Ne(a, 0)), (y/((-b - √(b<sup>2</sup>)) √(b<sup>2</sup>)), True))</sup>) |
| Kamke 1.431 | x<sup>2</sup> y'<sup>2</sup> - y<sup>4</sup> + y<sup>2</sup> = 0 | 2 | (e<sup>-Piecewise((I acosh(1/y), 1/Abs(y<sup>2</sup>) > 1), (-asin(1/y), True))</sup>, 0) |
| Kamke 1.438 | x<sup>2</sup> y'<sup>2</sup> + 3 x y y' + 2 y<sup>2</sup> = 0 | 6 | (0, x<sup>-2</sup>), (1/√y, 0), (x, zoo[^zoo]/x) ... |
| Kamke 1.439 | x<sup>2</sup> y'<sup>2</sup> + 3 x y y' + 3 y<sup>2</sup> = 0 | 6 | (0, e<sup>(-3/2 + √3 I/2) log(x)</sup>), (e<sup>-2 I log(y)/(√3 + 3 I)</sup>, 0), (x, zoo[^zoo]/x) ... |
| Kamke 1.440 | x<sup>2</sup> y'<sup>2</sup> + 4 x y y' - 5 y<sup>2</sup> = 0 | 6 | (0, x<sup>-5</sup>), (y<sup>-1/5</sup>, 0), (x, zoo[^zoo]/x) ... |
| Kamke 1.441 | x<sup>2</sup> y'<sup>2</sup> - 4 x y' (y + 2) + y (4 y + 8) = 0 | 3 | (0, 2 y - 2 √(2 y + 4) + 4), (√(√(2 y + 4) - 2) √(2 y - 2 √(2 y + 4) + 4)/(2 y + 4)<sup>1/4</sup>, 0) |
| Kamke 1.442 | x<sup>2</sup> y'<sup>2</sup> + y' (x<sup>3</sup> + x<sup>2</sup> y - 2 x y) + (1 - x) (-x<sup>2</sup> y + y<sup>2</sup>) = 0 | 4 | (0, x e<sup>-x</sup>), (0, y), (nan, nan) ... |
| Kamke 1.445 | a b y<sup>3</sup> + x<sup>2</sup> y'<sup>2</sup> + y' (a x<sup>2</sup> y<sup>3</sup> + b) = 0 | 2 | (0, y<sup>3</sup>), (1, 0) |
| Kamke 1.449 | 2 x y y' + y<sup>2</sup> + y'<sup>2</sup> (-a<sup>2</sup> + x<sup>2</sup>) = 0 | 6 | (0, 1/(-a + x)), (-a + x, 0), (zoo[^zoo]/y, y) ... |
| Kamke 1.471 | -x + y y'<sup>2</sup> - y' (-x + y) = 0 | 2 | (0, 1), (1, 0) |
| Kamke 1.481 | x y y'<sup>2</sup> + x y + y' (x<sup>2</sup> + y<sup>2</sup>) = 0 | 6 | (0, 1/x), (0, y), (x, 0) ... |
| Kamke 1.505 | -x<sup>3</sup> + x y<sup>2</sup> y'<sup>2</sup> + 2 x y<sup>2</sup> - 2 y<sup>3</sup> y' = 0 | 3 | (0, 1/y), (1/x, 0), (x + y, x + y) |
| Kamke 1.523 | -a x y' + x<sup>3</sup> + y'<sup>3</sup> = 0 | 3 | (e<sup>(-18 3<sup>1/3</sup> a (√3 √(27 - 4 a<sup>3</sup>) + 9)<sup>1/3</sup> - 9 2<sup>1/3</sup> √3 √(27 - 4 a<sup>3</sup>) - 81 2<sup>1/3</sup>) log(x)/(18 3<sup>1/3</sup> a (√3 √(27 - 4 a<sup>3</sup>) + 9)<sup>1/3</sup> + 9 2<sup>1/3</sup> √3 √(27 - 4 a<sup>3</sup>) + 81 2<sup>1/3</sup>)</sup>, 0), (x/2 - 3 2<sup>2/3</sup> (√3 √(27 - 4 a<sup>3</sup>) + 9)<sup>2/3</sup>/(2 3<sup>2/3</sup> a (√3 √(27 - 4 a<sup>3</sup>) + 9)<sup>1/3</sup> + 2<sup>1/3</sup> 3<sup>5/6</sup> √(27 - 4 a<sup>3</sup>) + 9 6<sup>1/3</sup>), x + y + 1) |
| Kamke 1.525 | -a x y y' + 2 a y<sup>2</sup> + y'<sup>2</sup> = 0 | 3 | (0, e<sup>a x<sup>2</sup>/4 - Piecewise((-4 a Piecewise((log(2 a<sup>2</sup> x + 2 √(a<sup>2</sup> x<sup>2</sup> - 8 a) √(a<sup>2</sup>))/√(a<sup>2</sup>), Ne(a, 0)), (x log(x)/√(a<sup>2</sup> x<sup>2</sup>), True)) + x √(a<sup>2</sup> x<sup>2</sup> - 8 a)/2, Ne(a<sup>2</sup>, 0)), (2 √2 x √(-a), True))/2</sup>), (1/(a x - √(a (a x<sup>2</sup> - 8))), 0), (nan, nan) |
| Kamke 1.536 | b x y'<sup>2</sup> (-a<sup>2</sup> + x<sup>2</sup>) + b x + y'<sup>3</sup> (-a<sup>2</sup> + x<sup>2</sup>) + y' = 0 | 2 | (√(-a<sup>2</sup> + x<sup>2</sup>), 0) |
| Kamke 1.539 | y sin(x) + y'<sup>3</sup> sin(x) + y'<sup>2</sup> (-y sin(x) + cos(x)<sup>2</sup>) - y' (y cos(x)<sup>2</sup> + sin(x)) = 0 | 2 | (0, 1), (sin(x), 0) |
| Kamke 1.540 | 2 x y' - x + 2 y y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 3 | (0, 1), (1, 0), (5 x/2 + y + 1, x + y + 1) |
| Kamke 1.549 | -a<sup>2</sup> + x<sup>2</sup> (y'<sup>2</sup> + 1)<sup>3</sup> = 0 | 2 | (1/√((a<sup>2</sup>/x<sup>2</sup>)<sup>1/3</sup> - 1), 0) |

#### Generator fails the symmetry condition (11)

SymPy's heuristic returns a generator that fails the textbook condition η<sub>x</sub> + (η<sub>y</sub> - ξ<sub>x</sub>) F - ξ<sub>y</sub> F<sup>2</sup> - ξ F<sub>x</sub> - η F<sub>y</sub> = 0 for y' = F, checked independently of delierium.

| entry | equation | generators | rejected | note |
|---|---|---|---|---|
| Kamke 1.38 | -a y<sup>3</sup> - b/x<sup>1.5</sup> + y' = 0 | 1 | (0, a y<sup>3</sup>/b + x<sup>-1.5</sup>) | – |
| Kamke 1.52 | -a y<sup>n</sup> - b x<sup>n/(1 - n)</sup> + y' = 0 | 2 | (0, Piecewise(((-1 + 1/n)/x<sup>n/(n - 1)</sup>, Ne(n, 0)), (log(x), True)) + Piecewise((-a y<sup>n</sup> (n - 1)/(b n), (n > 0) | (n < 0)), (-a y<sup>n</sup>/b + a y<sup>n</sup>/(b n) - log(y) - 1/y<sup>n/(n - 1)</sup> + 1/(n y<sup>n/(n - 1)</sup>), True))) | – |
| Kamke 1.81 | y' + 2 tan(x) tan(y) - 1 = 0 | 1 | (0, 2 tan(y) - 1/tan(x)) | – |
| Kamke 1.188 | -a y<sup>3</sup> - b x<sup>3 n</sup> + x<sup>2 n + 1</sup> y' = 0 | 2 | (0, Piecewise((x<sup>3 n</sup>/(3 n), Ne(n, 0)), (log(x), True)) + Piecewise((a y<sup>3</sup>/(3 b n), (n > 0) | (n < 0)), (a y<sup>3</sup>/(3 b n) - log(y) + y<sup>3 n</sup>/(3 n), True))) | – |
| Kamke 1.189 | -a y<sup>n</sup> - b x<sup>n (m + 1)</sup> + x<sup>m (n - 1) + n</sup> y' = 0 | 2 | (0, Piecewise(((a y<sup>n</sup> - b n (m + 1) log(y) + b y<sup>n (m + 1)</sup>)/(b n (m + 1)), Eq(m, -1) | Eq(n, 0)), (a y<sup>n</sup>/(b n (m + 1)), True)) + Piecewise((log(x), Eq(m, -1) | Eq(n, 0)), (x<sup>n (m + 1)</sup>/(n (m + 1)), True))) | – |
| Kamke 1.202 | y' f(x) + g(x) tg(y) + h(x) = 0 | 1 | (0, -tg(y) + Integral((g'(x) h(x) - h'(x) g(x))/g(x)<sup>2</sup>, x) - Integral((g'(y) h(y) - h'(y) g(y))/g(y)<sup>2</sup>, y) - h(y)/g(y)) | SymPy's generator has g(y), h(y) where the equation has g(x), h(x) (its integral in y of an expression in x). |
| Kamke 1.204 | a y + x + y y' = 0 | 3 | (0, 1/x + 1/(a y)) | – |
| Kamke 1.206 | a y - 2 a + b e<sup>x</sup> + y y' = 0 | 1 | (0, -1/(-2 a + b e<sup>x</sup>) + (-2 a + b e<sup>y</sup>)/(a y (2 a - b e<sup>y</sup>))) | – |
| Kamke 1.213 | -x - y + y' (y + 1) = 0 | 2 | (0, (1 - y)/((y - 1) (y + 1)) - 1/(x - 1)) | – |
| Kamke 1.237 | b y + c x + x y' (a + y) = 0 | 2 | (0, -1/(-a b + c x) + (-a b + c y)/(b (a<sup>2</sup> b + a b y - a c y - c y<sup>2</sup>))) | – |
| Kamke 1.640 | -y/(-log(x) + log(log(y)) + 1) + y' = 0 | 1 | (-log(x) + log(log(y)) + 1, 0) | – |

#### nan as generator (2)

SymPy's heuristic returns (nan, nan).

| entry | equation | generators | rejected |
|---|---|---|---|
| Kamke 1.161 | x<sup>2</sup> + 3 x y - 8 y + y' (x<sup>2</sup> - 5 x + 6) = 0 | 3 | (nan, nan) |
| Kamke 1.193 | -a x (log(x) + 1) + x y' log(x) + y = 0 | 3 | (nan, nan) |


---

<div style="page-break-before: always"></div>

## sympy-extras

sympy-extras 0.0.2 (`symmetries`, `check_symmetry`): explicit generators by a polynomial ansatz of total degree ≤ 2, so a lower bound of the dimension (`benchmarks/sympy_symmetries.py`, 60 s per task).

| | entries |
|---|---|
| finite catalogue entries answered | 608 of 611 |
| as many generators as the dimension | 363 |
| fewer, all correct (degree ≤ 2) | 173 |
| wrong generators | 72 |
| published generators rejected by `check_symmetry` | 43 entries |

### Wrong generators (72)

#### Divergence form (69)

The equation is in divergence form, e.g. (u<sup>s</sup> u<sub>x</sub>)<sub>x</sub> as an unevaluated Derivative of a product; sympy-extras does not evaluate it and returns transformations that are no symmetries (Upabjojr/sympy-extras#71).

| entry | equation | dimension | generators | rejected | examples of rejected |
|---|---|---|---|---|---|
| Arrigo Exercises 2.6, 3 | ((y/y')'' y y')' = 0 | 3 | 12 | 9 | (y, 0), (x<sup>2</sup>, 0) ... |
| nonlinear diffusion in the plane | -(u u<sub>x</sub>)<sub>x</sub> - (u u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| nonlinear diffusion u<sub>t</sub> = (u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> | -(u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| nonlinear diffusion u<sub>t</sub> = (u<sup>-4/3</sup> u<sub>x</sub>)<sub>x</sub> | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> + u<sub>t</sub> = 0 | 5 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Bluman-Anco (3.194) | ((y/y')'' y y')' = 0 | 3 | 12 | 9 | (y, 0), (x<sup>2</sup>, 0) ... |
| CRC 1, 10.2 | -(u<sub>x</sub> k(u))<sub>x</sub> + u<sub>t</sub> = 0 | 3 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.2 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub> k(u))<sub>x</sub> + u<sub>t</sub> - q(u) = 0 | 2 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - a e<sup>m u</sup> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - d + u<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 4 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - a/u<sup>1/3</sup> + u<sub>t</sub> = 0 | 5 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 5 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.7 | -(u<sub>x</sub> k(u))<sub>x</sub> - (u<sub>y</sub> k(u))<sub>y</sub> + u<sub>t</sub> - q(u) = 0 | 4 | 18 | 15 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.7 | -(u<sub>x</sub> k(u))<sub>x</sub> - (u<sub>y</sub> k(u))<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.7 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - (u<sub>y</sub> e<sup>u</sup>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.7 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - (u<sup>σ</sup> u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.7 | -(u<sub>x</sub>/u<sup>4/5</sup>)<sub>x</sub> - (u<sub>y</sub>/u<sup>4/5</sup>)<sub>y</sub> - (u<sub>z</sub>/u<sup>4/5</sup>)<sub>z</sub> + u<sub>t</sub> = 0 | 12 | 54 | 50 | (x, 0, 0, 0, 0), (y, 0, 0, 0, 0) ... |
| CRC 1, 10.8 | -(u<sub>x</sub> k1(u))<sub>x</sub> - (u<sub>y</sub> k2(u))<sub>y</sub> + u<sub>t</sub> = 0 | 4 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.8 | -(u<sub>x</sub> e<sup>a1 u</sup>)<sub>x</sub> - (u<sub>y</sub> e<sup>a2 u</sup>)<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.8 | -(u<sup>s1</sup> u<sub>x</sub>)<sub>x</sub> - (u<sup>s2</sup> u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 27 | 24 | (x, 0, 0, 0), (y, 0, 0, 0) ... |
| CRC 1, 10.11 | -(u<sub>x</sub> k(u))<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 2 | 9 | 7 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.11 | -(lam u<sub>x</sub> e<sup>ν u</sup>)<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 3 | 9 | 7 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.11 | -(lam u<sub>x</sub> (μ + u)<sup>ν</sup>)<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 3 | 9 | 7 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.11 | -(lam u<sub>x</sub>/(μ + u)<sup>4/3</sup>)<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 4 | 9 | 7 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 10.11 | -(lam u<sub>x</sub>/(μ + u)<sup>2</sup>)<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 4 | 9 | 7 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 11.6 | -(u<sub>x</sub> k(u))<sub>x</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 2 | 4 | 2 | (t, 0, 1), (x, t/2, u/2) |
| CRC 1, 11.6 | -(u<sup>2 m</sup> u<sub>x</sub>)<sub>x</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 3 | 4 | 2 | (t, 0, 1), (x, t/2, u/2) |
| CRC 1, 12.4 | -(u<sub>x</sub> φ(u))<sub>x</sub> + u<sub>tt</sub> = 0 | 3 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 12.4 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 4 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 12.4 | -(k u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>tt</sub> = 0 | 4 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 12.4 | -(k u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 5 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| CRC 1, 12.4 | -(k u<sub>x</sub>/u<sup>4</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 5 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 4 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 8 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - e<sup>-2 u</sup> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 9 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - e<sup>-u</sup> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 10 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + e<sup>u</sup> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 11 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + e<sup>2 u</sup> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 12 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - 1 = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 13 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + 1 = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| Gabel et al. 24 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 3 | 4 | 2 | (t, 0, 1), (x, t/2, u/2) |
| EqWorld 1.2.1 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a + w<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.2 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w + w<sub>t</sub> = 0 | 4 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.3 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>m + 1</sup> + w<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.4 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - m</sup> + w<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.5 | -(w<sup>2 n</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - n</sup> + w<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.6 | -(w<sup>n</sup> w<sub>x</sub>)<sub>x</sub> a - b w - c<sub>1</sub> w<sup>m</sup> - c<sub>2</sub> w<sup>k</sup> + w<sub>t</sub> = 0 | 2 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.7 | -(w<sub>x</sub> e<sup>lam w</sup>)<sub>x</sub> a + w<sub>t</sub> = 0 | 4 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.8 | -(w<sub>x</sub> e<sup>lam w</sup>)<sub>x</sub> a - b - c<sub>1</sub> e<sup>be w</sup> - c<sub>2</sub> e<sup>sig w</sup> + w<sub>t</sub> = 0 | 2 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.9 | -(w<sub>x</sub> f(w))<sub>x</sub> + w<sub>t</sub> = 0 | 3 | 11 | 9 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.2.10 | -(w<sub>x</sub> f(w))<sub>x</sub> + w<sub>t</sub> - g(w) = 0 | 2 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 1.3.4 | -(w<sub>x</sub><sup>n</sup> f(w))<sub>x</sub> + w<sub>t</sub> - g(w) = 0 | 2 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 2.2.1 | -(w w<sub>x</sub>)<sub>x</sub> a + w<sub>tt</sub> = 0 | 4 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 2.2.2 | -(w<sup>n</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>k</sup> + w<sub>tt</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 2.2.3 | -(w<sub>x</sub> e<sup>lam w</sup>)<sub>x</sub> a + w<sub>tt</sub> = 0 | 4 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 2.2.7 | -(w<sub>x</sub> f(w))<sub>x</sub> + w<sub>tt</sub> = 0 | 3 | 13 | 11 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| EqWorld 3.3.1 | (w<sub>y</sub> (al w + be))<sub>y</sub> + w<sub>xx</sub> = 0 | 4 | 13 | 11 | (x, 0, 2 w), (y, 0, 0) ... |
| EqWorld 3.3.2 | (a w<sub>y</sub> e<sup>be w</sup>)<sub>y</sub> + w<sub>xx</sub> = 0 | 4 | 13 | 11 | (x, 0, 2 w), (y, 0, 0) ... |
| EqWorld 3.3.3 | (w<sub>x</sub> f(w))<sub>x</sub> + (w<sub>y</sub> g(w))<sub>y</sub> = 0 | 3 | 30 | 28 | (w, 0, 0), (x, 0, 0) ... |
| EqWorld 6.1.1 | (w w<sub>x</sub>)<sub>x</sub> + w<sub>tt</sub> + w<sub>xxxx</sub> = 0 | 3 | 8 | 6 | (x, 2 t, 4 w), (0, 0, 1) ... |
| AIMS 2026 I-(1) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e u<sup>r</sup> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 I-(2) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u<sup>m + n</sup> + e<sub>3</sub> u/(m + n - 1) + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 I-(3) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u log(u) + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 I-(4) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 I-(5) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 II-(1) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>q u</sup> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |
| AIMS 2026 II-(2) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>u</sup> + e<sub>3</sub> + u<sub>t</sub> = 0 | 3 | 6 | 4 | (x, 0, 0), (x<sup>2</sup>, 0, 0) ... |

#### One branch of y' (3)

The equation is of degree ≥ 2 in y'; sympy-extras' generators and its check are those of one branch only (Upabjojr/sympy-extras#72).

| entry | equation | dimension | generators | rejected | examples of rejected |
|---|---|---|---|---|---|
| Kamke 1.526 | -x<sup>3</sup> y<sup>3</sup> + y'<sup>3</sup> - y'<sup>2</sup> (x<sup>2</sup> + x y + y<sup>2</sup>) + y' (x<sup>3</sup> y + x<sup>2</sup> y<sup>2</sup> + x y<sup>3</sup>) = 0 | 0 | 3 | 3 | (1, x<sup>2</sup>), (x, 3 y) ... |
| Kamke 1.527 | -x y<sup>4</sup> y' - y<sup>5</sup> + y'<sup>3</sup> = 0 | 3 | 1 | 1 | (nan, nan) |
| Kamke 1.540 | 2 x y' - x + 2 y y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 1 | 9 | 9 | (1, 0), (x, x/2) ... |

### Published generators rejected (43)

sympy-extras' `check_symmetry` rejects published generators that delierium confirms.

#### Divergence form (41)

`check_symmetry` does not evaluate the outer derivative of an equation in divergence form (Upabjojr/sympy-extras#71).

| entry | equation | dimension | published | rejected | rejected generators |
|---|---|---|---|---|---|
| nonlinear diffusion in the plane | -(u u<sub>x</sub>)<sub>x</sub> - (u u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 6 | 2 | (0, 0, t, -u), (x, y, 0, 2 u) |
| nonlinear diffusion u<sub>t</sub> = (u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> | -(u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 4 | 2 | (x, 2 t, 0), (x, 0, u) |
| nonlinear diffusion u<sub>t</sub> = (u<sup>-4/3</sup> u<sub>x</sub>)<sub>x</sub> | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> + u<sub>t</sub> = 0 | 5 | 5 | 3 | (x, 2 t, 0), (-4 x, 0, 6 u), (x<sup>2</sup>, 0, -3 u x) |
| CRC 1, 10.2 | -(u<sub>x</sub> k(u))<sub>x</sub> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x, 2 t, 0) |
| CRC 1, 10.2 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 4 | 2 | (x, 2 t, 0), (σ x/2, 0, u) |
| CRC 1, 10.5 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - a e<sup>m u</sup> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x (m - 1)/2, m t, -1) |
| CRC 1, 10.5 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - d + u<sub>t</sub> = 0 | 4 | 4 | 1 | (0, e<sup>-d t</sup>, d e<sup>-d t</sup>) |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x (n - σ - 1), t (2 n - 2), -2 u) |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 4 | 4 | 2 | (σ x, 0, 2 u), (0, e<sup>-d σ t</sup>, d u e<sup>-d σ t</sup>) |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x (n + 1/3), t (2 n - 2), -2 u) |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - a/u<sup>1/3</sup> + u<sub>t</sub> = 0 | 5 | 5 | 3 | (0, 4 t/3, u), (e<sup>2 √3 √a x/3</sup>, 0, -√3 √a u e<sup>2 √3 √a x/3</sup>), (e<sup>-2 √3 √a x/3</sup>, 0, √3 √a u e<sup>-2 √3 √a x/3</sup>) |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 5 | 5 | 3 | (-2 x/3, 0, u), (0, e<sup>4 d t/3</sup>, d u e<sup>4 d t/3</sup>), (-x<sup>2</sup>, 0, 3 u x) |
| CRC 1, 10.7 | -(u<sub>x</sub> k(u))<sub>x</sub> - (u<sub>y</sub> k(u))<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 5 | 1 | (x, y, 2 t, 0) |
| CRC 1, 10.7 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> - (u<sub>y</sub> e<sup>u</sup>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 6 | 2 | (x, y, 2 t, 0), (0, 0, t, -1) |
| CRC 1, 10.7 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - (u<sup>σ</sup> u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 6 | 6 | 2 | (x, y, 2 t, 0), (σ x, σ y, 0, 2 u) |
| CRC 1, 10.7 | -(u<sub>x</sub>/u)<sub>x</sub> - (u<sub>y</sub>/u)<sub>y</sub> + u<sub>t</sub> = 0 | infinite | 6 | 2 | (x, y, 2 t, 0), (-x, -y, 0, 2 u) |
| CRC 1, 10.7 | -(u<sub>x</sub>/u<sup>4/5</sup>)<sub>x</sub> - (u<sub>y</sub>/u<sup>4/5</sup>)<sub>y</sub> - (u<sub>z</sub>/u<sup>4/5</sup>)<sub>z</sub> + u<sub>t</sub> = 0 | 12 | 12 | 5 | (x, y, z, 2 t, 0), (-4 x/5, -4 y/5, -4 z/5, 0, 2 u), (x<sup>2</sup> - y<sup>2</sup> - z<sup>2</sup>, 2 x y, 2 x z, 0, -5 u x), (2 x y, -x<sup>2</sup> + y<sup>2</sup> - z<sup>2</sup>, 2 y z, 0, -5 u y), (2 x z, 2 y z, -x<sup>2</sup> - y<sup>2</sup> + z<sup>2</sup>, 0, -5 u z) |
| CRC 1, 10.8 | -(u<sub>x</sub> k1(u))<sub>x</sub> - (u<sub>y</sub> k2(u))<sub>y</sub> + u<sub>t</sub> = 0 | 4 | 4 | 1 | (x, y, 2 t, 0) |
| CRC 1, 10.8 | -(u<sub>x</sub> e<sup>a1 u</sup>)<sub>x</sub> - (u<sub>y</sub> e<sup>a2 u</sup>)<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 5 | 1 | (x, y, 2 t, 0) |
| CRC 1, 10.8 | -(u<sup>s1</sup> u<sub>x</sub>)<sub>x</sub> - (u<sup>s2</sup> u<sub>y</sub>)<sub>y</sub> + u<sub>t</sub> = 0 | 5 | 5 | 2 | (x, y, 2 t, 0), (s1 x, s2 y, 0, 2 u) |
| Gabel et al. 4 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | 4 | 1 | (x, 2 t, 0) |
| Gabel et al. 8 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - e<sup>-2 u</sup> = 0 | 3 | 1 | 1 | (3 x/2, 2 t, 1) |
| Gabel et al. 9 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - e<sup>-u</sup> = 0 | 3 | 1 | 1 | (x, t, 1) |
| Gabel et al. 10 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + e<sup>u</sup> = 0 | 3 | 1 | 1 | (0, t, -1) |
| Gabel et al. 11 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + e<sup>2 u</sup> = 0 | 3 | 1 | 1 | (x/2, 2 t, -1) |
| Gabel et al. 12 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> - 1 = 0 | 4 | 2 | 1 | (0, e<sup>-t</sup>, e<sup>-t</sup>) |
| Gabel et al. 13 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>t</sub> + 1 = 0 | 4 | 2 | 1 | (0, e<sup>t</sup>, -e<sup>t</sup>) |
| EqWorld 1.2.1 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a + w<sub>t</sub> = 0 | 4 | 4 | 2 | (x, 2 t, 0), (m x, 0, 2 w) |
| EqWorld 1.2.2 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w + w<sub>t</sub> = 0 | 4 | 4 | 2 | (m x, 0, 2 w), (0, e<sup>-b m t</sup>, b w e<sup>-b m t</sup>) |
| EqWorld 1.2.3 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>m + 1</sup> + w<sub>t</sub> = 0 | 3 | 3 | 1 | (0, -m t, w) |
| EqWorld 1.2.4 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - m</sup> + w<sub>t</sub> = 0 | 3 | 3 | 1 | (m x, m t, w) |
| EqWorld 1.2.5 | -(w<sup>2 n</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - n</sup> + w<sub>t</sub> = 0 | 3 | 3 | 1 | (3 n x, 2 n t, 2 w) |
| EqWorld 1.2.7 | -(w<sub>x</sub> e<sup>lam w</sup>)<sub>x</sub> a + w<sub>t</sub> = 0 | 4 | 4 | 1 | (x, 2 t, 0) |
| EqWorld 1.2.9 | -(w<sub>x</sub> f(w))<sub>x</sub> + w<sub>t</sub> = 0 | 3 | 3 | 1 | (x, 2 t, 0) |
| AIMS 2026 I-(1) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e u<sup>r</sup> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x (m + n - r), t (1 - r) (n + 1), u (n + 1)) |
| AIMS 2026 I-(2) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u<sup>m + n</sup> + e<sub>3</sub> u/(m + n - 1) + u<sub>t</sub> = 0 | 3 | 3 | 1 | (0, e<sup>e<sub>3</sub> t</sup>, -e<sub>3</sub> u e<sup>e<sub>3</sub> t</sup>/(m + n - 1)) |
| AIMS 2026 I-(3) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u log(u) + u<sub>t</sub> = 0 | 3 | 3 | 1 | (0, 0, u e<sup>e<sub>2</sub> t</sup>) |
| AIMS 2026 I-(4) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | 4 | 2 | (x (m + n - 1)/(n + 1), 0, u), (0, e<sup>e<sub>2</sub> t (-m - n + 1)</sup>, e<sub>2</sub> u e<sup>e<sub>2</sub> t (-m - n + 1)</sup>) |
| AIMS 2026 I-(5) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | 4 | 2 | (0, 0, u), (x, t (n + 1), e<sub>2</sub> t u (n + 1)) |
| AIMS 2026 II-(1) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>q u</sup> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (x (1 - q)/(n + 1), -q t, 1) |
| AIMS 2026 II-(2) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>u</sup> + e<sub>3</sub> + u<sub>t</sub> = 0 | 3 | 3 | 1 | (0, e<sup>e<sub>3</sub> t</sup>, -e<sub>3</sub> e<sup>e<sub>3</sub> t</sup>) |

#### Simplification without assumptions (1)

The residue has ((1 - x)/(1 + x))<sup>A</sup> next to (1 + x)<sup>A + 2</sup> (1 - x)<sup>2 - A</sup>; it vanishes once the power is split, which holds on -1 < x < 1, where c(x) is real (checked with x = (1 - q)/(1 + q), q > 0). sympy-extras' `check_symmetry` simplifies without assumptions on x; delierium checks locally, for positive bases.

| entry | equation | dimension | published | rejected | rejected generators |
|---|---|---|---|---|---|
| Bluman-Anco (4.64) | u<sub>tt</sub> - u<sub>xx</sub> (1 - x)<sup>2 - A</sup> (x + 1)<sup>A + 2</sup> = 0 | infinite | 4 | 1 | (t (1 - x<sup>2</sup>), -A t<sup>2</sup>/2 - ((1 - x)/(x + 1))<sup>A</sup>/(2 A), t u (A/2 - x)) |

#### One branch of y' (1)

The equation is of degree ≥ 2 in y'; sympy-extras' generators and its check are those of one branch only (Upabjojr/sympy-extras#72).

| entry | equation | dimension | published | rejected | rejected generators |
|---|---|---|---|---|---|
| Kamke 1.547 | -4 y (x y' - 2 y)<sup>2</sup> + y'<sup>4</sup> = 0 | 1 | 1 | 1 | (x, 4 y) |

### Fewer generators than the dimension (173)

#### Polynomial ansatz of degree ≤ 2 (173)

sympy-extras' ansatz has polynomials of degree ≤ 2 only, so it misses the generators of higher degree or with other functions; the ones it finds are correct. Where the published list has the missing generators, they are named.

| entry | equation | dimension | sympy-extras | published generators outside the ansatz |
|---|---|---|---|---|
| Arrigo 2.19 (modified Emden equation) | y<sup>3</sup> + 3 y y' + y'' = 0 | 8 | 3 | (y, -y<sup>3</sup>), (x y, -x y<sup>3</sup> + y<sup>2</sup>) |
| Schwarz Example 5.46 | -x y y'<sup>2</sup> y'' + 2 x y'<sup>4</sup> - 2 y<sup>2</sup> y' y'' + 3 y y'<sup>3</sup> + y y' y''' - 3 y y''<sup>2</sup> + 3 y'<sup>2</sup> y'' - y<sup>3</sup> y''/x - y<sup>2</sup> y'<sup>2</sup>/x + y<sup>2</sup> y'''/x - 12 y y' y''/x + 15 y'<sup>3</sup>/x - 3 y<sup>3</sup> y'/x<sup>2</sup> - 3 y<sup>2</sup> y''/x<sup>2</sup> - 3 y y'<sup>2</sup>/x<sup>2</sup> - y<sup>4</sup>/x<sup>3</sup> - 9 y<sup>2</sup> y'/x<sup>3</sup> - 3 y<sup>3</sup>/x<sup>4</sup> = 0 | 5 | 1 | – |
| Schwarz Example 5.13 | 4 x<sup>6</sup> y'<sup>4</sup> - 4 x<sup>4</sup> y'<sup>2</sup> y'' (x<sup>2</sup> y - 2) + 24 x<sup>3</sup> y'<sup>3</sup> + 24 x<sup>2</sup> y y'<sup>2</sup> + x<sup>2</sup> y''<sup>2</sup> (x<sup>2</sup> y - 2)<sup>2</sup> + 24 x y<sup>2</sup> y' - 8 x y' y'' (x<sup>2</sup> y - 2) + 8 y<sup>3</sup> + 16 y'<sup>2</sup> = 0 | 3 | 1 | – |
| Schwarz Example 5.16, (5.33) | -2 x<sup>2</sup> e<sup>(-2 y y' - 1)/(2 x)</sup> + y y'' + y'<sup>2</sup> - y y'/x - 1/(2 x) = 0 | 3 | 0 | – |
| Schwarz Example 5.33 | x<sup>5</sup> y<sup>6</sup> y' y''' - 3 x<sup>5</sup> y<sup>6</sup> y''<sup>2</sup> + 6 x<sup>5</sup> y<sup>5</sup> y'<sup>2</sup> y'' - 6 x<sup>5</sup> y<sup>4</sup> y'<sup>4</sup> + 3 x<sup>4</sup> y<sup>6</sup> y' y'' - 6 x<sup>4</sup> y<sup>5</sup> y'<sup>3</sup> + 2 x<sup>3</sup> y<sup>4</sup> y'<sup>2</sup> y'' - 4 x<sup>3</sup> y<sup>3</sup> y'<sup>4</sup> - y'<sup>5</sup> = 0 | 3 | 2 | – |
| Schwarz Example 5.43 | -8 x y<sup>2</sup> y'/(2 x - 1) + y<sup>2</sup> y''' - 6 y y' y'' + 6 y'<sup>3</sup> + 3 y<sup>2</sup> y''/x - 6 y y'<sup>2</sup>/x = 0 | 4 | 2 | – |
| Schwarz Example 5.45 | -4 x y'<sup>5</sup> + 4 y + y'<sup>4</sup> (-16 x + 4 y) + y'<sup>3</sup> (-24 x + 16 y) + y'<sup>2</sup> (-16 x + 24 y) + y' (-4 x + 16 y) - y''<sup>2</sup> (3 x + 3 y - 3/2) + y''' (y' + 1) (x + y - 1/2) = 0 | 4 | 2 | – |
| Schwarz Example 5.49 | y y' y''' - 3 y y''<sup>2</sup> + 3 y'<sup>2</sup> y'' + y<sup>2</sup> y'''/x - 12 y y' y''/x + 15 y'<sup>3</sup>/x - 3 y<sup>2</sup> y''/x<sup>2</sup> - 3 y y'<sup>2</sup>/x<sup>2</sup> - 9 y<sup>2</sup> y'/x<sup>3</sup> - 3 y<sup>3</sup>/x<sup>4</sup> = 0 | 7 | 2 | – |
| Hydon Example 4.1 | -4 y - y' (-2 x + 3/x) + y'' = 0 | 8 | 2 | – |
| y''' = 1 | y''' - 1 = 0 | 7 | 5 | – |
| y'''' = 0 | y'''' = 0 | 8 | 7 | (0, x<sup>3</sup>) |
| harmonic oscillator | y + y'' = 0 | 8 | 2 | (0, sin(x)), (0, cos(x)) |
| Kamke 1.535 | 8 x y'<sup>3</sup> - 12 y y'<sup>2</sup> + 9 y = 0 | 3 | 1 | ((3 x + √(9 x<sup>2</sup> - 4 y<sup>2</sup>))<sup>2/3</sup>, 3 y/(3 x + √(9 x<sup>2</sup> - 4 y<sup>2</sup>))<sup>1/3</sup>), ((3 x - √(9 x<sup>2</sup> - 4 y<sup>2</sup>))<sup>2/3</sup>, 3 y/(3 x - √(9 x<sup>2</sup> - 4 y<sup>2</sup>))<sup>1/3</sup>) |
| isotropic harmonic oscillator in the plane | x + x'' = 0; y + y'' = 0 | 15 | 5 | (0, sin(t), 0) |
| heat equation with logarithmic source | -u log(u) + u<sub>t</sub> - u<sub>xx</sub> = 0 | 4 | 2 | (e<sup>t</sup>, 0, -u x e<sup>t</sup>/2), (0, 0, u e<sup>t</sup>) |
| Baumann p. 181 | a e<sup>u</sup> + u'/x + u'' = 0 | 2 | 1 | (x (1 - log(x)), 2 log(x)) |
| Baumann p. 185 | -a u'<sup>2</sup> + u'' = 0 | 8 | 4 | (0, x e<sup>a u</sup>/a), (-e<sup>-a u</sup>/a, 0), (x e<sup>-a u</sup>, -e<sup>-a u</sup>/a) ... |
| Baumann p. 196 | -w<sup>3</sup> + 4 w<sup>2</sup> w'' + 2 w - 4 w' = 0 | 2 | 1 | (2 e<sup>t</sup>, w e<sup>t</sup>) |
| Baumann p. 297 | 6 u u<sub>x</sub> + u<sub>t</sub> + u<sub>xxx</sub> + u/(2 t) = 0 | 4 | 2 | (√t x/2, t<sup>3/2</sup>, (-24 t u + x)/(24 √t)), (2 √t, 0, 1/(6 √t)) |
| Baumann p. 298 | 6 u u<sub>x</sub> + u<sub>t</sub> + u<sub>xxx</sub> + u/t = 0 | 3 | 2 | (log(t), 0, 1/(6 t)) |
| Baumann p. 298: KdV with slowly varying coefficients | u u<sub>x</sub> A(e t) + u<sub>t</sub> + u<sub>xxx</sub> B(e t) = 0 | 2 | 1 | – |
| Hydon Exercise 3.5 | 6 y - 7 y' + y''' = 0 | 5 | 2 | (0, e<sup>x</sup>), (0, e<sup>2 x</sup>), (0, e<sup>-3 x</sup>) |
| Hydon Exercise 6.6 | -y'<sup>3</sup> (y<sup>2</sup>/2 + 1) + y''' - 3 y''<sup>2</sup>/(2 y') = 0 | 6 | 3 | – |
| Bluman-Anco (3.413) | y'' - (y'<sup>2</sup> + 1) (2 x y' - 2 y)/(x<sup>2</sup> + y<sup>2</sup>) = 0 | 8 | 4 | – |
| Bluman-Anco Exercise 3.5-3 | -2 y'<sup>2</sup> cot(y) + y'' - sin(y) cos(y) = 0 | 8 | 1 | – |
| CRC 1, 10.10 | τ0 u<sub>tt</sub> + u<sub>t</sub> - u<sub>xx</sub> k(u<sub>x</sub>) = 0 | 4 | 3 | (0, 0, e<sup>-t/τ0</sup>) |
| CRC 1, 10.10 | -k0 u<sub>x</sub><sup>n</sup> u<sub>xx</sub> + τ0 u<sub>tt</sub> + u<sub>t</sub> = 0 | 5 | 4 | – |
| CRC 1, 10.10 | -k0 u<sub>xx</sub> e<sup>m u<sub>x</sub></sup> + τ0 u<sub>tt</sub> + u<sub>t</sub> = 0 | 5 | 4 | – |
| CRC 1, 11.8 | -μ u<sub>xx</sub> + u u<sub>x</sub> + u<sub>t</sub> + u/(2 t) = 0 | 3 | 2 | (2 √t, 0, 1/√t) |
| CRC 1, 11.8 | -μ u<sub>xx</sub> + u u<sub>x</sub> + u<sub>t</sub> + u/t = 0 | 3 | 2 | (log(t), 0, 1/t) |
| Ko, Kim, Lee | u u<sub>x</sub> + u<sub>t</sub> e<sup>-t/t0</sup> + u<sub>xxx</sub> = 0 | 4 | 2 | (0, e<sup>-t/t0</sup>, 0), (t0 (e<sup>t/t0</sup> - 1), 0, 1), (x, 3 t0 (1 - e<sup>-t/t0</sup>), -2 u) |
| Ko, Kim, Lee | u u<sub>x</sub> + u/(2 t + 2) + u<sub>t</sub> + u<sub>xxx</sub> = 0 | 4 | 2 | (2 √(t + 1), 0, 1/√(t + 1)), (x √(t + 1)/2, (t + 1)<sup>3/2</sup>, (-u (4 t + 4) + x)/(4 √(t + 1))) |
| EqWorld 1.1.6 | -a w log(w) + w<sub>t</sub> - w<sub>xx</sub> = 0 | 4 | 2 | (0, 0, w e<sup>a t</sup>), (e<sup>a t</sup>, 0, -a w x e<sup>a t</sup>/2) |
| EqWorld 4.1.2 | a w<sub>y</sub>/y + b w<sub>x</sub> w<sub>xx</sub> + w<sub>yy</sub> = 0 | 5 | 4 | (0, 0, y<sup>1 - a</sup>) |
| EqWorld 5.1.2 | -6 w w<sub>x</sub> + w<sub>t</sub> + w<sub>xxx</sub> + w/(2 t) = 0 | 4 | 2 | (√t x/2, t<sup>3/2</sup>, (-24 t w - x)/(24 √t)), (2 √t, 0, -1/(6 √t)) |
| PINNacle Poisson1D | u'' + sin(x) = 0 | 8 | 2 | (1, cos(x)), (0, u - sin(x)), (x, x cos(x)) ... |
| Cherniha, King, Kovalenko 5 | -e<sub>1</sub> u<sup>k + 1</sup> - e<sub>2</sub> u + u<sub>t</sub> - u<sub>x</sub><sup>k</sup> u<sub>xx</sub> = 0 | 3 | 2 | (0, e<sup>-e<sub>2</sub> k t</sup>, e<sub>2</sub> u e<sup>-e<sub>2</sub> k t</sup>) |
| Cherniha, King, Kovalenko 10 | -e<sub>2</sub> u + u<sub>t</sub> - u<sub>x</sub><sup>k</sup> u<sub>xx</sub> = 0 | 5 | 3 | (0, e<sup>-e<sub>2</sub> k t</sup>, e<sub>2</sub> u e<sup>-e<sub>2</sub> k t</sup>), (0, 0, e<sup>e<sub>2</sub> t</sup>) |
| BGL 5.3-3 | -f<sub>0</sub> t<sup>2</sup> (u<sub>xxx</sub>/u<sub>x</sub><sup>3</sup> - 3 u<sub>xx</sub><sup>2</sup>/(2 u<sub>x</sub><sup>4</sup>)) - g0 + u<sub>t</sub> = 0 | 6 | 5 | (0, t<sup>-2</sup>, g0/t<sup>2</sup>) |
| Vaneeva, Bihlo, Popovych 14b | -ε u<sub>xx</sub>/u<sup>4</sup> - ε1/u<sup>3</sup> - u + u<sub>tt</sub> = 0 | 4 | 2 | (0, e<sup>2 t</sup>, u e<sup>2 t</sup>), (0, e<sup>-2 t</sup>, -u e<sup>-2 t</sup>) |
| Vaneeva, Bihlo, Popovych 14c | -ε u<sub>xx</sub>/u<sup>4</sup> - ε1/u<sup>3</sup> + u + u<sub>tt</sub> = 0 | 4 | 2 | (0, cos(2 t), -u sin(2 t)), (0, sin(2 t), u cos(2 t)) |
| Vaneeva, Bihlo, Popovych 15b | -ε u<sub>xx</sub>/u<sup>4</sup> - ν/(u<sup>3</sup> x<sup>2</sup>) - u + u<sub>tt</sub> = 0 | 4 | 2 | (0, e<sup>2 t</sup>, u e<sup>2 t</sup>), (0, e<sup>-2 t</sup>, -u e<sup>-2 t</sup>) |
| Vaneeva, Bihlo, Popovych 15c | -ε u<sub>xx</sub>/u<sup>4</sup> - ν/(u<sup>3</sup> x<sup>2</sup>) + u + u<sub>tt</sub> = 0 | 4 | 2 | (0, cos(2 t), -u sin(2 t)), (0, sin(2 t), u cos(2 t)) |
| Vaneeva, Bihlo, Popovych 18b | -ε1 u<sup>q</sup> e<sup>-2 x</sup> + u<sub>tt</sub> - u<sub>xx</sub> = 0 | 4 | 2 | (e<sup>t + x</sup>, e<sup>t + x</sup>, 0), (-e<sup>-t + x</sup>, e<sup>-t + x</sup>, 0) |
| Vaneeva, Bihlo, Popovych 18c | -ε1 u<sup>q</sup> e<sup>-2 x</sup> + u<sub>tt</sub> + u<sub>xx</sub> = 0 | 4 | 2 | (-e<sup>x</sup> sin(t), e<sup>x</sup> cos(t), 0), (e<sup>x</sup> cos(t), e<sup>x</sup> sin(t), 0) |
| Vaneeva, Bihlo, Popovych 19b | -ε u<sub>xx</sub>/u<sup>4</sup> - u + u<sub>tt</sub> = 0 | 5 | 3 | (0, e<sup>2 t</sup>, u e<sup>2 t</sup>), (0, e<sup>-2 t</sup>, -u e<sup>-2 t</sup>) |
| Vaneeva, Bihlo, Popovych 19c | -ε u<sub>xx</sub>/u<sup>4</sup> + u + u<sub>tt</sub> = 0 | 5 | 3 | (0, cos(2 t), -u sin(2 t)), (0, sin(2 t), u cos(2 t)) |
| Zhdanov 2005, dimension 5 | u<sup>2</sup>/x<sup>2</sup> - u u<sub>x</sub>/x + 2 u/x<sup>2</sup> + u<sub>t</sub> - u<sub>xx</sub> = 0 | 5 | 3 | (1, 0, (u + 2)/x), (t, 0, (t u + 2 t - x<sup>2</sup>)/x) |
| Kamke 1.518 | y'<sup>3</sup> - (-a + y)<sup>2</sup> (-b + y)<sup>2</sup> = 0 | 3 | 1 | – |
| Kamke 1.521 | x y' - y + y'<sup>3</sup> = 0 | 3 | 1 | – |
| Kamke 1.522 | y + y'<sup>3</sup> + y' (-x - 5) = 0 | 3 | 1 | – |
| Kamke 1.533 | a + x y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 3 | 1 | – |
| Kamke 1.537 | -2 x<sup>5</sup> y + x<sup>3</sup> y'<sup>3</sup> - 3 x<sup>2</sup> y y'<sup>2</sup> - y<sup>3</sup> + y' (x<sup>6</sup> + 3 x y<sup>2</sup>) = 0 | 3 | 1 | – |
| Kamke 1.541 | 2 x y' + y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | 1 | – |
| Kamke 1.542 | 2 x y' + 16 y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | 1 | – |
| Kamke 1.543 | -x<sup>2</sup> y + x y<sup>2</sup> y'<sup>3</sup> + x y' (x<sup>2</sup> + 1) - y<sup>3</sup> y'<sup>2</sup> = 0 | 3 | 0 | – |
| Kamke 1.544 | x<sup>7</sup> y<sup>2</sup> y'<sup>3</sup> + 3 x<sup>5</sup> y<sup>4</sup> y' - x<sup>4</sup> y<sup>5</sup> - y'<sup>2</sup> (3 x<sup>6</sup> y<sup>3</sup> - 1) = 0 | 3 | 1 | – |
| Kamke 1.545 | y'<sup>4</sup> - (-a + y)<sup>3</sup> (-b + y)<sup>2</sup> = 0 | 3 | 1 | – |
| Kamke 1.547 | -4 y (x y' - 2 y)<sup>2</sup> + y'<sup>4</sup> = 0 | 1 | 0 | – |
| Kamke 1.548 | y'<sup>6</sup> - (-a + y)<sup>4</sup> (-b + y)<sup>3</sup> = 0 | 3 | 1 | – |
| Kamke 3.1 | -λ y + y''' = 0 | 5 | 2 | – |
| Kamke 3.2 | a x<sup>3</sup> y - b x + y''' = 0 | 4 | 0 | – |
| Kamke 3.4 | -4 y + 3 y' + y''' = 0 | 5 | 2 | – |
| Kamke 3.6 | 2 a x y' + a y + y''' = 0 | 7 | 1 | – |
| Kamke 3.7 | -a b y - x<sup>2</sup> y'' + x y' (a + b - 1) + y''' = 0 | 4 | 1 | – |
| Kamke 3.16 | 10 y - 3 y' - 2 y'' + y''' = 0 | 5 | 2 | – |
| Kamke 3.21 | a<sup>3</sup> x<sup>3</sup> y + 3 a<sup>2</sup> x<sup>2</sup> y' + 3 a x y'' + y''' = 0 | 7 | 2 | – |
| Kamke 3.27 | -3 y - 11 y' - 8 y'' + 4 y''' + 18 e<sup>x</sup> = 0 | 5 | 1 | – |
| Kamke 3.29 | x y + x y''' + 3 y'' = 0 | 5 | 1 | – |
| Kamke 3.30 | -a x<sup>2</sup> y + x y''' + 3 y'' = 0 | 4 | 1 | – |
| Kamke 3.31 | -a y - x y' + x y''' + y'' (a + b) = 0 | 4 | 1 | – |
| Kamke 3.32 | x y''' + y (x - 1) - y' (-2 v + x - 1) - y'' (2 v + x) = 0 | 4 | 1 | – |
| Kamke 3.33 | 4 x y' + x y''' + 2 y + y'' (x<sup>2</sup> - 3) = 0 | 4 | 1 | – |
| Kamke 3.34 | a x y - b + 2 x y''' + 3 y'' = 0 | 4 | 0 | – |
| Kamke 3.35 | 2 x y''' + y (1 - 2 ν) + y' (6 ν + 2 x - 5) - y'' (4 ν + 4 x - 4) = 0 | 4 | 1 | – |
| Kamke 3.37 | -x y'' (x - 2) + x y''' (x - 2) + 2 y - 2 y' = 0 | 4 | 2 | – |
| Kamke 3.38 | -8 x y' + 8 y + y''' (2 x - 1) = 0 | 4 | 2 | – |
| Kamke 3.39 | 2 y' + y'' (x + 4) + y''' (2 x - 1) = 0 | 4 | 2 | – |
| Kamke 3.40 | a x<sup>2</sup> y + x<sup>2</sup> y''' - 6 y' = 0 | 4 | 1 | – |
| Kamke 3.41 | x<sup>2</sup> y''' - y + y'' (x + 1) = 0 | 4 | 1 | – |
| Kamke 3.42 | x<sup>2</sup> y''' - x y'' + y' (x<sup>2</sup> + 1) = 0 | 4 | 2 | – |
| Kamke 3.45 | x<sup>2</sup> y''' + 3 x y + 4 x y'' + y' (x<sup>2</sup> + 2) = 0 | 4 | 1 | – |
| Kamke 3.47 | x<sup>2</sup> y''' + 6 x y'' + 6 y' = 0 | 7 | 4 | – |
| Kamke 3.48 | a x<sup>2</sup> y + x<sup>2</sup> y''' + 6 x y'' + 6 y' = 0 | 5 | 1 | – |
| Kamke 3.49 | 3 p y' (3 q + 1) - x<sup>2</sup> y + x<sup>2</sup> y''' - x y'' (3 p + 3 q) = 0 | 4 | 1 | – |
| Kamke 3.50 | -2 a x y + x<sup>2</sup> y''' - x y'' (2 n + 2) + y' (a x<sup>2</sup> + 6 n) = 0 | 4 | 2 | – |
| Kamke 3.51 | x<sup>2</sup> y''' + y (ν<sup>2</sup> + x<sup>2</sup> - 2 x - 0.25) - y' (ν<sup>2</sup> + x<sup>2</sup> - 0.25) - y'' (x<sup>2</sup> - 2 x) = 0 | 4 | 1 | – |
| Kamke 3.53 | x<sup>2</sup> y''' + y (ν<sup>2</sup> - 0.25) + y' (-ν<sup>2</sup> + x<sup>2</sup> - 2 x + 0.25) - y'' (2 x<sup>2</sup> - 2 x) = 0 | 4 | 1 | – |
| Kamke 3.54 | 2 x<sup>2</sup> y + x<sup>2</sup> y''' - y' (2 x<sup>3</sup> - 6) - y'' (x<sup>4</sup> - 6 x) = 0 | 4 | 1 | – |
| Kamke 3.56 | -2 x y - 2 x y'' + y' (x<sup>2</sup> + 2) + y''' (x<sup>2</sup> + 2) = 0 | 4 | 2 | – |
| Kamke 3.57 | a y + 2 x y''' (x - 1) + y' (2 a x + b) + y'' (6 x - 3) = 0 | 7 | 1 | – |
| Kamke 3.58 | 4 x<sup>2</sup> y''' + 2 y + y' (4 x + 4) + y'' (x<sup>2</sup> + 14 x - 1) = 0 | 4 | 1 | – |
| Kamke 3.60 | x<sup>3</sup> y''' + x y' (1 - ν<sup>2</sup>) + y (a x<sup>3</sup> + ν<sup>2</sup> - 1) = 0 | 4 | 1 | – |
| Kamke 3.61 | x<sup>3</sup> y''' + y (4 ν<sup>2</sup> - 1) + y' (4 x<sup>3</sup> + x (1 - 4 ν<sup>2</sup>)) = 0 | 7 | 1 | – |
| Kamke 3.63 | x<sup>3</sup> y''' - 6 x<sup>3</sup> (x - 1) log(x) + x<sup>3</sup> (x + 8) + 3 x<sup>2</sup> y'' - 2 x y' + 2 y = 0 | 5 | 1 | – |
| Kamke 3.64 | x<sup>3</sup> y''' + 3 x<sup>2</sup> y'' + x y' (1 - a<sup>2</sup>) = 0 | 7 | 3 | – |
| Kamke 3.65 | x<sup>3</sup> y''' - 4 x<sup>2</sup> y'' + x y' (x<sup>2</sup> + 8) - y (2 x<sup>2</sup> + 8) = 0 | 4 | 2 | – |
| Kamke 3.66 | x<sup>3</sup> y''' + 6 x<sup>2</sup> y'' + y (a x<sup>3</sup> - 12) = 0 | 4 | 1 | – |
| Kamke 3.68 | x<sup>3</sup> y''' + x<sup>2</sup> y'' (x + 3) + x y' (5 x - 30) + y (4 x + 30) = 0 | 4 | 1 | – |
| Kamke 3.70 | x y''' (x<sup>2</sup> + 1) - 12 y + y'' (6 x<sup>2</sup> + 3) = 0 | 4 | 2 | – |
| Kamke 3.71 | x<sup>2</sup> y''' (x + 3) - x y'' (3 x + 6) - 6 y + y' (6 x + 6) = 0 | 5 | 4 | – |
| Kamke 3.73 | x<sup>3</sup> y''' (x + 1) - x<sup>2</sup> y'' (4 x + 2) + x y' (10 x + 4) - y (12 x + 4) = 0 | 4 | 2 | – |
| Kamke 3.74 | 4 x<sup>4</sup> y''' - 4 x<sup>3</sup> y'' + 4 x<sup>2</sup> y' - 1 = 0 | 5 | 3 | – |
| Kamke 3.75 | x<sup>3</sup> y''' (x<sup>2</sup> + 1) - x<sup>2</sup> y'' (4 x<sup>2</sup> + 2) + x y' (10 x<sup>2</sup> + 4) - y (12 x<sup>2</sup> + 4) = 0 | 4 | 2 | – |
| Kamke 3.76 | x<sup>6</sup> y''' + x<sup>2</sup> y'' - 2 y = 0 | 4 | 2 | – |
| Kamke 3.77 | a y + x<sup>6</sup> y''' + 6 x<sup>5</sup> y'' = 0 | 4 | 1 | – |
| Kamke 6.32 | 2 a<sup>2</sup> y + a y<sup>2</sup> - y<sup>3</sup> + y' (3 a + y) + y'' = 0 | 2 | 1 | – |
| Kamke 6.78 | x y'' - y' (1 - y) = 0 | 2 | 1 | – |
| Kamke 6.93 | -a (x y' - y)<sup>2</sup> + x<sup>3</sup> y'' = 0 | 8 | 3 | – |
| Kamke 6.97 | x<sup>4</sup> y'' - x y' (x<sup>2</sup> + 2 y) + 4 y<sup>2</sup> = 0 | 2 | 1 | – |
| Kamke 6.99 | x<sup>4</sup> y'' + (x y' - y)<sup>3</sup> = 0 | 8 | 2 | – |
| Kamke 6.107 | -a + y y'' + y'<sup>2</sup> = 0 | 8 | 3 | – |
| Kamke 6.117 | a y y' + b y<sup>2</sup> + y y'' - y'<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.124 | -y<sup>2</sup> + 3 y y' + y y'' - 3 y'<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.125 | -a y'<sup>2</sup> + y y'' = 0 | 8 | 4 | – |
| Kamke 6.128 | a y'<sup>2</sup> + b y y' + c y<sup>2</sup> + d y<sup>1 - a</sup> + y y'' = 0 | 8 | 1 | – |
| Kamke 6.134 | y' (2 y' + 2) + y'' (x - y) = 0 | 8 | 3 | – |
| Kamke 6.135 | y'' (x - y) - (y' + 1) (y'<sup>2</sup> + 1) = 0 | 8 | 3 | – |
| Kamke 6.150 | 2 y y'' - 3 y'<sup>2</sup> = 0 | 8 | 4 | – |
| Kamke 6.151 | -4 y<sup>2</sup> + 2 y y'' - 3 y'<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.157 | 3 y y'' - 5 y'<sup>2</sup> = 0 | 8 | 4 | – |
| Kamke 6.164 | n y y'' - y'<sup>2</sup> (n - 1) = 0 | 8 | 4 | – |
| Kamke 6.168 | c y'<sup>2</sup> + y'' (a y + b) = 0 | 8 | 4 | – |
| Kamke 6.169 | x y y'' + x y'<sup>2</sup> - y y' = 0 | 8 | 2 | – |
| Kamke 6.170 | a y y' + x y y'' + x y'<sup>2</sup> + f(x) = 0 | 8 | 0 | (0, 1/y), (0, x<sup>1 - a</sup>/y) |
| Kamke 6.173 | a y y' + x y y'' + 2 x y'<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.174 | x y y'' - 2 x y'<sup>2</sup> + y' (y + 1) = 0 | 2 | 1 | – |
| Kamke 6.175 | a y y' + x y y'' - 2 x y'<sup>2</sup> = 0 | 8 | 3 | – |
| Kamke 6.176 | x y y'' - 4 x y'<sup>2</sup> + 4 y y' = 0 | 8 | 2 | – |
| Kamke 6.178 | x y'<sup>2</sup> + x y'' (x + y) - y + y' (x - y) = 0 | 8 | 2 | – |
| Kamke 6.179 | 2 x y y'' - x y'<sup>2</sup> + y y' = 0 | 8 | 2 | – |
| Kamke 6.180 | -2 x<sup>2</sup> y'<sup>2</sup> + x<sup>2</sup> y'' (y - 1) - 2 x y' (y - 1) - 2 y (y - 1)<sup>2</sup> = 0 | 8 | 3 | – |
| Kamke 6.181 | x<sup>2</sup> y'' (x + y) - (x y' - y)<sup>2</sup> = 0 | 8 | 3 | – |
| Kamke 6.182 | a (x y' - y)<sup>2</sup> + x<sup>2</sup> y'' (x - y) = 0 | 8 | 3 | – |
| Kamke 6.183 | 2 x<sup>2</sup> y y'' - x<sup>2</sup> (y'<sup>2</sup> + 1) + y<sup>2</sup> = 0 | 3 | 1 | – |
| Kamke 6.184 | a x<sup>2</sup> y y'' + b x<sup>2</sup> y'<sup>2</sup> + c x y y' + d y<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.185 | -a y<sup>2</sup> (x + 2) + x y y'' (x + 1)<sup>2</sup> - x y'<sup>2</sup> (x + 1)<sup>2</sup> + 2 y y' (x + 1)<sup>2</sup> = 0 | 8 | 2 | – |
| Kamke 6.186 | -12 x<sup>2</sup> y y' + 3 x y<sup>2</sup> + y y'' (8 - 8 x<sup>3</sup>) - y'<sup>2</sup> (4 - 4 x<sup>3</sup>) = 0 | 8 | 1 | – |
| Kamke 6.191 | y'<sup>2</sup> (1 - 2 y) + y'' (y<sup>2</sup> + 1) = 0 | 8 | 3 | – |
| Kamke 6.192 | -3 y y'<sup>2</sup> + y'' (y<sup>2</sup> + 1) = 0 | 8 | 2 | – |
| Kamke 6.193 | -y'<sup>3</sup> (2 x - 2 y<sup>2</sup>) + y' (4 y y' + 1) + y'' (x + y<sup>2</sup>) = 0 | 8 | 3 | – |
| Kamke 6.194 | y'' (x<sup>2</sup> + y<sup>2</sup>) - (y'<sup>2</sup> + 1) (x y' - y) = 0 | 8 | 2 | – |
| Kamke 6.195 | y'' (x<sup>2</sup> + y<sup>2</sup>) - (2 y'<sup>2</sup> + 2) (x y' - y) = 0 | 8 | 4 | – |
| Kamke 6.206 | -x y' (a<sup>2</sup> - y<sup>2</sup>) + y y'<sup>2</sup> (a<sup>2</sup> - x<sup>2</sup>) + y'' (a<sup>2</sup> - x<sup>2</sup>) (a<sup>2</sup> - y<sup>2</sup>) = 0 | 8 | 0 | – |
| Kamke 6.208 | x<sup>3</sup> y<sup>2</sup> y'' + (x + y) (x y' - y)<sup>3</sup> = 0 | 8 | 1 | – |
| Kamke 6.210 | y y'' (y<sup>2</sup> + 1) + y'<sup>2</sup> (1 - 3 y<sup>2</sup>) = 0 | 8 | 2 | – |
| Kamke 6.214 | y'<sup>2</sup> (a/2 - 6 y<sup>2</sup>) + y'' (-a y - b + 4 y<sup>3</sup>) = 0 | 8 | 2 | – |
| Kamke 6.244 | -4 x y (x y' - y)<sup>3</sup> + (x<sup>2</sup> y y'' - x<sup>2</sup> y'<sup>2</sup> + y<sup>2</sup>)<sup>2</sup> = 0 | 3 | 1 | – |
| Kamke 7.8 | 4 y<sup>2</sup> y''' - 18 y y' y'' + 15 y'<sup>3</sup> = 0 | 7 | 4 | – |
| Kamke 7.9 | 9 y<sup>2</sup> y''' - 45 y y' y'' + 40 y'<sup>3</sup> = 0 | 7 | 4 | – |
| EqWorld ODE 3.3 | -a/y<sup>3</sup> + y f(x) + y'' = 0 | 3 | 0 | – |
| EqWorld ODE 3.15 | -ψ''(x) y/ψ(x) + y'' - f(y/ψ(x))/ψ(x)<sup>3</sup> = 0 | 1 | 0 | (ψ(x)<sup>2</sup>, ψ'(x) y ψ(x)) |
| EqWorld ODE 3.20 | -a y' + y'' - f(y) e<sup>2 a x</sup> = 0 | 1 | 0 | (e<sup>-a x</sup>, 0) |
| EqWorld ODE 3.22 | y' (-al - f(y) e<sup>al x</sup>) + y'' = 0 | 1 | 0 | (e<sup>-al x</sup>, 0) |
| EqWorld ODE 3.23 | -n y' + x y'' - x<sup>2 n + 1</sup> f(y) = 0 | 1 | 0 | (x<sup>-n</sup>, 0) |
| EqWorld ODE 3.25 | x y'' - y' (k + x<sup>k</sup> f(y) - 1) = 0 | 1 | 0 | (x/x<sup>k</sup>, 0) |
| EqWorld ODE 3.27 | a x y' + y'' (a x<sup>2</sup> + b) + f(y) = 0 | 1 | 0 | (√(a x<sup>2</sup> + b), 0) |
| EqWorld ODE 3.29 | x y'' - x<sup>n - 1</sup> f(x<sup>n</sup> y) + y' (n + 1) = 0 | 1 | 0 | (-x/(n x<sup>n</sup>), y/x<sup>n</sup>) |
| EqWorld ODE 3.30 | g'(x) y'/2 + y'' g(x) - f(y) = 0 | 1 | 0 | (√(g(x)), 0) |
| EqWorld ODE 3.31 | a y' + y'' - f(y e<sup>a x</sup>) e<sup>a x</sup> = 0 | 1 | 0 | (-e<sup>-a x</sup>/a, y e<sup>-a x</sup>) |
| EqWorld ODE 3.34 | y y' f(x) + y y'' + y'<sup>2</sup> + g(x) = 0 | 8 | 0 | (0, 1/y) |
| EqWorld ODE 3.35 | y<sup>2</sup> g(x) + y y' f(x) + y y'' - y'<sup>2</sup> = 0 | 8 | 1 | – |
| EqWorld ODE 3.36 | a y<sup>4 n - 2</sup> - n y'<sup>2</sup> + y<sup>2</sup> f(x) + y y'' = 0 | 3 | 0 | – |
| EqWorld ODE 3.37 | -n y'<sup>2</sup> + y<sup>2</sup> f(x) + y y'' + y<sup>n + 1</sup> g(x) = 0 | 8 | 0 | – |
| EqWorld ODE 3.38 | a y'<sup>2</sup> + y<sup>2</sup> g(x) + y y' f(x) + y y'' = 0 | 8 | 1 | – |
| EqWorld ODE 3.40 | -a y'<sup>2</sup> + y'' + f(x) e<sup>a y</sup> + g(x) = 0 | 8 | 0 | – |
| EqWorld ODE 3.41 | -a y'<sup>2</sup> + b e<sup>4 a y</sup> + y'' + f(x) = 0 | 3 | 0 | – |
| EqWorld ODE 3.42 | a y'<sup>2</sup> - y'/2 + y'' - f(y) e<sup>x</sup> = 0 | 1 | 0 | (e<sup>-x/2</sup>, 0) |
| EqWorld ODE 3.43 | al y'<sup>2</sup> - y' (be + f(y) e<sup>be x</sup>) + y'' = 0 | 1 | 0 | (e<sup>-be x</sup>, 0) |
| EqWorld ODE 3.45 | y'<sup>2</sup> f(y) - y'/2 + y'' - g(y) e<sup>x</sup> = 0 | 1 | 0 | (e<sup>-x/2</sup>, 0) |
| EqWorld ODE 3.46 | -x y'<sup>3</sup> f(y) + y'' = 0 | 8 | 1 | – |
| EqWorld ODE 3.47 | -y'<sup>2</sup> f(y) - y' g(x) + y'' = 0 | 8 | 0 | – |
| EqWorld ODE 3.50 | g'(x) y'/2 + y'' g(x) - f(y) h(y' √(g(x))) = 0 | 1 | 0 | (√(g(x)), 0) |

### Kamke chapters 1 and 2

sympy-extras' generators of the first order ODEs, checked by delierium 2.7.0: 1132 generators, 55 rejected, all in equations of degree ≥ 2 in y'.

#### One branch of y' (15)

The ODE is of degree ≥ 2 in y'; sympy-extras solves it for y' and uses one root, so its generators are symmetries of one branch only, not of the equation (Upabjojr/sympy-extras#72). delierium works with the equation as given.

| entry | equation | generators | rejected |
|---|---|---|---|
| Kamke 1.391 | a b x y + y'<sup>2</sup> + y' (a y + b x) = 0 | 4 | (1, 0), (x, -a x y), (y, -a y<sup>2</sup>) ... |
| Kamke 1.396 | -x y<sup>3</sup> + y y' (-x + y) + y'<sup>2</sup> = 0 | 4 | (1, 0), (x, -y), (x<sup>2</sup>, -2 x y + 1) ... |
| Kamke 1.438 | x<sup>2</sup> y'<sup>2</sup> + 3 x y y' + 2 y<sup>2</sup> = 0 | 4 | (x<sup>2</sup>, -2 x y), (x y, -2 y<sup>2</sup>) |
| Kamke 1.439 | x<sup>2</sup> y'<sup>2</sup> + 3 x y y' + 3 y<sup>2</sup> = 0 | 4 | (x<sup>2</sup>, -19766123228938883788950534717005268217019238601687045979401946115267427834105193477257762194788640190401304639326116750756405900693125192321831115114579149352478036620694996344617276729443037162919032678461504448319151050042886196295766384186626444668392723095190513689582967079725841221357121705129326845183712514570541127181 √3 x y/(4793948308133376050809356626790417130505696435385974610321006254196991189002939694090860515724206166552105643226582238650788994659192951900093458262499459229014829159542806380400945870314497034072243619514142687329172392466149123649695429897712948450032452801705995628312351763364213575030154444034770765224379668565267353027 I + 11579432716581463842363904269073373101177593589329372449494295325445954826402482420141554624617691404750167878475217087620674268909019144247856257322219613158647081360615728769611202529523859097255273912469622069769709902539874422980612446158513313628917664462891677250284527465362489622561362988741294308381015120191938300445 √3) + 10178226612672131687331821463424433956007845730915096758759933606873445456099314089076041163340227857297093352872952273454827911374739288521644198589580230894448378301609383583815384988814043094774545439433219073660806265110587948996375524391200547768327817491778522432958263552997414071296812817059785314734953177440006421127 I x y/(4793948308133376050809356626790417130505696435385974610321006254196991189002939694090860515724206166552105643226582238650788994659192951900093458262499459229014829159542806380400945870314497034072243619514142687329172392466149123649695429897712948450032452801705995628312351763364213575030154444034770765224379668565267353027 I + 11579432716581463842363904269073373101177593589329372449494295325445954826402482420141554624617691404750167878475217087620674268909019144247856257322219613158647081360615728769611202529523859097255273912469622069769709902539874422980612446158513313628917664462891677250284527465362489622561362988741294308381015120191938300445 √3)), (x y, -83268111227483531620898387284967890303586197981991010989810869616787239447330278902227589162986951403964442134111261445523162675375340336465960636656234744202508255659799020935856559539901596659118316132955226781603315112459404207135776302048444076255340433294101519210310660055998591539222137335561834361673035886537960146678 √3 y<sup>2</sup>/(-60479029679627410538277820570703004041050621525347433014441680542761209658502449833561926848149551619589678050817925844575717546192082346408407909472900072930271549827132530679878816684699209542017214436194380742962376110485237992281268481751428635741703993062304603421416021291715497506544372973368468104123525224330566811689 I + 75671750711531491260024865046879594882741005829776484998021139925445229517721002546005701724707818142506187439680149578540680965647587673113443060928456520445096020382243524183863978588167467620084615567368278102056335445134682135517607028616105596084128286550169213947345780467904226861662882548164045609156532332468829035015 √3) + 204226170586738352697454028426373898385687441032685877018694230702309658764335178569351442859286054643143798235747113134674597767759505029282776455602034890063051355314064082295614192909300015743152745005343988267528067333429880191698313265551301347738748419418710726053142702639429586552310883282298770569920086335199093770056 I y<sup>2</sup>/(-60479029679627410538277820570703004041050621525347433014441680542761209658502449833561926848149551619589678050817925844575717546192082346408407909472900072930271549827132530679878816684699209542017214436194380742962376110485237992281268481751428635741703993062304603421416021291715497506544372973368468104123525224330566811689 I + 75671750711531491260024865046879594882741005829776484998021139925445229517721002546005701724707818142506187439680149578540680965647587673113443060928456520445096020382243524183863978588167467620084615567368278102056335445134682135517607028616105596084128286550169213947345780467904226861662882548164045609156532332468829035015 √3)) |
| Kamke 1.440 | x<sup>2</sup> y'<sup>2</sup> + 4 x y y' - 5 y<sup>2</sup> = 0 | 4 | (x<sup>2</sup>, -5 x y), (x y, -5 y<sup>2</sup>) |
| Kamke 1.442 | x<sup>2</sup> y'<sup>2</sup> + y' (x<sup>3</sup> + x<sup>2</sup> y - 2 x y) + (1 - x) (-x<sup>2</sup> y + y<sup>2</sup>) = 0 | 4 | (x, -2 x<sup>2</sup>), (-x<sup>2</sup> + y, -4 x y), (0, x<sup>2</sup> + y) ... |
| Kamke 1.445 | a b y<sup>3</sup> + x<sup>2</sup> y'<sup>2</sup> + y' (a x<sup>2</sup> y<sup>3</sup> + b) = 0 | 2 | (1, 0), (x, -y/2) |
| Kamke 1.449 | 2 x y y' + y<sup>2</sup> + y'<sup>2</sup> (-a<sup>2</sup> + x<sup>2</sup>) = 0 | 4 | (x - x<sup>2</sup>/a, x y/a), (y - x y/a, y<sup>2</sup>/a) |
| Kamke 1.471 | -x + y y'<sup>2</sup> - y' (-x + y) = 0 | 9 | (1, 0), (x, x), (y, x) ... |
| Kamke 1.481 | x y y'<sup>2</sup> + x y + y' (x<sup>2</sup> + y<sup>2</sup>) = 0 | 4 | (x, 0), (x<sup>2</sup>, -x y), (x y, -y<sup>2</sup>) ... |
| Kamke 1.505 | -x<sup>3</sup> + x y<sup>2</sup> y'<sup>2</sup> + 2 x y<sup>2</sup> - 2 y<sup>3</sup> y' = 0 | 4 | (y, x), (x y, x<sup>2</sup>), (y<sup>2</sup>, x y) |
| Kamke 1.526 | -x<sup>3</sup> y<sup>3</sup> + y'<sup>3</sup> - y'<sup>2</sup> (x<sup>2</sup> + x y + y<sup>2</sup>) + y' (x<sup>3</sup> y + x<sup>2</sup> y<sup>2</sup> + x y<sup>3</sup>) = 0 | 3 | (1, x<sup>2</sup>), (x, 3 y), (0, 1) |
| Kamke 1.527 | -x y<sup>4</sup> y' - y<sup>5</sup> + y'<sup>3</sup> = 0 | 1 | (nan, nan) |
| Kamke 1.539 | y sin(x) + y'<sup>3</sup> sin(x) + y'<sup>2</sup> (-y sin(x) + cos(x)<sup>2</sup>) - y' (y cos(x)<sup>2</sup> + sin(x)) = 0 | 4 | (1, 0), (x, x y), (y, y<sup>2</sup>) ... |
| Kamke 1.540 | 2 x y' - x + 2 y y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 9 | (1, 0), (x, x/2), (y, x/4) ... |


---

<div style="page-break-before: always"></div>

## LIEPDE (REDUCE)

Thomas Wolf's LIEPDE, the determining equations solved by CRACK (REDUCE CSL rev. 7335, 120 s; `benchmarks/reduce_symmetries.py`). The comparison checks the dimension, each generator against delierium's determining equations, the closure, and the published generators in the tool's span.

| result | entries |
|---|---|
| same dimension | 689 |
| LIEPDE needs a solved form | 35 |
| different dimension | 34 |
| timeout | 13 |
| comparison crashed: exit code -9 | 8 |
| comparison crashed: exit code -6 | 4 |
| read back failed: RecursionError: Stack overflow (used 8156 kB) during compilation | 1 |
| comparison timeout | 1 |
| no result | 1 |


### Entries that differ (34)

#### Arbitrary function of an expression (18)

An arbitrary function of an expression (f(y/x), f(x y' - y), ...): LIEPDE takes it as an opaque operator of the variables, without the chain rule, and its splitting by the jet variables is too strong.

| entry | equation | dimension | result |
|---|---|---|---|
| EqWorld ODE 3.4 | y'' - f(a y + b x + c) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.5 | y'' - f(a x<sup>2</sup> + b x + c + y) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.6 | y'' - f(y/x)/x = 0 | 1 | dimension 0 |
| EqWorld ODE 3.7 | y'' - f(y/x)/x<sup>3</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.8 | y'' - f(y/√x)/x<sup>3/2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.9 | -x<sup>k - 2</sup> f(y/x<sup>k</sup>) + y'' = 0 | 1 | dimension 0 |
| EqWorld ODE 3.10 | y'' - y f(x<sup>n</sup> y<sup>m</sup>)/x<sup>2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.12 | y'' - f(y e<sup>a x</sup>) e<sup>-a x</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.13 | -y f(y<sup>m</sup> e<sup>a x</sup>) + y'' = 0 | 1 | dimension 0 |
| EqWorld ODE 3.14 | y'' - f(x<sup>n</sup> e<sup>a y</sup>)/x<sup>2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.15 | -ψ''(x) y/ψ(x) + y'' - f(y/ψ(x))/ψ(x)<sup>3</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.29 | x y'' - x<sup>n - 1</sup> f(x<sup>n</sup> y) + y' (n + 1) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.31 | a y' + y'' - f(y e<sup>a x</sup>) e<sup>a x</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.32 | x y'' - y' f(x<sup>n</sup> e<sup>a y</sup>) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.33 | x<sup>2</sup> y'' + x y' - f(x<sup>n</sup> e<sup>a y</sup>) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.48 | y'' - f(x) g(x y' - y) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.49 | y'' - y f(x y'/y)/x<sup>2</sup> = 0 | 2 | dimension 0 |
| EqWorld ODE 3.50 | g'(x) y'/2 + y'' g(x) - f(y) h(y' √(g(x))) = 0 | 1 | dimension 0 |

#### Fractional powers missed by CRACK (6)

CRACK (used by LIEPDE) misses generators with fractional powers of the dependent variable or of a derivative; DIMSYM finds them with the same input.

| entry | equation | dimension | result | note |
|---|---|---|---|---|
| Hydon Example 5.8 | -y'''<sup>4/3</sup> + y'''' = 0 | 5 | dimension 4. Missing: (x, 0) | The scaling x d/dx is missing. |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (x (n + 1/3), t (2 n - 2), -2 u) | The generators with u<sup>-4/3</sup> are missing. |
| CRC 1, 10.5 | -(u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 5 | dimension 2. Missing: (-2 x/3, 0, u), (0, e<sup>4 d t/3</sup>, d u e<sup>4 d t/3</sup>), (-x<sup>2</sup>, 0, 3 u x) | The generators with u<sup>-4/3</sup> are missing. |
| Kamke 6.157 | 3 y y'' - 5 y'<sup>2</sup> = 0 | 8 | dimension 7. Not closed | X y<sup>5/3</sup> d/dy is missing. |
| Kamke 7.8 | 4 y<sup>2</sup> y''' - 18 y y' y'' + 15 y'<sup>3</sup> = 0 | 7 | dimension 4 | Y = v<sup>-2</sup> gives v''' = 0; the generators with y<sup>3/2</sup> are missing. |
| Kamke 7.9 | 9 y<sup>2</sup> y''' - 45 y y' y'' + 40 y'<sup>3</sup> = 0 | 7 | dimension 4 | The generators with y<sup>5/3</sup> are missing. |

#### abs() from REDUCE's simplification (4)

REDUCE simplifies the power of a product with a fractional exponent in the input to an expression with abs(u1); abs breaks the scalings, and LIEPDE finds only those that survive it.

| entry | equation | dimension | result |
|---|---|---|---|
| BGL 5.3-4: sl(2) + <d<sub>t</sub>, u d<sub>u</sub>> | -f<sub>0</sub> (-9 u<sub>x</sub> u<sub>xx</sub>/u<sup>7</sup> + 12 u<sub>x</sub><sup>3</sup>/u<sup>8</sup>)/(u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup> - f<sub>0</sub> u<sub>xxx</sub>/(u<sup>6</sup> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup>) - g0 u + u<sub>t</sub> = 0 | 5 | dimension 3. Missing: (2 x, 0, -u), (-x<sup>2</sup>, 0, u x), (0, 0, u) |
| BGL 5.3-5: sl(2) + <d<sub>t</sub>, t d<sub>t</sub> + c u d<sub>u</sub>> | -f<sub>0</sub> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>(1 - 6 c)/(4 c)</sup> (-9 u<sub>x</sub> u<sub>xx</sub>/u<sup>7</sup> + 12 u<sub>x</sub><sup>3</sup>/u<sup>8</sup>) - f<sub>0</sub> u<sub>xxx</sub> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>(1 - 6 c)/(4 c)</sup>/u<sup>6</sup> - g0 u (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>1/(4 c)</sup> + u<sub>t</sub> = 0 | 5 | dimension 3. Missing: (2 x, 0, -u), (-x<sup>2</sup>, 0, u x), (0, t, c u) |
| BGL 5.3-6: sl(2) + <t u d<sub>u</sub>, -t d<sub>t</sub>> | -f<sub>0</sub> u<sub>xxx</sub>/(t u<sup>6</sup> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup>) + u<sub>t</sub> - (f<sub>0</sub> (-9 u<sub>x</sub> u<sub>xx</sub>/u<sup>7</sup> + 12 u<sub>x</sub><sup>3</sup>/u<sup>8</sup>)/(u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup> + u (g0 - log(u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)/4))/t = 0 | 5 | dimension 2. Missing: (2 x, 0, -u), (-x<sup>2</sup>, 0, u x), (0, 0, t u) |
| BGL 5.3-7: sl(2) + <t d<sub>t</sub>, u d<sub>u</sub>> | -f<sub>0</sub> u<sub>xxx</sub>/(t u<sup>6</sup> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup>) + u<sub>t</sub> - (f<sub>0</sub> (-9 u<sub>x</sub> u<sub>xx</sub>/u<sup>7</sup> + 12 u<sub>x</sub><sup>3</sup>/u<sup>8</sup>)/(u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>3/2</sup> + g0 u)/t = 0 | 5 | dimension 3. Missing: (2 x, 0, -u), (-x<sup>2</sup>, 0, u x), (0, 0, u) |

#### Rational generators missed by CRACK (3)

LIEPDE's solver CRACK does not find all rational generators; DIMSYM, with the same input, finds them.

| entry | equation | dimension | result |
|---|---|---|---|
| Bluman-Anco (3.413) | y'' - (y'<sup>2</sup> + 1) (2 x y' - 2 y)/(x<sup>2</sup> + y<sup>2</sup>) = 0 | 8 | dimension 7. Not closed |
| Kamke 6.186 | -12 x<sup>2</sup> y y' + 3 x y<sup>2</sup> + y y'' (8 - 8 x<sup>3</sup>) - y'<sup>2</sup> (4 - 4 x<sup>3</sup>) = 0 | 8 | dimension 6 |
| Kamke 6.195 | y'' (x<sup>2</sup> + y<sup>2</sup>) - (2 y'<sup>2</sup> + 2) (x y' - y) = 0 | 8 | dimension 7. Not closed |

#### Trigonometric functions taken as independent (1)

The equation has cot(y) and sin(y) cos(y) (REDUCE writes sin(2 u1)/2). LIEPDE splits the determining equations by them as independent functions (DIMSYM's log: 'found special function: cot(u(1)) ... cos(2*u(1))'), without cot = cos/sin and sin<sup>2</sup> + cos<sup>2</sup> = 1, so its conditions are too strong; the equation is linearizable, dimension 8.

| entry | equation | dimension | result |
|---|---|---|---|
| Bluman-Anco Exercise 3.5-3 | -2 y'<sup>2</sup> cot(y) + y'' - sin(y) cos(y) = 0 | 8 | dimension 1 |

#### Infinite part of a linear PDE lost (1)

For a linear PDE the generators φ d/du, φ any solution of the equation, make the algebra infinite; LIEPDE returns the finite part only.

| entry | equation | dimension | result |
|---|---|---|---|
| PINNacle HeatND | -u<sub>t</sub> + u<sub>x1x1</sub> + u<sub>x2x2</sub> + u<sub>x3x3</sub> + u<sub>x4x4</sub> + u<sub>x5x5</sub>/5 - (x1<sup>2</sup>/5 + x2<sup>2</sup>/5 + x3<sup>2</sup>/5 + x4<sup>2</sup>/5 + x5<sup>2</sup>/5) e<sup>t + x1<sup>2</sup>/2 + x2<sup>2</sup>/2 + x3<sup>2</sup>/2 + x4<sup>2</sup>/2 + x5<sup>2</sup>/2</sup> = 0 | infinite | dimension 8 |

#### Linearizable ODE, no symmetry found (1)

Linearizable (u = int e<sup>-int f dy</sup> dy gives u'' = g(x) u'); LIEPDE finds no symmetry, ReLie (also CRACK) the right dimension; not traced further.

| entry | equation | dimension | result |
|---|---|---|---|
| EqWorld ODE 3.47 | -y'<sup>2</sup> f(y) - y' g(x) + y'' = 0 | 8 | dimension 0 |


---

<div style="page-break-before: always"></div>

## ReLie (REDUCE)

Francesco Oliveri's ReLie 3.0, also with CRACK (`benchmarks/relie_symmetries.py`; ReLie is not redistributed); compared as LIEPDE.

| result | entries |
|---|---|
| same dimension | 691 |
| several roots for the leading derivative (one<sub>of</sub>), not solved | 25 |
| different dimension | 24 |
| timeout | 15 |
| comparison crashed: exit code -9 | 12 |
| no result | 10 |
| comparison crashed: exit code -6 | 6 |
| comparison timeout | 3 |


### Entries that differ (24)

#### Arbitrary function of an expression (18)

An arbitrary function of an expression (f(y/x), f(x y' - y), ...): ReLie takes it as an opaque operator of the variables, without the chain rule, and its splitting by the jet variables is too strong.

| entry | equation | dimension | result |
|---|---|---|---|
| EqWorld ODE 3.4 | y'' - f(a y + b x + c) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.5 | y'' - f(a x<sup>2</sup> + b x + c + y) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.6 | y'' - f(y/x)/x = 0 | 1 | dimension 0 |
| EqWorld ODE 3.7 | y'' - f(y/x)/x<sup>3</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.8 | y'' - f(y/√x)/x<sup>3/2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.9 | -x<sup>k - 2</sup> f(y/x<sup>k</sup>) + y'' = 0 | 1 | dimension 0 |
| EqWorld ODE 3.10 | y'' - y f(x<sup>n</sup> y<sup>m</sup>)/x<sup>2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.12 | y'' - f(y e<sup>a x</sup>) e<sup>-a x</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.13 | -y f(y<sup>m</sup> e<sup>a x</sup>) + y'' = 0 | 1 | dimension 0 |
| EqWorld ODE 3.14 | y'' - f(x<sup>n</sup> e<sup>a y</sup>)/x<sup>2</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.15 | -ψ''(x) y/ψ(x) + y'' - f(y/ψ(x))/ψ(x)<sup>3</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.29 | x y'' - x<sup>n - 1</sup> f(x<sup>n</sup> y) + y' (n + 1) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.31 | a y' + y'' - f(y e<sup>a x</sup>) e<sup>a x</sup> = 0 | 1 | dimension 0 |
| EqWorld ODE 3.32 | x y'' - y' f(x<sup>n</sup> e<sup>a y</sup>) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.33 | x<sup>2</sup> y'' + x y' - f(x<sup>n</sup> e<sup>a y</sup>) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.48 | y'' - f(x) g(x y' - y) = 0 | 1 | dimension 0 |
| EqWorld ODE 3.49 | y'' - y f(x y'/y)/x<sup>2</sup> = 0 | 2 | dimension 0 |
| EqWorld ODE 3.50 | g'(x) y'/2 + y'' g(x) - f(y) h(y' √(g(x))) = 0 | 1 | dimension 0 |

#### Fractional powers missed by CRACK (3)

CRACK (used by ReLie) misses generators with fractional powers of the dependent variable or of a derivative; DIMSYM finds them with the same input.

| entry | equation | dimension | result | note |
|---|---|---|---|---|
| Kamke 6.157 | 3 y y'' - 5 y'<sup>2</sup> = 0 | 8 | dimension 7. Not closed | X y<sup>5/3</sup> d/dy is missing. |
| Kamke 7.8 | 4 y<sup>2</sup> y''' - 18 y y' y'' + 15 y'<sup>3</sup> = 0 | 7 | dimension 4 | Y = v<sup>-2</sup> gives v''' = 0; the generators with y<sup>3/2</sup> are missing. |
| Kamke 7.9 | 9 y<sup>2</sup> y''' - 45 y y' y'' + 40 y'<sup>3</sup> = 0 | 7 | dimension 4 | The generators with y<sup>5/3</sup> are missing. |

#### Trigonometric functions taken as independent (1)

The equation has cot(y) and sin(y) cos(y) (REDUCE writes sin(2 u1)/2). ReLie splits the determining equations by them as independent functions (DIMSYM's log: 'found special function: cot(u(1)) ... cos(2*u(1))'), without cot = cos/sin and sin<sup>2</sup> + cos<sup>2</sup> = 1, so its conditions are too strong; the equation is linearizable, dimension 8.

| entry | equation | dimension | result |
|---|---|---|---|
| Bluman-Anco Exercise 3.5-3 | -2 y'<sup>2</sup> cot(y) + y'' - sin(y) cos(y) = 0 | 8 | dimension 2 |

#### Free functions with too many arguments (1)

ReLie takes the arguments of its free functions from REDUCE's global list after CRACK (fargs), which still has the variables CRACK started with: it returns f<sub>1</sub>(x, t), i.e. infinitely many generators; with f<sub>1</sub> = f<sub>1</sub>(x) its own condition gives the 5.

| entry | equation | dimension | result |
|---|---|---|---|
| Gabel et al. 7 | u<sub>t</sub> - atan(u<sub>xx</sub>) = 0 | 5 | dimension infinite |

#### Rational generators missed by CRACK (1)

ReLie's solver CRACK does not find all rational generators; DIMSYM, with the same input, finds them.

| entry | equation | dimension | result |
|---|---|---|---|
| Kamke 6.186 | -12 x<sup>2</sup> y y' + 3 x y<sup>2</sup> + y y'' (8 - 8 x<sup>3</sup>) - y'<sup>2</sup> (4 - 4 x<sup>3</sup>) = 0 | 8 | dimension 6 |


---

<div style="page-break-before: always"></div>

## DIMSYM (REDUCE)

DIMSYM 2.3 (Sherring, Prince, Jerie), with its own solver (`benchmarks/dimsym_symmetries.py`; DIMSYM is not redistributed); compared as LIEPDE.

| result | entries |
|---|---|
| same dimension | 713 |
| not converted: 3 solutions for the leading derivative | 23 |
| timeout | 9 |
| not converted: 2 solutions for the leading derivative | 6 |
| not converted: 4 solutions for the leading derivative | 4 |
| comparison crashed: exit code -6 | 4 |
| comparison crashed: exit code -9 | 3 |
| not converted: arbitrary function of x<sup>n</sup> e<sup>a y</sup> | 3 |
| not converted: 6 solutions for the leading derivative | 2 |
| not converted: arbitrary function of y/x | 2 |
| not converted: arbitrary function of y e<sup>a x</sup> | 2 |
| not converted: arbitrary function of e t | 1 |
| different dimension | 1 |
| not converted: arbitrary function of a y + b x + c | 1 |
| not converted: arbitrary function of a x<sup>2</sup> + b x + c + y | 1 |
| not converted: arbitrary function of y/√x | 1 |
| not converted: arbitrary function of y/x<sup>k</sup> | 1 |
| not converted: arbitrary function of x<sup>n</sup> y<sup>m</sup> | 1 |
| not converted: arbitrary function of y<sup>m</sup> e<sup>a x</sup> | 1 |
| not converted: arbitrary function of y/ψ(x) | 1 |
| not converted: arbitrary function of x<sup>n</sup> y | 1 |
| comparison timeout | 1 |
| not converted: arbitrary function of x y' - y | 1 |
| not converted: arbitrary function of x y'/y | 1 |
| not converted: arbitrary function of y' √(g(x)) | 1 |
| not converted: arbitrary function of a y + y'<sup>2</sup> | 1 |


### Entries that differ (1)

#### Trigonometric functions taken as independent (1)

The equation has cot(y) and sin(y) cos(y) (REDUCE writes sin(2 u1)/2). DIMSYM splits the determining equations by them as independent functions (DIMSYM's log: 'found special function: cot(u(1)) ... cos(2*u(1))'), without cot = cos/sin and sin<sup>2</sup> + cos<sup>2</sup> = 1, so its conditions are too strong; the equation is linearizable, dimension 8.

| entry | equation | dimension | result |
|---|---|---|---|
| Bluman-Anco Exercise 3.5-3 | -2 y'<sup>2</sup> cot(y) + y'' - sin(y) cos(y) = 0 | 8 | dimension 1 |


---

<div style="page-break-before: always"></div>

## SPDE (REDUCE)

Fritz Schwarz's SPDE (1986), part of REDUCE (`benchmarks/spde_symmetries.py`); compared as LIEPDE.

| result | entries |
|---|---|
| same dimension | 582 |
| timeout | 116 |
| different dimension | 62 |
| comparison timeout | 3 |
| not converted: arbitrary function of x<sup>n</sup> e<sup>a y</sup> | 3 |
| not converted: arbitrary function of y/x | 2 |
| not converted: arbitrary function of y e<sup>a x</sup> | 2 |
| not converted: arbitrary function of e t | 1 |
| read back failed: SyntaxError: invalid syntax (<string>, line 1) | 1 |
| comparison crashed: exit code -9 | 1 |
| not converted: arbitrary function of a y + b x + c | 1 |
| not converted: arbitrary function of a x<sup>2</sup> + b x + c + y | 1 |
| not converted: arbitrary function of y/√x | 1 |
| not converted: arbitrary function of y/x<sup>k</sup> | 1 |
| not converted: arbitrary function of x<sup>n</sup> y<sup>m</sup> | 1 |
| not converted: arbitrary function of y<sup>m</sup> e<sup>a x</sup> | 1 |
| not converted: arbitrary function of y/ψ(x) | 1 |
| comparison crashed: exit code -6 | 1 |
| not converted: arbitrary function of x<sup>n</sup> y | 1 |
| not converted: arbitrary function of x y' - y | 1 |
| not converted: arbitrary function of x y'/y | 1 |
| not converted: arbitrary function of y' √(g(x)) | 1 |
| not converted: arbitrary function of a y + y'<sup>2</sup> | 1 |


### Entries that differ (152)

#### Wrong η components (90)

SPDE (version of November 1986) computes wrong η components in today's REDUCE, by its own result(): y'' = 0 gives x<sup>2</sup> d/dx - x y d/dy instead of + x y d/dy. The dimension is right, the generators are not.

| entry | equation | dimension | rejected | missing | closed |
|---|---|---|---|---|---|
| y'' = 0 | y'' = 0 | 8 | (-x<sup>2</sup>, x y), (x y, -y<sup>2</sup>) | (x<sup>2</sup>, x y), (x y, y<sup>2</sup>) | no |
| Arrigo 2.18 | x y<sup>4</sup> + y y' + y'' = 0 | 1 | (1, 1/3) | (x, -y) | yes |
| modified Emden family, k = 1/3 | y<sup>3</sup> + y y'/3 + y'' = 0 | 2 | (x/54, 1/162) | (x, -y) | yes |
| Schwarz Example 5.15, (5.32) | x<sup>6</sup> y y' y'' - 2 x<sup>6</sup> y'<sup>3</sup> + 2 x<sup>5</sup> y y'<sup>2</sup> + y<sup>5</sup> = 0 | 3 | (1, 3/2), (x, 0), (0, y) | – | no |
| Schwarz Example 5.17 | -9 x<sup>5</sup> y'<sup>4</sup> + 8 x y<sup>6</sup> y'' - 16 x y<sup>5</sup> y'<sup>2</sup> + 16 y<sup>6</sup> y' = 0 | 3 | (1, 2/3), (x, 0), (0, y) | – | no |
| Blasius equation | y y'' + y''' = 0 | 2 | (x, 1) | (x, -y) | yes |
| Ermakov-Pinney equation | y'' - 1/y<sup>3</sup> = 0 | 3 | (-2 x, 1), (-x<sup>2</sup>, x) | (2 x, y), (x<sup>2</sup>, x y) | yes |
| Chazy equation | -2 y y'' + 3 y'<sup>2</sup> + y''' = 0 | 3 | (x, y), (x<sup>2</sup>/2, x y + 3) | (x, -y), (x<sup>2</sup>, -2 x y - 6) | no |
| Arrigo Exercises 2.6, 1 (i) | y y'' - y'<sup>2</sup> + y''' = 0 | 2 | (-x, 1) | (x, -y) | yes |
| Arrigo Exercises 2.6, 1 (iii) | y''' - 1/y<sup>3</sup> = 0 | 2 | (x, 3/4) | (4 x, 3 y) | yes |
| Arrigo Exercises 2.6, 3 | ((y/y')'' y y')' = 0 | 3 | (0, 1) | (0, y) | yes |
| Lane-Emden equation, n = 5 | y<sup>5</sup> + y'' + 2 y'/x = 0 | 1 | (2, 1/x) | (x, -y/2) | yes |
| heat equation with power source | -u<sup>2</sup> + u<sub>t</sub> - u<sub>xx</sub> = 0 | 3 | (x/2, t, 1) | (x, 2 t, -2 u) | yes |
| u<sub>t</sub> = u<sub>xx</sub> - 2u<sup>3</sup> | 2 u<sup>3</sup> + u<sub>t</sub> - u<sub>xx</sub> = 0 | 3 | (x/2, t, -1/2) | (x, 2 t, -u) | yes |
| Harry Dym equation | -u<sup>3</sup> u<sub>xxx</sub> + u<sub>t</sub> = 0 | 5 | (x<sup>2</sup>/4, 0, x/2), (0, -t, 1/3), (-x/2, -t, -1/6) | (x, 0, u), (x<sup>2</sup>, 0, 2 u x), (0, 3 t, -u) | yes |
| modified KdV equation | u<sup>2</sup> u<sub>x</sub> + u<sub>t</sub> + u<sub>xxx</sub> = 0 | 3 | (-x, -3 t, 1) | (x, 3 t, -u) | yes |
| nonlinear diffusion u<sub>t</sub> = (u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> | -(u<sup>2</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>t</sub> = 0 | 4 | (0, -2 t, 1), (x, -2 t, 0) | (x, 2 t, 0), (x, 0, u) | yes |
| Baumann p. 299 | 6 λ u<sub>x</sub> - 6 u<sup>2</sup> u<sub>x</sub> + u<sub>t</sub> + u<sub>xxx</sub> = 0 | 3 | (-12 λ t - x, -3 t, 1) | (12 λ t + x, 3 t, -u) | yes |
| Baumann p. 301 | μ u<sub>xxx</sub> - ν u<sub>xx</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 3 | (-t, 0, 1) | (t, 0, 1) | yes |
| Hydon Example 3.4 | y''' - 1/y<sup>3</sup> = 0 | 2 | (x, 3/4) | (x, 3 y/4) | yes |
| Hydon Example 5.2 | y'''' - y''' (2 - 2 y')/y = 0 | 3 | (x, 1), (x<sup>2</sup>, 2 x) | (x, y), (x<sup>2</sup>, 2 x y) | yes |
| Hydon Example 6.5 | y''' - 2 y''<sup>2</sup>/y' - y'<sup>2</sup>/x - y''/x = 0 | 2 | (1, 0) | (x, 0) | yes |
| Hydon Example 7.2 | y''' - y''<sup>2</sup> (3 y' - 1)/y'<sup>2</sup> = 0 | 4 | (x, -y) | (x, y) | yes |
| Hydon Example 7.7 | -3 y y' + y''' = 0 | 2 | (-x/2, 1) | (x, -2 y) | yes |
| Hydon Example 11.4 | y''' + y''/y' - y''<sup>2</sup>/x = 0 | 2 | (1/2, y) | (x/2, y) | yes |
| Hydon Exercise 6.2 | y'' - y y'/x<sup>3</sup> + y<sup>2</sup>/x<sup>4</sup> = 0 | 2 | (1, 2/(3 x<sup>3</sup>)), (x, 1/(3 x<sup>2</sup>)) | (x<sup>2</sup>, x y), (x, 2 y) | no |
| Hydon Exercise 6.5 | y'' - y'<sup>2</sup>/y + y<sup>2</sup>/(x<sup>3</sup> y') = 0 | 2 | (1, 0), (0, 1) | (x, 0), (0, y) | yes |
| Bluman-Anco (3.194) | ((y/y')'' y y')' = 0 | 3 | (0, 1) | (0, y) | yes |
| Bluman-Anco (3.245) | -6 x y''<sup>3</sup>/y'<sup>2</sup> + y''' - 6 y''<sup>2</sup>/y' = 0 | 3 | (1, 0) | (x, 0) | yes |
| Bluman-Anco (3.499) | y y' + y''' = 0 | 2 | (-x/2, 1) | (x, -2 y) | yes |
| Bluman-Anco Exercise 3.5-4 | -y y''<sup>3</sup>/y'<sup>3</sup> + y''' = 0 | 3 | (0, 1) | – | yes |
| Bluman-Anco Exercise 3.5-6 | y'''' - y' y'''/y = 0 | 3 | (0, -1/6), (x/5, 1/15) | – | yes |
| Bluman-Kumei Exercise 4.2-8 | -A<sup>2</sup> u<sub>xx</sub> (B + u)<sup>4</sup> + u<sub>tt</sub> = 0 | 5 | (-x, t, 0) | (x, t, 0) | yes |
| CRC 1, 10.4 | -w<sub>t</sub><sup>3</sup>/27 + w<sub>xx</sub> = 0 | 7 | (0, t, -3 w/2) | (x, 2 t, 2 w), (0, 2 t/3, w) | yes |
| CRC 1, 11.8 | b u<sub>xxx</sub> + g u u<sub>x</sub> - μ u<sub>xx</sub> + u<sub>t</sub> = 0 | 3 | (-g t, 0, 1) | (g t, 0, 1) | yes |
| CRC 1, 11.10 | b u<sub>ttt</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 3 | (x, 0, 1) | (x, 0, u) | yes |
| CRC 1, 12.4 | -(u<sub>x</sub> e<sup>u</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 4 | (-x, t, 0), (-x/2, 0, 1) | (x, t, 0), (x, 0, 2) | yes |
| CRC 1, 12.4 | -(k u<sub>x</sub>/u<sup>4</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 5 | (2 x, 0, 1), (0, -t<sup>2</sup>, t) | (0, t<sup>2</sup>, t u), (2 x, 0, -u) | yes |
| CRC 1, 12.4 | -k/w<sub>xx</sub><sup>3</sup> + w<sub>tt</sub> = 0 | 9 | (0, -t<sup>2</sup>, t w), (-2 x/3, 0, w) | (x, t, 2 w), (2 x, 0, 3 w), (0, t<sup>2</sup>, t w) | no |
| APEBench phy<sub>kdv</sub> | 6 u u<sub>x</sub> + u<sub>t</sub> + u<sub>xxx</sub> + u<sub>xxxx</sub>/8 = 0 | 3 | (-6 t, 0, 1) | (6 t, 0, 1) | yes |
| APEBench phy_burgers_sc, 2D | u (u<sub>x</sub> + u<sub>y</sub>)/8 + u<sub>t</sub> - 3 u<sub>xx</sub>/10000 - 3 u<sub>yy</sub>/10000 = 0 | 5 | (x, -y, 2 t, u), (t/8, -t/8, 0, -1) | (t/8, t/8, 0, 1), (x, y, 2 t, -u) | no |
| APEBench phy<sub>kdv</sub>, 2D | 6 u (u<sub>x</sub> + u<sub>y</sub>) + u<sub>t</sub> + u<sub>xxx</sub> + u<sub>xxxx</sub>/8 + u<sub>yyy</sub> + u<sub>yyyy</sub>/8 = 0 | 4 | (6 t, -6 t, 0, 1) | (6 t, 6 t, 0, 1) | yes |
| Gabel et al. 15 | u<sub>t</sub> - u<sub>xx</sub> - 1/u = 0 | 3 | (x/2, t, 1/2) | (x, 2 t, u) | yes |
| Gabel et al. 17 | u<sup>2</sup> + u<sub>t</sub> - u<sub>xx</sub> = 0 | 3 | (x/2, t, 1) | (x, 2 t, -2 u) | yes |
| EqWorld 2.2.1 | -(w w<sub>x</sub>)<sub>x</sub> a + w<sub>tt</sub> = 0 | 4 | (-x/2, 0, 1) | (x, 0, 2 w), (0, t, -2 w) | yes |
| EqWorld 2.2.3 | -(w<sub>x</sub> e<sup>lam w</sup>)<sub>x</sub> a + w<sub>tt</sub> = 0 | 4 | (-x, t, 0), (-lam x/2, 0, 1) | (x, t, 0), (lam x, 0, 2) | yes |
| EqWorld 3.3.1 | (w<sub>y</sub> (al w + be))<sub>y</sub> + w<sub>xx</sub> = 0 | 4 | (x/2, 0, 1/al) | (0, y, 2 w + 2 be/al) | yes |
| EqWorld 3.3.2 | (a w<sub>y</sub> e<sup>be w</sup>)<sub>y</sub> + w<sub>xx</sub> = 0 | 4 | (x, -y, 0), (0, -be y/2, 1) | (x, y, 0), (0, y, 2/be) | yes |
| EqWorld 4.1.1 | a w<sub>x</sub> w<sub>xx</sub> + w<sub>yy</sub> = 0 | 6 | (x, -3 y/2, 0), (0, y/2, w) | (0, y, -2 w) | yes |
| EqWorld 4.2.2 | -A - w<sub>xx</sub> w<sub>yy</sub> + w<sub>xy</sub><sup>2</sup> = 0 | 9 | (-x, 0, w) | (x, y, 2 w) | yes |
| EqWorld 5.1.3 | 6 sig w<sup>2</sup> w<sub>x</sub> + w<sub>t</sub> + w<sub>xxx</sub> = 0 | 3 | (-x, -3 t, 1) | (x, 3 t, -w) | yes |
| EqWorld 6.1.1 | (w w<sub>x</sub>)<sub>x</sub> + w<sub>tt</sub> + w<sub>xxxx</sub> = 0 | 3 | (x/2, -t, 1) | (x, 2 t, -2 w) | yes |
| EqWorld 6.1.2 | -a (w<sub>xxxx</sub> + 2 w<sub>xxyy</sub> + w<sub>yyyy</sub>) - w<sub>x</sub> (w<sub>xxy</sub> + w<sub>yyy</sub>) + w<sub>y</sub> (w<sub>xxx</sub> + w<sub>xyy</sub>) = 0 | 5 | (y, x, 0), (x, -y, 0) | (x, y, 0), (y, -x, 0) | no |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 12 | -δ u<sub>xx</sub> e<sup>2 u<sub>x</sub></sup> - 2 ε2 x + u<sub>tt</sub> - e<sup>u<sub>x</sub></sup> = 0 | 5 | (-x, 0, u + x), (1, 0, -ε2 t<sup>2</sup>) | (x, 0, u + x), (1, 0, ε2 t<sup>2</sup>) | no |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 17 | -δ u<sub>xx</sub>/u<sub>x</sub> + u<sub>tt</sub> - 2 x - 2 log(u<sub>x</sub>) = 0 | 5 | (0, -t/2, t<sup>2</sup> + u) | (0, t, 2 t<sup>2</sup> + 2 u) | no |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 19 | -δ u<sub>xx</sub>/u<sub>x</sub><sup>4</sup> - ν/(u<sub>x</sub><sup>3</sup> x) + u<sub>tt</sub> = 0 | 6 | (2, 0, u), (0, -t<sup>2</sup>, t u), (1, t, 0) | (0, 2 t, u), (0, t<sup>2</sup>, t u), (2 x, 0, u) | no |
| Vaneeva, Bihlo, Popovych 14a | -ε u<sub>xx</sub>/u<sup>4</sup> - ε1/u<sup>3</sup> + u<sub>tt</sub> = 0 | 4 | (0, t<sup>2</sup>, t), (0, -t, -1/2) | (0, 2 t, u), (0, t<sup>2</sup>, t u) | yes |
| Vaneeva, Bihlo, Popovych 14d | -ε u<sup>4</sup> u<sub>xx</sub> - ε1 u + u<sub>tt</sub> = 0 | 4 | (-x<sup>2</sup>, 0, x), (-x, 0, 1/2) | (2 x, 0, u), (x<sup>2</sup>, 0, u x) | yes |
| Vaneeva, Bihlo, Popovych 15a | -ε u<sub>xx</sub>/u<sup>4</sup> - ν/(u<sup>3</sup> x<sup>2</sup>) + u<sub>tt</sub> = 0 | 4 | (0, -t<sup>2</sup>, t), (-1/2, t, -1/4), (-1/2, 0, 1/4) | (0, 2 t, u), (0, t<sup>2</sup>, t u), (2 x, 0, -u) | yes |
| Vaneeva, Bihlo, Popovych 19a | -ε u<sub>xx</sub>/u<sup>4</sup> + u<sub>tt</sub> = 0 | 5 | (2 x, 0, 1), (0, -t<sup>2</sup>, t) | (0, 2 t, u), (0, t<sup>2</sup>, t u), (2 x, 0, -u) | yes |
| Vaneeva, Bihlo, Popovych 19d | -ε u<sup>4</sup> u<sub>xx</sub> + u<sub>tt</sub> = 0 | 5 | (x<sup>2</sup>, 0, x), (2 x, 0, 1), (-x, t, 0) | (x, t, 0), (2 x, 0, u), (x<sup>2</sup>, 0, u x) | yes |
| Zhdanov 2005, dimension 5 | u<sub>t</sub> - u<sub>xx</sub>/u<sup>4</sup> + 2 u<sub>x</sub><sup>2</sup>/u<sup>5</sup> = 0 | 5 | (0, 4 t, 1), (-x<sup>2</sup>, 0, x) | (-2 x, 0, u), (-x<sup>2</sup>, 0, u x) | yes |
| Gungor, Lahno, Zhdanov (4.11) | -lam u<sub>x</sub>/x<sup>2</sup> + u<sub>t</sub> - u<sub>xxx</sub> + 3 u<sub>xx</sub><sup>2</sup>/(2 u<sub>x</sub>) = 0 | 5 | (1/3, t, 0) | (x/3, t, 0) | yes |
| Nadjafikhah et al. | -u<sup>4</sup> (u<sub>xx</sub> + u<sub>yy</sub>) + u<sub>tt</sub> = 0 | 6 | (0, 0, t, 1/2), (-x, -y, 0, 1/2) | (x, y, 0, u/2), (0, 0, t, -u/2) | yes |
| Fornberg-Whitham equation | u u<sub>x</sub> - u u<sub>xxx</sub> + u<sub>t</sub> - 3 u<sub>x</sub> u<sub>xx</sub> + u<sub>x</sub> - u<sub>xxt</sub> = 0 | 3 | (t, 0, 1/2) | (t, 0, 1) | yes |
| mGVE (D = d/dt + u d/dx) | be u<sub>x</sub> + p u u<sub>x</sub> + q u u<sub>x</sub> + q u<sub>t</sub> + u<sup>2</sup> u<sub>xxx</sub> + 2 u u<sub>txx</sub> + 4 u u<sub>x</sub> u<sub>xx</sub> + u<sub>t</sub> u<sub>xx</sub> + u<sub>ttx</sub> + 3 u<sub>tx</sub> u<sub>x</sub> + u<sub>x</sub><sup>3</sup> = 0 | 3 | ((2 be t + p x)/(p q), -t, (-2 be - 2 p u)/p) | (be t + p x/2, -p t/2, be + p u) | yes |
| mGVE, p = be = 0 | q u u<sub>x</sub> + q u<sub>t</sub> + u<sup>2</sup> u<sub>xxx</sub> + 2 u u<sub>txx</sub> + 4 u u<sub>x</sub> u<sub>xx</sub> + u<sub>t</sub> u<sub>xx</sub> + u<sub>ttx</sub> + 3 u<sub>tx</sub> u<sub>x</sub> + u<sub>x</sub><sup>3</sup> = 0 | 4 | (x, -t, -2 u), (-t, 0, 1) | (t, 0, 1), (x, -t, 2 u) | no |
| MEE circular rod | -c<sup>2</sup> u<sub>xx</sub><sup>2</sup>/2 - c<sup>2</sup> u<sub>xx</sub> - n u<sub>ttxx</sub> + u<sub>tt</sub> = 0 | 7 | (0, t/2, c<sup>2</sup> t<sup>2</sup>/2 + u + x<sup>2</sup>/2) | (0, t, -c<sup>2</sup> t<sup>2</sup> - 2 u - x<sup>2</sup>) | yes |
| Hashemi, Baleanu 1.1.4 | a1 u u<sub>x</sub> - a2 u<sub>xx</sub> + a3 u<sub>xxx</sub> + a4 u<sub>xxxx</sub> + u<sub>t</sub> = 0 | 3 | (-a1 t, 0, 1) | (a1 t, 0, 1) | yes |
| Kamke 6.1 | -y<sup>2</sup> + y'' = 0 | 2 | (x, 1) | – | yes |
| Kamke 6.2 | -6 y<sup>2</sup> + y'' = 0 | 2 | (x, 1) | – | yes |
| Kamke 6.7 | -a y<sup>3</sup> + y'' = 0 | 2 | (-x, 1) | – | yes |
| Kamke 6.30 | -y<sup>3</sup> + y y' + y'' = 0 | 2 | (x/6, 1/18) | – | yes |
| Kamke 6.42 | -2 a y y' + y'' = 0 | 2 | (-x, 1/3) | – | yes |
| Kamke 6.43 | a y y' + b y<sup>3</sup> + y'' = 0 | 2 | (x/6, 1/18) | – | yes |
| Kamke 6.92 | x<sup>3</sup> (-y<sup>3</sup> + y y' + y'') + 12 x y + 24 = 0 | 1 | (1, 1) | – | yes |
| Kamke 6.104 | -a + y y'' = 0 | 2 | (x, 1) | – | yes |
| Kamke 6.105 | -a x + y y'' = 0 | 1 | (2/3, 1) | – | yes |
| Kamke 6.106 | -a x<sup>2</sup> + y y'' = 0 | 1 | (1/2, 1) | – | yes |
| Kamke 6.188 | -a + y<sup>2</sup> y'' = 0 | 2 | (3 x/2, 1) | – | yes |
| Kamke 6.205 | -a + x y<sup>2</sup> y'' = 0 | 2 | (3, 1), (x, x) | – | no |
| Kamke 6.209 | -a + y<sup>3</sup> y'' = 0 | 3 | (-2 x, 1), (-x<sup>2</sup>, x) | – | yes |
| Kamke 6.219 | d y + y'' (a x<sup>2</sup> + 2 b x + c + y<sup>2</sup>)<sup>2</sup> = 0 | 1 | ((-a x<sup>2</sup> - 2 b x - c)/b, (a x + b)/b) | (a x<sup>2</sup> + 2 b x + c, y (a x + b)) | yes |
| Kamke 6.226 | -x<sup>2</sup> y y' - x y<sup>2</sup> + y' y'' = 0 | 1 | (0, 1) | – | yes |
| Kamke 6.229 | a x<sup>3</sup> y' y'' + b y<sup>2</sup> = 0 | 2 | (0, 1), (1, 0) | – | yes |
| Kamke 6.232 | y<sup>3</sup> + y'' (y<sup>2</sup> + y'<sup>2</sup>) = 0 | 2 | (0, 1) | – | yes |
| Kamke 6.233 | -b + y'' (a (x y' - y) + y'<sup>2</sup>) = 0 | 1 | (1/4, 1/2) | – | yes |
| Kamke 7.3 | -y y'' + y'<sup>2</sup> + y''' = 0 | 2 | (-x, 1) | – | yes |
| Kamke 7.4 | a y y'' + y''' = 0 | 2 | (x, 1) | – | yes |
| Kamke 7.7 | y<sup>3</sup> y' + y y''' - y' y'' = 0 | 2 | (-x, 1) | – | yes |

#### Remaining conditions incomplete (39)

SPDE's remaining conditions are incomplete, so it reports more generators than there are (its wrong η components enter too).

| entry | equation | dimension | result |
|---|---|---|---|
| Kamke 1.535 | 8 x y'<sup>3</sup> - 12 y y'<sup>2</sup> + 9 y = 0 | 3 | dimension infinite |
| Baumann p. 203 | -a √(b<sup>2</sup> u''<sup>2</sup> + 1) + u'' u''' = 0 | 3 | dimension 4 |
| Hydon Example 11.1 | y'' - tan(y') = 0 | 2 | dimension 6 |
| CRC 1, 10.3 | v<sub>t</sub> - v<sub>xx</sub> k(v<sub>x</sub>) = 0 | 4 | dimension 5 |
| CRC 1, 10.4 | w<sub>xx</sub> - G(w<sub>t</sub>) = 0 | 5 | dimension infinite |
| CRC 1, 10.10 | τ0 u<sub>tt</sub> + u<sub>t</sub> - u<sub>xx</sub> k(u<sub>x</sub>) = 0 | 4 | dimension 5 |
| CRC 1, 12.4 | v<sub>tt</sub> - v<sub>xx</sub> φ(v<sub>x</sub>) = 0 | 5 | dimension 6 |
| CRC 1, 12.4 | -k e<sup>w<sub>xx</sub></sup> + w<sub>tt</sub> = 0 | 8 | dimension 11 |
| Gabel et al. 7 | u<sub>t</sub> - atan(u<sub>xx</sub>) = 0 | 5 | dimension infinite |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 13 | -δ u<sub>xx</sub> e<sup>2 u<sub>x</sub></sup> + u<sub>tt</sub> - e<sup>q u<sub>x</sub></sup> = 0 | 5 | dimension 6 |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 14 | -δ u<sub>x</sub><sup>2 p</sup> u<sub>xx</sub> + u<sub>tt</sub> - u<sub>x</sub><sup>q</sup> = 0 | 5 | dimension 6 |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 16 | -δ u<sub>x</sub><sup>2 p</sup> u<sub>xx</sub> + u<sub>tt</sub> - 2 log(u<sub>x</sub>) = 0 | 5 | dimension 6 |
| Kamke 1.518 | y'<sup>3</sup> - (-a + y)<sup>2</sup> (-b + y)<sup>2</sup> = 0 | 3 | dimension infinite |
| Kamke 1.520 | -y + y'<sup>3</sup> + y' = 0 | 1 | dimension infinite |
| Kamke 1.521 | x y' - y + y'<sup>3</sup> = 0 | 3 | dimension infinite |
| Kamke 1.522 | y + y'<sup>3</sup> + y' (-x - 5) = 0 | 3 | dimension infinite |
| Kamke 1.523 | -a x y' + x<sup>3</sup> + y'<sup>3</sup> = 0 | 1 | dimension infinite |
| Kamke 1.524 | y<sup>2</sup> - 2 y y' + y'<sup>3</sup> = 0 | 1 | dimension infinite |
| Kamke 1.526 | -x<sup>3</sup> y<sup>3</sup> + y'<sup>3</sup> - y'<sup>2</sup> (x<sup>2</sup> + x y + y<sup>2</sup>) + y' (x<sup>3</sup> y + x<sup>2</sup> y<sup>2</sup> + x y<sup>3</sup>) = 0 | 0 | dimension infinite |
| Kamke 1.527 | -x y<sup>4</sup> y' - y<sup>5</sup> + y'<sup>3</sup> = 0 | 3 | dimension infinite |
| Kamke 1.528 | a b x + a y'<sup>2</sup> + b y + y'<sup>3</sup> = 0 | 1 | dimension infinite |
| Kamke 1.529 | x y'<sup>2</sup> - y + y'<sup>3</sup> = 0 | 0 | dimension infinite |
| Kamke 1.530 | y<sup>2</sup> - y y'<sup>2</sup> + y'<sup>3</sup> = 0 | 1 | dimension infinite |
| Kamke 1.532 | a y'<sup>3</sup> + b y'<sup>2</sup> + c y' - d - y = 0 | 1 | dimension infinite |
| Kamke 1.533 | a + x y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 3 | dimension infinite |
| Kamke 1.534 | 4 x y'<sup>3</sup> - x - 6 y y'<sup>2</sup> + 3 y = 0 | 1 | dimension infinite |
| Kamke 1.536 | b x y'<sup>2</sup> (-a<sup>2</sup> + x<sup>2</sup>) + b x + y'<sup>3</sup> (-a<sup>2</sup> + x<sup>2</sup>) + y' = 0 | 1 | dimension infinite |
| Kamke 1.537 | -2 x<sup>5</sup> y + x<sup>3</sup> y'<sup>3</sup> - 3 x<sup>2</sup> y y'<sup>2</sup> - y<sup>3</sup> + y' (x<sup>6</sup> + 3 x y<sup>2</sup>) = 0 | 3 | dimension infinite |
| Kamke 1.538 | -y y' + 2 (x y' + y)<sup>3</sup> = 0 | 1 | dimension infinite |
| Kamke 1.540 | 2 x y' - x + 2 y y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 1 | dimension infinite |
| Kamke 1.541 | 2 x y' + y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | dimension infinite |
| Kamke 1.542 | 2 x y' + 16 y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | dimension infinite |
| Kamke 1.543 | -x<sup>2</sup> y + x y<sup>2</sup> y'<sup>3</sup> + x y' (x<sup>2</sup> + 1) - y<sup>3</sup> y'<sup>2</sup> = 0 | 3 | dimension infinite |
| Kamke 1.544 | x<sup>7</sup> y<sup>2</sup> y'<sup>3</sup> + 3 x<sup>5</sup> y<sup>4</sup> y' - x<sup>4</sup> y<sup>5</sup> - y'<sup>2</sup> (3 x<sup>6</sup> y<sup>3</sup> - 1) = 0 | 3 | dimension infinite |
| Kamke 1.545 | y'<sup>4</sup> - (-a + y)<sup>3</sup> (-b + y)<sup>2</sup> = 0 | 3 | dimension infinite |
| Kamke 1.546 | 3 x + y'<sup>4</sup> + y'<sup>2</sup> (3 x - 3) - y' (6 y - 3) = 0 | 0 | dimension infinite |
| Kamke 1.547 | -4 y (x y' - 2 y)<sup>2</sup> + y'<sup>4</sup> = 0 | 1 | dimension infinite |
| Kamke 1.548 | y'<sup>6</sup> - (-a + y)<sup>4</sup> (-b + y)<sup>3</sup> = 0 | 3 | dimension infinite |
| Kamke 1.549 | -a<sup>2</sup> + x<sup>2</sup> (y'<sup>2</sup> + 1)<sup>3</sup> = 0 | 1 | dimension infinite |

#### Generators that depend on the parameters lost (21)

SPDE solves the determining equations for generic values of the parameters and loses the generators that depend on them: scalings whose exponents combine the parameters, factors like e<sup>-b m t</sup>.

| entry | equation | dimension | result | note |
|---|---|---|---|---|
| CRC 1, 10.3 | v<sub>t</sub> - v<sub>xx</sub> e<sup>n atan(v<sub>x</sub>)</sup>/(v<sub>x</sub><sup>2</sup> + 1) = 0 | 5 | dimension 4. Missing: (v, n t, -x) | Parameters: n. |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - a u<sup>n</sup> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (x (n - σ - 1), t (2 n - 2), -2 u) | Parameters: a, n, σ. |
| CRC 1, 10.5 | -(u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> - d u + u<sub>t</sub> = 0 | 4 | dimension 2. Missing: (σ x, 0, 2 u), (0, e<sup>-d σ t</sup>, d u e<sup>-d σ t</sup>) | Parameters: d, σ. |
| CRC 1, 10.11 | -(lam u<sub>x</sub> (μ + u)<sup>ν</sup>)<sub>x</sub> + u<sub>t</sub> + u<sub>tt</sub> = 0 | 3 | dimension 2. Missing: (ν x, 0, 2 μ + 2 u) | Parameters: lam, μ, ν. |
| CRC 1, 11.6 | -(u<sup>2 m</sup> u<sub>x</sub>)<sub>x</sub> + u u<sub>x</sub> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (x (2 m - 1), t (2 m - 2), u) | Parameters: m. |
| CRC 1, 12.4 | -(k u<sup>σ</sup> u<sub>x</sub>)<sub>x</sub> + u<sub>tt</sub> = 0 | 4 | dimension 3. Missing: (x, 0, 2 u/σ) | Parameters: k, σ. |
| CRC 1, 12.4 | -(k u<sub>x</sub>/u<sup>4/3</sup>)<sub>x</sub> + u<sub>tt</sub> = 0 | 5 | dimension 3 | Parameters: k. |
| EqWorld 1.2.2 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w + w<sub>t</sub> = 0 | 4 | dimension 2. Missing: (m x, 0, 2 w), (0, e<sup>-b m t</sup>, b w e<sup>-b m t</sup>) | Parameters: a, b, m. |
| EqWorld 1.2.3 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>m + 1</sup> + w<sub>t</sub> = 0 | 3 | dimension 2. Missing: (0, -m t, w) | Parameters: a, b, m. |
| EqWorld 1.2.4 | -(w<sup>m</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - m</sup> + w<sub>t</sub> = 0 | 3 | dimension 2. Missing: (m x, m t, w) | Parameters: a, b, m. |
| EqWorld 1.2.5 | -(w<sup>2 n</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>1 - n</sup> + w<sub>t</sub> = 0 | 3 | dimension 2. Missing: (3 n x, 2 n t, 2 w) | Parameters: a, b, n. |
| EqWorld 2.2.2 | -(w<sup>n</sup> w<sub>x</sub>)<sub>x</sub> a - b w<sup>k</sup> + w<sub>tt</sub> = 0 | 3 | dimension 2. Missing: (x (-k + n + 1), t (1 - k), 2 w) | Parameters: a, b, k, n. |
| Cherniha, King, Kovalenko 10 | -e<sub>2</sub> u + u<sub>t</sub> - u<sub>x</sub><sup>k</sup> u<sub>xx</sub> = 0 | 5 | dimension 3 | Parameters: e<sub>2</sub>, k. |
| AIMS 2026 I-(1) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e u<sup>r</sup> + u<sub>t</sub> = 0 | 3 | dimension 2 | Parameters: e, m, n, r. |
| AIMS 2026 I-(2) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u<sup>m + n</sup> + e<sub>3</sub> u/(m + n - 1) + u<sub>t</sub> = 0 | 3 | dimension 2 | Parameters: e<sub>2</sub>, e<sub>3</sub>, m, n. |
| AIMS 2026 I-(4) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | dimension 2. Missing: (x (m + n - 1)/(n + 1), 0, u), (0, e<sup>e<sub>2</sub> t (-m - n + 1)</sup>, e<sub>2</sub> u e<sup>e<sub>2</sub> t (-m - n + 1)</sup>) | Parameters: e<sub>2</sub>, m, n. |
| AIMS 2026 I-(5) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | dimension 2. Missing: (0, 0, u), (x, t (n + 1), e<sub>2</sub> t u (n + 1)) | Parameters: e<sub>2</sub>, n. |
| AIMS 2026 II-(1) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>q u</sup> + u<sub>t</sub> = 0 | 3 | dimension 2 | Parameters: e<sub>2</sub>, n, q. |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 7 | -δ u<sub>x</sub><sup>2 p</sup> u<sub>xx</sub> e<sup>2 x</sup> - ν u<sub>x</sub><sup>2 p + 1</sup> e<sup>2 x</sup> + u<sub>tt</sub> = 0 | 5 | dimension 4. Rejected: (1, t, 0). Missing: (p, 0, -u), (-1, t, 0) | Parameters: δ, ν, p. |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 15 | -δ u<sub>x</sub><sup>2 p</sup> u<sub>xx</sub> - ε u<sub>x</sub><sup>p + 1/2</sup> + u<sub>tt</sub> - 2 x = 0 | 5 | dimension 4. Rejected: (1, 0, -t<sup>2</sup>). Missing: (1, 0, t<sup>2</sup>), (x (2 p + 1), t, u (2 p + 3)) | Parameters: δ, ε, p. |
| Kamke 6.128 | a y'<sup>2</sup> + b y y' + c y<sup>2</sup> + d y<sup>1 - a</sup> + y y'' = 0 | 8 | dimension 1 | Parameters: a, b, c, d. |

#### Non-polynomial function of a derivative (2)

SPDE splits the determining equations only by polynomial dependence on the derivatives; with F(w<sub>xx</sub>) or e<sup>3 atan(u<sub>x</sub>)</sup> its conditions are wrong.

| entry | equation | dimension | result |
|---|---|---|---|
| CRC 1, 12.4 | w<sub>tt</sub> - F(w<sub>xx</sub>) = 0 | 7 | dimension 0 |
| Gabel et al. 6 | u<sub>t</sub> - u<sub>xx</sub> e<sup>3 atan(u<sub>x</sub>)</sup>/(u<sub>x</sub><sup>2</sup> + 1) = 0 | 5 | dimension 4. Missing: (u, 3 t, -x) |


---

<div style="page-break-before: always"></div>

## MathLie (Mathematica)

Baumann's MathLie 3.0 under Mathematica 15.0, one kernel per entry, 120 s and 8 GB (`benchmarks/mathlie_symmetries.py`; MathLie and its output are not redistributed). MathLie does not take first order ODEs. Where free functions or unsolved conditions remain, the dimension is the rank of the remaining conditions in an elimination Janet basis; where that is not possible (unsolved linear ODEs, special functions) the entry is not compared.

| result | entries |
|---|---|
| same dimension | 523 |
| first order ODE: not supported | 125 |
| timeout | 51 |
| different | 36 |
| remaining conditions not solvable for the comparison | 33 |
| out of memory | 10 |
| unexpected | 8 |

### Entries that differ (36)

#### Generators that depend on the parameters lost (16)

MathLie solves the determining equations for generic values of the parameters and misses the generators whose exponents or factors combine them.

| entry | equation | dimension | result | note |
|---|---|---|---|---|
| CRC 1, 10.3 | v<sub>t</sub> - v<sub>xx</sub> e<sup>n atan(v<sub>x</sub>)</sup>/(v<sub>x</sub><sup>2</sup> + 1) = 0 | 5 | dimension 4. Missing: (v, n t, -x) | Parameters: n. |
| CRC 1, 10.10 | -k0 u<sub>xx</sub> e<sup>m u<sub>x</sub></sup> + τ0 u<sub>tt</sub> + u<sub>t</sub> = 0 | 5 | dimension 4. Missing: (m x, 0, m u + 2 x) | Parameters: k0, m, τ0. |
| CRC 1, 10.10 | -k0 u<sub>x</sub><sup>n</sup> u<sub>xx</sub> + τ0 u<sub>tt</sub> u<sub>x</sub><sup>l</sup> + u<sub>t</sub> = 0 | 4 | dimension 3. Missing: (x (l + n), 2 l t, u (l + n + 2)) | Parameters: k0, l, n, τ0. |
| CRC 1, 10.10 | -k0 u<sub>xx</sub> e<sup>m u<sub>x</sub></sup> + τ0 u<sub>tt</sub> e<sup>l u<sub>x</sub></sup> + u<sub>t</sub> = 0 | 4 | dimension 3. Missing: (x (l + m), 2 l t, u (l + m) + 2 x) | Parameters: k0, l, m, τ0. |
| CRC 1, 12.4 | -k log(w<sub>xx</sub>) + w<sub>tt</sub> = 0 | 8 | dimension 7. Missing: (x, 0, -k t<sup>2</sup>) | Parameters: k. |
| Cherniha, King, Kovalenko 5 | -e<sub>1</sub> u<sup>k + 1</sup> - e<sub>2</sub> u + u<sub>t</sub> - u<sub>x</sub><sup>k</sup> u<sub>xx</sub> = 0 | 3 | dimension 2. Missing: (0, e<sup>-e<sub>2</sub> k t</sup>, e<sub>2</sub> u e<sup>-e<sub>2</sub> k t</sup>) | Parameters: e<sub>1</sub>, e<sub>2</sub>, k. |
| Cherniha, King, Kovalenko 10 | -e<sub>2</sub> u + u<sub>t</sub> - u<sub>x</sub><sup>k</sup> u<sub>xx</sub> = 0 | 5 | dimension 3. Missing: (0, e<sup>-e<sub>2</sub> k t</sup>, e<sub>2</sub> u e<sup>-e<sub>2</sub> k t</sup>), (0, 0, e<sup>e<sub>2</sub> t</sup>) | Parameters: e<sub>2</sub>, k. |
| AIMS 2026 I-(3) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u log(u) + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (0, 0, u e<sup>e<sub>2</sub> t</sup>) | Parameters: e<sub>2</sub>, n. |
| AIMS 2026 I-(5) | -(u<sup>1 - n</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u + u<sub>t</sub> = 0 | 4 | dimension 3. Missing: (x, t (n + 1), e<sub>2</sub> t u (n + 1)) | Parameters: e<sub>2</sub>, n. |
| AIMS 2026 II-(1) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>q u</sup> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (x (1 - q)/(n + 1), -q t, 1) | Parameters: e<sub>2</sub>, n, q. |
| AIMS 2026 II-(2) | -(u<sub>x</sub><sup>n</sup> e<sup>u</sup>)<sub>x</sub> - e<sub>2</sub> e<sup>u</sup> + e<sub>3</sub> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (0, e<sup>e<sub>3</sub> t</sup>, -e<sub>3</sub> e<sup>e<sub>3</sub> t</sup>) | Parameters: e<sub>2</sub>, e<sub>3</sub>, n. |
| Anco et al. | -c (a + u)<sup>q</sup> + κ p u<sub>x</sub><sup>p - 1</sup> u<sub>xx</sub> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (x (p - q), t (1 - q) (p + 1), (a + u) (p + 1)) | Parameters: a, c, κ, p, q. |
| Anco et al. | -c e<sup>q u</sup> + κ p u<sub>x</sub><sup>p - 1</sup> u<sub>xx</sub> + u<sub>t</sub> = 0 | 3 | dimension 2. Missing: (q x, q t (p + 1), -p - 1) | Parameters: c, κ, p, q. |
| BGL 5.3-5: sl(2) + <d<sub>t</sub>, t d<sub>t</sub> + c u d<sub>u</sub>> | -f<sub>0</sub> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>(1 - 6 c)/(4 c)</sup> (-9 u<sub>x</sub> u<sub>xx</sub>/u<sup>7</sup> + 12 u<sub>x</sub><sup>3</sup>/u<sup>8</sup>) - f<sub>0</sub> u<sub>xxx</sub> (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>(1 - 6 c)/(4 c)</sup>/u<sup>6</sup> - g0 u (u<sub>xx</sub>/u<sup>5</sup> - 2 u<sub>x</sub><sup>2</sup>/u<sup>6</sup>)<sup>1/(4 c)</sup> + u<sub>t</sub> = 0 | 5 | dimension 4. Missing: (0, t, c u) | Parameters: c, f<sub>0</sub>, g0. |
| BGL A4.8 | -κ u<sub>x</sub> log(u<sub>x</sub>) - u u<sub>x</sub> + u<sub>t</sub> - u<sub>xxx</sub>/u<sub>x</sub><sup>2</sup> = 0 | 4 | dimension 3. Missing: (x, t, κ) | Parameters: κ. |
| Bihlo, Dos Santos Cardoso-Bihlo, Popovych 14 | -δ u<sub>x</sub><sup>2 p</sup> u<sub>xx</sub> + u<sub>tt</sub> - u<sub>x</sub><sup>q</sup> = 0 | 5 | dimension 4. Missing: (x (2 p - q + 1), t (p - q + 1), u (2 p - q + 2)) | Parameters: δ, p, q. |

#### Determining equations not solved completely (14)

MathLie does not solve the determining equations completely; the generators it returns are correct.

| entry | equation | dimension | result |
|---|---|---|---|
| Schwarz Example 5.33 | x<sup>5</sup> y<sup>6</sup> y' y''' - 3 x<sup>5</sup> y<sup>6</sup> y''<sup>2</sup> + 6 x<sup>5</sup> y<sup>5</sup> y'<sup>2</sup> y'' - 6 x<sup>5</sup> y<sup>4</sup> y'<sup>4</sup> + 3 x<sup>4</sup> y<sup>6</sup> y' y'' - 6 x<sup>4</sup> y<sup>5</sup> y'<sup>3</sup> + 2 x<sup>3</sup> y<sup>4</sup> y'<sup>2</sup> y'' - 4 x<sup>3</sup> y<sup>3</sup> y'<sup>4</sup> - y'<sup>5</sup> = 0 | 3 | dimension 0 |
| Schwarz Example 5.45 | -4 x y'<sup>5</sup> + 4 y + y'<sup>4</sup> (-16 x + 4 y) + y'<sup>3</sup> (-24 x + 16 y) + y'<sup>2</sup> (-16 x + 24 y) + y' (-4 x + 16 y) - y''<sup>2</sup> (3 x + 3 y - 3/2) + y''' (y' + 1) (x + y - 1/2) = 0 | 4 | dimension 0 |
| Hydon Exercise 6.6 | -y'<sup>3</sup> (y<sup>2</sup>/2 + 1) + y''' - 3 y''<sup>2</sup>/(2 y') = 0 | 6 | dimension 5 |
| Bluman-Anco Exercise 3.3-3 | -a y'<sup>k</sup> + y'' = 0 | 3 | dimension 2 |
| CRC 1, 10.10 | -k0 u<sub>x</sub><sup>n</sup> u<sub>xx</sub> + τ0 u<sub>tt</sub> + u<sub>t</sub> = 0 | 5 | dimension 4 |
| Kamke 3.42 | x<sup>2</sup> y''' - x y'' + y' (x<sup>2</sup> + 1) = 0 | 4 | dimension 2 |
| Kamke 3.45 | x<sup>2</sup> y''' + 3 x y + 4 x y'' + y' (x<sup>2</sup> + 2) = 0 | 4 | dimension 3 |
| Kamke 6.93 | -a (x y' - y)<sup>2</sup> + x<sup>3</sup> y'' = 0 | 8 | dimension 3 |
| Kamke 6.170 | a y y' + x y y'' + x y'<sup>2</sup> + f(x) = 0 | 8 | dimension 6 |
| Kamke 6.173 | a y y' + x y y'' + 2 x y'<sup>2</sup> = 0 | 8 | dimension 6 |
| Kamke 6.182 | a (x y' - y)<sup>2</sup> + x<sup>2</sup> y'' (x - y) = 0 | 8 | dimension 3 |
| Kamke 6.184 | a x<sup>2</sup> y y'' + b x<sup>2</sup> y'<sup>2</sup> + c x y y' + d y<sup>2</sup> = 0 | 8 | dimension 2 |
| Kamke 6.206 | -x y' (a<sup>2</sup> - y<sup>2</sup>) + y y'<sup>2</sup> (a<sup>2</sup> - x<sup>2</sup>) + y'' (a<sup>2</sup> - x<sup>2</sup>) (a<sup>2</sup> - y<sup>2</sup>) = 0 | 8 | dimension 2 |
| EqWorld ODE 3.38 | a y'<sup>2</sup> + y<sup>2</sup> g(x) + y y' f(x) + y y'' = 0 | 8 | dimension 4 |

#### Too few conditions, infinite algebra (4)

MathLie leaves too few conditions (ξ, η partly unresolved), so the algebra comes out infinite.

| entry | equation | dimension | result |
|---|---|---|---|
| CRC 1, 10.4 | w<sub>xx</sub> - (σ w<sub>t</sub>)<sup>1/σ</sup> = 0 | 6 | dimension infinite |
| AIMS 2026 I-(2) | -(u<sup>m</sup> u<sub>x</sub><sup>n</sup>)<sub>x</sub> - e<sub>2</sub> u<sup>m + n</sup> + e<sub>3</sub> u/(m + n - 1) + u<sub>t</sub> = 0 | 3 | dimension infinite |
| Kamke 6.133 | y'<sup>2</sup> - y' + y'' (x + y) = 0 | 3 | dimension infinite |
| Kamke 6.228 | y'' (x y' - y) - (y'<sup>2</sup> + 1)<sup>2</sup> = 0 | 2 | dimension infinite |

#### Solutions of the determining equations lost (1)

MathLie's determining equations are right (delierium's Janet basis of them, from DeterminingEquations, has rank 8: the equation is linearizable), but its solver returns ξ = k1, η = 0 only: it loses the solutions of the system with trigonometric coefficients.

| entry | equation | dimension | result |
|---|---|---|---|
| Bluman-Anco Exercise 3.5-3 | -2 y'<sup>2</sup> cot(y) + y'' - sin(y) cos(y) = 0 | 8 | dimension 1 |

#### Indeterminate in the generators (1)

MathLie's generators contain Indeterminate or ComplexInfinity (from its solution in hypergeometric functions), so they are no generators.

| entry | equation | dimension | result |
|---|---|---|---|
| Kamke 3.34 | a x y - b + 2 x y''' + 3 y'' = 0 | 4 | dimension 1. Rejected: (0, Indeterminate) |


---

<div style="page-break-before: always"></div>

## symmgrp2020 (Maxima)

Hereman's symmgrp2020.max (Champagne, Hereman, Winternitz) computes the determining equations; delierium computes their Janet basis, so the comparison is by dimension (`benchmarks/symmgrp_symmetries.py`, 120 s). symmgrp splits only polynomial dependence on the derivatives, so equations with √(u'), e<sup>u<sub>x</sub></sup>, F(u<sub>x</sub>) keep derivatives in its determining equations; those are not compared.

| result | entries |
|---|---|
| same dimension | 676 |
| symmgrp left derivatives of u in its equations | 53 |
| symmgrp timeout | 29 |
| different dimension | 18 |
| Janet basis timeout | 8 |
| read back failed: TokenError: ('unexpected EOF in multi-line statement', (1, 89833)) | 1 |
| symmgrp failed | 1 |


### Entries that differ (18)

#### One branch of y' (18)

The equation is of degree ≥ 2 in y'; symmgrp needs it solved for y' and takes one root, a first order ODE in solved form, whose algebra is infinite. The whole equation has a finite algebra (delierium works with the equation as given).

| entry | equation | dimension | symmgrp |
|---|---|---|---|
| Kamke 1.535 | 8 x y'<sup>3</sup> - 12 y y'<sup>2</sup> + 9 y = 0 | 3 | infinite |
| Kamke 1.518 | y'<sup>3</sup> - (-a + y)<sup>2</sup> (-b + y)<sup>2</sup> = 0 | 3 | infinite |
| Kamke 1.520 | -y + y'<sup>3</sup> + y' = 0 | 1 | infinite |
| Kamke 1.521 | x y' - y + y'<sup>3</sup> = 0 | 3 | infinite |
| Kamke 1.522 | y + y'<sup>3</sup> + y' (-x - 5) = 0 | 3 | infinite |
| Kamke 1.524 | y<sup>2</sup> - 2 y y' + y'<sup>3</sup> = 0 | 1 | infinite |
| Kamke 1.526 | -x<sup>3</sup> y<sup>3</sup> + y'<sup>3</sup> - y'<sup>2</sup> (x<sup>2</sup> + x y + y<sup>2</sup>) + y' (x<sup>3</sup> y + x<sup>2</sup> y<sup>2</sup> + x y<sup>3</sup>) = 0 | 0 | infinite |
| Kamke 1.527 | -x y<sup>4</sup> y' - y<sup>5</sup> + y'<sup>3</sup> = 0 | 3 | infinite |
| Kamke 1.530 | y<sup>2</sup> - y y'<sup>2</sup> + y'<sup>3</sup> = 0 | 1 | infinite |
| Kamke 1.534 | 4 x y'<sup>3</sup> - x - 6 y y'<sup>2</sup> + 3 y = 0 | 1 | infinite |
| Kamke 1.536 | b x y'<sup>2</sup> (-a<sup>2</sup> + x<sup>2</sup>) + b x + y'<sup>3</sup> (-a<sup>2</sup> + x<sup>2</sup>) + y' = 0 | 1 | infinite |
| Kamke 1.540 | 2 x y' - x + 2 y y'<sup>3</sup> - y y'<sup>2</sup> = 0 | 1 | infinite |
| Kamke 1.541 | 2 x y' + y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | infinite |
| Kamke 1.542 | 2 x y' + 16 y<sup>2</sup> y'<sup>3</sup> - y = 0 | 3 | infinite |
| Kamke 1.545 | y'<sup>4</sup> - (-a + y)<sup>3</sup> (-b + y)<sup>2</sup> = 0 | 3 | infinite |
| Kamke 1.547 | -4 y (x y' - 2 y)<sup>2</sup> + y'<sup>4</sup> = 0 | 1 | infinite |
| Kamke 1.548 | y'<sup>6</sup> - (-a + y)<sup>4</sup> (-b + y)<sup>3</sup> = 0 | 3 | infinite |
| Kamke 1.549 | -a<sup>2</sup> + x<sup>2</sup> (y'<sup>2</sup> + 1)<sup>3</sup> = 0 | 1 | infinite |


---

<div style="page-break-before: always"></div>

## BLAD (DifferentialAlgebra)

Boulier's BLAD through DifferentialAlgebra: the Rosenfeld-Groebner decomposition of delierium's determining equations with an orderly ranking; the dimension is the number of parametric derivatives (`benchmarks/blad_crosscheck.py`, 300 s). BLAD takes rational coefficients only.

| result | entries |
|---|---|
| agree | 539 |
| not supported (function) | 174 |
| not supported (power) | 63 |
| RuntimeError: out of memory error | 6 |
| RuntimeError: out of time error | 4 |

### Entries that differ (0)

None.


---

<div style="page-break-before: always"></div>

## Janet bases, Groebner bases, Lie algebras

- **CoCoA 5.4 and Singular 4** (`benchmarks/cocoa_janet.py`): linear systems with constant
  coefficients are polynomial ideals, and the minimal reduced Janet basis of an ideal is
  unique for a term order. 207 systems (7 from the literature, 200 random): delierium's
  Janet basis, CoCoA's `JanetBasis` (JBMill) and Singular's `rJanet` are the same for all
  207.
- **Singular Plural** (`benchmarks/weyl_janet.py`): systems with polynomial coefficients as
  left ideals of the Weyl algebra (the Leibniz rule); each basis reduces the other to zero,
  and the leading derivatives agree. 205 systems: 199 agree, 0 differ, 6 Plural timeouts
  (60 s; delierium needs at most 0.9 s for them).
- **GAP 4** (`benchmarks/gap_lie_algebra.py`): for the 377 complete generator lists of finite
  algebras in the catalogue, delierium's structure constants as
  `LieAlgebraByStructureConstants`: derived and lower central series, solvability,
  nilpotency, center and Killing form agree for all 376 that GAP can take (1 skipped: the
  constants are not rational at the parameter values).


## delierium alone

- Dimension: right for all 786 entries (`pytest -m slow`); all 1790 published generators
  confirmed by its determining equations.
- Generators by its solver (`lie_symmetries(...).generators()`): complete for 525 of the 611
  finite entries, all of them verified.
- `integrate_ode` with the catalogue's generators: 121 of the 176 ODEs solved.
- Not supported: systems of PDEs (#21); Painleve VI and EqWorld ODE 3.11 (the Janet basis
  exceeds 6 GB).


## Reproduction

    benchmarks/tool-comparison/pipeline.sh     # all tools, about 4.5 hours at 3 processes
    benchmarks/tool-comparison/rerun.sh        # the stages repeated after the fix
    uv run python benchmarks/tool-comparison/report.py > BENCHMARK.md

The tools need local installations: REDUCE (with LIEPDE and SPDE; ReLie and DIMSYM from
their authors), Mathematica with MathLie, Maxima with symmgrp2020, CoCoA 5, Singular, GAP;
SymPy, sympy-extras and DifferentialAlgebra come from PyPI (`uv run --with ...`).

