"""Open problems: equations delierium cannot handle (yet), kept as tests.

An open problem is a test marked ``too_slow``: skipped unless pytest runs with
``--run-too-slow``, so that it documents the problem without holding up the
test suite. Run it with

    uv run pytest -m too_slow --run-too-slow tests/test_open_problems.py

When it starts passing, the problem is solved: move it to the regular tests.


1. The Boltzmann-reduced nonlinear diffusion equation with arbitrary K(u)
=========================================================================

The equation
-------------

    2 (K(u) u')' + x u' = 0,   i.e.   2 K(u) u'' + 2 K'(u) u'**2 + x u' = 0,

for u = u(x), with K an *arbitrary* function. It is the ordinary differential
equation of the similarity solutions u(x/sqrt(t)) of the nonlinear diffusion
equation u_t = (K(u) u_x)_x, with x standing for the similarity variable
x/sqrt(t) (the Boltzmann transformation). It comes from G. W. Bluman,
G. J. Reid, "New symmetries for ordinary differential equations", the source
of the former notebook notebooks/Bluman/differnt examples.ipynb.

What is asked
-------------

Its Lie point symmetries X d/dx + U d/du, and so the dimension of their Lie
algebra, depend on K: finding them for every K is a *group classification*
problem. For an arbitrary K, the determining equations are linear in X and U
with coefficients in K and its derivatives, and the question is the
dimension of their solution space for a generic K, i.e. K satisfying no
differential equation.

What delierium does
-------------------

The determining equations come out at once, four of them (in the notation
of Lie, K_u = K'(u)):

    2 K U_xx + x U_x
    2 K_u X_u - 2 K X_uu
    4 K**2 U_xu - 2 K**2 X_xx + 4 K K_u U_x + K X + x K X_x - x K_u U
    2 K**2 U_uu - 4 K**2 X_xu + 2 K K_u U_u + 2 K K_uu U + 2 x K X_u - 2 K_u**2 U

The Janet basis of these does not finish: it was still running after 250 s,
and after 35 s its coefficients were polynomials of 4700 terms.

Why
---

The coefficient field (delierium.coefficients) represents K(H) and every
derivative K'(H), K''(H), ... as a generator of its own, H standing for u:
that is correct, K being arbitrary, they are algebraically independent. But
the completion differentiates the equations by H, and every such derivative
brings in the next derivative of K. After 35 s the field had the generators
x, K, K', ..., K^(6), and each new integrability condition makes the
coefficients longer. This is the growth of the coefficients that
fraction-free reduction fixed for fixed generators (Kamke 6.87), now in a
field that keeps growing.

What is known
-------------

For concrete K the Janet basis takes well under a second
(test_concrete_diffusivities below; delierium's results, not from a source):

    K = 1               dimension 8  (the equation is linear)
    K = exp(u)          dimension 1  (x d/dx + 2 d/du)
    K = u**n            dimension 1  (x d/dx + (2/n) u d/du), n symbolic
    K = u**(-2)         dimension 1
    K = 1/(u**2 + 1)    dimension 0

This suggests 0 for a generic K, with more symmetries for the special K a
group classification would find (constants, powers, exponentials, ...);
that is a guess, not a result.

Ways forward
------------

* Classify: branch on the leading coefficients of the integrability
  conditions (the assumed_nonzero factors, differential polynomials in K)
  instead of assuming them nonzero, as a group classification does.
* Order the generators K, K', K'', ... so that the reduction eliminates the
  higher derivatives of K first, keeping the coefficients short.
* Treat K as an unknown of the system: add K to the unknown functions,
  with the equation K_x = 0, and compute the Janet basis of the enlarged
  (then nonlinear) system; this needs differential algebra
  (Rosenfeld-Groebner), not a Janet basis of a linear system.


2. The general second order ODE u'' = F(x, u, u')
=================================================

The equation
-------------

    u'' = F(x, u, u'),   F arbitrary,

from G. Baumann, Symmetry Analysis of Differential Equations with
Mathematica (Springer 2000), p. 138, the source of the former notebook
notebooks/Baumann/Baumann_p138_3.ipynb. The first order cases of the same
section, u' = F(u, x) and u' = f(x) g(u) (pp. 136, 137), work and are in the
catalogue.

What is asked
-------------

The determining equation of its Lie point symmetries X d/dx + U d/du: the
condition pr X(u'' - F) = 0 on u'' = F, a single linear PDE for X and U with
coefficients in F and its partial derivatives, as Baumann derives it.

What delierium does
-------------------

overdetermined_system_ode fails:

    PolynomialError: F(x, u, _Dummy) contains an element of the set of generators.

Why
---

delierium splits the symmetry condition into determining equations: the
condition must hold for every value of the jet variables (here u'), so the
coefficients of its powers vanish separately (split_jet_coefficients, with
Poly in the jet variables). That needs the condition to be polynomial (or
rational, or exponential, or a symbolic power, all handled) in the jet
variables. An arbitrary function F of u' is none of these: nothing can be
split, and Poly refuses the expression.

What is known
-------------

As F is arbitrary in u', the condition cannot be split: the determining
"system" is the one unsplit PDE. For a generic F there are no point
symmetries at all; a second order ODE has at most 8 (u'' = 0), and Lie
classified the possible symmetry algebras. The first order equations of the
same section have infinitely many (catalogue: "Baumann p. 136", "Baumann
p. 137").

Ways forward
------------

* When a jet variable occurs inside an arbitrary function, return the
  unsplit condition as the only determining equation (this test asks for
  that). Its Janet basis is a different matter: the jet variable u' stays
  in it, a variable the ranking does not know.
* As in problem 1, a group classification: split by the dependence of F on
  u' (F polynomial in u' of a given degree, ...) and treat each class.
"""

import pytest
from sympy import Function, Symbol, diff, exp, oo

from delierium import JanetBasis
from delierium.infinitesimals import _linear_system_ode, overdetermined_system_ode

x = Symbol("x")
n = Symbol("n")
u = Function("u")(x)
K = Function("K")


def boltzmann_diffusion(k):
    """2 (k u')' + x u' for the diffusivity k, an expression in u."""
    return 2 * diff(k * diff(u, x), x) + x * diff(u, x)


def dimension(ode):
    system, functions, variables, _ = _linear_system_ode(ode, u, x)
    return JanetBasis(system, functions, variables).type().dimension


@pytest.mark.slow
@pytest.mark.too_slow
def test_arbitrary_diffusivity():
    """Open problem 1: the Janet basis for an arbitrary K(u) does not finish.

    Its dimension is unknown, so the test only asks for a finite one.
    """
    assert dimension(boltzmann_diffusion(K(u))) != oo


@pytest.mark.slow
@pytest.mark.too_slow
def test_general_second_order_ode():
    """Open problem 2: the determining equation of u'' = F(x, u, u'), F
    arbitrary, is the one unsplit symmetry condition."""
    F = Function("F")
    ode = diff(u, x, 2) - F(x, u, diff(u, x))
    assert len(overdetermined_system_ode(ode, [u], [x])) == 1


@pytest.mark.parametrize(
    "k, expected",
    [
        (1, 8),
        (exp(u), 1),
        (u**n, 1),
        (u**-2, 1),
        (1 / (u**2 + 1), 0),
    ],
    ids=["1", "exp(u)", "u**n", "u**(-2)", "1/(u**2 + 1)"],
)
def test_concrete_diffusivities(k, expected):
    """The concrete cases of open problem 1, see the module docstring."""
    assert dimension(boltzmann_diffusion(k)) == expected
