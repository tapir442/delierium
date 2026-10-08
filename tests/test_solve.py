"""Tests for delierium.solve: generators by an ansatz (#9)"""

import pytest
from sympy import Function, diff, exp, sqrt, symbols

from delierium import lie_symmetries
from delierium.solve import ansatz_generators, candidate_functions


def complete_and_verified(equation, dependent, independent):
    s = lie_symmetries(equation, dependent, independent)
    generators = s.generators()
    return s.complete(generators) and all(s.verify(generators)), generators


def test_sl3_needs_log():
    """y'' = y'**2/y, linearized by w = log y: sl(3), with y log(y)**2."""
    x = symbols("x")
    y = Function("y")(x)
    ok, generators = complete_and_verified(diff(y, x, 2) - diff(y, x) ** 2 / y, y, x)
    assert ok and len(generators) == 8


def test_baumann_4_3_3():
    """u'' + u'/x - e^u = 0: Baumann's two generators, with log x."""
    x = symbols("x")
    u = Function("u")(x)
    ok, generators = complete_and_verified(diff(u, x, 2) + diff(u, x) / x - exp(u), u, x)
    assert ok and len(generators) == 2


def test_kamke_7_16():
    x = symbols("x")
    y = Function("y")(x)
    eq = 3 * diff(y, x, 2) * diff(y, x, 4) - 5 * diff(y, x, 3) ** 2
    ok, generators = complete_and_verified(eq, y, x)
    assert ok and len(generators) == 6


def test_tang_rotation():
    """u_t = u_xx/(1 + u_x**2): five, among them the rotation (-u, 0, x)."""
    x, t, u_ = symbols("x t u")
    u = Function("u")(x, t)
    ok, generators = complete_and_verified(
        diff(u, t) - diff(u, x, 2) / (1 + diff(u, x) ** 2), u, [x, t]
    )
    assert ok and (-u_, 0, x) in generators


@pytest.mark.slow
def test_cylindrical_kdv_needs_sqrt():
    """u_t + 6 u u_x + u_xxx + u/(2t) = 0: generators with sqrt(t), 1/sqrt(t)."""
    x, t = symbols("x t")
    u = Function("u")(x, t)
    eq = diff(u, t) + 6 * u * diff(u, x) + diff(u, x, 3) + u / (2 * t)
    ok, generators = complete_and_verified(eq, u, [x, t])
    assert ok and any(g[0] == 12 * sqrt(t) for g in generators)


def test_infinite_algebra_gives_a_part():
    """The heat equation: the six point symmetries and polynomial solutions."""
    x, t = symbols("x t")
    u = Function("u")(x, t)
    s = lie_symmetries(diff(u, t) - diff(u, x, 2), u, [x, t])
    generators = s.generators(max_degree=2, functions=[])
    assert not s.complete(generators)
    assert all(s.verify(generators)) and len(generators) >= 6


def test_ansatz_generators_linear_system():
    x, y = symbols("x y")
    X, Y = Function("X")(x, y), Function("Y")(x, y)
    system = [diff(X, y), diff(Y, y), diff(X, x)]
    assert ansatz_generators(system, [X, Y], [x, y], 1) == [(1, 0), (0, 1), (0, x)]


def test_candidate_functions():
    t = symbols("t")
    assert [sqrt(t), 1 / t] in candidate_functions([t])


def test_candidate_functions_order():
    """1/t in the equation (cleared from the determining equations: powers of
    t in some terms only) puts the families of t first (#9)."""
    x, t = symbols("x t")
    u = Function("u")(x, t)
    s = lie_symmetries(diff(u, t) + 6 * u * diff(u, x) + diff(u, x, 3) + u / (2 * t), u, [x, t])
    families = candidate_functions(s.coordinates, s.determining_equations)
    assert [sqrt(t), 1 / t] in families[:3]
    assert families.index([sqrt(t), 1 / t]) < families.index([sqrt(x), 1 / x])


def test_linear_ode_solved_by_dsolve():
    """y''' = 7y' - 6y (Hydon, Exercise 3.5): the reduction leaves an ODE for
    the y-independent part of Y, solved by dsolve: exp(x), exp(2x),
    exp(-3x) (the infinitesimals must not be multiplied by a denominator)."""
    x = symbols("x")
    y = Function("y")(x)
    ok, generators = complete_and_verified(diff(y, x, 3) - 7 * diff(y, x) + 6 * y, y, x)
    assert ok and (0, exp(-3 * x)) in generators


def test_constant_coefficient_is_not_one_term():
    """c * g' = 0 with an unknown constant c does not give g' = 0."""
    from delierium.solve import _one_term  # pylint: disable=import-outside-toplevel

    x, c = symbols("x c")
    g = Function("g")(x)
    assert _one_term(c * diff(g, x), [g], [c]) is None
    assert _one_term(x * diff(g, x), [g], [c]) == (g, {x: 1})


def test_steps_without_ansatz():
    """Blasius is solved by integration and dsolve alone: the generators
    come from the remaining constants."""
    from delierium.solve import (  # pylint: disable=import-outside-toplevel
        integrate_one_term,
        solve_linear_ode,
    )

    x = symbols("x")
    y = Function("y")(x)
    s = lie_symmetries(diff(y, x, 3) + y * diff(y, x, 2), y, x)
    generators = s.generators(steps=[integrate_one_term, solve_linear_ode])
    assert s.complete(generators) and all(s.verify(generators))


def test_own_step():
    """A step of one's own, before the default ones: called, and its
    substitution kept (here X = F(x), as integrate_one_term would)."""
    from delierium.solve import default_steps  # pylint: disable=import-outside-toplevel

    x, y_ = symbols("x y")
    y = Function("y")(x)
    calls = []

    def x_independent_of_y(state):
        calls.append(len(state.system))
        X = next((f for f in state.functions if f.func.__name__ == "X"), None)
        if X is None or y_ not in X.args:
            return False
        new = state.fresh_function([x])
        state.log(f"  own step: {X} = {new}")
        state.substitute(X, new, [new])
        return True

    s = lie_symmetries(diff(y, x, 3) + y * diff(y, x, 2), y, x)
    generators = s.generators(steps=[x_independent_of_y, *default_steps()])
    assert calls and s.complete(generators) and all(s.verify(generators))


def test_step_that_always_changes_stops():
    from delierium.solve import SolverState, run_steps  # pylint: disable=import-outside-toplevel

    x = symbols("x")
    X = Function("X")(x)
    state = SolverState([diff(X, x, 2)], [X], [x])
    run_steps(state, [lambda s: True], max_iterations=5)
    assert state.history[-1] == "stopped after 5 steps"
