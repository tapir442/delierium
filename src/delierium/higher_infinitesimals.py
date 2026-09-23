"""Determining equations for PDEs of the form u_i = f(x, t, u, u_k, ...).

u = u(x, t) is the dependent variable, u_i the derivative the PDE is solved
for and f may depend on x, t, u and any other derivative of u up to third
order. Derivatives are written as jet variables: u_x, u_t, u_xx, u_xt, u_tt,
u_xxx, u_xxt, u_xtt, u_ttt (x before t).

The symmetry generator is X(x, t, u) d/dx + T(x, t, u) d/dt + U(x, t, u) d/du.
Its prolongation is applied to u_i - f, u_i = f is substituted and the result
is split by the remaining jet variables; every coefficient must vanish.

    $ python -m delierium.higher_infinitesimals u_xxx "u_t*u*u_x"
    $ python -m delierium.higher_infinitesimals u_t u_xx

f must be rational in the jet variables.
"""

import argparse
import itertools
from typing import Any

from sympy import Expr, Function, Mul, Symbol, factor_terms, sympify, together

x, t, u = Symbol("x"), Symbol("t"), Symbol("u")
INDEPENDENT = (x, t)
MAX_ORDER = 3


def _name(index):
    # ('t', 'x', 'x') -> "u_xxt"
    return "u_" + "".join(sorted(index, key="xt".index))


def jet_variables(max_order=MAX_ORDER + 1):
    """{multi-index: jet symbol} for all derivatives of u up to max_order.

    Multi-indices are sorted tuples of variable names, e.g. ('t', 'x').

    >>> jets = jet_variables(2)
    >>> [str(v) for v in jets.values()]
    ['u_x', 'u_t', 'u_xx', 'u_xt', 'u_tt']
    """
    jets = {}
    for order in range(1, max_order + 1):
        for index in itertools.combinations_with_replacement("xt", order):
            key = tuple(sorted(index))
            jets[key] = Symbol(_name(index))
    return jets


JETS = jet_variables()


def _index(var):
    return (str(var),)


def total_derivative(expr, var):
    """D_var expr for an expression in x, t, u and the jet variables.

    >>> u_x = JETS[('x',)]
    >>> total_derivative(u * u_x, x)
    u*u_xx + u_x**2
    """
    result = expr.diff(var) + JETS[_index(var)] * expr.diff(u)
    for index, jet in JETS.items():
        if len(index) > MAX_ORDER:
            continue
        derivative = expr.diff(jet)
        if derivative != 0:
            result += JETS[tuple(sorted(index + _index(var)))] * derivative
    return result


def prolongation(X, T, U, max_order=MAX_ORDER):
    """Prolongation coefficients {multi-index: U^J} up to max_order.

    U^{J,i} = D_i U^J - u_{J,x} D_i X - u_{J,t} D_i T
    """
    xi = {x: X, t: T}
    coefficients: dict[tuple[str, ...], Any] = {(): U}
    for order in range(1, max_order + 1):
        for index in itertools.combinations_with_replacement("tx", order):
            index = tuple(sorted(index))
            if index in coefficients:
                continue
            var = Symbol(index[-1])
            parent = coefficients[index[:-1]]
            coefficient = total_derivative(parent, var)
            for j in INDEPENDENT:
                prev = index[:-1]
                jet = JETS[tuple(sorted(prev + _index(j)))]
                coefficient -= jet * total_derivative(xi[j], var)
            coefficients[index] = coefficient.expand()
    return coefficients


def determining_equations(lhs, rhs, infinitesimals=None):
    """Determining equations of the PDE lhs = rhs, lhs a jet variable.

    Returns a sorted list of expressions that must all vanish.

    Heat equation u_t = u_xx:

    >>> for eq in determining_equations(JETS[('t',)], JETS[('x', 'x')]):
    ...     print(eq)
    Derivative(T(x, t, u), u)
    Derivative(T(x, t, u), x)
    Derivative(T(x, t, u), (u, 2))
    Derivative(X(x, t, u), (u, 2))
    Derivative(X(x, t, u), u) + Derivative(T(x, t, u), u, x)
    Derivative(U(x, t, u), t) - Derivative(U(x, t, u), (x, 2))
    Derivative(U(x, t, u), (u, 2)) - 2*Derivative(X(x, t, u), u, x)
    -Derivative(T(x, t, u), t) + Derivative(T(x, t, u), (x, 2)) + 2*Derivative(X(x, t, u), x)
    Derivative(X(x, t, u), t) - Derivative(X(x, t, u), (x, 2)) + 2*Derivative(U(x, t, u), u, x)
    """
    if infinitesimals is None:
        infinitesimals = [Function(name)(x, t, u) for name in "XTU"]  # pylint: disable=not-callable
    X, T, U = infinitesimals
    lhs_index = next(index for index, jet in JETS.items() if jet == lhs)
    rhs = sympify(rhs)
    if lhs in rhs.free_symbols:
        raise ValueError(f"{lhs} must not appear on the right hand side")
    order = max([len(lhs_index)] + [len(i) for i, v in JETS.items() if v in rhs.free_symbols])
    if order > MAX_ORDER:
        raise ValueError(f"only derivatives up to order {MAX_ORDER} are supported")

    coefficients = prolongation(X, T, U, order)
    # pr X (lhs - rhs)
    applied = coefficients[lhs_index] - (X * rhs.diff(x) + T * rhs.diff(t) + U * rhs.diff(u))
    for index, jet in JETS.items():
        if len(index) <= order and jet in rhs.free_symbols:
            applied -= coefficients[index] * rhs.diff(jet)
    # on solutions of the PDE
    applied = together(applied.subs(lhs, rhs))
    numerator = applied.as_numer_denom()[0].expand()

    jets = [jet for index, jet in JETS.items() if len(index) <= order and jet != lhs]
    poly = numerator.as_poly(*jets)
    if poly is None:
        raise ValueError("the right hand side must be rational in the jet variables")
    equations = {_normalize(c) for c in poly.coeffs()}
    equations.discard(0)
    return sorted(equations, key=lambda e: (len(str(e)), str(e)))


def _normalize(expr):
    """Drop constant factors and powers of u (u is arbitrary), fix the sign."""
    expr = factor_terms(expr.expand())
    if expr.is_Mul:
        expr = Mul(*(f for f in expr.args if not (f.is_number or f.as_base_exp()[0] == u)))
    expr = expr.expand()
    if expr.could_extract_minus_sign():
        expr = -expr
    return expr


def _parse(text: str) -> Expr:
    names = {str(v): v for v in (x, t, u, *JETS.values())}
    return sympify(text, locals=names)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", maxsplit=1)[0])
    parser.add_argument("lhs", nargs="?", default="u_xxx", help="u_i, default u_xxx")
    parser.add_argument("rhs", nargs="?", default="u_t*u*u_x", help="f, default u_t*u*u_x")
    args = parser.parse_args(argv)
    lhs, rhs = _parse(args.lhs), _parse(args.rhs)
    print(f"determining equations of {lhs} = {rhs}:")
    for eq in determining_equations(lhs, rhs):
        print(f"  {eq} = 0")


if __name__ == "__main__":
    main()
