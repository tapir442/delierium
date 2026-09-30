#!/usr/bin/env python3
"""
Created on Tue Jan 18 13:45:11 2022

@author: tapir (rewritten for SymPy by GitHub Copilot Chat Assistant)
"""

from collections.abc import Iterable

from sympy import Derivative, Function, S, diff, symbols

__all__ = [
    "adjoint_frechet_derivative",
    "euler_operator",
    "frechet_derivative",
    "variational_derivative",
]


def is_op_du(expr, u):
    """
    Check if expr is a derivative of u.
    """
    return isinstance(expr, Derivative) and expr.expr.func == u.func


def iter_du_orders(expr, u):
    """
    Yield all derivative orders of u appearing in expr.
    """
    if hasattr(expr, 'args') and expr.args:
        for sub_expr in expr.args:
            if sub_expr == []:
                continue
            if is_op_du(sub_expr, u):
                yield sub_expr.derivative_count
            else:
                yield from iter_du_orders(sub_expr, u)


def variational_derivative(L, u_in):
    """The variational derivative (Euler-Lagrange operator) of L with respect
    to u(x), a function of one variable.

    >>> x = symbols("x")
    >>> u = Function("u")(x)
    >>> variational_derivative(diff(u, x) ** 2 / 2, u)
    -Derivative(u(x), (x, 2))
    >>> variational_derivative(u * diff(u, x, 2), u)
    2*Derivative(u(x), (x, 2))
    """
    if len(u_in.free_symbols) == 1:
        x = next(iter(u_in.free_symbols))
        u = Function(u_in.func.__name__)(x)  # pylint: disable=not-callable
    else:
        raise TypeError("Input function must have exactly one variable.")
    t = symbols('tapir')  # dummy variable
    result = S(0)
    orders = set(iter_du_orders(L, u)).union((0,))
    for c in orders:
        du = diff(u, x, c)
        sign = (-1) ** c
        # Replace all c-th derivatives of u with t, differentiate, then substitute back
        dL_du = L.subs({du: t}).diff(t).subs({t: du})
        result += sign * diff(dL_du, x, c)
    return result


def euler_operator(density, depend, independ):
    r"""Euler operator (variational derivative) of density with respect to
    each of the dependent variables:

        E_u(L) = sum over alpha of (-D)^alpha dL/du_alpha,

    where u_alpha runs over u and all its derivatives occurring in L, and D
    is the total derivative. depend are the undefined functions (u, v, ...),
    independ one independent variable or a sequence of them.

    >>> from sympy import symbols, Function, diff
    >>> t = symbols("t")
    >>> u = Function('u')
    >>> v = Function('v')
    >>> L = u(t) * v(t) + diff(u(t), t) ** 2 + diff(v(t), t) ** 2 - u(t) ** 2 - v(t) ** 2
    >>> euler_operator(L, (u, v), t)
    [-2*u(t) + v(t) - 2*Derivative(u(t), (t, 2)), u(t) - 2*v(t) - 2*Derivative(v(t), (t, 2))]
    >>> L2 = (
    ...     u(t) * v(t)
    ...     + diff(u(t), t) ** 2
    ...     + diff(v(t), t) ** 2
    ...     + 2 * diff(u(t), t) * diff(v(t), t)
    ... )
    >>> euler_operator(L2, (u, v), t)  # doctest: +NORMALIZE_WHITESPACE
    [v(t) - 2*Derivative(u(t), (t, 2)) - 2*Derivative(v(t), (t, 2)),
     u(t) - 2*Derivative(u(t), (t, 2)) - 2*Derivative(v(t), (t, 2))]

    Several independent variables: the wave equation u_tt = u_xx from its
    Lagrangian (u_t**2 - u_x**2)/2:

    >>> x = symbols("x")
    >>> euler_operator((diff(u(x, t), t) ** 2 - diff(u(x, t), x) ** 2) / 2, (u,), (x, t))
    [-Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), (x, 2))]
    """
    variables = tuple(independ) if isinstance(independ, Iterable) else (independ,)
    result = []
    for f in depend:
        u = f(*variables)
        jets = {u} | {d for d in density.atoms(Derivative) if d.expr == u}
        result.append(
            sum((-1) ** _order(jet) * _total_derivative(diff(density, jet), jet) for jet in jets)
        )
    return result


def _order(jet):
    return jet.derivative_count if isinstance(jet, Derivative) else 0


def _total_derivative(expr, jet):
    """D^alpha expr, alpha the multi-index of the derivative jet."""
    return diff(expr, *jet.variable_count) if isinstance(jet, Derivative) else expr


def frechet_derivative(support, dependVar, independVar, testfunction):
    """
    >>> from sympy import symbols, Function, diff, Matrix
    >>> x, t = symbols("x t")
    >>> v = Function("v")
    >>> u = Function("u")
    >>> w1 = Function("w1")
    >>> w2 = Function("w2")
    >>> eqsys = [diff(v(x, t), x) - u(x, t), diff(v(x, t), t) - diff(u(x, t), x) / (u(x, t) ** 2)]
    >>> m = Matrix(frechet_derivative(eqsys, [u, v], [x, t], [w1, w2]))
    >>> m[0, 0]
    -w1(x, t)
    >>> m[0, 1]
    Derivative(w2(x, t), x)
    >>> m[1, 0]
    -Derivative(w1(x, t), x)/u(x, t)**2 + 2*w1(x, t)*Derivative(u(x, t), x)/u(x, t)**3
    >>> m[1, 1]
    Derivative(w2(x, t), t)
    """
    frechet = []
    eps = symbols("eps")
    for eq in support:
        deriv = []
        for i in range(len(support)):
            perturbed = dependVar[i](*independVar) + testfunction[i](*independVar) * eps
            s = eq.replace(dependVar[i], lambda *_, p=perturbed: p)
            deriv.append(diff(s, eps).subs({eps: 0}))
        frechet.append(deriv)
    return frechet


def adjoint_frechet_derivative(support, dependVar, independVar, testfunction):
    # Placeholder: in SymPy, adjoint computation is not built-in
    return frechet_derivative(support, dependVar, independVar, testfunction)


if __name__ == "__main__":
    import doctest

    doctest.testmod()
