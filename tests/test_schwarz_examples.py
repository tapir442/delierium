"""The Janet bases printed in Schwarz, Algorithmic Lie Theory for Solving
Ordinary Differential Equations (2008), chapter 5.

For each example, the Janet basis of the determining equations of the ODE,
as printed in the book, has to be a Janet basis of what delierium computes
(is_janet_basis_of_ode). This checks more than the dimension in the
symmetry catalogue: the whole basis, coefficients included. X and Y are the
infinitesimals (Schwarz's xi and eta), functions of y (the symbol ys) and x.
Unless stated otherwise the ranking is Schwarz's: eta above xi, grevlex.

Formerly the notebooks notebooks/Schwarz/Schwarz_5.*.ipynb.
"""

import pytest
from sympy import Function, Rational, Symbol, diff, exp

from delierium.infinitesimals import is_janet_basis_of_ode

x = Symbol("x")
y = Function("y")(x)
ys = Symbol("y")
X, Y = Function("X")(ys, x), Function("Y")(ys, x)
d0, d1, d2, d3 = y, diff(y, x), diff(y, x, 2), diff(y, x, 3)

ETA_ABOVE_XI = {"dependent_order": ["Y", "X"]}
ETA_ABOVE_XI_Y_ABOVE_X = {"dependent_order": ["Y", "X"], "independent_order": [ys, x]}

EXAMPLES = [
    (
        "5.2 (Kamke 6.159)",
        4 * d2 * d0 - 3 * d1**2 - 12 * d0**3,
        [diff(X, x) + Y / (2 * ys), diff(X, ys), diff(Y, x), diff(Y, ys) - Y / ys],
        {},
    ),
    (
        "5.9, (5.27)",
        4 * x**2 * d2 - x**4 * d1**2 + 4 * d0,
        [Y + 2 * ys / x * X, diff(X, x) - X / x, diff(X, ys)],
        ETA_ABOVE_XI,
    ),
    (
        "5.10, (5.29)",
        x**4 * d2 - (x * d1) ** 2 - x**3 * d1 + 4 * d0**2,
        [Y - 2 * ys / x * X, diff(X, x) - X / x, diff(X, ys)],
        ETA_ABOVE_XI,
    ),
    (
        # the book prints (x - y')y'' + 4y'^2; Kamke 6.227, whose Janet basis it
        # prints, is (x y' - y)y'' + 4y'^2
        "5.11 (Kamke 6.227)",
        (x * d1 - d0) * d2 + 4 * d1**2,
        [diff(X, x) - X / x, diff(X, ys), diff(Y, x), diff(Y, ys) - Y / ys],
        {},
    ),
    (
        "5.13",
        x**2 * ((x**2) * d0 - 2) ** 2 * d2**2
        - 4 * x**4 * (x**2 * d0 - 2) * d2 * d1**2
        - 8 * x * (x**2 * d0 - 2) * d2 * d1
        + 4 * x**6 * d1**4
        + 24 * x**3 * d1**3
        + 24 * x**2 * d1**2 * d0
        + 16 * d1**2
        + 24 * x * d1 * d0**2
        + 8 * d0**3,
        [
            X.diff(ys),
            Y.diff(x)
            + 2 * ys * X.diff(x) / x
            - (x * x * ys + 2) * Y / (x * (x * x * ys - 2))
            - 4 * ys * ys * X / (x * x * ys - 2),
            Y.diff(ys)
            + X.diff(x)
            - 2 * x * x * Y / (x * x * ys - 2)
            - (3 * x * x * ys + 2) * X / (x * (x * x * ys - 2)),
            X.diff(x, x)
            - 2 * x * ys * X.diff(x) / (x * x * ys - 2)
            + 4 * x * Y / (x * x * ys - 2) ** 2
            + 2 * ys * X * (x * x * ys + 2) / (x * x * ys - 2) ** 2,
        ],
        {"dependent_order": [Y, X], "independent_order": [ys, x]},
    ),
    (
        "5.14",
        d2 * d0 + x * d2 + d1**2 - d1,
        [
            diff(X, ys) + diff(X, x) - (Y + X) / (x + ys),
            diff(Y, x) - diff(X, x) + (Y + X) / (x + ys),
            diff(Y, ys) + diff(X, x) - 2 * (Y + X) / (x + ys),
            diff(X, x, 2) - 3 * diff(X, x) / (x + ys) + 3 * (Y + X) / (x + ys) ** 2,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        "5.15, (5.32)",
        d2 * d1 * d0 * x**6 - 2 * d1**3 * x**6 + 2 * d1**2 * d0 * x**5 + d0**5,
        [
            diff(X, ys),
            diff(Y, x),
            diff(Y, ys) - 3 * diff(X, x) / 2 - 2 * Y / ys + 3 * X / x,
            diff(X, x, 2) - 2 * diff(X, x) / x + 2 * X / x**2,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        "5.15, second equation",
        d2 * d1 + 2 * d2 - d1**4 - 12 * d1**3 - 54 * d1**2 - 108 * d1 - 81,
        [diff(X, x), diff(Y, x) + 6 * diff(X, ys), diff(Y, ys) + 5 * diff(X, ys), diff(X, ys, 2)],
        ETA_ABOVE_XI,
    ),
    (
        "5.16",
        d2 * d0 + d1**2 - d1 * d0 / x - 1 / (2 * x) - 2 * x**2 * exp(-(1 + 2 * d1 * d0) / (2 * x)),
        [
            diff(X, ys),
            diff(Y, x) - x / ys * diff(X, x) - (2 * x + 1) / (2 * x * ys) * X,
            diff(Y, ys) - diff(X, x) + Y / ys - X / x,
            diff(X, x, 2) + diff(X, x) / x - X / x**2,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        "5.17",
        8 * x * d2 * d0**6 - 9 * x**5 * d1**4 - 16 * x * d1**2 * d0**5 + 16 * d1 * d0**6,
        [
            diff(X, ys),
            diff(Y, x),
            diff(Y, ys) - 2 * diff(X, x) / 3 - 2 * Y / ys + 4 * X / (3 * x),
            diff(X, x, 2) - 2 * diff(X, x) / x + 2 * X / x**2,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        "5.18",
        d2 * d1**2 + d2 * d0**2 + d0**3,
        [diff(X, x), diff(X, ys), diff(Y, x), diff(Y, ys) - Y / ys],
        {},
    ),
    (
        # type J3,7 (3.44), p. 151, with a3 = -1/x, c2 = -2/y, c3 = -2/x, d1 = 2/y
        "5.33",
        (
            (
                d3 * d1 * d0**6
                - 3 * (d2**2) * d0**6
                + (6 * d1 * d0 + 2 * d1 / (x**2) + (3 * d0**2) / x) * d2 * d1 * d0**4
                - (d1 / x) ** 5
                - 2 * (3 * d0 + 2 / x**2) * d1**4 * d0**3
                - 6 * (d0**5) * d1**3 / x
            )
            * x**5
        ).expand(),
        [
            diff(X, x) - X / x,
            diff(Y, x),
            diff(Y, ys) - 2 * Y / ys - 2 * X / x,
            diff(X, ys, 2) + 2 * diff(X, ys) / ys,
        ],
        {},
    ),
    (
        "5.45",
        d3 * (d1 + 1) * (d0 + x - Rational(1, 2))
        - 3 * (d2**2) * (d0 + x - Rational(1, 2))
        - 4 * x * d1**5
        + (4 * d1**4) * (d0 - 4 * x)
        + (8 * d1**3) * (2 * d0 - 3 * x)
        + (8 * d1**2) * (3 * d0 - 2 * x)
        + 4 * d1 * (4 * d0 - x)
        + 4 * d0,
        [
            Y + X,
            diff(X, x, ys) - diff(X, x, 2),
            diff(X, ys, 2) - diff(X, x, 2),
            diff(X, x, 3)
            - 4 * ys / (x + ys - Rational(1, 2)) * diff(X, ys)
            - 4 * x / (x + ys - Rational(1, 2)) * diff(X, x)
            + 4 / (x + ys - Rational(1, 2)) * X,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        "5.46",
        d3 * d1 * d0
        + d3 * d0 * d0 / x
        - 3 * d2**2 * d0
        - x * d0 * d2 * d1**2
        + 3 * d2 * d1**2
        - 2 * d2 * d1 * d0 * d0
        - 12 * d2 * d1 * d0 / x
        - d2 * (d0**3) / x
        - (3 * d2 * d0**2) / (x**2)
        + 2 * x * d1**4
        + 3 * d1**3 * d0
        + (15 * d1**3) / x
        - (d1 * d0) ** 2 / x
        - 3 * d1**2 * d0 / x**2
        - (3 / x**2) * d1 * d0**3
        - (9 / x**3) * d1 * d0**2
        - (d0**4) / (x**3)
        - (3 * d0**3) / (x**4),
        [
            diff(Y, x) + ys / x * diff(X, x) + Y / x,
            diff(Y, ys) + ys / x * diff(X, ys) + X / x,
            diff(X, x, ys)
            - x / ys * diff(X, x, 2)
            - diff(X, ys) / x
            + 3 / ys * diff(X, x)
            + Y / ys**2
            - 2 / (x * ys) * X,
            diff(X, ys, 2)
            - x**2 / ys**2 * diff(X, x, 2)
            + 3 / ys * diff(X, ys)
            + 3 * x / ys**2 * diff(X, x)
            + 2 * x / ys**3 * Y
            - X / ys**2,
            diff(X, x, 3)
            - (x * ys + 6) / x * diff(X, x, 2)
            + (x * ys**2 + 3 * ys) / x**3 * diff(X, ys)
            + (3 * x * ys + 15) / x**2 * diff(X, x)
            + (2 * x * ys + 9) / (x**2 * ys) * Y
            - (x * ys + 6) / x**3 * X,
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
    (
        # symmetry class S^3_7: 7 parameters. The former notebook
        # Schwarz_5.48.ipynb had a garbled copy of the equation of 5.46 instead
        "5.48 (Kamke 7.8)",
        d3 * d0**2 - Rational(9, 2) * d2 * d1 * d0 + Rational(15, 4) * d1**3,
        [
            diff(X, ys),
            diff(Y, x, ys) - diff(X, x, 2) - 3 * diff(Y, x) / (2 * ys),
            diff(Y, ys, 2) - 3 * diff(Y, ys) / (2 * ys) + 3 * Y / (2 * ys**2),
            diff(X, x, 3),
            diff(Y, x, 3),
        ],
        ETA_ABOVE_XI_Y_ABOVE_X,
    ),
]


@pytest.mark.parametrize(
    ("ode", "basis", "options"),
    [pytest.param(ode, basis, options, id=name) for name, ode, basis, options in EXAMPLES],
)
def test_printed_janet_basis(ode, basis, options):
    assert is_janet_basis_of_ode(basis, ode, y, x, **options)
