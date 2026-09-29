# ruff: noqa: E501 - data: generated equations do not fit in a line
"""Differential equations with known Lie point symmetries, from the literature.

Every entry gives the equation(s), the variables, the dimension of the Lie
algebra of point symmetries (INFINITE if it is infinite-dimensional, None if
the sources disagree) and, where the source gives them, some or all
generators. A generator is a tuple of its components, in the order of the
independent variables followed by the dependent ones, written in plain
symbols named like the variables: (x**2, x*y) for the ODE y(x) means
x**2 d/dx + x*y d/dy.

Equations are strings in SymPy syntax: the dependent variables are written as
functions of the independent ones, y(x) or u(x, t); every other name is a
constant parameter, assumed to be generic (unconstrained), as in the sources.

Starting point and inspiration has been:

https://github.com/sympy/kamke-test-suite

which has been adopted and brushed up for our purposes.



Sources:

- Arrigo: D. J. Arrigo, Symmetry Analysis of Differential Equations, Wiley 2015.
- Schwarz: F. Schwarz, Algorithmic Lie Theory for Solving Ordinary Differential
  Equations, Chapman & Hall/CRC 2008, Appendix E (symmetry classes of the
  equations of Kamke's collection; the class gives the dimension).
- Kamke: E. Kamke, Differentialgleichungen. Lösungsmethoden und Lösungen,
  equations numbered as in chapters 3, 6 and 7, taken from the SymPy Kamke
  test suite.
- Hydon: P. E. Hydon, Symmetry Methods for Differential Equations, Cambridge
  University Press 2000.
- Baumann: G. Baumann, Symmetry Analysis of Differential Equations with
  Mathematica, Springer 2000.
- classical: standard results found in any textbook (Lie, Ovsiannikov, Olver,
  Ibragimov); the entry says which.
"""

from dataclasses import dataclass

from sympy import Function, Symbol
from sympy.parsing.sympy_parser import parse_expr

INFINITE = "infinite"

ARRIGO = "Arrigo, Symmetry Analysis of Differential Equations (2015)"
SCHWARZ_E = "Schwarz, Algorithmic Lie Theory (2008), Appendix E"
HYDON = "Hydon, Symmetry Methods for Differential Equations (2000)"
BAUMANN = "Baumann, Symmetry Analysis of Differential Equations with Mathematica (2000)"
KHARE_TIMOL = (
    "Khare, Timol, Determining equations for infinitesimal transformation of second and "
    "third-order ODE using algorithm in open-source SageMath"
)
# Arrigo's exercises ask for the symmetries without giving them
ARRIGO_EXERCISE = (
    "the book gives no answer: dimension and generators are delierium's, the generators "
    "checked against the determining equations"
)


@dataclass(frozen=True)
class Entry:
    name: str
    equations: tuple[str, ...]
    independent: tuple[str, ...]
    dependent: tuple[str, ...]
    dimension: int | str | None
    generators: tuple[tuple[str, ...], ...] = ()
    source: str = ""
    note: str = ""

    @property
    def kind(self):
        if len(self.independent) > 1:
            return "pde"
        return "ode" if len(self.equations) == 1 else "odes"

    def variables(self):
        """(independent symbols, dependent functions applied to them)."""
        indep = [Symbol(v) for v in self.independent]
        dep = [Function(f)(*indep) for f in self.dependent]
        return indep, dep

    def parsed_equations(self):
        indep, dep = self.variables()
        names = {str(v): v for v in indep} | {f.func.__name__: f.func for f in dep}
        return [parse_expr(e, local_dict=names) for e in self.equations]

    def parsed_generators(self):
        """The generators as tuples of expressions in plain symbols."""
        names = {v: Symbol(v) for v in self.independent + self.dependent}
        return [tuple(parse_expr(c, local_dict=names) for c in g) for g in self.generators]


def ode(name, equation, dimension, generators=(), source="", note="", x="x", y="y"):
    return Entry(name, (equation,), (x,), (y,), dimension, tuple(generators), source, note)


def odes(name, equations, dependent, dimension, generators=(), source="", note="", t="t"):
    return Entry(
        name, tuple(equations), (t,), tuple(dependent), dimension, tuple(generators), source, note
    )


def pde(name, equation, independent, dimension, generators=(), source="", note="", u="u"):
    return Entry(
        name, (equation,), tuple(independent), (u,), dimension, tuple(generators), source, note
    )


def kamke(number, equation, dimension, generators=(), note=""):
    return ode(f"Kamke {number}", equation, dimension, generators, SCHWARZ_E, note)


CLASSICAL_ODES = [
    ode(
        "y'' = 0",
        "Derivative(y(x), (x, 2))",
        8,
        [
            ("1", "0"),
            ("0", "1"),
            ("x", "0"),
            ("y", "0"),
            ("0", "x"),
            ("0", "y"),
            ("x**2", "x*y"),
            ("x*y", "y**2"),
        ],
        f"{ARRIGO}, Example 2.17",
    ),
    ode(
        "Arrigo 2.18",
        "Derivative(y(x), (x, 2)) + y(x)*Derivative(y(x), x) + x*y(x)**4",
        1,
        [("x", "-y")],
        f"{ARRIGO}, Example 2.18, (2.111)",
    ),
    ode(
        "Arrigo 2.19 (modified Emden equation)",
        "Derivative(y(x), (x, 2)) + 3*y(x)*Derivative(y(x), x) + y(x)**3",
        8,
        [("1", "0"), ("x", "-y"), ("y", "-y**3"), ("x*y", "-x*y**3 + y**2")],
        f"{ARRIGO}, Example 2.19",
    ),
    ode(
        "modified Emden family, k = 1/3",
        "Derivative(y(x), (x, 2)) + y(x)*Derivative(y(x), x)/3 + y(x)**3",
        2,
        [("1", "0"), ("x", "-y")],
        "classical: y'' + k*y*y' + y**3 has d/dx and x d/dx - y d/dy for every k",
        note="the dimension is delierium's, not from a source; "
        "k = 3 is linearizable (8, Arrigo 2.19)",
    ),
    ode(
        "Schwarz Example 5.46",
        "-x*y(x)*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) "
        "+ 2*x*Derivative(y(x), x)**4 "
        "- 2*y(x)**2*Derivative(y(x), x)*Derivative(y(x), (x, 2)) "
        "+ 3*y(x)*Derivative(y(x), x)**3 + y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 3)) "
        "- 3*y(x)*Derivative(y(x), (x, 2))**2 "
        "+ 3*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) "
        "- y(x)**3*Derivative(y(x), (x, 2))/x - y(x)**2*Derivative(y(x), x)**2/x "
        "+ y(x)**2*Derivative(y(x), (x, 3))/x "
        "- 12*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2))/x "
        "+ 15*Derivative(y(x), x)**3/x - 3*y(x)**3*Derivative(y(x), x)/x**2 "
        "- 3*y(x)**2*Derivative(y(x), (x, 2))/x**2 - 3*y(x)*Derivative(y(x), x)**2/x**2 "
        "- y(x)**4/x**3 - 9*y(x)**2*Derivative(y(x), x)/x**3 - 3*y(x)**3/x**4",
        5,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.46",
        note="type J^(2,2)_{5,3} Janet basis, symmetry class S^3_{5,1}; canonical form "
        "v''' - v'' = 0 (Example 6.35), general solution in Example 7.36",
    ),
    ode(
        "Schwarz Example 5.13",
        "4*x**6*Derivative(y(x), x)**4 - 4*x**4*(x**2*y(x) - 2)*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) + 24*x**3*Derivative(y(x), x)**3 + x**2*(x**2*y(x) - 2)**2*Derivative(y(x), (x, 2))**2 + 24*x**2*y(x)*Derivative(y(x), x)**2 - 8*x*(x**2*y(x) - 2)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) + 24*x*y(x)**2*Derivative(y(x), x) + 8*y(x)**3 + 16*Derivative(y(x), x)**2",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.13",
        note="type J3,6 Janet basis, symmetry class S3,1",
    ),
    ode(
        "Schwarz Example 5.15, (5.32)",
        "x**6*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) - 2*x**6*Derivative(y(x), x)**3 + 2*x**5*y(x)*Derivative(y(x), x)**2 + y(x)**5",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.15",
        note="type J3,6 Janet basis, symmetry class S3,3",
    ),
    ode(
        "Schwarz Example 5.15, second equation",
        "-Derivative(y(x), x)**4 - 12*Derivative(y(x), x)**3 - 54*Derivative(y(x), x)**2 + Derivative(y(x), x)*Derivative(y(x), (x, 2)) - 108*Derivative(y(x), x) + 2*Derivative(y(x), (x, 2)) - 81",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.15",
        note="type J3,7 Janet basis, symmetry class S3,3",
    ),
    ode(
        "Schwarz Example 5.16, (5.33)",
        "-2*x**2*exp((-2*y(x)*Derivative(y(x), x) - 1)/(2*x)) + y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 - y(x)*Derivative(y(x), x)/x - 1/(2*x)",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.16",
        note="type J3,6 Janet basis, symmetry class S3,3; an exponential in y'",
    ),
    ode(
        "Schwarz Example 5.17",
        "-9*x**5*Derivative(y(x), x)**4 + 8*x*y(x)**6*Derivative(y(x), (x, 2)) - 16*x*y(x)**5*Derivative(y(x), x)**2 + 16*y(x)**6*Derivative(y(x), x)",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.17",
        note="all absolute invariants constant: a three-parameter group",
    ),
    ode(
        "Schwarz Example 5.33",
        "x**5*y(x)**6*Derivative(y(x), x)*Derivative(y(x), (x, 3)) - 3*x**5*y(x)**6*Derivative(y(x), (x, 2))**2 + 6*x**5*y(x)**5*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) - 6*x**5*y(x)**4*Derivative(y(x), x)**4 + 3*x**4*y(x)**6*Derivative(y(x), x)*Derivative(y(x), (x, 2)) - 6*x**4*y(x)**5*Derivative(y(x), x)**3 + 2*x**3*y(x)**4*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) - 4*x**3*y(x)**3*Derivative(y(x), x)**4 - Derivative(y(x), x)**5",
        3,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.33",
        note="type J3,7 Janet basis, symmetry class S3,2",
    ),
    ode(
        "Schwarz Example 5.43",
        "-8*x*y(x)**2*Derivative(y(x), x)/(2*x - 1) + y(x)**2*Derivative(y(x), (x, 3)) - 6*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) + 6*Derivative(y(x), x)**3 + 3*y(x)**2*Derivative(y(x), (x, 2))/x - 6*y(x)*Derivative(y(x), x)**2/x",
        4,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.43",
        note="type J4,2 Janet basis, symmetry class S4,5",
    ),
    ode(
        "Schwarz Example 5.45",
        "-4*x*Derivative(y(x), x)**5 + 4*(-4*x + y(x))*Derivative(y(x), x)**4 + 8*(-3*x + 2*y(x))*Derivative(y(x), x)**3 + 8*(-2*x + 3*y(x))*Derivative(y(x), x)**2 + 4*(-x + 4*y(x))*Derivative(y(x), x) + (Derivative(y(x), x) + 1)*(x + y(x) - 1/2)*Derivative(y(x), (x, 3)) - 3*(x + y(x) - 1/2)*Derivative(y(x), (x, 2))**2 + 4*y(x)",
        4,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.45",
        note="type J4,17 Janet basis, symmetry class S4,5",
    ),
    ode(
        "Schwarz Example 5.49",
        "y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 3)) - 3*y(x)*Derivative(y(x), (x, 2))**2 + 3*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) + y(x)**2*Derivative(y(x), (x, 3))/x - 12*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2))/x + 15*Derivative(y(x), x)**3/x - 3*y(x)**2*Derivative(y(x), (x, 2))/x**2 - 3*y(x)*Derivative(y(x), x)**2/x**2 - 9*y(x)**2*Derivative(y(x), x)/x**3 - 3*y(x)**3/x**4",
        7,
        source="Schwarz, Algorithmic Lie Theory (2008), Example 5.49",
        note="symmetry class S^3_7; the book prints no Janet basis",
    ),
    ode(
        "Hydon Example 3.3",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2/y(x) + y(x)**2",
        2,
        [("1", "0"), ("x", "-2*y")],
        f"{HYDON}, Example 3.3",
    ),
    ode(
        "Hydon Example 4.1",
        "Derivative(y(x), (x, 2)) - (3/x - 2*x)*Derivative(y(x), x) - 4*y(x)",
        8,
        [("0", "y")],
        f"{HYDON}, Example 4.1",
        note="linear: like every linear second order ODE, 8 symmetries; y d/dy is one of them",
    ),
    ode(
        "Blasius equation",
        "Derivative(y(x), (x, 3)) + y(x)*Derivative(y(x), (x, 2))",
        2,
        [("1", "0"), ("x", "-y")],
        f"{ARRIGO}, Example 2.20, (2.144)",
    ),
    ode(
        "y''' = 0",
        "Derivative(y(x), (x, 3))",
        7,
        [
            ("1", "0"),
            ("0", "1"),
            ("x", "0"),
            ("0", "x"),
            ("0", "x**2"),
            ("0", "y"),
            ("x**2", "2*x*y"),
        ],
        "classical (Lie): y^(n) = 0, n >= 3, has n + 4 point symmetries",
    ),
    ode(
        "y''' = 1",
        "Derivative(y(x), (x, 3)) - 1",
        7,
        [("1", "0"), ("0", "1"), ("x", "3*y")],
        "Kumar, Solution of Third Order Non-Homogeneous Ordinary Differential Equations "
        "by Lie Symmetry Method",
        note="y -> y - x**3/6 maps it onto y''' = 0, so 7 symmetries as there",
    ),
    ode(
        "y'''' = 0",
        "Derivative(y(x), (x, 4))",
        8,
        [
            ("1", "0"),
            ("0", "1"),
            ("x", "0"),
            ("0", "x"),
            ("0", "x**2"),
            ("0", "x**3"),
            ("0", "y"),
            ("x**2", "3*x*y"),
        ],
        "classical (Lie): y^(n) = 0, n >= 3, has n + 4 point symmetries",
    ),
    ode(
        "harmonic oscillator",
        "Derivative(y(x), (x, 2)) + y(x)",
        8,
        [("1", "0"), ("0", "y"), ("0", "sin(x)"), ("0", "cos(x)")],
        "classical: every linear second order ODE has 8 point symmetries",
    ),
    ode(
        "Ermakov-Pinney equation",
        "Derivative(y(x), (x, 2)) - y(x)**(-3)",
        3,
        [("1", "0"), ("2*x", "y"), ("x**2", "x*y")],
        "classical (sl(2))",
    ),
    ode(
        "y'' = exp(y)",
        "Derivative(y(x), (x, 2)) - exp(y(x))",
        2,
        [("1", "0"), ("x", "-2")],
        "classical",
    ),
    ode(
        "Chazy equation",
        "Derivative(y(x), (x, 3)) - 2*y(x)*Derivative(y(x), (x, 2)) + 3*Derivative(y(x), x)**2",
        3,
        [("1", "0"), ("x", "-y"), ("x**2", "-2*x*y - 6")],
        "classical (sl(2)); Clarkson and Olver, J. Diff. Eqns. 124 (1996), "
        f"cited in {ARRIGO}, Exercises 2.6, 2",
    ),
    ode(
        "Arrigo Exercises 2.6, 1 (i)",
        "Derivative(y(x), (x, 3)) + y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2",
        2,
        [("1", "0"), ("x", "-y")],
        f"{ARRIGO}, Exercises 2.6, 1 (i)",
        note=ARRIGO_EXERCISE,
    ),
    ode(
        "Arrigo Exercises 2.6, 1 (ii)",
        "Derivative(y(x), (x, 3)) + 4*y(x)*Derivative(y(x), (x, 2)) + 3*Derivative(y(x), x)**2"
        " + 6*y(x)**2*Derivative(y(x), x) + y(x)**4",
        3,
        [("1", "0"), ("x", "-y"), ("x**2", "3 - 2*x*y")],
        f"{ARRIGO}, Exercises 2.6, 1 (ii)",
        note=ARRIGO_EXERCISE,
    ),
    ode(
        "Arrigo Exercises 2.6, 1 (iii)",
        "Derivative(y(x), (x, 3)) - y(x)**(-3)",
        2,
        [("1", "0"), ("4*x", "3*y")],
        f"{ARRIGO}, Exercises 2.6, 1 (iii)",
        note=ARRIGO_EXERCISE,
    ),
    ode(
        "Arrigo Exercises 2.6, 3",
        "Derivative(y(x)*Derivative(y(x), x)*Derivative(y(x)/Derivative(y(x), x), (x, 2)), x)",
        3,
        [("1", "0"), ("x", "0"), ("0", "y")],
        f"{ARRIGO}, Exercises 2.6, 3 (from the symmetries of the wave equation, Bluman and Kumei)",
        note=ARRIGO_EXERCISE,
    ),
    ode(
        "pendulum",
        "Derivative(y(x), (x, 2)) + sin(y(x))",
        1,
        [("1", "0")],
        "classical",
    ),
    ode(
        "Lane-Emden equation, n = 5",
        "Derivative(y(x), (x, 2)) + 2*Derivative(y(x), x)/x + y(x)**5",
        1,
        [("x", "-y/2")],
        "classical: the Lane-Emden equation has the scaling symmetry x d/dx - 2/(n-1) y d/dy",
        note="this entry first claimed a second symmetry x**2 d/dx - x*y d/dy for n = 5 (written "
        "from memory); it is none (the condition leaves -2*y' - 2*y/x), and delierium and an "
        "independent polynomial ansatz both find only the scaling. n = 5 is special for its "
        "explicit solution (1 + x**2/3)**(-1/2) and first integral, not its point symmetries",
    ),
]

FIRST_ORDER_ODES = [
    ode(
        "Arrigo 2.1",
        "Derivative(y(x), x) - y(x)**2 + y(x)/x + 1/x**2",
        INFINITE,
        [("x", "-y")],
        f"{ARRIGO}, Example 2.1, (2.23)",
        "every first order ODE has infinitely many point symmetries",
    ),
    ode(
        "Arrigo 2.2",
        "Derivative(y(x), x) - y(x)/x - x**2/(x + y(x))",
        INFINITE,
        [("1", "y/x")],
        f"{ARRIGO}, Examples 2.2 and 2.9",
    ),
    ode(
        "Baumann p. 136: u' = F(u, x)",
        "Derivative(u(x), x) - F(u(x), x)",
        INFINITE,
        [],
        f"{BAUMANN}, Example 1, p. 136",
        note="a general first order ODE, F arbitrary: every first order ODE has infinitely "
        "many point symmetries",
        y="u",
    ),
    ode(
        "Baumann p. 137: u' = f(x) g(u)",
        "Derivative(u(x), x) - f(x)*g(u(x))",
        INFINITE,
        [("0", "g(u)"), ("1/f(x)", "0")],
        f"{BAUMANN}, Example 2, p. 137",
        note="separable, f and g arbitrary; the two generators hold for every f and g",
        y="u",
    ),
    ode(
        "Khare-Timol Example 3: y'' = F(x)/y**2",
        "Derivative(y(x), (x, 2)) - F(x)/y(x)**2",
        0,
        [],
        f"{KHARE_TIMOL}, Example 3",
        note="F arbitrary: no symmetries for a generic F (delierium's result). The Janet basis "
        "assumes differential polynomials in F nonzero (F F'' - 2 F'**2, 2 F F'' - 3 F'**2, "
        "...); where one vanishes there may be more, e.g. F = 1: 2, F = x: 1",
    ),
]

ODE_SYSTEMS = [
    odes(
        "Arrigo 2.21",
        ["Derivative(x(t), t) - 2*x(t)*y(t)", "Derivative(y(t), t) - x(t)**2 - y(t)**2"],
        ("x", "y"),
        INFINITE,
        [("1", "0", "0"), ("t", "-x", "-y")],
        f"{ARRIGO}, Example 2.21, (2.163)",
        "a first order system has infinitely many point symmetries; the book's determining"
        " equation (2.155b) has +(x**2 + y**2)**2*T_y, the correct sign is minus",
    ),
    odes(
        "Arrigo 2.22",
        [
            "Derivative(x(t), (t, 2)) - x(t)/(x(t)**2 + y(t)**2)**2",
            "Derivative(y(t), (t, 2)) - y(t)/(x(t)**2 + y(t)**2)**2",
        ],
        ("x", "y"),
        4,
        [("1", "0", "0"), ("2*t", "x", "y"), ("0", "y", "-x"), ("t**2", "t*x", "t*y")],
        f"{ARRIGO}, Example 2.22, (2.185), (2.186)",
    ),
    odes(
        "free particle in the plane",
        ["Derivative(x(t), (t, 2))", "Derivative(y(t), (t, 2))"],
        ("x", "y"),
        15,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("t", "0", "0"),
            ("0", "t", "0"),
            ("0", "0", "t"),
            ("0", "x", "0"),
            ("0", "y", "0"),
            ("0", "0", "x"),
            ("0", "0", "y"),
            ("x", "0", "0"),
            ("y", "0", "0"),
            ("t**2", "t*x", "t*y"),
            ("t*x", "x**2", "x*y"),
            ("t*y", "x*y", "y**2"),
        ],
        "classical: x'' = 0 in n dimensions has sl(n + 2), here dimension 15",
    ),
    odes(
        "isotropic harmonic oscillator in the plane",
        ["Derivative(x(t), (t, 2)) + x(t)", "Derivative(y(t), (t, 2)) + y(t)"],
        ("x", "y"),
        15,
        [("1", "0", "0"), ("0", "y", "-x"), ("0", "x", "y"), ("0", "sin(t)", "0")],
        "classical: point-equivalent to the free particle",
    ),
    odes(
        "Kepler problem in the plane",
        [
            "Derivative(x(t), (t, 2)) + x(t)/(x(t)**2 + y(t)**2)**Rational(3, 2)",
            "Derivative(y(t), (t, 2)) + y(t)/(x(t)**2 + y(t)**2)**Rational(3, 2)",
        ],
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "-y", "x"), ("3*t", "2*x", "2*y")],
        "classical: time translation, rotation, and the scaling of Kepler's third law",
    ),
]

PDES = [
    pde(
        "heat equation",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "u"),
            ("x", "2*t", "0"),
            ("2*t", "0", "-x*u"),
            ("4*t*x", "4*t**2", "-(x**2 + 2*t)*u"),
        ],
        f"{ARRIGO}, Section 3.2.1",
        "6 generators plus the superposition of solutions",
    ),
    pde(
        "u_t = u_x**2",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**2",
        ("x", "t"),
        10,
        [
            ("-4*x*u", "x**2", "-4*u**2"),
            ("-4*t*u + x**2", "2*t*x", "2*x*u"),
            ("-2*u", "x", "0"),
            ("4*t*x", "4*t**2", "-x**2"),
            ("0", "t", "-u"),
            ("0", "1", "0"),
            ("x", "0", "2*u"),
            ("2*t", "0", "-x"),
            ("1", "0", "0"),
            ("0", "0", "1"),
        ],
        f"{ARRIGO}, Example 3.1, (3.16)",
    ),
    pde(
        "Laplace equation",
        "Derivative(u(x, y), (x, 2)) + Derivative(u(x, y), (y, 2))",
        ("x", "y"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "y", "0"), ("y", "-x", "0"), ("0", "0", "u")],
        f"{ARRIGO}, Section 3.2.2",
        "conformal maps plus the superposition of solutions",
    ),
    pde(
        "Burgers equation",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("x", "2*t", "-u"),
            ("t*x", "t**2", "-t*u + x"),
            ("1", "0", "0"),
            ("t", "0", "1"),
        ],
        f"{ARRIGO}, Section 3.2.3, (3.49), (3.53)",
    ),
    pde(
        "potential Burgers equation",
        "Derivative(u(x, t), t) + Derivative(u(x, t), x)**2/2 - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1"), ("x", "2*t", "0")],
        f"{ARRIGO}, Section 3.2.3, (3.50)",
        "linearizable to the heat equation by u = -2 log(w)",
    ),
    pde(
        "heat equation with exponential source",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - exp(-u(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "2")],
        f"{ARRIGO}, Section 3.2.4, (3.71), with F(u) = exp(-u)",
    ),
    pde(
        "heat equation with power source",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - u(x, t)**2",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "-2*u")],
        f"{ARRIGO}, Section 3.2.4, (3.76), with F(u) = u**2",
    ),
    pde(
        "heat equation with logarithmic source",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - u(x, t)*log(u(x, t))",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("exp(t)", "0", "-x*exp(t)*u/2"),
            ("0", "0", "exp(t)*u"),
        ],
        f"{ARRIGO}, Section 3.2.4, (3.74), with F(u) = u log(u)",
    ),
    pde(
        "Fisher equation",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - u(x, t)*(1 - u(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{ARRIGO}, Section 3.2.4, (3.68) (arbitrary source), Exercises 3.2, 5",
    ),
    pde(
        "u_t = u_xx - 2u**3",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + 2*u(x, t)**3",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "-u")],
        f"{ARRIGO}, Example 4.2",
    ),
    pde(
        "Korteweg-de Vries equation",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        4,
        [("0", "1", "0"), ("x", "3*t", "-2*u"), ("1", "0", "0"), ("t", "0", "1")],
        f"{ARRIGO}, Example 3.17, (3.89)",
    ),
    pde(
        "Boussinesq equation",
        "Derivative(u(x, t), (t, 2)) + u(x, t)*Derivative(u(x, t), (x, 2))"
        " + Derivative(u(x, t), x)**2 + Derivative(u(x, t), (x, 4))",
        ("x", "t"),
        3,
        [("x", "2*t", "-2*u"), ("0", "1", "0"), ("1", "0", "0")],
        f"{ARRIGO}, Example 3.18, (3.94)",
    ),
    pde(
        "nonlinear diffusion in the plane",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t)*Derivative(u(x, y, t), x), x)"
        " - Derivative(u(x, y, t)*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        6,
        [
            ("0", "0", "t", "-u"),
            ("0", "0", "1", "0"),
            ("x", "y", "0", "2*u"),
            ("y", "-x", "0", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
        ],
        f"{ARRIGO}, Example 3.21, (3.143)",
    ),
    pde(
        "Harry Dym equation",
        "Derivative(u(x, t), t) - u(x, t)**3*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "0", "u"),
            ("x**2", "0", "2*x*u"),
            ("0", "3*t", "-u"),
        ],
        f"{BAUMANN}, p. 226",
    ),
    pde(
        "modified KdV equation",
        "Derivative(u(x, t), t) + u(x, t)**2*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "3*t", "-u")],
        "classical",
    ),
    pde(
        "nonlinear diffusion u_t = (u**2 u_x)_x",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**2*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "0"), ("x", "0", "u")],
        "classical (Ovsiannikov): u_t = (u**n u_x)_x has 4 point symmetries for generic n",
    ),
    pde(
        "nonlinear diffusion u_t = (u**(-4/3) u_x)_x",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**Rational(-4, 3)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "2*t", "0"),
            ("-4*x", "0", "6*u"),
            ("x**2", "0", "-3*x*u"),
        ],
        "classical (Ovsiannikov): the exponent -4/3 adds a projective symmetry",
    ),
    pde(
        "Kuramoto-Sivashinsky equation",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x)"
        " + Derivative(u(x, t), (x, 2)) + Derivative(u(x, t), (x, 4))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "0", "1")],
        "classical",
    ),
    pde(
        "Huxley equation u_t = u_xx + 2u**2 (1 - u)",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - 2*u(x, t)**2*(1 - u(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        "Dimas, Tsoubelis; classical: u_t = u_xx + f(u) with a cubic f has only the translations",
    ),
    pde(
        "sine-Gordon equation",
        "Derivative(u(x, t), x, t) - sin(u(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "-t", "0")],
        "classical (light-cone coordinates)",
    ),
    pde(
        "Liouville equation",
        "Derivative(u(x, t), x, t) - exp(u(x, t))",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "0", "-1"), ("x**2", "0", "-2*x")],
        "classical: f(x) d/dx - f'(x) d/du and g(t) d/dt - g'(t) d/du",
    ),
    pde(
        "wave equation in light-cone coordinates",
        "Derivative(u(x, t), x, t)",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x**2", "0", "0"),
            ("0", "t**3", "0"),
            ("0", "0", "u"),
            ("0", "0", "x**2 + sin(t)"),
        ],
        "classical: f(x) d/dx, g(t) d/dt, u d/du and (h(x) + k(t)) d/du; the linear partner "
        "of the Liouville equation under a Baecklund transformation",
    ),
    pde(
        "Boyer-Finley equation",
        "Derivative(u(x, y, z), (x, 2)) + Derivative(u(x, y, z), (y, 2))"
        " + Derivative(exp(u(x, y, z)), (z, 2))",
        ("x", "y", "z"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "z", "2"),
            ("y", "-x", "0", "0"),
            ("x", "y", "0", "-2"),
            ("x**2 - y**2", "2*x*y", "0", "-4*x"),
        ],
        "Boyer, Finley, J. Math. Phys. 23 (1982) 1126 (self-dual Einstein spaces, SU(oo) Toda):"
        " a(x, y) d/dx + b(x, y) d/dy - 2 a_x d/du for a + i b holomorphic,"
        " plus d/dz and z d/dz + 2 d/du",
    ),
    pde(
        "nonlinear Klein-Gordon equation",
        "Derivative(u(x, t), (t, 2)) - Derivative(u(x, t), (x, 2)) - u(x, t)**3",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "x", "0"), ("x", "t", "-u")],
        "classical: Poincare group and scaling",
    ),
    pde(
        "Benjamin-Bona-Mahony equation",
        "Derivative(u(x, t), t) + Derivative(u(x, t), x) + u(x, t)*Derivative(u(x, t), x)"
        " - Derivative(u(x, t), (x, 2), t)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "t", "-1 - u")],
        "classical",
    ),
    pde(
        "minimal surface equation",
        "(1 + Derivative(u(x, y), y)**2)*Derivative(u(x, y), (x, 2))"
        " - 2*Derivative(u(x, y), x)*Derivative(u(x, y), y)*Derivative(u(x, y), x, y)"
        " + (1 + Derivative(u(x, y), x)**2)*Derivative(u(x, y), (y, 2))",
        ("x", "y"),
        7,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("y", "-x", "0"),
            ("u", "0", "-x"),
            ("0", "u", "-y"),
            ("x", "y", "u"),
        ],
        f"classical: Euclidean motions and scaling of R^3; {ARRIGO}, Exercises 3.2, 7",
    ),
    pde(
        "heat equation in the plane",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t), (x, 2))"
        " - Derivative(u(x, y, t), (y, 2))",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("y", "-x", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("2*t", "0", "0", "-x*u"),
        ],
        "classical: 9 generators plus the superposition of solutions",
    ),
]

# Kamke's equations with their symmetry class from Schwarz, Appendix E;
# generated from the SymPy Kamke test suite, see the module docstring.
KAMKE = [
    # BEGIN KAMKE
    kamke('3.1', '-lambda_*y(x) + Derivative(y(x), (x, 3))', dimension=5),
    kamke('3.2', 'a*x**3*y(x) - b*x + Derivative(y(x), (x, 3))', dimension=4),
    kamke('3.4', '-4*y(x) + 3*Derivative(y(x), x) + Derivative(y(x), (x, 3))', dimension=5),
    kamke('3.6', '2*a*x*Derivative(y(x), x) + a*y(x) + Derivative(y(x), (x, 3))', dimension=7),
    kamke(
        '3.7',
        '-a*b*y(x) - x**2*Derivative(y(x), (x, 2)) + x*(a + b - 1)*Derivative(y(x), x) + Derivative(y(x), (x, 3))',
        dimension=4,
    ),
    kamke(
        '3.16',
        '10*y(x) - 3*Derivative(y(x), x) - 2*Derivative(y(x), (x, 2)) + Derivative(y(x), (x, 3))',
        dimension=5,
    ),
    kamke(
        '3.21',
        'a**3*x**3*y(x) + 3*a**2*x**2*Derivative(y(x), x) + 3*a*x*Derivative(y(x), (x, 2)) + Derivative(y(x), (x, 3))',
        dimension=7,
    ),
    kamke(
        '3.27',
        '-3*y(x) + 18*exp(x) - 11*Derivative(y(x), x) - 8*Derivative(y(x), (x, 2)) + 4*Derivative(y(x), (x, 3))',
        dimension=5,
    ),
    kamke('3.29', 'x*y(x) + x*Derivative(y(x), (x, 3)) + 3*Derivative(y(x), (x, 2))', dimension=5),
    kamke(
        '3.30',
        '-a*x**2*y(x) + x*Derivative(y(x), (x, 3)) + 3*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke(
        '3.31',
        '-a*y(x) - x*Derivative(y(x), x) + x*Derivative(y(x), (x, 3)) + (a + b)*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke(
        '3.32',
        'x*Derivative(y(x), (x, 3)) - (2*v + x)*Derivative(y(x), (x, 2)) + (x - 1)*y(x) - (-2*v + x - 1)*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.33',
        '4*x*Derivative(y(x), x) + x*Derivative(y(x), (x, 3)) + (x**2 - 3)*Derivative(y(x), (x, 2)) + 2*y(x)',
        dimension=4,
        note='inhomogeneous term f(x) set to 0, as in Schwarz',
    ),
    kamke(
        '3.34',
        'a*x*y(x) - b + 2*x*Derivative(y(x), (x, 3)) + 3*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke(
        '3.35',
        '2*x*Derivative(y(x), (x, 3)) + (1 - 2*nu)*y(x) - (4*nu + 4*x - 4)*Derivative(y(x), (x, 2)) + (6*nu + 2*x - 5)*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.37',
        '-x*(x - 2)*Derivative(y(x), (x, 2)) + x*(x - 2)*Derivative(y(x), (x, 3)) + 2*y(x) - 2*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.38',
        '-8*x*Derivative(y(x), x) + (2*x - 1)*Derivative(y(x), (x, 3)) + 8*y(x)',
        dimension=4,
    ),
    kamke(
        '3.39',
        '(x + 4)*Derivative(y(x), (x, 2)) + (2*x - 1)*Derivative(y(x), (x, 3)) + 2*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.40', 'a*x**2*y(x) + x**2*Derivative(y(x), (x, 3)) - 6*Derivative(y(x), x)', dimension=4
    ),
    kamke(
        '3.41',
        'x**2*Derivative(y(x), (x, 3)) + (x + 1)*Derivative(y(x), (x, 2)) - y(x)',
        dimension=4,
    ),
    kamke(
        '3.42',
        'x**2*Derivative(y(x), (x, 3)) - x*Derivative(y(x), (x, 2)) + (x**2 + 1)*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.45',
        'x**2*Derivative(y(x), (x, 3)) + 3*x*y(x) + 4*x*Derivative(y(x), (x, 2)) + (x**2 + 2)*Derivative(y(x), x)',
        dimension=4,
        note='inhomogeneous term f(x) set to 0, as in Schwarz; Schwarz contradicts himself: '
        'S^3_7 in the table (p. 412), S^3_{4,5} in the listing (p. 414); 4 is right: the '
        'Laguerre-Forsyth invariant (45x^2 + 2)/(27x^3) does not vanish, so the equation '
        'is not equivalent to y\'\'\' = 0',
    ),
    kamke(
        '3.47',
        'x**2*Derivative(y(x), (x, 3)) + 6*x*Derivative(y(x), (x, 2)) + 6*Derivative(y(x), x)',
        dimension=7,
    ),
    kamke(
        '3.48',
        'a*x**2*y(x) + x**2*Derivative(y(x), (x, 3)) + 6*x*Derivative(y(x), (x, 2)) + 6*Derivative(y(x), x)',
        dimension=5,
        note='Schwarz (pp. 412, 414): S^3_7, right only for a = 0 (that is Kamke 3.47): the '
        'equation is (x^2 y)\'\'\' + a x^2 y = 0, i.e. w\'\'\' + a w = 0 for w = x^2 y, constant '
        'coefficients like Kamke 3.1 (S^3_{5,2}); Laguerre-Forsyth invariant a',
    ),
    kamke(
        '3.49',
        '3*p*(3*q + 1)*Derivative(y(x), x) - x**2*y(x) + x**2*Derivative(y(x), (x, 3)) - x*(3*p + 3*q)*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke(
        '3.50',
        '-2*a*x*y(x) + x**2*Derivative(y(x), (x, 3)) - x*(2*n + 2)*Derivative(y(x), (x, 2)) + (a*x**2 + 6*n)*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.51',
        'x**2*Derivative(y(x), (x, 3)) - (x**2 - 2*x)*Derivative(y(x), (x, 2)) - (nu**2 + x**2 - 0.25)*Derivative(y(x), x) + (nu**2 + x**2 - 2*x - 0.25)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.53',
        'x**2*Derivative(y(x), (x, 3)) + (nu**2 - 0.25)*y(x) - (2*x**2 - 2*x)*Derivative(y(x), (x, 2)) + (-nu**2 + x**2 - 2*x + 0.25)*Derivative(y(x), x)',
        dimension=4,
    ),
    kamke(
        '3.54',
        '2*x**2*y(x) + x**2*Derivative(y(x), (x, 3)) - (2*x**3 - 6)*Derivative(y(x), x) - (x**4 - 6*x)*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke(
        '3.56',
        '-2*x*y(x) - 2*x*Derivative(y(x), (x, 2)) + (x**2 + 2)*Derivative(y(x), x) + (x**2 + 2)*Derivative(y(x), (x, 3))',
        dimension=4,
    ),
    kamke(
        '3.57',
        'a*y(x) + 2*x*(x - 1)*Derivative(y(x), (x, 3)) + (6*x - 3)*Derivative(y(x), (x, 2)) + (2*a*x + b)*Derivative(y(x), x)',
        dimension=7,
    ),
    kamke(
        '3.58',
        '4*x**2*Derivative(y(x), (x, 3)) + (4*x + 4)*Derivative(y(x), x) + (x**2 + 14*x - 1)*Derivative(y(x), (x, 2)) + 2*y(x)',
        dimension=4,
    ),
    kamke(
        '3.60',
        'x**3*Derivative(y(x), (x, 3)) + x*(1 - nu**2)*Derivative(y(x), x) + (a*x**3 + nu**2 - 1)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.61',
        'x**3*Derivative(y(x), (x, 3)) + (4*nu**2 - 1)*y(x) + (4*x**3 + x*(1 - 4*nu**2))*Derivative(y(x), x)',
        dimension=7,
    ),
    kamke(
        '3.63',
        '-6*x**3*(x - 1)*log(x) + x**3*(x + 8) + x**3*Derivative(y(x), (x, 3)) + 3*x**2*Derivative(y(x), (x, 2)) - 2*x*Derivative(y(x), x) + 2*y(x)',
        dimension=5,
    ),
    kamke(
        '3.64',
        'x**3*Derivative(y(x), (x, 3)) + 3*x**2*Derivative(y(x), (x, 2)) + x*(1 - a**2)*Derivative(y(x), x)',
        dimension=7,
    ),
    kamke(
        '3.65',
        'x**3*Derivative(y(x), (x, 3)) - 4*x**2*Derivative(y(x), (x, 2)) + x*(x**2 + 8)*Derivative(y(x), x) - (2*x**2 + 8)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.66',
        'x**3*Derivative(y(x), (x, 3)) + 6*x**2*Derivative(y(x), (x, 2)) + (a*x**3 - 12)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.68',
        'x**3*Derivative(y(x), (x, 3)) + x**2*(x + 3)*Derivative(y(x), (x, 2)) + x*(5*x - 30)*Derivative(y(x), x) + (4*x + 30)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.70',
        'x*(x**2 + 1)*Derivative(y(x), (x, 3)) + (6*x**2 + 3)*Derivative(y(x), (x, 2)) - 12*y(x)',
        dimension=4,
    ),
    kamke(
        '3.71',
        'x**2*(x + 3)*Derivative(y(x), (x, 3)) - x*(3*x + 6)*Derivative(y(x), (x, 2)) + (6*x + 6)*Derivative(y(x), x) - 6*y(x)',
        dimension=5,
    ),
    kamke(
        '3.73',
        'x**3*(x + 1)*Derivative(y(x), (x, 3)) - x**2*(4*x + 2)*Derivative(y(x), (x, 2)) + x*(10*x + 4)*Derivative(y(x), x) - (12*x + 4)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.74',
        '4*x**4*Derivative(y(x), (x, 3)) - 4*x**3*Derivative(y(x), (x, 2)) + 4*x**2*Derivative(y(x), x) - 1',
        dimension=5,
    ),
    kamke(
        '3.75',
        'x**3*(x**2 + 1)*Derivative(y(x), (x, 3)) - x**2*(4*x**2 + 2)*Derivative(y(x), (x, 2)) + x*(10*x**2 + 4)*Derivative(y(x), x) - (12*x**2 + 4)*y(x)',
        dimension=4,
    ),
    kamke(
        '3.76',
        'x**6*Derivative(y(x), (x, 3)) + x**2*Derivative(y(x), (x, 2)) - 2*y(x)',
        dimension=4,
    ),
    kamke(
        '3.77',
        'a*y(x) + x**6*Derivative(y(x), (x, 3)) + 6*x**5*Derivative(y(x), (x, 2))',
        dimension=4,
    ),
    kamke('6.1', '-y(x)**2 + Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.2', '-6*y(x)**2 + Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.3', '-x - 6*y(x)**2 + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.4', '-6*y(x)**2 + 4*y(x) + Derivative(y(x), (x, 2))', dimension=1),
    kamke('6.5', 'a*y(x)**2 + b*x + c + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.6', 'a - x*y(x) - 2*y(x)**3 + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.7', '-a*y(x)**3 + Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.8', '-2*a**2*y(x)**3 + 2*a*b*x*y(x) - b + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.9', 'a*y(x)**3 + b*x*y(x) + c*y(x) + d + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.10', 'a*y(x)**3 + b*y(x)**2 + c*y(x) + d + Derivative(y(x), (x, 2))', dimension=1),
    kamke('6.11', 'a*x**r*y(x)**n + Derivative(y(x), (x, 2))', dimension=1),
    kamke(
        '6.12',
        'a**(2*n)*(n + 1)*y(x)**(2*n + 1) + Derivative(y(x), (x, 2))',
        dimension=2,
        generators=[('1', '0'), ('x', '-y/n')],
        note='equation as printed by Schwarz (p. 404), who gives the dimension and generators; '
        'the SymPy Kamke suite has an additional -y(x), which breaks the scaling symmetry '
        '(dimension 1, only d/dx). Schwarz\'s own solution x = int dy/(y*sqrt((a*y)**(2n) - 1)) '
        'belongs to y\'\' = (n + 1) a^(2n) y^(2n+1) - y, i.e. to an equation with a linear '
        'term: the printed equation has probably lost it; Kamke\'s original not checked',
    ),
    kamke(
        '6.21', '-y(x)**2 - 2*y(x) - 3*Derivative(y(x), x) + Derivative(y(x), (x, 2))', dimension=1
    ),
    kamke(
        '6.26',
        'a*Derivative(y(x), x) + b*y(x)**n + (a**2/4 - 0.25)*y(x) + Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke('6.27', 'a*Derivative(y(x), x) + b*x**r*y(x)**n + Derivative(y(x), (x, 2))', dimension=0),
    kamke('6.30', '-y(x)**3 + y(x)*Derivative(y(x), x) + Derivative(y(x), (x, 2))', dimension=2),
    kamke(
        '6.31',
        'a*y(x) - y(x)**3 + y(x)*Derivative(y(x), x) + Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke(
        '6.32',
        '2*a**2*y(x) + a*y(x)**2 + (3*a + y(x))*Derivative(y(x), x) - y(x)**3 + Derivative(y(x), (x, 2))',
        dimension=2,
    ),
    kamke(
        '6.40',
        '-4*a**2*y(x) - 3*a*y(x)**2 - b - 3*y(x)*Derivative(y(x), x) + Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke('6.42', '-2*a*y(x)*Derivative(y(x), x) + Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.43', 'a*y(x)*Derivative(y(x), x) + b*y(x)**3 + Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.45', 'a*Derivative(y(x), x)**2 + b*y(x) + Derivative(y(x), (x, 2))', dimension=1),
    kamke(
        '6.47',
        'a*Derivative(y(x), x)**2 + b*Derivative(y(x), x) + c*y(x) + Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke('6.50', 'a*y(x)*Derivative(y(x), x)**2 + b*y(x) + Derivative(y(x), (x, 2))', dimension=1),
    kamke('6.56', 'a*(Derivative(y(x), x)**2 + 1)**2*y(x) + Derivative(y(x), (x, 2))', dimension=1),
    kamke(
        '6.57',
        '-a*(x*Derivative(y(x), x) - y(x))**r + Derivative(y(x), (x, 2))',
        dimension=2,
        generators=[('0', 'x'), ('(1 - r)*x', '2*y')],
        note='Schwarz lists it in classes of dimension [2, 3]: 2 for generic r,'
        ' the determining equations contain (r - 3)*X_y',
    ),
    kamke(
        '6.57, r = 3',
        '-a*(x*Derivative(y(x), x) - y(x))**3 + Derivative(y(x), (x, 2))',
        dimension=3,
        generators=[('0', 'x'), ('y', '0'), ('x', '-y')],
        note='the special exponent of Kamke 6.57: sl(2), the linear maps of the plane'
        ' with determinant 1, which leave x*y\' - y invariant',
    ),
    kamke('6.71', '9*Derivative(y(x), x)**4 + 8*Derivative(y(x), (x, 2))', dimension=3),
    kamke('6.73', '-x*y(x)**n + x*Derivative(y(x), (x, 2)) + 2*Derivative(y(x), x)', dimension=1),
    kamke(
        '6.74', 'a*x**m*y(x)**n + x*Derivative(y(x), (x, 2)) + 2*Derivative(y(x), x)', dimension=1
    ),
    kamke('6.78', 'x*Derivative(y(x), (x, 2)) - (1 - y(x))*Derivative(y(x), x)', dimension=2),
    kamke(
        '6.79',
        '-x**2*Derivative(y(x), x)**2 + x*Derivative(y(x), (x, 2)) + y(x)**2 + 2*Derivative(y(x), x)',
        dimension=1,
    ),
    kamke(
        '6.80', 'a*(x*Derivative(y(x), x) - y(x))**2 - b + x*Derivative(y(x), (x, 2))', dimension=1
    ),
    kamke(
        '6.81',
        '2*x*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**3 + Derivative(y(x), x)',
        dimension=3,
    ),
    kamke('6.82', '-a*(-y(x) + y(x)**n) + x**2*Derivative(y(x), (x, 2))', dimension=1),
    kamke(
        '6.86',
        'a*(x*Derivative(y(x), x) - y(x))**2 - b*x**2 + x**2*Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke(
        '6.87', 'a*y(x)*Derivative(y(x), x)**2 + b*x + x**2*Derivative(y(x), (x, 2))', dimension=1
    ),
    kamke('6.89', '(x**2 + 1)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 + 1', dimension=1),
    kamke(
        '6.90',
        '-x**4*Derivative(y(x), x)**2 + 4*x**2*Derivative(y(x), (x, 2)) + 4*y(x)',
        dimension=1,
    ),
    kamke(
        '6.92',
        'x**3*(-y(x)**3 + y(x)*Derivative(y(x), x) + Derivative(y(x), (x, 2))) + 12*x*y(x) + 24',
        dimension=1,
    ),
    kamke(
        '6.93', '-a*(x*Derivative(y(x), x) - y(x))**2 + x**3*Derivative(y(x), (x, 2))', dimension=8
    ),
    kamke(
        '6.94',
        'b + 2*x**3*Derivative(y(x), (x, 2)) + x**2*(2*x*y(x) + 9)*Derivative(y(x), x) + x*(a - 2*x**2*y(x)**2 + 3*x*y(x))*y(x)',
        dimension=1,
    ),
    kamke('6.96', 'a**2*y(x)**n + x**4*Derivative(y(x), (x, 2))', dimension=1),
    kamke(
        '6.97',
        'x**4*Derivative(y(x), (x, 2)) - x*(x**2 + 2*y(x))*Derivative(y(x), x) + 4*y(x)**2',
        dimension=2,
    ),
    kamke(
        '6.98',
        'x**4*Derivative(y(x), (x, 2)) - x**2*(x + Derivative(y(x), x))*Derivative(y(x), x) + 4*y(x)**2',
        dimension=1,
    ),
    kamke('6.99', 'x**4*Derivative(y(x), (x, 2)) + (x*Derivative(y(x), x) - y(x))**3', dimension=8),
    kamke('6.104', '-a + y(x)*Derivative(y(x), (x, 2))', dimension=2),
    kamke('6.105', '-a*x + y(x)*Derivative(y(x), (x, 2))', dimension=1),
    kamke('6.106', '-a*x**2 + y(x)*Derivative(y(x), (x, 2))', dimension=1),
    kamke('6.107', '-a + y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2', dimension=8),
    kamke('6.108', '-a*x - b + y(x)**2 + y(x)*Derivative(y(x), (x, 2))', dimension=0),
    kamke(
        '6.109',
        'y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 - Derivative(y(x), x)',
        dimension=2,
    ),
    kamke('6.110', 'y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2 + 1', dimension=2),
    kamke('6.111', 'y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2 - 1', dimension=2),
    kamke(
        '6.117',
        'a*y(x)*Derivative(y(x), x) + b*y(x)**2 + y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.118',
        '-2*a*y(x)**2 + a*y(x)*Derivative(y(x), x) + b*y(x)**3 + y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.119',
        '2*a**2*y(x)**2 + a*y(x) - 2*b**2*y(x)**3 - (a*y(x) - 1)*Derivative(y(x), x) + y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.120',
        '(a**2 - b**2*y(x)**2)*(y(x) + 1)*y(x) + (a*y(x) - 1)*Derivative(y(x), x) + y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.124',
        '-y(x)**2 + 3*y(x)*Derivative(y(x), x) + y(x)*Derivative(y(x), (x, 2)) - 3*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke('6.125', '-a*Derivative(y(x), x)**2 + y(x)*Derivative(y(x), (x, 2))', dimension=8),
    kamke(
        '6.126',
        'a*(Derivative(y(x), x)**2 + 1) + y(x)*Derivative(y(x), (x, 2))',
        dimension=2,
        generators=[('1', '0'), ('x', 'y')],
        note='Schwarz contradicts himself: class 8 in the table, but only the two generators '
        'd/dx, x d/dx + y d/dy in the listing. 2 is right for generic a: u = y**(a + 1) gives '
        'u\'\' = -a*(a + 1)*u**((a - 1)/(a + 1)), which has only these two symmetries',
    ),
    kamke(
        '6.127', 'a*Derivative(y(x), x)**2 + b*y(x)**3 + y(x)*Derivative(y(x), (x, 2))', dimension=2
    ),
    kamke(
        '6.128',
        'a*Derivative(y(x), x)**2 + b*y(x)*Derivative(y(x), x) + c*y(x)**2 + d*y(x)**(1 - a) + y(x)*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke(
        '6.130',
        'a*Derivative(y(x), x)**2 + b*y(x)**2*Derivative(y(x), x) + c*y(x)**4 + y(x)*Derivative(y(x), (x, 2))',
        dimension=2,
    ),
    kamke(
        '6.133',
        '(x + y(x))*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 - Derivative(y(x), x)',
        dimension=3,
    ),
    kamke(
        '6.134',
        '(x - y(x))*Derivative(y(x), (x, 2)) + (2*Derivative(y(x), x) + 2)*Derivative(y(x), x)',
        dimension=8,
    ),
    kamke(
        '6.135',
        '(x - y(x))*Derivative(y(x), (x, 2)) - (Derivative(y(x), x) + 1)*(Derivative(y(x), x)**2 + 1)',
        dimension=8,
    ),
    kamke('6.137', '2*y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 + 1', dimension=2),
    kamke('6.138', 'a + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2', dimension=3),
    kamke(
        '6.140',
        '-8*y(x)**3 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=2,
    ),
    kamke(
        '6.141',
        '-8*y(x)**3 - 4*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.142',
        '(-4*x - 8*y(x))*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=0,
    ),
    kamke(
        '6.143',
        '(a*y(x) + b)*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.144',
        'a*y(x)**3 + 2*x*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2 + 1',
        dimension=0,
    ),
    kamke(
        '6.145',
        '(a*y(x) + b*x)*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=0,
    ),
    kamke(
        '6.146',
        '-3*y(x)**4 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=2,
    ),
    kamke(
        '6.147',
        'b - 8*x*y(x)**3 - (4*a + 4*x**2)*y(x)**2 - 3*y(x)**4 + 2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2',
        dimension=0,
    ),
    kamke('6.150', '2*y(x)*Derivative(y(x), (x, 2)) - 3*Derivative(y(x), x)**2', dimension=8),
    kamke(
        '6.151',
        '-4*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - 3*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.153',
        '(a*y(x)**3 + 1)*y(x)**2 + 2*y(x)*Derivative(y(x), (x, 2)) - 6*Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.154',
        '(-Derivative(y(x), x)**2 - 1)*Derivative(y(x), x)**2 + 2*y(x)*Derivative(y(x), (x, 2))',
        dimension=2,
    ),
    kamke(
        '6.155',
        '(-2*a + 2*y(x))*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 + 1',
        dimension=2,
    ),
    kamke(
        '6.156',
        '-a*x**2 - b*x - c + 3*y(x)*Derivative(y(x), (x, 2)) - 2*Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke('6.157', '3*y(x)*Derivative(y(x), (x, 2)) - 5*Derivative(y(x), x)**2', dimension=8),
    kamke(
        '6.158', '4*y(x)*Derivative(y(x), (x, 2)) + 4*y(x) - 3*Derivative(y(x), x)**2', dimension=3
    ),
    kamke(
        '6.159',
        '-12*y(x)**3 + 4*y(x)*Derivative(y(x), (x, 2)) - 3*Derivative(y(x), x)**2',
        dimension=2,
    ),
    kamke(
        '6.160',
        'a*y(x)**3 + b*y(x)**2 + c*y(x) + 4*y(x)*Derivative(y(x), (x, 2)) - 3*Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.162',
        'a*y(x)**3 + 4*y(x)*Derivative(y(x), (x, 2)) - 5*Derivative(y(x), x)**2',
        dimension=3,
        generators=[('1', '0'), ('x', '-2*y'), ('x**2', '-4*x*y')],
        note='equation as printed by Schwarz (p. 408), consistent with his generators, his '
        'solution and 6.163; the SymPy Kamke suite has a*y(x)**2 instead, probably a typo: '
        'then y = u**-4 gives the linear u\'\' = a*u/16 (dimension 8), while with y**3 it is '
        'the Ermakov-Pinney equation u\'\' = a/(16*u**3) (dimension 3)',
    ),
    kamke(
        '6.163',
        '8*y(x)**3 + 12*y(x)*Derivative(y(x), (x, 2)) - 15*Derivative(y(x), x)**2',
        dimension=3,
    ),
    kamke('6.164', 'n*y(x)*Derivative(y(x), (x, 2)) - (n - 1)*Derivative(y(x), x)**2', dimension=8),
    kamke('6.168', 'c*Derivative(y(x), x)**2 + (a*y(x) + b)*Derivative(y(x), (x, 2))', dimension=8),
    kamke(
        '6.169',
        'x*y(x)*Derivative(y(x), (x, 2)) + x*Derivative(y(x), x)**2 - y(x)*Derivative(y(x), x)',
        dimension=8,
    ),
    ode(
        "Kamke 6.170",
        "x*y(x)*Derivative(y(x), (x, 2)) + x*Derivative(y(x), x)**2"
        " + a*y(x)*Derivative(y(x), x) + f(x)",
        8,
        [("0", "1/y"), ("0", "x**(1 - a)/y")],
        "Kamke, Differentialgleichungen, 6.170; not in Schwarz's Appendix E",
        note="f arbitrary. Linearizable: with u = y**2 it is x u'' + a u' + 2 f(x) = 0, a linear "
        "second order ODE, so 8 symmetries for every a and f; the generators add the "
        "solutions 1 and x**(1 - a) of x u'' + a u' = 0 to u",
    ),
    kamke(
        '6.171',
        'x*(a*y(x)**4 + d) + x*y(x)*Derivative(y(x), (x, 2)) - x*Derivative(y(x), x)**2 + (b*y(x)**2 + c)*y(x) + y(x)*Derivative(y(x), x)',
        dimension=0,
        note='equation of the SymPy Kamke suite (d*x); Schwarz (p. 409) prints + d instead. '
        'Both have no symmetry (checked with random parameter values; the symbolic Janet '
        'basis takes more than 20 min)',
    ),
    kamke(
        '6.172',
        'a*y(x)*Derivative(y(x), x) + b*x*y(x)**3 + x*y(x)*Derivative(y(x), (x, 2)) - x*Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.173',
        'a*y(x)*Derivative(y(x), x) + x*y(x)*Derivative(y(x), (x, 2)) + 2*x*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.174',
        'x*y(x)*Derivative(y(x), (x, 2)) - 2*x*Derivative(y(x), x)**2 + (y(x) + 1)*Derivative(y(x), x)',
        dimension=2,
    ),
    kamke(
        '6.175',
        'a*y(x)*Derivative(y(x), x) + x*y(x)*Derivative(y(x), (x, 2)) - 2*x*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.176',
        'x*y(x)*Derivative(y(x), (x, 2)) - 4*x*Derivative(y(x), x)**2 + 4*y(x)*Derivative(y(x), x)',
        dimension=8,
    ),
    kamke(
        '6.178',
        'x*(x + y(x))*Derivative(y(x), (x, 2)) + x*Derivative(y(x), x)**2 + (x - y(x))*Derivative(y(x), x) - y(x)',
        dimension=8,
    ),
    kamke(
        '6.179',
        '2*x*y(x)*Derivative(y(x), (x, 2)) - x*Derivative(y(x), x)**2 + y(x)*Derivative(y(x), x)',
        dimension=8,
    ),
    kamke(
        '6.180',
        'x**2*(y(x) - 1)*Derivative(y(x), (x, 2)) - 2*x**2*Derivative(y(x), x)**2 - 2*x*(y(x) - 1)*Derivative(y(x), x) - 2*(y(x) - 1)**2*y(x)',
        dimension=8,
    ),
    kamke(
        '6.181',
        'x**2*(x + y(x))*Derivative(y(x), (x, 2)) - (x*Derivative(y(x), x) - y(x))**2',
        dimension=8,
    ),
    kamke(
        '6.182',
        'a*(x*Derivative(y(x), x) - y(x))**2 + x**2*(x - y(x))*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke(
        '6.183',
        '-x**2*(Derivative(y(x), x)**2 + 1) + 2*x**2*y(x)*Derivative(y(x), (x, 2)) + y(x)**2',
        dimension=3,
    ),
    kamke(
        '6.184',
        'a*x**2*y(x)*Derivative(y(x), (x, 2)) + b*x**2*Derivative(y(x), x)**2 + c*x*y(x)*Derivative(y(x), x) + d*y(x)**2',
        dimension=8,
    ),
    kamke(
        '6.185',
        '-a*(x + 2)*y(x)**2 + x*(x + 1)**2*y(x)*Derivative(y(x), (x, 2)) - x*(x + 1)**2*Derivative(y(x), x)**2 + 2*(x + 1)**2*y(x)*Derivative(y(x), x)',
        dimension=8,
    ),
    kamke(
        '6.186',
        '-12*x**2*y(x)*Derivative(y(x), x) + 3*x*y(x)**2 - (4 - 4*x**3)*Derivative(y(x), x)**2 + (8 - 8*x**3)*y(x)*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke('6.188', '-a + y(x)**2*Derivative(y(x), (x, 2))', dimension=2),
    kamke(
        '6.189', 'a*x + y(x)**2*Derivative(y(x), (x, 2)) + y(x)*Derivative(y(x), x)**2', dimension=1
    ),
    kamke(
        '6.190',
        '-a*x - b + y(x)**2*Derivative(y(x), (x, 2)) + y(x)*Derivative(y(x), x)**2',
        dimension=1,
    ),
    kamke(
        '6.191',
        '(1 - 2*y(x))*Derivative(y(x), x)**2 + (y(x)**2 + 1)*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke(
        '6.192',
        '(y(x)**2 + 1)*Derivative(y(x), (x, 2)) - 3*y(x)*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.193',
        '(x + y(x)**2)*Derivative(y(x), (x, 2)) - (2*x - 2*y(x)**2)*Derivative(y(x), x)**3 + (4*y(x)*Derivative(y(x), x) + 1)*Derivative(y(x), x)',
        dimension=8,
    ),
    kamke(
        '6.194',
        '(x**2 + y(x)**2)*Derivative(y(x), (x, 2)) - (x*Derivative(y(x), x) - y(x))*(Derivative(y(x), x)**2 + 1)',
        dimension=8,
    ),
    kamke(
        '6.195',
        '(x**2 + y(x)**2)*Derivative(y(x), (x, 2)) - (x*Derivative(y(x), x) - y(x))*(2*Derivative(y(x), x)**2 + 2)',
        dimension=8,
    ),
    kamke('6.205', '-a + x*y(x)**2*Derivative(y(x), (x, 2))', dimension=2),
    kamke(
        '6.206',
        '-x*(a**2 - y(x)**2)*Derivative(y(x), x) + (a**2 - x**2)*(a**2 - y(x)**2)*Derivative(y(x), (x, 2)) + (a**2 - x**2)*y(x)*Derivative(y(x), x)**2',
        dimension=8,
    ),
    kamke(
        '6.208',
        'x**3*y(x)**2*Derivative(y(x), (x, 2)) + (x + y(x))*(x*Derivative(y(x), x) - y(x))**3',
        dimension=8,
    ),
    kamke('6.209', '-a + y(x)**3*Derivative(y(x), (x, 2))', dimension=3),
    kamke(
        '6.210',
        '(1 - 3*y(x)**2)*Derivative(y(x), x)**2 + (y(x)**2 + 1)*y(x)*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke(
        '6.211', '-a**2*x*y(x)**2 + y(x)**4 + 2*y(x)**3*Derivative(y(x), (x, 2)) - 1', dimension=0
    ),
    kamke(
        '6.212',
        '-a*x**2 - b*x - c + 2*y(x)**3*Derivative(y(x), (x, 2)) + y(x)**2*Derivative(y(x), x)**2',
        dimension=0,
    ),
    kamke(
        '6.214',
        '(a/2 - 6*y(x)**2)*Derivative(y(x), x)**2 + (-a*y(x) - b + 4*y(x)**3)*Derivative(y(x), (x, 2))',
        dimension=8,
    ),
    kamke(
        '6.219',
        'd*y(x) + (a*x**2 + 2*b*x + c + y(x)**2)**2*Derivative(y(x), (x, 2))',
        dimension=1,
        generators=[('a*x**2 + 2*b*x + c', '(a*x + b)*y')],
        note='equation of the SymPy Kamke suite; Schwarz (p. 410) prints (y**2 + a*x**2 + 2*b*x + '
        'c**2)*y\'\' + d*y = 0 (square lost, c**2) and the generator (a*x**2 + 2*b*x + c) d/dx + '
        '(x*y + b*y/a) d/dy, off by the factor a in the second component; the corrected '
        'generator satisfies the symmetry condition of the suite equation exactly',
    ),
    kamke(
        '6.226',
        '-x**2*y(x)*Derivative(y(x), x) - x*y(x)**2 + Derivative(y(x), x)*Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke(
        '6.227',
        '(x*Derivative(y(x), x) - y(x))*Derivative(y(x), (x, 2)) + 4*Derivative(y(x), x)**2',
        dimension=2,
    ),
    kamke(
        '6.228',
        '(x*Derivative(y(x), x) - y(x))*Derivative(y(x), (x, 2)) - (Derivative(y(x), x)**2 + 1)**2',
        dimension=2,
    ),
    kamke('6.229', 'a*x**3*Derivative(y(x), x)*Derivative(y(x), (x, 2)) + b*y(x)**2', dimension=2),
    kamke(
        '6.232',
        '(y(x)**2 + Derivative(y(x), x)**2)*Derivative(y(x), (x, 2)) + y(x)**3',
        dimension=2,
    ),
    kamke(
        '6.233',
        '-b + (a*(x*Derivative(y(x), x) - y(x)) + Derivative(y(x), x)**2)*Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke(
        '6.237',
        'a**2*Derivative(y(x), (x, 2))**2 - 2*a*x*Derivative(y(x), (x, 2)) + Derivative(y(x), x)',
        dimension=2,
    ),
    kamke(
        '6.239',
        '3*x**2*Derivative(y(x), (x, 2))**2 - (6*x*Derivative(y(x), x) + 2*y(x))*Derivative(y(x), (x, 2)) + 4*Derivative(y(x), x)**2',
        dimension=2,
    ),
    kamke(
        '6.240',
        'x**2*(2 - 9*x)*Derivative(y(x), (x, 2))**2 - 6*x*(1 - 6*x)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) - 36*x*Derivative(y(x), x)**2 + 6*y(x)*Derivative(y(x), (x, 2))',
        dimension=1,
    ),
    kamke(
        '6.243',
        '-2*a**2*y(x)*Derivative(y(x), x)**2*Derivative(y(x), (x, 2)) + (a**2*y(x)**2 - b**2)*Derivative(y(x), (x, 2))**2 + (a**2*Derivative(y(x), x)**2 - 1)*Derivative(y(x), x)**2',
        dimension=1,
        generators=[('1', '0')],
        note='Schwarz (p. 411): class S^2_{2,1} but only the generator d/dx; the class is right '
        'only for b = 0, with the generators d/dx, x d/dx + y d/dy (scaling x, y by the same '
        'factor; for b != 0 the term b**2*y\'\'**2 breaks it). In p = y\'(y) the equation is '
        'the Clairaut equation p = y p\' +- sqrt(b**2 p\'**2 + 1)/a',
    ),
    kamke(
        '6.244',
        '-4*x*(x*Derivative(y(x), x) - y(x))**3*y(x) + (x**2*y(x)*Derivative(y(x), (x, 2)) - x**2*Derivative(y(x), x)**2 + y(x)**2)**2',
        dimension=3,
    ),
    kamke(
        '6.245',
        '32*(x*Derivative(y(x), (x, 2)) - Derivative(y(x), x))**3*Derivative(y(x), (x, 2)) + (2*y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2)**3',
        dimension=1,
    ),
    kamke(
        '7.1',
        '-a**2*(Derivative(y(x), x)**5 + 2*Derivative(y(x), x)**3 + Derivative(y(x), x)) + Derivative(y(x), (x, 3))',
        dimension=2,
    ),
    kamke(
        '7.2',
        'y(x)*Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2 + Derivative(y(x), (x, 3)) + 1',
        dimension=1,
    ),
    kamke(
        '7.3',
        '-y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), x)**2 + Derivative(y(x), (x, 3))',
        dimension=2,
    ),
    kamke('7.4', 'a*y(x)*Derivative(y(x), (x, 2)) + Derivative(y(x), (x, 3))', dimension=2),
    kamke(
        '7.5',
        'x**2*Derivative(y(x), (x, 3)) + x*Derivative(y(x), (x, 2)) + (2*x*y(x) - 1)*Derivative(y(x), x) + y(x)**2',
        dimension=1,
        note='inhomogeneous term f(x) set to 0, as in Schwarz',
    ),
    kamke(
        '7.6',
        'x**2*Derivative(y(x), (x, 3)) + x*(y(x) - 1)*Derivative(y(x), (x, 2)) + x*Derivative(y(x), x)**2 + (1 - y(x))*Derivative(y(x), x)',
        dimension=1,
    ),
    kamke(
        '7.7',
        'y(x)**3*Derivative(y(x), x) + y(x)*Derivative(y(x), (x, 3)) - Derivative(y(x), x)*Derivative(y(x), (x, 2))',
        dimension=2,
    ),
    kamke(
        '7.8',
        '4*y(x)**2*Derivative(y(x), (x, 3)) - 18*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) + 15*Derivative(y(x), x)**3',
        dimension=7,
    ),
    kamke(
        '7.9',
        '9*y(x)**2*Derivative(y(x), (x, 3)) - 45*y(x)*Derivative(y(x), x)*Derivative(y(x), (x, 2)) + 40*Derivative(y(x), x)**3',
        dimension=7,
    ),
    kamke(
        '7.10',
        '-3*Derivative(y(x), (x, 2))**2 + 2*Derivative(y(x), x)*Derivative(y(x), (x, 3))',
        dimension=6,
        generators=[('1', '0'), ('0', '1'), ('x', '0'), ('0', 'y'), ('x**2', '0'), ('0', 'y**2')],
        note='equation as printed by Schwarz (p. 412): the Schwarzian derivative of y vanishes, '
        'solutions (C1*x + C2)/(C3*x + C4), projective transformations of x and of y; the SymPy '
        'Kamke suite has -3*y\'**2 instead of -3*y\'\'**2, probably a typo: then y\'\'\' = 3*y\'/2, '
        'a linear equation equivalent to y\'\'\' = 0 (dimension 7)',
    ),
    kamke(
        '7.11',
        '(Derivative(y(x), x)**2 + 1)*Derivative(y(x), (x, 3)) - 3*Derivative(y(x), x)*Derivative(y(x), (x, 2))**2',
        dimension=6,
    ),
    kamke(
        '7.12',
        '(-a - 3*Derivative(y(x), x))*Derivative(y(x), (x, 2))**2 + (Derivative(y(x), x)**2 + 1)*Derivative(y(x), (x, 3))',
        dimension=4,
    ),
    # END KAMKE
]

CATALOG = CLASSICAL_ODES + FIRST_ORDER_ODES + ODE_SYSTEMS + PDES + KAMKE
