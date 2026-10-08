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
- Bluman, Anco: G. W. Bluman, S. C. Anco, Symmetry and Integration Methods for
  Differential Equations, Springer 2002 (Applied Mathematical Sciences 154).
- CRC 1: N. H. Ibragimov (ed.), CRC Handbook of Lie Group Analysis of
  Differential Equations, Vol. 1, CRC Press 1994, Part B (group
  classifications); cited with section and page.
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
BLUMAN_ANCO = "Bluman, Anco, Symmetry and Integration Methods for Differential Equations (2002)"
BLUMAN_ANCO_DELIERIUM = (
    "the book gives no dimension: it is delierium's, the generators checked against the "
    "determining equations"
)
CRC1 = (
    "Ibragimov (ed.), CRC Handbook of Lie Group Analysis of Differential Equations, Vol. 1 (1994)"
)
KHARE_TIMOL = (
    "Khare, Timol, Determining equations for infinitesimal transformation of second and "
    "third-order ODE using algorithm in open-source SageMath"
)
CKK_SOURCE = (
    "Cherniha, King, Kovalenko, Lie symmetry properties of nonlinear reaction-diffusion "
    "equations with gradient-dependent diffusivity, arXiv:1507.01893 (2015)"
)
AIMS_SOURCE = (
    "Lie group classification of u_t = (Phi(u) (u_x)**n)_x + F(u), AIMS Mathematics 11(9) "
    "(2026) 28009-28054, doi:10.3934/math.20261118"
)
ANCO_SOURCE = (
    "Anco et al., Conservation laws and symmetries of radial generalized nonlinear "
    "p-Laplacian evolution equations, arXiv:1609.07652 (2016)"
)
THE_WELL_SOURCE = (
    "Ohana et al., The Well: a Large-Scale Collection of Diverse Physics Simulations for "
    "Machine Learning, NeurIPS 2024, arXiv:2412.00568; github.com/PolymathicAI/the_well"
)
SYMMETRY_INFORMED_SOURCE = (
    "Yang, Rao, Dehmamy, Walters, Yu, Symmetry-Informed Governing Equation Discovery, "
    "NeurIPS 2024, "
    "arXiv:2405.16756; github.com/Rose-STL-Lab/symmetry-ode-discovery"
)
PDEFIND_SOURCE = (
    "Rudy, Brunton, Proctor, Kutz, Data-driven discovery of partial differential equations, "
    "Sci. Adv. 3 (2017) e1602614; github.com/snagcliffs/PDE-FIND"
)
PINNACLE_SOURCE = (
    "Hao et al., PINNacle: A Comprehensive Benchmark of Physics-Informed Neural Networks for "
    "Solving PDEs, NeurIPS 2024, arXiv:2306.08827; github.com/i207M/PINNacle, src/pde"
)
ODESYM_SOURCE = (
    "Kahlmeyer, Merk, Giesen, Discovering Symmetries of ODEs by Symbolic Regression, AAAI 2025, "
    "arXiv:2506.19550; github.com/kahlmeyer94/ODESym, ode_examples.py"
)
EQWORLD_SOURCE = "EqWorld, Polyanin, Zhurov, Levitin, eqworld.ipmnet.ru/en/solutions/npde"
KO_KIM_LEE_SOURCE = (
    "Ko, Kim, Lee, Learning Infinitesimal Generators of Continuous Symmetries from Data, "
    "arXiv:2410.21853v2 (2024)"
)
ODEBENCH_SOURCE = (
    "d'Ascoli, Becker, Mathis, Schwaller, Kilbertus, ODEFormer: Symbolic Regression of "
    "Dynamical Systems with Transformers, ICLR 2024; ODEBench, "
    "github.com/sdascoli/odeformer, odeformer/odebench/strogatz_equations.py"
)
GABEL_SOURCE = (
    "Gabel, Quax, Gavves, Data-driven Lie point symmetry detection for continuous dynamical "
    "systems, Mach. Learn.: Sci. Technol. 5 (2024) 015037, doi:10.1088/2632-2153/ad2629"
)
APEBENCH_SOURCE = (
    "Koehler, Niedermayr, Westermann, Thuerey, APEBench: A Benchmark for Autoregressive Neural "
    "Emulators of PDEs, NeurIPS 2024, arXiv:2411.00180; the physical scenarios (phy_*) of "
    "github.com/tum-pbs/apebench with their default coefficients, the equations of the exponax "
    "0.1.0 steppers"
)
PDEBENCH_SOURCE = (
    "Takamoto et al., PDEBench: An Extensive Benchmark for Scientific Machine Learning, "
    "NeurIPS 2022, arXiv:2210.07182, appendix D"
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
        f"{HYDON}, Examples 3.3 and 6.1",
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
        f"{ARRIGO}, Example 2.20, (2.144); {HYDON}, Example 4.6",
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
        f"classical (sl(2)); {HYDON}, Example 10.3",
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
    ode(
        "Kamke 1.535",
        "8*x*Derivative(y(x), x)**3 - 12*y(x)*Derivative(y(x), x)**2 + 9*y(x)",
        3,
        [
            ("x", "y"),
            ("(3*x + sqrt(9*x**2 - 4*y**2))**(2/3)", "3*y/(3*x + sqrt(9*x**2 - 4*y**2))**(1/3)"),
            ("(3*x - sqrt(9*x**2 - 4*y**2))**(2/3)", "3*y/(3*x - sqrt(9*x**2 - 4*y**2))**(1/3)"),
        ],
        "Kamke, equation 1.535, from the SymPy Kamke test suite",
        note="cubic in y': three solution curves through each point, so unlike y' = h(x, y) a "
        "finite algebra. Dimension and generators are delierium's (the book gives neither), "
        "checked independently: power series solutions of the determining equations, and the "
        "invariance condition on F = 0. The generators hold for x > 0 between the singular "
        "solutions y = +-3*x/2; general solution (x + 9*C)**3 = 27*C*y**2",
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
        f"{ARRIGO}, Example 3.1, (3.16); {HYDON}, Example 8.2",
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
        "u_t = u_xx - 2u**3",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + 2*u(x, t)**3",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "-u")],
        f"{ARRIGO}, Example 4.2",
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
        f"{BAUMANN}, p. 226; {HYDON}, Example 11.6",
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
        f"Dimas, Tsoubelis; {HYDON}, Example 9.7; classical: u_t = u_xx + f(u) with a cubic f "
        "has only the translations",
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

# Baumann's worked examples: section 4.4 (ODEs) and the scalar PDEs of 5.6.
# The dimension is that of the symmetries MathLie finds (Infinitesimals[],
# LieSolve[]); the generators are Baumann's, one per group constant.
BAUMANN_4_4 = f"{BAUMANN}, section 4.4"
BAUMANN_5_6 = f"{BAUMANN}, section 5.6"
BAUMANN_EXAMPLES = [
    # 4.4.1 first order ODEs: the generators Baumann uses
    ode(
        "Baumann p. 150: Riccati u' + u**2 - 2/x**2 = 0",
        "Derivative(u(x), x) + u(x)**2 - 2/x**2",
        INFINITE,
        [("x", "-u")],
        f"{BAUMANN_4_4}, Example 1, p. 150",
        note="the non-homogeneous dilation x d/dx - u d/du (Ibragimov)",
        y="u",
    ),
    ode(
        "Baumann p. 153: u**2/x**2 + u**3/x - u'/x**2 = 0",
        "-Derivative(u(x), x)/x**2 + u(x)**2/x**2 + u(x)**3/x",
        INFINITE,
        [("x", "-u")],
        f"{BAUMANN_4_4}, Example 2, p. 153",
        y="u",
    ),
    ode(
        "Baumann p. 155: x u' - u + sqrt(u/x) = 0",
        "x*Derivative(u(x), x) - u(x) + sqrt(u(x)/x)",
        INFINITE,
        [("x**2", "x*u")],
        f"{BAUMANN_4_4}, Example 3, p. 155",
        note="the projective transformation x/(1 - eps*x), u/(1 - eps*x)",
        y="u",
    ),
    ode(
        "Baumann p. 164: u' = 1 + tan(x - u)/x",
        "Derivative(u(x), x) - 1 - tan(x - u(x))/x",
        INFINITE,
        [("0", "1/(x*cos(x - u))")],
        f"{BAUMANN_4_4}, integrating factor, Example 1, p. 164",
        y="u",
    ),
    ode(
        "Baumann p. 169: u' = (x**2 + u**2)/(x u)",
        "Derivative(u(x), x) - (x**2 + u(x)**2)/(x*u(x))",
        INFINITE,
        [("x", "u")],
        f"{BAUMANN_4_4}, integrating factor, Example 3, p. 169",
        y="u",
    ),
    ode(
        "Baumann p. 170: u' = u (1 - u**2 exp(u))",
        "Derivative(u(x), x) - u(x)*(1 - u(x)**2*exp(u(x)))",
        INFINITE,
        [("1", "0")],
        f"{BAUMANN_4_4}, integrating factor, Example 4, p. 170",
        y="u",
    ),
    # 4.4.2 second order ODEs
    ode(
        "Baumann p. 176: u'' - u'/u**2 + 1/(u x) = 0",
        "Derivative(u(x), (x, 2)) - Derivative(u(x), x)/u(x)**2 + 1/(u(x)*x)",
        2,
        [("x", "u/2"), ("x**2", "x*u")],
        f"{BAUMANN_4_4}, group classification, Example 1, p. 176",
        note="from Ibragimov (1994); a scaling and a projection",
        y="u",
    ),
    ode(
        "Baumann p. 181: Ames u'' + u'/x + a exp(u) = 0",
        "Derivative(u(x), (x, 2)) + Derivative(u(x), x)/x + a*exp(u(x))",
        2,
        [("x", "-2"), ("x*(1 - log(x))", "2*log(x)")],
        f"{BAUMANN_4_4}, group classification, Example 2, p. 181",
        note="Ames (1968): heat transfer, vortex motion, the nebular theory",
        y="u",
    ),
    ode(
        "Baumann p. 185: u'' - a u'**2 = 0",
        "Derivative(u(x), (x, 2)) - a*Derivative(u(x), x)**2",
        8,
        [
            ("0", "x*exp(a*u)/a"),
            ("-a*x**2", "x"),
            ("-exp(-a*u)/a", "0"),
            ("1", "0"),
            ("x", "0"),
            ("x*exp(-a*u)", "-exp(-a*u)/a"),
            ("0", "exp(a*u)/a"),
            ("0", "1"),
        ],
        f"{BAUMANN_4_4}, integrating factor, Example 1, p. 185",
        note="linearizable: u = -log(v)/a turns it into v'' = 0",
        y="u",
    ),
    ode(
        "Baumann p. 189: generalized cable u'' - a (1 + u'**2)**nu = 0",
        "Derivative(u(x), (x, 2)) - a*(1 + Derivative(u(x), x)**2)**nu",
        2,
        [("1", "0"), ("0", "1")],
        f"{BAUMANN_4_4}, integrating factor, Example 2, p. 189",
        note="nu generic; the suspended cable of Ames (1968) is nu = 1/2. Eqs. (4.63) and "
        "(4.64) print 1 - u'**2, the computation (input and output) uses 1 + u'**2",
        y="u",
    ),
    ode(
        "Baumann p. 196: 4 w**2 w'' - 4 w' + 2 w - w**3 = 0",
        "4*w(t)**2*Derivative(w(t), (t, 2)) - 4*Derivative(w(t), t) + 2*w(t) - w(t)**3",
        2,
        [("2*exp(t)", "exp(t)*w"), ("1", "0")],
        f"{BAUMANN_4_4}, canonical variables, pp. 196 and 198",
        note="the equation of p. 176 in the canonical variables t = log(x), w = u/sqrt(x)",
        x="t",
        y="w",
    ),
    ode(
        "Baumann p. 198: v' - v**2 v'' = 0",
        "Derivative(v(s), s) - v(s)**2*Derivative(v(s), (s, 2))",
        2,
        [("1", "0"), ("s", "v/2")],
        f"{BAUMANN_4_4}, canonical variables, p. 198",
        note="the equation of p. 196 in the canonical variables of its symmetry exp(t)*(2 d/dt "
        "+ w d/dw)",
        x="s",
        y="v",
    ),
    # 4.4.3 higher order ODEs
    ode(
        "Baumann p. 203: Kamke 7.13 u'' u''' - a sqrt(1 + b**2 u''**2) = 0",
        "Derivative(u(x), (x, 2))*Derivative(u(x), (x, 3))"
        " - a*sqrt(1 + b**2*Derivative(u(x), (x, 2))**2)",
        3,
        [("1", "0"), ("0", "1"), ("0", "x")],
        f"{BAUMANN_4_4}, Example 1, p. 203",
        y="u",
    ),
    ode(
        "Baumann p. 209: u''' + R (u' u'' - u u''') = 0",
        "Derivative(u(x), (x, 3))"
        " + R*(Derivative(u(x), x)*Derivative(u(x), (x, 2)) - u(x)*Derivative(u(x), (x, 3)))",
        3,
        [("1", "0"), ("x", "0"), ("0", "u - 1/R")],
        f"{BAUMANN_4_4}, Example 2, p. 209",
        note="Baumann's constant Re (a Reynolds number) is R here",
        y="u",
    ),
    ode(
        "Baumann p. 212: Kamke 7.16 3 u'' u'''' - 5 u'''**2 = 0",
        "3*Derivative(u(x), (x, 2))*Derivative(u(x), (x, 4)) - 5*Derivative(u(x), (x, 3))**2",
        6,
        [("1", "0"), ("x", "0"), ("u", "0"), ("0", "1"), ("0", "x"), ("0", "u")],
        f"{BAUMANN_4_4}, Example 3, p. 212",
        note="solutions (u + C1*x + C2)**2 = C3*x + C4 (Kamke)",
        y="u",
    ),
    # 5.5 similarity reduction
    pde(
        "Baumann p. 270: Karpman-Belashov"
        " (u_t + 6 u u_x - mu u_xx - epsilon u_xxx - lambda u_xxxxx)_x - u_yy = 0",
        "6*Derivative(u(x, y, t), x)**2 + Derivative(u(x, y, t), t, x)"
        " + 6*u(x, y, t)*Derivative(u(x, y, t), (x, 2)) - Derivative(u(x, y, t), (y, 2))"
        " - mu*Derivative(u(x, y, t), (x, 3)) - epsilon*Derivative(u(x, y, t), (x, 4))"
        " - lambda_*Derivative(u(x, y, t), (x, 6))",
        ("x", "y", "t"),
        INFINITE,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("t", "0", "0", "1/6"),
            ("0", "1", "0", "0"),
            ("y/2", "t", "0", "0"),
            ("y*t", "t**2", "0", "y/6"),
        ],
        f"{BAUMANN}, section 5.5, Example 4, p. 270, equation (5.47)",
        note="Karpman, Belashov (1991); contains the Zabolotskaya-Khokhlov (epsilon = lambda = 0)"
        " and the Kadomtsev-Petviashvili equation (mu = lambda = 0). xi_x = F2 + y F1'/2,"
        " xi_y = F1, xi_t = k1, phi = (2 F2' + y F1'')/12 with free functions F1(t), F2(t); the"
        " generators are those of F2 = 1, t and F1 = 1, t, t**2",
    ),
    # 5.6 working examples, the scalar PDEs (5.6.1/5.6.2, the diffusion
    # equation, is the heat equation above)
    pde(
        "Baumann p. 289: single flux line u_t = k u_xx/(1 + u_x**2)",
        "Derivative(u(x, t), t) - k*Derivative(u(x, t), (x, 2))/(1 + Derivative(u(x, t), x)**2)",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("-u", "0", "x"),
            ("x", "2*t", "u"),
        ],
        f"{BAUMANN_5_6}.3, p. 291",
        note="Tang, Feng, Golubovic, Phys. Rev. Lett. 72 (1994), equation 7; the generator "
        "-u d/dx + x d/du is a rotation in the (x, u)-plane; k = 1 is the nonlinear filtration "
        f"equation of {HYDON}, Example 9.3",
    ),
    pde(
        "Baumann p. 297: cylindrical KdV u_t + 6 u u_x + u_xxx + u/(2t) = 0",
        "Derivative(u(x, t), t) + 6*u(x, t)*Derivative(u(x, t), x)"
        " + Derivative(u(x, t), (x, 3)) + u(x, t)/(2*t)",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("x", "3*t", "-2*u"),
            ("x*sqrt(t)/2", "t**(3/2)", "(x - 24*t*u)/(24*sqrt(t))"),
            ("2*sqrt(t)", "0", "1/(6*sqrt(t))"),
        ],
        f"{BAUMANN_5_6}.4, p. 297 and Table 5.1",
        note="Calogero, Degasperis (1978)",
    ),
    pde(
        "Baumann p. 298: spherical KdV u_t + 6 u u_x + u_xxx + u/t = 0",
        "Derivative(u(x, t), t) + 6*u(x, t)*Derivative(u(x, t), x)"
        " + Derivative(u(x, t), (x, 3)) + u(x, t)/t",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("x", "3*t", "-2*u"), ("log(t)", "0", "1/(6*t)")],
        f"{BAUMANN_5_6}.4, p. 298 and Table 5.1",
    ),
    pde(
        "Baumann p. 298: KdV with slowly varying coefficients",
        "Derivative(u(x, t), t) + A(e*t)*u(x, t)*Derivative(u(x, t), x)"
        " + B(e*t)*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        2,
        [("1", "0", "0")],
        f"{BAUMANN_5_6}.4, p. 298 and Table 5.1",
        note="Ko, Kuehl (1978); Baumann's arbitrary alpha and beta are A and B here. The "
        "second generator, (Integral(A(e*s), (s, 0, t)), 0, 1), is not listed (an integral)",
    ),
    pde(
        "Baumann p. 299: u_t - 6 u**2 u_x + 6 lambda u_x + u_xxx = 0",
        "Derivative(u(x, t), t) - 6*u(x, t)**2*Derivative(u(x, t), x)"
        " + 6*lambda_*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x + 12*lambda_*t", "3*t", "-u")],
        f"{BAUMANN_5_6}.4, p. 300 and Table 5.1",
        note="Fung, Au (1982)",
    ),
    pde(
        "Baumann p. 300: generalized KdV u_t + b u**alpha u_x + u_xxx = 0",
        "Derivative(u(x, t), t) + b*u(x, t)**alpha*Derivative(u(x, t), x)"
        " + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "3*t", "-2*u/alpha")],
        f"{BAUMANN_5_6}.4, p. 300 and Table 5.1",
        note="Yang (1994); alpha generic, Baumann's beta is b here",
    ),
    pde(
        "Baumann p. 300: perturbed KdV",
        "Derivative(u(x, t), t) + 6*u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))"
        " + e*(-a*u(x, t)**2*Derivative(u(x, t), x) + b*u(x, t)*Derivative(u(x, t), (x, 3))"
        " + g*Derivative(u(x, t), x)*Derivative(u(x, t), (x, 2)) + d*Derivative(u(x, t), (x, 5)))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{BAUMANN_5_6}.4, p. 301 and Table 5.1",
        note="Baumann's alpha, beta, gamma, delta, epsilon are a, b, g, d, e here",
    ),
    pde(
        "Baumann p. 301: KdV-Burgers u_t + u u_x + mu u_xxx - nu u_xx = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x)"
        " + mu*Derivative(u(x, t), (x, 3)) - nu*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "0", "1")],
        f"{BAUMANN_5_6}.4, p. 301 and Table 5.1",
        note="Parkes (1994)",
    ),
    pde(
        "Baumann p. 301: Kadomtsev-Petviashvili (u_t + u u_x + mu u_xxx)_x + sigma u_yy = 0",
        "Derivative(u(x, y, t), t, x) + Derivative(u(x, y, t), x)**2"
        " + u(x, y, t)*Derivative(u(x, y, t), (x, 2)) + mu*Derivative(u(x, y, t), (x, 4))"
        " + sigma*Derivative(u(x, y, t), (y, 2))",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("x", "2*y", "3*t", "-2*u"),
        ],
        f"{BAUMANN_5_6}.4, p. 302 and Table 5.1",
        note="Baumann's two-dimensional KdV-Burgers equation (5.57) of Parkes and Ma, computed "
        "without the term nu u_xxx; the generators are those of constant free functions and of "
        "free[1] = t",
    ),
    pde(
        "Baumann p. 305: Stokes' creeping flow",
        "Derivative(Psi(r, theta), (r, 4))"
        " - 2*cot(theta)*Derivative(Psi(r, theta), (r, 2), theta)/r**2"
        " + 2*Derivative(Psi(r, theta), (r, 2), (theta, 2))/r**2"
        " + 4*cot(theta)*Derivative(Psi(r, theta), r, theta)/r**3"
        " - 4*Derivative(Psi(r, theta), r, (theta, 2))/r**3"
        " - 3*cot(theta)**3*Derivative(Psi(r, theta), theta)/r**4"
        " + 3*cot(theta)**2*Derivative(Psi(r, theta), (theta, 2))/r**4"
        " - 9*cot(theta)*Derivative(Psi(r, theta), theta)/r**4"
        " - 2*cot(theta)*Derivative(Psi(r, theta), (theta, 3))/r**4"
        " + 8*Derivative(Psi(r, theta), (theta, 2))/r**4"
        " + Derivative(Psi(r, theta), (theta, 4))/r**4",
        ("r", "theta"),
        INFINITE,
        [("r", "0", "0"), ("0", "0", "Psi")],
        f"{BAUMANN_5_6}.5, p. 305",
        note="E**2(E**2 Psi) = 0 for the stream function, E**2 = d_rr + (d_thetatheta - "
        "cot(theta) d_theta)/r**2; linear, so the superposition of solutions besides",
        u="Psi",
    ),
    pde(
        "Baumann p. 341: Fokker-Planck equation of the Rayleigh particle",
        "Derivative(P(v, tau), tau) - P(v, tau) - v*Derivative(P(v, tau), v)"
        " - Derivative(P(v, tau), (v, 2))",
        ("v", "tau"),
        INFINITE,
        [
            ("exp(-tau)", "0", "0"),
            ("exp(tau)", "0", "-exp(tau)*v*P"),
            ("exp(-2*tau)*v", "-exp(-2*tau)", "-exp(-2*tau)*P"),
            ("0", "0", "P"),
            ("exp(2*tau)*v", "exp(2*tau)", "-exp(2*tau)*v**2*P"),
            ("0", "1", "0"),
        ],
        f"{BAUMANN_5_6}.9, p. 341",
        note="Van Kampen (1981), Cicogna and Vitali (1990); scaled, free of parameters. "
        "Linear, so the superposition of solutions besides",
        u="P",
    ),
    pde(
        "Baumann p. 348: molecular beam epitaxy",
        "Derivative(a(x, t), t) + kappa*Derivative(a(x, t), (x, 4))"
        " - alpha*Derivative(a(x, t), (x, 2))"
        " - g*(2*Derivative(a(x, t), (x, 2))**2"
        " + 2*Derivative(a(x, t), x)*Derivative(a(x, t), (x, 3)))"
        " - 3*lambda_*Derivative(a(x, t), x)**2*Derivative(a(x, t), (x, 2)) - Phi",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1")],
        f"{BAUMANN_5_6}.10, p. 349",
        note="the growth equation (5.83) in one dimension, Wolf, Villain (1990); Baumann's gamma "
        "is g here",
        u="a",
    ),
    pde(
        "Baumann p. 350: molecular beam epitaxy, surface diffusion",
        "Derivative(a(x, t), t) + kappa*Derivative(a(x, t), (x, 4))"
        " - g*(2*Derivative(a(x, t), (x, 2))**2"
        " + 2*Derivative(a(x, t), x)*Derivative(a(x, t), (x, 3))) - Phi",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1"), ("x/4", "t", "t*Phi")],
        f"{BAUMANN_5_6}.10.1, p. 350",
        note="(5.83) with alpha = lambda = 0; Baumann's gamma is g here",
        u="a",
    ),
    pde(
        "Baumann p. 352: molecular beam epitaxy, desorption",
        "Derivative(a(x, t), t) - alpha*Derivative(a(x, t), (x, 2))"
        " - 3*lambda_*Derivative(a(x, t), x)**2*Derivative(a(x, t), (x, 2)) - Phi",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1"), ("x", "2*t", "a + t*Phi")],
        f"{BAUMANN_5_6}.10.2, p. 352",
        note="(5.83) with kappa = gamma = 0",
        u="a",
    ),
]

# Hydon's worked examples (#50): the equations with their symmetries as the
# book gives them. Where Hydon says "generated by" or "spanned by", the list is
# complete and the dimension is that of the list; first order ODEs (and the
# first order system 7.8) have infinitely many symmetries, Hydon gives some.
# Equations already in the catalogue from another source keep their entry,
# with a note (Blasius 4.6, Ermakov-Pinney 10.3, u_t = u_x**2 8.2, Burgers
# 8.3, Huxley 9.7, filtration 9.3, Harry-Dym 11.6).
HYDON_EXAMPLES = [
    ode(
        "Hydon Example 2.10: Riccati y' = x y**2 - 2 y/x - 1/x**3",
        "Derivative(y(x), x) - x*y(x)**2 + 2*y(x)/x + 1/x**3",
        INFINITE,
        [("x", "-2*y")],
        f"{HYDON}, Example 2.10",
    ),
    ode(
        "Hydon Example 2.11: y' = (y + 1)/x + y**2/x**3",
        "Derivative(y(x), x) - (y(x) + 1)/x - y(x)**2/x**3",
        INFINITE,
        [("x**2", "x*y")],
        f"{HYDON}, Examples 1.2 and 2.11",
        note="the inversions (x/(1 - eps x), y/(1 - eps x))",
    ),
    ode(
        "Hydon Example 2.12: y' = (y - 4 x y**2 - 16 x**3)/(y**3 + 4 x**2 y + x)",
        "Derivative(y(x), x) - (y(x) - 4*x*y(x)**2 - 16*x**3)/(y(x)**3 + 4*x**2*y(x) + x)",
        INFINITE,
        [("-y", "4*x")],
        f"{HYDON}, Examples 2.12 and 2.14",
    ),
    ode(
        "Hydon Example 2.13: y' = (1 - y**2)/(x y) + 1",
        "Derivative(y(x), x) - (1 - y(x)**2)/(x*y(x)) - 1",
        INFINITE,
        [("1/x", "-y/x**2")],
        f"{HYDON}, Example 2.13",
    ),
    ode(
        "Hydon Example 2.17: y' = (y**3 + y - 3 x**2 y)/(3 x y**2 + x - x**3)",
        "Derivative(y(x), x) - (y(x)**3 + y(x) - 3*x**2*y(x))/(3*x*y(x)**2 + x - x**3)",
        INFINITE,
        [("y**3 + y - 3*x**2*y", "x**3 - x - 3*x*y**2")],
        f"{HYDON}, Example 2.17",
    ),
    ode(
        "Hydon Example 3.4: y''' = y**(-3)",
        "Derivative(y(x), (x, 3)) - y(x)**(-3)",
        2,
        [("1", "0"), ("x", "3*y/4")],
        f"{HYDON}, Examples 3.4, 4.3, 4.7 and 5.4",
        note="flow in thin films with free boundaries",
    ),
    ode(
        "Hydon Example 4.2: y'' = y'**2/y + (y - 1/y) y'",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2/y(x) - (y(x) - 1/y(x))*Derivative(y(x), x)",
        1,
        [("1", "0")],
        f"{HYDON}, Example 4.2",
        note="the translations are the only Lie point symmetries",
    ),
    ode(
        "Hydon Example 4.5: y'' = y'/x + 3 y**2/(2 x**3)",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)/x - 3*y(x)**2/(2*x**3)",
        1,
        [("x", "y")],
        f"{HYDON}, Example 4.5",
        note="the Euler-Lagrange equation of L = y'**2/(2 x) + y**3/(2 x**4); the scalings are "
        "its only Lie point symmetries, and variational",
    ),
    ode(
        "Hydon Example 5.2: y'''' = 2 (1 - y') y'''/y",
        "Derivative(y(x), (x, 4)) - 2*(1 - Derivative(y(x), x))*Derivative(y(x), (x, 3))/y(x)",
        3,
        [("1", "0"), ("x", "y"), ("x**2", "2*x*y")],
        f"{HYDON}, Examples 5.2 and 6.6",
    ),
    ode(
        "Hydon Example 5.8: y'''' = y'''**(4/3)",
        "Derivative(y(x), (x, 4)) - Derivative(y(x), (x, 3))**(4/3)",
        5,
        [("0", "1"), ("0", "x"), ("0", "x**2"), ("1", "0"), ("x", "0")],
        f"{HYDON}, Example 5.8",
        note="solvable: derived series of dimensions 5, 4, 2, 0",
    ),
    ode(
        "Hydon Example 6.2: y''' = y''**2/(y' (1 + y'))",
        "Derivative(y(x), (x, 3)) - Derivative(y(x), (x, 2))**2/(Derivative(y(x), x)*(1 + Derivative(y(x), x)))",
        3,
        [("1", "0"), ("0", "1"), ("x", "y")],
        f"{HYDON}, Example 6.2",
    ),
    ode(
        "Hydon Example 6.4: y'' = y'**3/(y'**3 - 2)",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)**3/(Derivative(y(x), x)**3 - 2)",
        2,
        [("1", "0"), ("0", "1")],
        f"{HYDON}, Example 6.4",
    ),
    ode(
        "Hydon Example 6.5: y''' = 2 y''**2/y' + y''/x + y'**2/x",
        "Derivative(y(x), (x, 3)) - 2*Derivative(y(x), (x, 2))**2/Derivative(y(x), x) - Derivative(y(x), (x, 2))/x - Derivative(y(x), x)**2/x",
        2,
        [("0", "1"), ("x", "0")],
        f"{HYDON}, Example 6.5",
        note="abelian algebra",
    ),
    ode(
        "Hydon Example 7.2: y''' = (3 y' - 1) y''**2/y'**2",
        "Derivative(y(x), (x, 3)) - (3*Derivative(y(x), x) - 1)*Derivative(y(x), (x, 2))**2/Derivative(y(x), x)**2",
        4,
        [("0", "1"), ("1", "0"), ("x", "y"), ("y", "0")],
        f"{HYDON}, Example 7.2",
    ),
    ode(
        "Hydon Example 7.5: y'''' = (y''' + y'''**2)/y''",
        "Derivative(y(x), (x, 4)) - (Derivative(y(x), (x, 3)) + Derivative(y(x), (x, 3))**2)/Derivative(y(x), (x, 2))",
        4,
        [("0", "1"), ("1", "0"), ("0", "x"), ("x", "3*y")],
        f"{HYDON}, Example 7.5",
        note="Hydon gives characteristics Q = eta - xi y'; the point symmetries among them are "
        "Q = 1, y', x, 3 y - x y' (the other two depend on y'')",
    ),
    ode(
        "Hydon Example 7.7: y''' = 3 y y'",
        "Derivative(y(x), (x, 3)) - 3*y(x)*Derivative(y(x), x)",
        2,
        [("1", "0"), ("x", "-2*y")],
        f"{HYDON}, Example 7.7",
        note="these are also the only Lie contact symmetries",
    ),
    odes(
        "Hydon Example 7.8: y1' = (x y1 + y2**2)/(y1 y2 - x**2), y2' = (x y2 + y1**2)/(y1 y2 - x**2)",
        [
            "Derivative(y1(x), x) - (x*y1(x) + y2(x)**2)/(y1(x)*y2(x) - x**2)",
            "Derivative(y2(x), x) - (x*y2(x) + y1(x)**2)/(y1(x)*y2(x) - x**2)",
        ],
        ["y1", "y2"],
        INFINITE,
        [("x", "y1", "y2")],
        f"{HYDON}, Example 7.8",
        note="a first order system; the scalings are the only generator linear in y1, y2",
        t="x",
    ),
    pde(
        "Hydon Example 8.4: Thomas equation u_xt = u_x u_t - 1",
        "Derivative(u(x, t), x, t) - Derivative(u(x, t), x)*Derivative(u(x, t), t) + 1",
        ["x", "t"],
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("x", "-t", "0"),
            ("0", "0", "exp(x + t + u)"),
        ],
        f"{HYDON}, Examples 8.4 and 9.6",
        note="and V(x, t) exp(u) d/du for every solution of V_xt = V (here V = exp(x + t)): "
        "linearizable",
    ),
    ode(
        "Hydon Example 11.1: y'' = tan(y')",
        "Derivative(y(x), (x, 2)) - tan(Derivative(y(x), x))",
        2,
        [("1", "0"), ("0", "1")],
        f"{HYDON}, Example 11.1",
    ),
    ode(
        "Hydon Example 11.4: y''' = y''**2/x - y''/y'",
        "Derivative(y(x), (x, 3)) - Derivative(y(x), (x, 2))**2/x + Derivative(y(x), (x, 2))/Derivative(y(x), x)",
        2,
        [("0", "1"), ("x/2", "y")],
        f"{HYDON}, Example 11.4",
    ),
    ode(
        "Hydon Example 11.5: Chazy y''' = 2 y y'' - 3 y'**2 + lam (6 y' - y**2)**2",
        "Derivative(y(x), (x, 3)) - 2*y(x)*Derivative(y(x), (x, 2)) + 3*Derivative(y(x), x)**2 - lam*(6*Derivative(y(x), x) - y(x)**2)**2",
        3,
        [("1", "0"), ("x", "-y"), ("x**2", "-(2*x*y + 6)")],
        f"{HYDON}, Example 11.5",
        note="sl(2) for every lam; lam = 0 is the classical Chazy equation",
    ),
]

# Hydon's exercises with an answer in "Hints and Partial Solutions to Some
# Exercises" (p. 201) or symmetries given in the exercise itself.
HYDON_EXERCISES = [
    ode(
        "Hydon Exercise 2.3: y' = 2 y/x",
        "Derivative(y(x), x) - 2*y(x)/x",
        INFINITE,
        [("x", "a*y")],
        f"{HYDON}, Exercise 2.3",
        note="the scalings (e**eps x, e**(a eps) y) for every a",
    ),
    ode(
        "Hydon Exercise 2.5: y' = 3 y/x + x**5/(2 y + x**3)",
        "Derivative(y(x), x) - 3*y(x)/x - x**5/(2*y(x) + x**3)",
        INFINITE,
        [("x", "3*y")],
        f"{HYDON}, Exercise 2.5",
    ),
    ode(
        "Hydon Exercise 2.6: y' = exp(-x) y**2 + y + exp(x)",
        "Derivative(y(x), x) - exp(-x)*y(x)**2 - y(x) - exp(x)",
        INFINITE,
        [("1", "y")],
        f"{HYDON}, Exercise 2.6 and its solution",
    ),
    ode(
        "Hydon Exercise 2.7: y' = (y + y**3)/(x + (x + 1) y**2)",
        "Derivative(y(x), x) - (y(x) + y(x)**3)/(x + (x + 1)*y(x)**2)",
        INFINITE,
        [("y", "0")],
        f"{HYDON}, Exercise 2.7 and its solution",
    ),
    ode(
        "Hydon Exercise 3.4: y'' = y'**4 + a y'**2",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)**4 - a*Derivative(y(x), x)**2",
        2,
        [("1", "0"), ("0", "1")],
        f"{HYDON}, Exercise 3.4 and its solution",
        note="three-dimensional for a = 0; the solution gives the dimension, the generators are "
        "the translations",
    ),
    ode(
        "Hydon Exercise 3.5: y''' = 7 y' - 6 y",
        "Derivative(y(x), (x, 3)) - 7*Derivative(y(x), x) + 6*y(x)",
        5,
        [("1", "0"), ("0", "exp(x)"), ("0", "exp(2*x)"), ("0", "exp(-3*x)"), ("0", "y")],
        f"{HYDON}, Exercise 3.5 and its solution",
        note="linear, yet only 5 symmetries (a linear third order ODE has 4, 5 or 7)",
    ),
    ode(
        "Hydon Exercise 4.5: y' = y**3/((x + 1) y**2 - x**2)",
        "Derivative(y(x), x) - y(x)**3/((x + 1)*y(x)**2 - x**2)",
        INFINITE,
        [("x*y", "y**2")],
        f"{HYDON}, Exercise 4.5",
    ),
    ode(
        "Hydon Exercise 4.8: Poisson-Boltzmann y'' = -k y'/x - d exp(y)",
        "Derivative(y(x), (x, 2)) + k*Derivative(y(x), x)/x + d*exp(y(x))",
        1,
        [("x", "-2")],
        f"{HYDON}, Exercise 4.8",
        note="d = +-1 in the book; k != 0",
    ),
    ode(
        "Hydon Exercise 6.1: y'' = y' (1 - y')/y",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)*(1 - Derivative(y(x), x))/y(x)",
        2,
        [("1", "0"), ("x", "y")],
        f"{HYDON}, Exercise 6.1",
    ),
    ode(
        "Hydon Exercise 6.2: y'' = y y'/x**3 - y**2/x**4",
        "Derivative(y(x), (x, 2)) - y(x)*Derivative(y(x), x)/x**3 + y(x)**2/x**4",
        2,
        [("x**2", "x*y"), ("x", "2*y")],
        f"{HYDON}, Exercise 6.2 and its solution",
    ),
    ode(
        "Hydon Exercise 6.5: y'' = y'**2/y - y**2/(x**3 y')",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)**2/y(x) + y(x)**2/(x**3*Derivative(y(x), x))",
        2,
        [("x", "0"), ("0", "y")],
        f"{HYDON}, Exercise 6.5",
    ),
    ode(
        "Hydon Exercise 6.6: y''' = 3 y''**2/(2 y') + (y**2/2 + 1) y'**3",
        "Derivative(y(x), (x, 3)) - 3*Derivative(y(x), (x, 2))**2/(2*Derivative(y(x), x)) - (y(x)**2/2 + 1)*Derivative(y(x), x)**3",
        6,
        [("1", "0"), ("x", "0"), ("x**2", "0")],
        f"{HYDON}, Exercise 6.6",
        note="Hydon gives the sl(2) of the Moebius transformations of x; the dimension is "
        "delierium's: with the Schwarzian derivative the ODE is S_y(x) = -(y**2/2 + 1) for the "
        "inverse function, which also has the symmetries eta(y) d/dy + ... for the 3 solutions of "
        "eta''' + 4 q eta' + 2 q' eta = 0, q = y**2/2 + 1: sl(2) + sl(2)",
    ),
    pde(
        "Hydon Exercise 8.2: u_t = u_x**3",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**3",
        ["x", "t"],
        5,
        [("0", "-2*t", "u"), ("0", "0", "1"), ("x", "3*t", "0"), ("1", "0", "0"), ("0", "1", "0")],
        f"{HYDON}, Exercise 8.2 and its solution",
        note="the solution gives eta = c1 u + c2, xi = c3 x + c4, tau = (3 c3 - 2 c1) t + c5",
    ),
    ode(
        "Hydon Exercise 11.1: y'' = y'/x + 4 y**2/x**3",
        "Derivative(y(x), (x, 2)) - Derivative(y(x), x)/x - 4*y(x)**2/x**3",
        1,
        [("x", "y")],
        f"{HYDON}, Exercise 11.1",
    ),
]

# Bluman and Anco's examples and exercises (#50), numbered by the book's
# equation numbers. The book often says only that an equation "admits" some
# symmetries, and has no answers to its exercises: then the dimension is
# delierium's (BLUMAN_ANCO_DELIERIUM), the generators are the book's where it
# gives them, all checked against the determining equations.
BLUMAN_ANCO_EXAMPLES = [
    ode(
        "Bluman-Anco (3.173): y y' (y/y')'' = 1",
        "y(x)*Derivative(y(x), x)*Derivative(y(x)/Derivative(y(x), x), (x, 2)) - 1",
        2,
        [("1", "0"), ("x", "y")],
        f"{BLUMAN_ANCO}, (3.173)",
        note=f"wave equation with wave speed y(x) (Bluman, Kumei 1987); the book has = +-1; "
        f"{BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco (3.194): (y y' (y/y')'')' = 0",
        "Derivative(y(x)*Derivative(y(x), x)*Derivative(y(x)/Derivative(y(x), x), (x, 2)), x)",
        3,
        [("1", "0"), ("x", "0"), ("0", "y")],
        f"{BLUMAN_ANCO}, (3.194) and (3.264)",
        note="the book gives these three at (3.194); at (3.264) it says four, with the "
        "translations in y, but d/dy is no symmetry (y occurs explicitly in (3.265))",
    ),
    ode(
        "Bluman-Anco (3.245): y''' = 6 x y''**3/y'**2 + 6 y''**2/y'",
        "Derivative(y(x), (x, 3)) - 6*x*Derivative(y(x), (x, 2))**3/Derivative(y(x), x)**2 - 6*Derivative(y(x), (x, 2))**2/Derivative(y(x), x)",
        3,
        [("x", "0"), ("0", "y"), ("0", "1")],
        f"{BLUMAN_ANCO}, (3.245) and (3.506)",
        note="also seven contact symmetries (3.249), (3.252)",
    ),
    ode(
        "Bluman-Anco (3.257): y'''' = 4 y'''**2/(3 y'')",
        "Derivative(y(x), (x, 4)) - 4*Derivative(y(x), (x, 3))**2/(3*Derivative(y(x), (x, 2)))",
        6,
        [("1", "0"), ("0", "1"), ("x", "0"), ("0", "y"), ("0", "x"), ("x**2", "x*y")],
        f"{BLUMAN_ANCO}, (3.257)",
        note="the book says five point symmetries; there are six (delierium, not solvable): "
        "w = y'' satisfies w'' = 4 w'**2/(3 w), i.e. (w**(-1/3))'' = 0, and x**2 d/dx + x y d/dy "
        "is a symmetry as well; also 12 second order symmetries (3.263)",
    ),
    ode(
        "Bluman-Anco (3.413): y'' = 2 (x y' - y)(1 + y'**2)/(x**2 + y**2)",
        "Derivative(y(x), (x, 2)) - 2*(x*Derivative(y(x), x) - y(x))*(1 + Derivative(y(x), x)**2)/(x**2 + y(x)**2)",
        8,
        [("y", "-x"), ("x", "y")],
        f"{BLUMAN_ANCO}, (3.413) and Exercise 3.3-9",
        note="the circles through the origin, which an inversion maps to straight lines: "
        f"linearizable; the book gives the rotation and the scaling; {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco (3.499): KdV traveling waves y''' = -y y'",
        "Derivative(y(x), (x, 3)) + y(x)*Derivative(y(x), x)",
        2,
        [("1", "0"), ("x", "-2*y")],
        f"{BLUMAN_ANCO}, (3.499) and Exercise 3.5-5",
        note="the point symmetries consist of the translation and the scaling",
    ),
    ode(
        "Bluman-Anco Exercise 3.3-3: y'' = a y'**k",
        "Derivative(y(x), (x, 2)) - a*Derivative(y(x), x)**k",
        3,
        [("1", "0"), ("0", "1")],
        f"{BLUMAN_ANCO}, Exercise 3.3-3",
        note=f"k generic (the book: k = N = 1, 2, ..., special for N = 1, 2, 3); {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco Exercise 3.3-4: y'' = exp(-y')",
        "Derivative(y(x), (x, 2)) - exp(-Derivative(y(x), x))",
        3,
        [("1", "0"), ("0", "1")],
        f"{BLUMAN_ANCO}, Exercise 3.3-4 (b)",
        note=BLUMAN_ANCO_DELIERIUM,
    ),
    ode(
        "Bluman-Anco Exercise 3.5-2: Duffing y'' + a y' + b y + y**3 = 0",
        "Derivative(y(x), (x, 2)) + a*Derivative(y(x), x) + b*y(x) + y(x)**3",
        1,
        [("1", "0")],
        f"{BLUMAN_ANCO}, Exercise 3.5-2",
        note=f"a, b generic; {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco Exercise 3.5-3: y'' = 2 y'**2 cot(y) + sin(y) cos(y)",
        "Derivative(y(x), (x, 2)) - 2*Derivative(y(x), x)**2*cot(y(x)) - sin(y(x))*cos(y(x))",
        8,
        [],
        f"{BLUMAN_ANCO}, Exercise 3.5-3 (Stephani 1989)",
        note="the book asks to show that the symmetries form so(3); there are 8 (delierium): "
        "w = cot(y) satisfies w'' = -w, so the ODE is linearizable and so(3) a subalgebra",
    ),
    ode(
        "Bluman-Anco Exercise 3.5-4: y''' = x (x - 1) y''**3 - 2 x y''**2 + y''",
        "Derivative(y(x), (x, 3)) - x*(x - 1)*Derivative(y(x), (x, 2))**3 + 2*x*Derivative(y(x), (x, 2))**2 - Derivative(y(x), (x, 2))",
        2,
        [],
        f"{BLUMAN_ANCO}, Exercise 3.5-4 (b); {HYDON}, Example 7.4",
        note=f"the exercise asks for contact symmetries; {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco Exercise 3.5-4: y''' = y (y''/y')**3",
        "Derivative(y(x), (x, 3)) - y(x)*(Derivative(y(x), (x, 2))/Derivative(y(x), x))**3",
        3,
        [],
        f"{BLUMAN_ANCO}, Exercise 3.5-4 (c)",
        note=f"the exercise asks for contact symmetries; {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco Exercise 3.5-6: y'''' = y' y'''/y",
        "Derivative(y(x), (x, 4)) - Derivative(y(x), x)*Derivative(y(x), (x, 3))/y(x)",
        3,
        [],
        f"{BLUMAN_ANCO}, Exercise 3.5-6",
        note=f"the exercise asks for second order symmetries; {BLUMAN_ANCO_DELIERIUM}",
    ),
    ode(
        "Bluman-Anco Exercise 3.5-7: y'''' = y**(-5/3)",
        "Derivative(y(x), (x, 4)) - y(x)**(-5/3)",
        3,
        [("1", "0"), ("2*x", "3*y"), ("x**2", "3*x*y")],
        f"{BLUMAN_ANCO}, Exercise 3.5-7 (Sheftel 1997)",
        note="the book gives the dimension and the commutators (sl(2)); the generators are "
        "delierium's, checked",
    ),
    pde(
        "Bluman-Anco (4.80): biharmonic equation u_xxxx + 2 u_xxyy + u_yyyy = 0",
        "Derivative(u(x, y), (x, 4)) + 2*Derivative(u(x, y), (x, 2), (y, 2)) + Derivative(u(x, y), (y, 4))",
        ["x", "y"],
        INFINITE,
        [
            ("x**2 - y**2", "2*x*y", "2*x*u"),
            ("-2*x*y", "x**2 - y**2", "-2*y*u"),
            ("x", "y", "0"),
            ("-y", "x", "0"),
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "u"),
        ],
        f"{BLUMAN_ANCO}, (4.86a-c)",
        note="linear: the 7 generators plus the superposition of solutions; "
        "z -> (a z + b)/(c z + d), u -> lam |dz*/dz| u with z = x + i y",
    ),
    pde(
        "Bluman-Anco (4.64): u_tt = c(x)**2 u_xx, c = (1 + x**2) exp(A atan(x))",
        "Derivative(u(x, t), (t, 2)) - (1 + x**2)**2*exp(2*A*atan(x))*Derivative(u(x, t), (x, 2))",
        ["x", "t"],
        INFINITE,
        [
            ("0", "1", "0"),
            ("1 + x**2", "-A*t", "(A/2 + x)*u"),
            ("(1 + x**2)*t", "-A*t**2/2 - exp(-2*A*atan(x))/(2*A)", "(A/2 + x)*t*u"),
            ("0", "0", "u"),
        ],
        f"{BLUMAN_ANCO}, section 4.2.3, wave speed (c)",
        note="linear; the generators of case (i) with B = D = 1, C = 0 (the integral in X3 "
        "evaluated for A != 0)",
    ),
    pde(
        "Bluman-Anco (4.64): u_tt = c(x)**2 u_xx, c = (1 + x)**(1 + A/2) (1 - x)**(1 - A/2)",
        "Derivative(u(x, t), (t, 2)) - (1 + x)**(2 + A)*(1 - x)**(2 - A)*Derivative(u(x, t), (x, 2))",
        ["x", "t"],
        INFINITE,
        [
            ("0", "1", "0"),
            ("1 - x**2", "-A*t", "(A/2 - x)*u"),
            ("(1 - x**2)*t", "-A*t**2/2 - ((1 - x)/(1 + x))**A/(2*A)", "(A/2 - x)*t*u"),
            ("0", "0", "u"),
        ],
        f"{BLUMAN_ANCO}, section 4.2.3, wave speed (d)",
        note="linear; the generators of case (i) with B = -1, D = 1, C = 0 (the integral in "
        "X3 evaluated for A != 0)",
    ),
    pde(
        "Bluman-Anco (4.64): u_tt = c(x)**2 u_xx, c = x**2 exp(1/x)",
        "Derivative(u(x, t), (t, 2)) - x**4*exp(2/x)*Derivative(u(x, t), (x, 2))",
        ["x", "t"],
        INFINITE,
        [
            ("0", "1", "0"),
            ("x**2", "t", "(x - 1/2)*u"),
            ("x**2*t", "t**2/2 + exp(-2/x)/2", "(x - 1/2)*t*u"),
            ("0", "0", "u"),
        ],
        f"{BLUMAN_ANCO}, section 4.2.3, wave speed (e)",
        note="linear; the generators of case (i) with B = 1, C = D = 0, A = -1",
    ),
    pde(
        "Bluman-Anco (4.88): axisymmetric wave equation u_tt = u_rr + u_r/r",
        "Derivative(u(r, t), (t, 2)) - Derivative(u(r, t), (r, 2)) - Derivative(u(r, t), r)/r",
        ["r", "t"],
        INFINITE,
        [("r", "t", "0"), ("2*r*t", "r**2 + t**2", "-t*u"), ("0", "0", "u"), ("0", "1", "0")],
        f"{BLUMAN_ANCO}, Exercise 4.2-7",
        note="linear: these plus the superposition of solutions",
    ),
]

# CRC Handbook Vol. 1, Part B: scalar equations of the group classifications.
# Signs +-1 of the book are generic parameters here where the result holds
# for them; for the potential filtration equation see the notes.
# Page numbers are those of the printed edition (CRC Press, 1994), read from a
# scanned copy.
CRC_VOL1 = [
    pde(
        "CRC 1, 10.2: nonlinear heat equation u_t = (k(u) u_x)_x",
        "Derivative(u(x, t), t) - Derivative(k(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "2*t", "0"),
        ],
        f"{CRC1}, section 10.2, p. 110",
        note="k arbitrary (Ovsiannikov 1959)",
    ),
    pde(
        "CRC 1, 10.2: nonlinear heat equation u_t = (u**sigma u_x)_x",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**sigma*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "2*t", "0"),
            ("sigma*x/2", "0", "u"),
        ],
        f"{CRC1}, section 10.2, p. 110",
        note="sigma generic (sigma = -4/3 has 5 symmetries, see above)",
    ),
    pde(
        "CRC 1, 10.3: nonlinear filtration equation v_t = k(v_x) v_xx",
        "Derivative(v(x, t), t) - k(Derivative(v(x, t), x))*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "v"),
        ],
        f"{CRC1}, section 10.3, p. 129",
        note="k arbitrary (Akhatov, Gazizov, Ibragimov 1987)",
        u="v",
    ),
    pde(
        "CRC 1, 10.3: nonlinear filtration equation v_t = v_x**n v_xx",
        "Derivative(v(x, t), t) - Derivative(v(x, t), x)**n*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "v"),
            ("0", "n*t", "-v"),
        ],
        f"{CRC1}, section 10.3, p. 129",
        note="n generic; n = -2 is equivalent to the linear heat equation (hodograph, p. 130)",
        u="v",
    ),
    pde(
        "CRC 1, 10.3: nonlinear filtration equation v_t = exp(n atan(v_x))/(1 + v_x**2) v_xx",
        "Derivative(v(x, t), t) - exp(n*atan(Derivative(v(x, t), x)))*Derivative(v(x, t), (x, 2))/(1 + Derivative(v(x, t), x)**2)",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "v"),
            ("v", "n*t", "-x"),
        ],
        f"{CRC1}, section 10.3, p. 129",
        u="v",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = K(w_xx)",
        "Derivative(w(x, t), (x, 2)) - G(Derivative(w(x, t), t))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
        ],
        f"{CRC1}, section 10.4, p. 131",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries); G is the inverse of K, arbitrary (Gazizov 1987)",
        u="w",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = exp(w_xx)",
        "Derivative(w(x, t), (x, 2)) - log(Derivative(w(x, t), t))",
        ("x", "t"),
        6,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
            ("0", "t", "-x**2/2"),
        ],
        f"{CRC1}, section 10.4, p. 131",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries)",
        u="w",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = w_xx**sigma/sigma",
        "Derivative(w(x, t), (x, 2)) - (sigma*Derivative(w(x, t), t))**(1/sigma)",
        ("x", "t"),
        6,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
            ("0", "(1 - sigma)*t", "w"),
        ],
        f"{CRC1}, section 10.4, p. 131",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries); sigma generic",
        u="w",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = 3 w_xx**(1/3)",
        "Derivative(w(x, t), (x, 2)) - (Derivative(w(x, t), t)/3)**3",
        ("x", "t"),
        7,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
            ("0", "2*t/3", "w"),
            ("w", "0", "0"),
        ],
        f"{CRC1}, section 10.2, p. 117",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries)",
        u="w",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = -3 w_xx**(-1/3)",
        "Derivative(w(x, t), (x, 2)) + 27/Derivative(w(x, t), t)**3",
        ("x", "t"),
        7,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
            ("0", "4*t/3", "w"),
            ("x**2", "0", "x*w"),
        ],
        f"{CRC1}, section 10.2, p. 117",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries)",
        u="w",
    ),
    pde(
        "CRC 1, 10.4: potential filtration equation w_t = log(w_xx)",
        "Derivative(w(x, t), (x, 2)) - exp(Derivative(w(x, t), t))",
        ("x", "t"),
        6,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "2*w"),
            ("0", "0", "x"),
            ("0", "t", "t + w"),
        ],
        f"{CRC1}, section 10.2, p. 117",
        note="the potential filtration equation w_t = K(w_xx), written solved for its highest derivative w_xx (the same solutions, hence the same point symmetries)",
        u="w",
    ),
    pde(
        "CRC 1, 10.5: heat equation with a source u_t = (k(u) u_x)_x + q(u)",
        "Derivative(u(x, t), t) - Derivative(k(u(x, t))*Derivative(u(x, t), x), x) - (q(u(x, t)))",
        ("x", "t"),
        2,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
        ],
        f"{CRC1}, section 10.5, p. 133",
        note="k and q arbitrary (Dorodnitsyn 1979, 1982)",
    ),
    pde(
        "CRC 1, 10.5: u_t = (exp(u) u_x)_x + a exp(m u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) - (a*exp(m*u(x, t)))",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("(m - 1)*x/2", "m*t", "-1"),
        ],
        f"{CRC1}, section 10.5, p. 133",
        note="the book's +-1 is a, its beta is m; generic",
    ),
    pde(
        "CRC 1, 10.5: u_t = (exp(u) u_x)_x + d",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) - (d)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "exp(-d*t)", "d*exp(-d*t)"),
            ("x", "0", "2"),
        ],
        f"{CRC1}, section 10.5, p. 133",
        note="the book's delta = +-1 is d; generic",
    ),
    pde(
        "CRC 1, 10.5: u_t = (u**sigma u_x)_x + a u**n",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**sigma*Derivative(u(x, t), x), x) - (a*u(x, t)**n)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("(n - sigma - 1)*x", "2*(n - 1)*t", "-2*u"),
        ],
        f"{CRC1}, section 10.5, p. 134",
        note="the book prints q = +-u**u, from the generator it is u**n; sigma, n generic",
    ),
    pde(
        "CRC 1, 10.5: u_t = (u**sigma u_x)_x + d u",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**sigma*Derivative(u(x, t), x), x) - (d*u(x, t))",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("sigma*x", "0", "2*u"),
            ("0", "exp(-d*sigma*t)", "d*exp(-d*sigma*t)*u"),
        ],
        f"{CRC1}, section 10.5, p. 134",
        note="the book's delta = +-1 is d; generic",
    ),
    pde(
        "CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + a u**n",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**Rational(-4, 3)*Derivative(u(x, t), x), x) - (a*u(x, t)**n)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("(n + Rational(1, 3))*x", "2*(n - 1)*t", "-2*u"),
        ],
        f"{CRC1}, section 10.5, p. 134",
        note="n generic",
    ),
    pde(
        "CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + a u**(-1/3)",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**Rational(-4, 3)*Derivative(u(x, t), x), x) - (a*u(x, t)**Rational(-1, 3))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "4*t/3", "u"),
            ("exp(2*sqrt(a/3)*x)", "0", "-sqrt(3*a)*exp(2*sqrt(a/3)*x)*u"),
            ("exp(-2*sqrt(a/3)*x)", "0", "sqrt(3*a)*exp(-2*sqrt(a/3)*x)*u"),
        ],
        f"{CRC1}, section 10.5, p. 134",
        note="the book's alpha = +-1 is a",
    ),
    pde(
        "CRC 1, 10.5: u_t = (u**(-4/3) u_x)_x + d u",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**Rational(-4, 3)*Derivative(u(x, t), x), x) - (d*u(x, t))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("-2*x/3", "0", "u"),
            ("0", "exp(4*d*t/3)", "d*exp(4*d*t/3)*u"),
            ("-x**2", "0", "3*x*u"),
        ],
        f"{CRC1}, section 10.5, p. 135",
        note="the book's delta = +-1 is d",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(k(u) grad u) + q(u) in the plane",
        "Derivative(u(x, y, t), t) - Derivative(k(u(x, y, t))*Derivative(u(x, y, t), x), x) - Derivative(k(u(x, y, t))*Derivative(u(x, y, t), y), y) - (q(u(x, y, t)))",
        ("x", "y", "t"),
        4,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("y", "-x", "0", "0"),
        ],
        f"{CRC1}, section 10.7, p. 145",
        note="k and q arbitrary: (N**2 + N + 2)/2 = 4 symmetries for N = 2",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(k(u) grad u) in the plane",
        "Derivative(u(x, y, t), t) - Derivative(k(u(x, y, t))*Derivative(u(x, y, t), x), x) - Derivative(k(u(x, y, t))*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        5,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("y", "-x", "0", "0"),
            ("x", "y", "2*t", "0"),
        ],
        f"{CRC1}, section 10.7, p. 145",
        note="k arbitrary",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(exp(u) grad u) in the plane",
        "Derivative(u(x, y, t), t) - Derivative(exp(u(x, y, t))*Derivative(u(x, y, t), x), x) - Derivative(exp(u(x, y, t))*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        6,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("y", "-x", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("0", "0", "t", "-1"),
        ],
        f"{CRC1}, section 10.7, p. 145",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(u**sigma grad u) in the plane",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t)**sigma*Derivative(u(x, y, t), x), x) - Derivative(u(x, y, t)**sigma*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        6,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("y", "-x", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("sigma*x", "sigma*y", "0", "2*u"),
        ],
        f"{CRC1}, section 10.7, p. 146",
        note="sigma generic",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(grad u/u) in the plane",
        "Derivative(u(x, y, t), t) - Derivative(1/u(x, y, t)*Derivative(u(x, y, t), x), x) - Derivative(1/u(x, y, t)*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        INFINITE,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("y", "-x", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("-x", "-y", "0", "2*u"),
        ],
        f"{CRC1}, section 10.7, p. 146",
        note="sigma = -4/(N + 2) = -1 for N = 2: infinitely many symmetries A d/dx + B d/dy - 2 A_x u d/du, A + i B analytic",
    ),
    pde(
        "CRC 1, 10.7: u_t = div(u**(-4/5) grad u) in space",
        "Derivative(u(x, y, z, t), t) - Derivative(u(x, y, z, t)**Rational(-4, 5)*Derivative(u(x, y, z, t), x), x) - Derivative(u(x, y, z, t)**Rational(-4, 5)*Derivative(u(x, y, z, t), y), y) - Derivative(u(x, y, z, t)**Rational(-4, 5)*Derivative(u(x, y, z, t), z), z)",
        ("x", "y", "z", "t"),
        12,
        [
            ("0", "0", "0", "1", "0"),
            ("1", "0", "0", "0", "0"),
            ("0", "1", "0", "0", "0"),
            ("0", "0", "1", "0", "0"),
            ("y", "-x", "0", "0", "0"),
            ("z", "0", "-x", "0", "0"),
            ("0", "z", "-y", "0", "0"),
            ("x", "y", "z", "2*t", "0"),
            ("-4*x/5", "-4*y/5", "-4*z/5", "0", "2*u"),
            ("x**2 - y**2 - z**2", "2*x*y", "2*x*z", "0", "-5*x*u"),
            ("2*x*y", "y**2 - x**2 - z**2", "2*y*z", "0", "-5*y*u"),
            ("2*x*z", "2*y*z", "z**2 - x**2 - y**2", "0", "-5*z*u"),
        ],
        f"{CRC1}, section 10.7, p. 146",
        note="sigma = -4/(N + 2) = -4/5 for N = 3: 7 + 2 symmetries and N = 3 more",
    ),
    pde(
        "CRC 1, 10.8: anisotropic u_t = (k1(u) u_x)_x + (k2(u) u_y)_y",
        "Derivative(u(x, y, t), t) - Derivative(k1(u(x, y, t))*Derivative(u(x, y, t), x), x) - Derivative(k2(u(x, y, t))*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        4,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("x", "y", "2*t", "0"),
        ],
        f"{CRC1}, section 10.8, p. 156",
        note="k1, k2 arbitrary, k1/k2 not constant",
    ),
    pde(
        "CRC 1, 10.8: anisotropic u_t = (exp(a1 u) u_x)_x + (exp(a2 u) u_y)_y",
        "Derivative(u(x, y, t), t) - Derivative(exp(a1*u(x, y, t))*Derivative(u(x, y, t), x), x) - Derivative(exp(a2*u(x, y, t))*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        5,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("a1*x", "a2*y", "0", "2"),
        ],
        f"{CRC1}, section 10.8, p. 156",
        note="a1, a2 generic; the book prints a1 x d/dx + a2 y d/dy - 2 d/du, a sign misprint "
        "(it is not a symmetry; the case with a source, p. 156, gives + 2 d/du for alpha = 0)",
    ),
    pde(
        "CRC 1, 10.8: anisotropic u_t = (u**s1 u_x)_x + (u**s2 u_y)_y",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t)**s1*Derivative(u(x, y, t), x), x) - Derivative(u(x, y, t)**s2*Derivative(u(x, y, t), y), y)",
        ("x", "y", "t"),
        5,
        [
            ("0", "0", "1", "0"),
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("x", "y", "2*t", "0"),
            ("s1*x", "s2*y", "0", "2*u"),
        ],
        f"{CRC1}, section 10.8, p. 156",
        note="s1, s2 generic",
    ),
    pde(
        "CRC 1, 10.10: potential hyperbolic heat equation tau0 u_tt + u_t = k(u_x) u_xx",
        "tau0*Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - k(Derivative(u(x, t), x))*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "exp(-t/tau0)"),
        ],
        f"{CRC1}, section 10.10, p. 164",
        note="classified by contact symmetries (generating functions U); the cases listed are point symmetries; k arbitrary",
    ),
    pde(
        "CRC 1, 10.10: potential hyperbolic heat equation tau0 u_tt + u_t = k0 u_x**n u_xx",
        "tau0*Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - k0*Derivative(u(x, t), x)**n*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("n*x", "0", "(n + 2)*u"),
        ],
        f"{CRC1}, section 10.10, p. 165",
        note="classified by contact symmetries (generating functions U); the cases listed are point symmetries; n generic",
    ),
    pde(
        "CRC 1, 10.10: potential hyperbolic heat equation tau0 u_tt + u_t = k0 exp(m u_x) u_xx",
        "tau0*Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - k0*exp(m*Derivative(u(x, t), x))*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("m*x", "0", "m*u + 2*x"),
        ],
        f"{CRC1}, section 10.10, p. 165",
        note="classified by contact symmetries (generating functions U); the cases listed are point symmetries",
    ),
    pde(
        "CRC 1, 10.10: potential hyperbolic heat equation tau0 u_x**l u_tt + u_t = k0 u_x**n u_xx",
        "tau0*Derivative(u(x, t), x)**l*Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - k0*Derivative(u(x, t), x)**n*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("(l + n)*x", "2*l*t", "(l + n + 2)*u"),
        ],
        f"{CRC1}, section 10.10, p. 164",
        note="classified by contact symmetries (generating functions U); the cases listed are point "
        "symmetries; l, n generic. The book's U4 gives (2l - n) x d/dx + 2l t d/dt + (2l - n - 2) u "
        "d/du, which is not a symmetry (l = 1, n = 0); the invariance condition gives l + n for 2l - n "
        "and agrees with the book for l = 0 (case 3.4)",
    ),
    pde(
        "CRC 1, 10.10: potential hyperbolic heat equation tau0 exp(l u_x) u_tt + u_t = k0 exp(m u_x) u_xx",
        "tau0*exp(l*Derivative(u(x, t), x))*Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - k0*exp(m*Derivative(u(x, t), x))*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("(l + m)*x", "2*l*t", "(l + m)*u + 2*x"),
        ],
        f"{CRC1}, section 10.10, p. 164",
        note="classified by contact symmetries (generating functions U); the cases listed are point "
        "symmetries. The book's U4 gives (2l - m) x d/dx + 2l t d/dt + ((2l - m) u - 2x) d/du, not a "
        "symmetry; the invariance condition gives l + m for 2l - m and + 2x, as case 3.5 for l = 0",
    ),
    pde(
        "CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (k(u) u_x)_x",
        "Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - Derivative(k(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        2,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
        ],
        f"{CRC1}, section 10.11, p. 169",
        note="k arbitrary (Oron, Rosenau 1986)",
    ),
    pde(
        "CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam exp(nu u) u_x)_x",
        "Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - Derivative(lam*exp(nu*u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("nu*x", "0", "2"),
        ],
        f"{CRC1}, section 10.11, p. 169",
    ),
    pde(
        "CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**nu u_x)_x",
        "Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - Derivative(lam*(u(x, t) + mu)**nu*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("nu*x", "0", "2*(u + mu)"),
        ],
        f"{CRC1}, section 10.11, p. 169",
        note="nu generic; the book prints nu*X d/dx",
    ),
    pde(
        "CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**(-4/3) u_x)_x",
        "Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - Derivative(lam*(u(x, t) + mu)**Rational(-4, 3)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "0", "-3*(u + mu)/2"),
            ("-x**2", "0", "3*x*(u + mu)"),
        ],
        f"{CRC1}, section 10.11, p. 169",
    ),
    pde(
        "CRC 1, 10.11: hyperbolic heat equation u_tt + u_t = (lam (u + mu)**(-2) u_x)_x",
        "Derivative(u(x, t), (t, 2)) + Derivative(u(x, t), t) - Derivative(lam*(u(x, t) + mu)**(-2)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "0", "-(u + mu)"),
            ("0", "exp(-t)", "-exp(-t)*(u + mu)"),
        ],
        f"{CRC1}, section 10.11, p. 169",
    ),
    pde(
        "CRC 1, 11.1: w_s = 0",
        "Derivative(w(s, y), s)",
        ("s", "y"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("s*w", "0", "0"),
            ("0", "w", "0"),
            ("0", "0", "y"),
        ],
        f"{CRC1}, section 11.1, p. 177",
        note="xi(s, y, w) d/ds + psi(y, w) d/dy + phi(y, w) d/dw, arbitrary functions",
        u="w",
    ),
    pde(
        "CRC 1, 11.2: simplest transfer equation v_t = v v_x",
        "Derivative(v(x, t), t) - v(x, t)*Derivative(v(x, t), x)",
        ("x", "t"),
        INFINITE,
        [
            ("-v", "1", "0"),
            ("1", "0", "0"),
            ("-t", "0", "1"),
            ("-t*v", "t", "0"),
            ("v", "0", "0"),
        ],
        f"{CRC1}, section 11.2, p. 178",
        note="Katkov (1965); three arbitrary functions",
        u="v",
    ),
    pde(
        "CRC 1, 11.3: transfer equation u_t = h(u) u_x",
        "Derivative(u(x, t), t) - h(u(x, t))*Derivative(u(x, t), x)",
        ("x", "t"),
        INFINITE,
        [
            ("-h(u)", "1", "0"),
            ("1", "0", "0"),
            ("-t*Derivative(h(u), u)", "0", "1"),
        ],
        f"{CRC1}, section 11.3, p. 179",
        note="h arbitrary; three arbitrary functions",
    ),
    pde(
        "CRC 1, 11.6: generalized Hopf equation u_t + u u_x = (k(u) u_x)_x",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - Derivative(k(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        2,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
        ],
        f"{CRC1}, section 11.6, p. 184",
        note="k arbitrary (Katkov 1965)",
    ),
    pde(
        "CRC 1, 11.6: generalized Hopf equation u_t + u u_x = (u**(2 m) u_x)_x",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t)**(2*m)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("(2*m - 1)*x", "2*(m - 1)*t", "u"),
        ],
        f"{CRC1}, section 11.6, p. 185",
        note="m generic",
    ),
    pde(
        "CRC 1, 11.8: u_t + g u u_x - mu u_xx + b u_xxx = 0",
        "Derivative(u(x, t), t) + g*u(x, t)*Derivative(u(x, t), x) - mu*Derivative(u(x, t), (x, 2)) + b*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("g*t", "0", "1"),
        ],
        f"{CRC1}, section 11.8, p. 192",
        note="generalized KdV-Burgers equation, j = 0, m = 1 (Korobeinikov 1983); the book's gamma, beta are g, b",
    ),
    pde(
        "CRC 1, 11.8: u_t + g u_x - mu u_xx + b u_xxx = 0",
        "Derivative(u(x, t), t) + g*Derivative(u(x, t), x) - mu*Derivative(u(x, t), (x, 2)) + b*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "u"),
            ("x + 2*(g - mu**2/(3*b))*t", "3*t", "mu*(x - g*t)*u/(3*b)"),
        ],
        f"{CRC1}, section 11.8, p. 193",
        note="j = 0, m = 0: linear, the superposition of solutions besides. The book prints the "
        "u-component of X4 as -mu*(x + gamma*t)*u/(3*beta), a sign misprint: solving the "
        "determining equations for this form gives +mu*(x - gamma*t)*u/(3*beta)",
    ),
    pde(
        "CRC 1, 11.8: u_t + g u**m u_x - mu u_xx + b u_xxx = 0",
        "Derivative(u(x, t), t) + g*u(x, t)**m*Derivative(u(x, t), x) - mu*Derivative(u(x, t), (x, 2)) + b*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        2,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
        ],
        f"{CRC1}, section 11.8, p. 193",
        note="j = 0, m generic",
    ),
    pde(
        "CRC 1, 11.8: linearized KdV u_t + j u/(2t) + b u_xxx = 0",
        "Derivative(u(x, t), t) + j*u(x, t)/(2*t) + b*Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "1", "-j*u/(2*t)"),
            ("1", "0", "0"),
            ("x", "3*t", "0"),
            ("0", "0", "u"),
            ("0", "0", "x*t**(-j/2)"),
            ("0", "0", "t**(-j/2)"),
        ],
        f"{CRC1}, section 11.8, p. 193",
        note="gamma = mu = 0, j generic; linear",
    ),
    pde(
        "CRC 1, 11.8: cylindrical Burgers u_t + u/(2t) + u u_x - mu u_xx = 0",
        "Derivative(u(x, t), t) + 1*u(x, t)/(2*t) + 1*u(x, t)*Derivative(u(x, t), x) - mu*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        3,
        [
            ("1", "0", "0"),
            ("x", "2*t", "-u"),
            ("2*sqrt(t)", "0", "1/sqrt(t)"),
        ],
        f"{CRC1}, section 11.8, p. 194",
        note="j = 1, gamma = 1, beta = 0",
    ),
    pde(
        "CRC 1, 11.8: spherical Burgers u_t + u/t + u u_x - mu u_xx = 0",
        "Derivative(u(x, t), t) + 2*u(x, t)/(2*t) + 1*u(x, t)*Derivative(u(x, t), x) - mu*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        3,
        [
            ("1", "0", "0"),
            ("x", "2*t", "-u"),
            ("log(t)", "0", "1/t"),
        ],
        f"{CRC1}, section 11.8, p. 194",
        note="j = 2, gamma = 1, beta = 0",
    ),
    pde(
        "CRC 1, 11.10: u_t + u u_x + b u_ttt = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) + b*Derivative(u(x, t), (t, 3))",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "0", "u"),
        ],
        f"{CRC1}, section 11.10, p. 196",
        note="Kostin (1969); the book's beta is b. The book gives X3 = t d/dt + 3x d/dx + 2u d/du, "
        "which is not a symmetry (u_t and u*u_x scale as lambda, u_ttt as 1/lambda); the third "
        "symmetry is x d/dx + u d/du, the only scaling (t fixed)",
    ),
    pde(
        "CRC 1, 12.1: wave equation u_tt = u_xx",
        "Derivative(u(x, t), (t, 2)) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("t", "x", "0"),
            ("x", "t", "0"),
            ("0", "0", "u"),
            ("0", "0", "1"),
            ("t + x", "t + x", "0"),
        ],
        f"{CRC1}, section 12.1.2, p. 198",
        note="alpha1(t + x), alpha2(t - x), beta1, beta2 arbitrary (Ibragimov 1983)",
    ),
    pde(
        "CRC 1, 12.2: u_tt = c(x)**2 u_xx",
        "Derivative(u(x, t), (t, 2)) - (c(x))**2*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "0", "u"),
            ("0", "1", "0"),
        ],
        f"{CRC1}, section 12.2.1, p. 199",
        note="c arbitrary: u d/du, d/dt and the superposition of solutions (Bluman, Kumei 1987)",
    ),
    pde(
        "CRC 1, 12.2: u_tt = (A x + B)**(2 C) u_xx",
        "Derivative(u(x, t), (t, 2)) - ((A*x + B)**C)**2*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "0", "u"),
            ("0", "1", "0"),
            ("A*x + B", "A*(1 - C)*t", "A*C*u/2"),
            ("(A*x + B)*t", "(A*(1 - C)*t**2 + (A*x + B)**(2 - 2*C)/(A*(1 - C)))/2", "A*C*t*u/2"),
        ],
        f"{CRC1}, section 12.2.1, p. 200",
        note="case ii, C generic",
    ),
    pde(
        "CRC 1, 12.2: u_tt = (A x + B)**2 u_xx",
        "Derivative(u(x, t), (t, 2)) - (A*x + B)**2*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "0", "u"),
            ("0", "1", "0"),
            ("A*x + B", "0", "A*u/2"),
            ("(A*x + B)*t", "log(A*x + B)/A", "A*t*u/2"),
        ],
        f"{CRC1}, section 12.2.1, p. 200",
        note="case iii",
    ),
    pde(
        "CRC 1, 12.2: u_tt = A**2 exp(2 B x) u_xx",
        "Derivative(u(x, t), (t, 2)) - (A*exp(B*x))**2*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("0", "0", "u"),
            ("0", "1", "0"),
            ("A", "-A*B*t", "A*B*u/2"),
            ("A*t", "-(A*B*t**2 + exp(-2*B*x)/(A*B))/2", "A*B*t*u/2"),
        ],
        f"{CRC1}, section 12.2.1, p. 200",
        note="case iv",
    ),
    pde(
        "CRC 1, 12.3: z_xy = F(z)",
        "Derivative(z(x, y), x, y) - F(z(x, y))",
        ("x", "y"),
        3,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "-y", "0"),
        ],
        f"{CRC1}, section 12.3, p. 204",
        note="F arbitrary (Lie 1881)",
        u="z",
    ),
    pde(
        "CRC 1, 12.3: z_xy = z",
        "Derivative(z(x, y), x, y) - z(x, y)",
        ("x", "y"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "-y", "0"),
            ("0", "0", "z"),
        ],
        f"{CRC1}, section 12.3, p. 204",
        note="linear: and the superposition of solutions",
        u="z",
    ),
    pde(
        "CRC 1, 12.3: z_xy = z**(1 - s)",
        "Derivative(z(x, y), x, y) - z(x, y)**(1 - s)",
        ("x", "y"),
        4,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "-y", "0"),
            ("s*x", "s*y", "2*z"),
        ],
        f"{CRC1}, section 12.3, p. 204",
        note="s generic",
        u="z",
    ),
    pde(
        "CRC 1, 12.4: nonlinear wave equation u_tt = (phi(u) u_x)_x",
        "Derivative(u(x, t), (t, 2)) - Derivative(phi(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "t", "0"),
        ],
        f"{CRC1}, section 12.4.1, p. 208",
        note="phi arbitrary (Ames, Lohner, Adams 1981)",
    ),
    pde(
        "CRC 1, 12.4: nonlinear wave equation u_tt = (exp(u) u_x)_x",
        "Derivative(u(x, t), (t, 2)) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "t", "0"),
            ("x", "0", "2"),
        ],
        f"{CRC1}, section 12.4.1, p. 209",
    ),
    pde(
        "CRC 1, 12.4: nonlinear wave equation u_tt = (k u**sigma u_x)_x",
        "Derivative(u(x, t), (t, 2)) - Derivative(k*u(x, t)**sigma*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "t", "0"),
            ("x", "0", "2*u/sigma"),
        ],
        f"{CRC1}, section 12.4.1, p. 209",
        note="the book's epsilon = -+1 is k; sigma generic",
    ),
    pde(
        "CRC 1, 12.4: nonlinear wave equation u_tt = (k u**(-4/3) u_x)_x",
        "Derivative(u(x, t), (t, 2)) - Derivative(k*u(x, t)**Rational(-4, 3)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "t", "0"),
            ("x", "0", "-3*u/2"),
            ("x**2", "0", "-3*x*u"),
        ],
        f"{CRC1}, section 12.4.1, p. 209",
        note="the book's epsilon = -+1 is k",
    ),
    pde(
        "CRC 1, 12.4: nonlinear wave equation u_tt = (k u**(-4) u_x)_x",
        "Derivative(u(x, t), (t, 2)) - Derivative(k*u(x, t)**(-4)*Derivative(u(x, t), x), x)",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "t", "0"),
            ("0", "t**2", "t*u"),
            ("2*x", "0", "-u"),
        ],
        f"{CRC1}, section 12.4.1, p. 209",
        note=(
            "the book's epsilon = -+1 is k; its X5 = x d/dx - u d/du is a misprint "
            "for x d/dx - u/2 d/du, case 2 at sigma = -4"
        ),
    ),
    pde(
        "CRC 1, 12.4: v_tt = phi(v_x) v_xx",
        "Derivative(v(x, t), (t, 2)) - phi(Derivative(v(x, t), x))*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "t"),
            ("x", "t", "v"),
        ],
        f"{CRC1}, section 12.4.2, p. 213",
        note="phi arbitrary (Baikov, Gazizov 1989); Y5 = t d/dt + x d/dx + v d/dv (p. 213; p. 216 prints d/dx for x d/dx)",
        u="v",
    ),
    pde(
        "CRC 1, 12.4: v_tt = k exp(v_x) v_xx",
        "Derivative(v(x, t), (t, 2)) - k*exp(Derivative(v(x, t), x))*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        6,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "t"),
            ("x", "t", "v"),
            ("x", "0", "v + 2*x"),
        ],
        f"{CRC1}, section 12.4.2, p. 213",
        note="the book's epsilon = +-1 is k",
        u="v",
    ),
    pde(
        "CRC 1, 12.4: v_tt = k v_x**m v_xx",
        "Derivative(v(x, t), (t, 2)) - k*Derivative(v(x, t), x)**m*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        6,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "t"),
            ("x", "t", "v"),
            ("m*x", "0", "(m + 2)*v"),
        ],
        f"{CRC1}, section 12.4.2, p. 213",
        note="the book's epsilon = +-1 is k; m generic",
        u="v",
    ),
    pde(
        "CRC 1, 12.4: v_tt = k v_x**(-4) v_xx",
        "Derivative(v(x, t), (t, 2)) - k*Derivative(v(x, t), x)**(-4)*Derivative(v(x, t), (x, 2))",
        ("x", "t"),
        7,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "t"),
            ("x", "t", "v"),
            ("2*x", "0", "v"),
            ("0", "t**2", "t*v"),
        ],
        f"{CRC1}, section 12.4.2, p. 213",
        note="the book's epsilon = +-1 is k",
        u="v",
    ),
    pde(
        "CRC 1, 12.4: w_tt = F(w_xx)",
        "Derivative(w(x, t), (t, 2)) - F(Derivative(w(x, t), (x, 2)))",
        ("x", "t"),
        7,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="F arbitrary (Baikov, Gazizov 1989); X6 = t d/dt + x d/dx + 2w d/dw (Z6 on p. 216; p. 215 prints d/dt for t d/dt)",
        u="w",
    ),
    pde(
        "CRC 1, 12.4: w_tt = k exp(w_xx)",
        "Derivative(w(x, t), (t, 2)) - k*exp(Derivative(w(x, t), (x, 2)))",
        ("x", "t"),
        8,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
            ("x", "0", "2*w + x**2"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="the book's epsilon = +-1 is k",
        u="w",
    ),
    pde(
        "CRC 1, 12.4: w_tt = k w_xx**m",
        "Derivative(w(x, t), (t, 2)) - k*Derivative(w(x, t), (x, 2))**m",
        ("x", "t"),
        8,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
            ("(m - 1)*x", "0", "2*m*w"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="the book's epsilon = +-1 is k; m generic",
        u="w",
    ),
    pde(
        "CRC 1, 12.4: w_tt = k w_xx**(-3)",
        "Derivative(w(x, t), (t, 2)) - k*Derivative(w(x, t), (x, 2))**(-3)",
        ("x", "t"),
        9,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
            ("2*x", "0", "3*w"),
            ("0", "t**2", "t*w"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="the book's epsilon = +-1 is k",
        u="w",
    ),
    pde(
        "CRC 1, 12.4: w_tt = k w_xx**(-1/3)",
        "Derivative(w(x, t), (t, 2)) - k*Derivative(w(x, t), (x, 2))**Rational(-1, 3)",
        ("x", "t"),
        9,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
            ("2*x", "0", "w"),
            ("x**2", "0", "w*x"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="the book's epsilon = +-1 is k",
        u="w",
    ),
    pde(
        "CRC 1, 12.4: w_tt = k log(w_xx)",
        "Derivative(w(x, t), (t, 2)) - k*log(Derivative(w(x, t), (x, 2)))",
        ("x", "t"),
        8,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "t"),
            ("x", "t", "2*w"),
            ("0", "0", "t*x"),
            ("x", "0", "-k*t**2"),
        ],
        f"{CRC1}, section 12.4.3, p. 215",
        note="the book's epsilon = +-1 is k",
        u="w",
    ),
]

# The scalar equations of the PDEBench datasets (the systems need #21). PDEBench
# gives no symmetries: dimensions and generators are delierium's, the generators
# checked against the determining equations.
PDEBENCH = [
    pde(
        "PDEBench: advection u_t + b u_x = 0",
        "Derivative(u(x, t), t) + b*Derivative(u(x, t), x)",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "t", "0"),
            ("0", "0", "u"),
            ("0", "0", "x - b*t"),
        ],
        PDEBENCH_SOURCE,
        note="first order: any function of x - b t and u is a symmetry; PDEBench's beta is b",
    ),
    pde(
        "PDEBench: Fisher-KPP u_t = nu u_xx + rho u (1 - u)",
        "Derivative(u(x, t), t) - nu*Derivative(u(x, t), (x, 2)) - rho*u(x, t)*(1 - u(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        PDEBENCH_SOURCE,
        note="the 1D diffusion-reaction set; only the translations",
    ),
    pde(
        "PDEBench: diffusion-sorption u_t = D u_xx / (1 + c u**m)",
        "Derivative(u(x, t), t) - D*Derivative(u(x, t), (x, 2))/(1 + c*u(x, t)**m)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "0")],
        PDEBENCH_SOURCE,
        note="R(u) = 1 + c u**m with c = (1 - phi)/phi rho_s k n_f and m = n_f - 1 (Freundlich "
        "isotherm); the data use n_f = 0.874. u_t = K(u) u_xx, K generic: the translations "
        "and x d/dx + 2t d/dt",
    ),
]

# The scalar physical scenarios of APEBench with their default coefficients as
# exact fractions (#37). APEBench gives no symmetries: dimensions and
# generators are delierium's, the generators checked against the determining
# equations; the 2D versions of the 1D scenarios follow the exponax operators
# (derivatives direction by direction). Gray-Scott, Navier-Stokes and the
# multi channel Burgers need #21.
APEBENCH = [
    pde(
        "APEBench phy_adv: u_t = -1/4 u_x",
        "Derivative(u(x, t), t) + Derivative(u(x, t), x)/4",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "t", "0"),
            ("0", "0", "u"),
            ("0", "0", "x - t/4"),
        ],
        APEBENCH_SOURCE,
        note="first order: any function of x - t/4 and u is a symmetry",
    ),
    pde(
        "APEBench phy_diff: u_t = 1/125 u_xx",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2))/125",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "u"),
            ("x", "2*t", "0"),
            ("2*t/125", "0", "-x*u"),
            ("4*t*x/125", "4*t**2/125", "-(x**2 + 2*t/125)*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation; 6 generators plus the superposition of solutions (Lie 1881). "
        "Replaces the heat equation u_t = u_xx of Arrigo, section 3.2.1, and u_t = k0 u_xx of "
        "the CRC Handbook, Vol. 1, section 10.1, p. 103",
    ),
    pde(
        "APEBench phy_adv_diff: u_t = -1/4 u_x + 1/125 u_xx",
        "Derivative(u(x, t), t) + Derivative(u(x, t), x)/4 - Derivative(u(x, t), (x, 2))/125",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "u"),
            ("x + t/4", "2*t", "0"),
            ("2*t/125", "0", "-(x - t/4)*u"),
            ("4*t*(x - t/4)/125 + t**2/125", "4*t**2/125", "-((x - t/4)**2 + 2*t/125)*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation in the frame moving with x - t/4",
    ),
    pde(
        "APEBench phy_disp: u_t = 1/4000 u_xxx",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 3))/4000",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "u"), ("x", "3*t", "0")],
        APEBENCH_SOURCE,
        note="linear: the superposition of solutions besides",
    ),
    pde(
        "APEBench phy_hyp_diff: u_t = -3/40000 u_xxxx",
        "Derivative(u(x, t), t) + 3*Derivative(u(x, t), (x, 4))/40000",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "u"), ("x", "4*t", "0")],
        APEBENCH_SOURCE,
        note="linear: the superposition of solutions besides",
    ),
    pde(
        "APEBench phy_four: u_t = -2500 u_x + 80 u_xx + 1/40 u_xxx - 3/40000 u_xxxx",
        "Derivative(u(x, t), t) + 2500*Derivative(u(x, t), x) - 80*Derivative(u(x, t), (x, 2))"
        " - Derivative(u(x, t), (x, 3))/40 + 3*Derivative(u(x, t), (x, 4))/40000",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "u")],
        APEBENCH_SOURCE,
        note="linear, derivatives of mixed order: no scaling, the superposition of solutions",
    ),
    pde(
        "APEBench phy_burgers: u_t + 1/8 u u_x = 3/10000 u_xx",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x)/8"
        " - 3*Derivative(u(x, t), (x, 2))/10000",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("t/8", "0", "1"),
            ("x", "2*t", "-u"),
            ("t*x", "t**2", "8*x - t*u"),
        ],
        APEBENCH_SOURCE,
        note="phy_burgers_sc is the same equation in 1D. Replaces u_t + u u_x = u_xx of Arrigo, "
        "section 3.2.3, (3.49), (3.53)",
    ),
    pde(
        "APEBench phy_kdv: u_t = -6 u u_x - u_xxx - 1/8 u_xxxx",
        "Derivative(u(x, t), t) + 6*u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))"
        " + Derivative(u(x, t), (x, 4))/8",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("6*t", "0", "1")],
        APEBENCH_SOURCE,
        note="the KdV equation with a hyperdiffusion, which breaks its scaling symmetry",
    ),
    pde(
        "APEBench phy_ks: u_t = -1/2 u_x**2 - u_xx - u_xxxx",
        "Derivative(u(x, t), t) + Derivative(u(x, t), x)**2/2 + Derivative(u(x, t), (x, 2))"
        " + Derivative(u(x, t), (x, 4))",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1"), ("t", "0", "x")],
        APEBENCH_SOURCE,
        note="Kuramoto-Sivashinsky in combustion (gradient) form; u_x satisfies the "
        "conservative form. exponax subtracts the spatial mean of u_x**2, which only shifts u "
        "by a function of t",
    ),
    pde(
        "APEBench phy_ks_cons: u_t + 18/5 u u_x = -36/25 u_xx - 2/5 u_xxxx",
        "Derivative(u(x, t), t) + 18*u(x, t)*Derivative(u(x, t), x)/5"
        " + 36*Derivative(u(x, t), (x, 2))/25 + 2*Derivative(u(x, t), (x, 4))/5",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("18*t/5", "0", "1")],
        APEBENCH_SOURCE,
        note="Kuramoto-Sivashinsky, conservative form",
    ),
    pde(
        "APEBench phy_fisher: u_t = 1/250 u_xx + 20 u (1 - u)",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2))/250 - 20*u(x, t)*(1 - u(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        APEBENCH_SOURCE,
        note="Fisher-KPP; only the translations. Replaces u_t = u_xx + u(1 - u) of Arrigo, "
        "section 3.2.4, (3.68), Exercises 3.2, 5",
    ),
    pde(
        "APEBench phy_adv, 2D: u_t = -1/4 (u_x + u_y)",
        "Derivative(u(x, y, t), t) + (Derivative(u(x, y, t), x) + Derivative(u(x, y, t), y))/4",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "t", "0"),
            ("0", "0", "0", "x - t/4"),
            ("0", "0", "0", "y - t/4"),
        ],
        APEBENCH_SOURCE,
        note="first order: any function of x - t/4, y - t/4 and u is a symmetry",
    ),
    pde(
        "APEBench phy_diff, 2D: u_t = 1/125 Laplace u",
        "Derivative(u(x, y, t), t)"
        " - (Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))/125",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "2*t", "0"),
            ("y", "-x", "0", "0"),
            ("2*t/125", "0", "0", "-x*u"),
            ("4*t*x/125", "4*t*y/125", "4*t**2/125", "-(x**2 + y**2 + 4*t/125)*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation in the plane; 9 generators plus the superposition of solutions",
    ),
    pde(
        "APEBench phy_adv_diff, 2D: u_t = -1/4 (u_x + u_y) + 1/125 Laplace u",
        "Derivative(u(x, y, t), t) + (Derivative(u(x, y, t), x) + Derivative(u(x, y, t), y))/4"
        " - (Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))/125",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x + t/4", "y + t/4", "2*t", "0"),
            ("y - t/4", "t/4 - x", "0", "0"),
            ("2*t/125", "0", "0", "-(x - t/4)*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation in the frame moving with (x - t/4, y - t/4)",
    ),
    pde(
        "APEBench phy_disp, 2D: u_t = 1/4000 (u_xxx + u_yyy)",
        "Derivative(u(x, y, t), t)"
        " - (Derivative(u(x, y, t), (x, 3)) + Derivative(u(x, y, t), (y, 3)))/4000",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "3*t", "0"),
        ],
        APEBENCH_SOURCE,
        note="exponax applies the odd derivatives direction by direction: no rotation",
    ),
    pde(
        "APEBench phy_hyp_diff, 2D: u_t = -3/40000 (u_xxxx + u_yyyy)",
        "Derivative(u(x, y, t), t)"
        " + 3*(Derivative(u(x, y, t), (x, 4)) + Derivative(u(x, y, t), (y, 4)))/40000",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "4*t", "0"),
        ],
        APEBENCH_SOURCE,
        note="exponax's fourth order term has no mixed derivative: no rotation",
    ),
    pde(
        "APEBench phy_four, 2D: the four linear terms of phy_four in x and y",
        "Derivative(u(x, y, t), t) + 2500*(Derivative(u(x, y, t), x) + Derivative(u(x, y, t), y)) - 80*(Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))"
        " - (Derivative(u(x, y, t), (x, 3)) + Derivative(u(x, y, t), (y, 3)))/40 + 3*(Derivative(u(x, y, t), (x, 4)) + Derivative(u(x, y, t), (y, 4)))/40000",
        ("x", "y", "t"),
        INFINITE,
        [("1", "0", "0", "0"), ("0", "1", "0", "0"), ("0", "0", "1", "0"), ("0", "0", "0", "u")],
        APEBENCH_SOURCE,
        note="linear, derivatives of mixed order: the translations, u d/du and the superposition",
    ),
    pde(
        "APEBench phy_burgers_sc, 2D: u_t + 1/8 u (u_x + u_y) = 3/10000 Laplace u",
        "Derivative(u(x, y, t), t) + u(x, y, t)*(Derivative(u(x, y, t), x) + Derivative(u(x, y, t), y))/8"
        " - 3*(Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))/10000",
        ("x", "y", "t"),
        5,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("t/8", "t/8", "0", "1"),
            ("x", "y", "2*t", "-u"),
        ],
        APEBENCH_SOURCE,
        note="single channel Burgers; phy_burgers in 2D is a system for a vector u (#21)",
    ),
    pde(
        "APEBench phy_kdv, 2D: u_t = -6 u (u_x + u_y) - (u_xxx + u_yyy) - 1/8 (u_xxxx + u_yyyy)",
        "Derivative(u(x, y, t), t) + 6*u(x, y, t)*(Derivative(u(x, y, t), x) + Derivative(u(x, y, t), y))"
        " + Derivative(u(x, y, t), (x, 3)) + Derivative(u(x, y, t), (y, 3)) + (Derivative(u(x, y, t), (x, 4)) + Derivative(u(x, y, t), (y, 4)))/8",
        ("x", "y", "t"),
        4,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("6*t", "6*t", "0", "1"),
        ],
        APEBENCH_SOURCE,
        note="the translations and the Galilei boost along (1, 1)",
    ),
    pde(
        "APEBench phy_ks, 2D: u_t = -1/2 |grad u|**2 - Laplace u - (u_xxxx + u_yyyy)",
        "Derivative(u(x, y, t), t) + (Derivative(u(x, y, t), x)**2 + Derivative(u(x, y, t), y)**2)/2"
        " + Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)) + Derivative(u(x, y, t), (x, 4)) + Derivative(u(x, y, t), (y, 4))",
        ("x", "y", "t"),
        6,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "1"),
            ("t", "0", "0", "x"),
            ("0", "t", "0", "y"),
        ],
        APEBENCH_SOURCE,
        note="the fourth order term without mixed derivative breaks the rotation; exponax subtracts the spatial mean of the gradient norm, which only shifts u by a function of t",
    ),
    pde(
        "APEBench phy_fisher, 2D: u_t = 1/250 Laplace u + 20 u (1 - u)",
        "Derivative(u(x, y, t), t)"
        " - (Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))/250 - 20*u(x, y, t)*(1 - u(x, y, t))",
        ("x", "y", "t"),
        4,
        [("1", "0", "0", "0"), ("0", "1", "0", "0"), ("0", "0", "1", "0"), ("y", "-x", "0", "0")],
        APEBENCH_SOURCE,
        note="Fisher-KPP; the translations and the rotation",
    ),
    pde(
        "APEBench phy_mix_disp: u_t = 1/4000 (d/dx + d/dy) Laplace u",
        "Derivative(u(x, y, t), t)"
        " - (Derivative(u(x, y, t), (x, 3)) + Derivative(u(x, y, t), (x, 2), y) + Derivative(u(x, y, t), x, (y, 2)) + Derivative(u(x, y, t), (y, 3)))/4000",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "3*t", "0"),
        ],
        APEBENCH_SOURCE,
        note="spatially mixed dispersion (only 2D and 3D in APEBench)",
    ),
    pde(
        "APEBench phy_mix_hyp: u_t = -3/40000 Laplace(Laplace u)",
        "Derivative(u(x, y, t), t)"
        " + 3*(Derivative(u(x, y, t), (x, 4)) + 2*Derivative(u(x, y, t), (x, 2), (y, 2)) + Derivative(u(x, y, t), (y, 4)))/40000",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "4*t", "0"),
            ("y", "-x", "0", "0"),
        ],
        APEBENCH_SOURCE,
        note="spatially mixed hyperdiffusion (only 2D and 3D in APEBench); rotation invariant",
    ),
    pde(
        "APEBench phy_sh: u_t = 7/10 u - (1 + Laplace)**2 u + u**2 - u**3 in the plane",
        "Derivative(u(x, y, t), t) + 3*u(x, y, t)/10"
        " + 2*(Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))"
        " + Derivative(u(x, y, t), (x, 4)) + 2*Derivative(u(x, y, t), (x, 2), (y, 2))"
        " + Derivative(u(x, y, t), (y, 4)) - u(x, y, t)**2 + u(x, y, t)**3",
        ("x", "y", "t"),
        4,
        [("1", "0", "0", "0"), ("0", "1", "0", "0"), ("0", "0", "1", "0"), ("y", "-x", "0", "0")],
        APEBENCH_SOURCE,
        note="Swift-Hohenberg, reactivity 0.7, critical number 1 (only 2D and 3D in APEBench); "
        "translations and the rotation",
    ),
    pde(
        "APEBench phy_diag_diff: u_t = 1/1000 u_xx + 1/500 u_yy",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t), (x, 2))/1000"
        " - Derivative(u(x, y, t), (y, 2))/500",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "2*t", "0"),
            ("y/1000", "-x/500", "0", "0"),
            ("2*t/1000", "0", "0", "-x*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation in the plane after scaling y",
    ),
    pde(
        "APEBench phy_aniso_diff: u_t = div(A grad u), A = ((1/1000, 1/2000), (1/2000, 1/500))",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t), (x, 2))/1000"
        " - Derivative(u(x, y, t), x, y)/1000 - Derivative(u(x, y, t), (y, 2))/500",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "2*t", "0"),
            ("y/1000 - x/2000", "y/2000 - x/500", "0", "0"),
            ("2*t/1000", "2*t/2000", "0", "-x*u"),
        ],
        APEBENCH_SOURCE,
        note="the heat equation in the plane after a linear change of x, y; the rotation is "
        "A (y, -x), the Galilei boost 2t A e_x - x u d/du",
    ),
    pde(
        "APEBench phy_unbal_adv: u_t + 1/100 u_x - 1/25 u_y + 1/200 u_z = 0",
        "Derivative(u(x, y, z, t), t) + Derivative(u(x, y, z, t), x)/100"
        " - Derivative(u(x, y, z, t), y)/25 + Derivative(u(x, y, z, t), z)/200",
        ("x", "y", "z", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0", "0"),
            ("0", "0", "0", "1", "0"),
            ("0", "0", "0", "0", "u"),
            ("x", "y", "z", "t", "0"),
            ("0", "0", "0", "0", "x - t/100"),
        ],
        APEBENCH_SOURCE,
        note="3D: the default velocity (0.01, -0.04, 0.005) has three components; first order, "
        "any function of the characteristics is a symmetry",
    ),
]

# Gabel, Quax, Gavves (2024), table A1: evolution equations with generators
# (written [t, x, u] there), used to train a symmetry detector. The paper takes
# them from the handbooks and gives no dimensions: the dimensions are
# delierium's. Equations 4, 5 and 24 replace the CRC Handbook's entries (Vol. 1,
# 10.2, 10.3, 11.6) and keep its full algebras; 16 is Arrigo's heat equation
# with power source.
GABEL = [
    pde(
        "Gabel et al. 1: u_t = 1/10 u_xx",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2))/10",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "0"),
            ("2*t", "0", "-10*x*u"),
            ("0", "0", "u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="the superposition of solutions besides",
    ),
    pde(
        "Gabel et al. 2: u_t = u_xx",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "0"),
            ("2*t", "0", "-x*u"),
            ("0", "0", "u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="the superposition of solutions besides",
    ),
    pde(
        "Gabel et al. 3: u_t = 10 u_xx",
        "Derivative(u(x, t), t) - 10*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "0"),
            ("2*t", "0", "-x*u/10"),
            ("0", "0", "u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="the superposition of solutions besides",
    ),
    pde(
        "Gabel et al. 4: u_t = (exp(u) u_x)_x",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        4,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("x", "2*t", "0"),
            ("x", "0", "2"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="replaces the nonlinear heat equation of the CRC Handbook, Vol. 1, section 10.2, "
        "p. 110, which gives the full algebra",
    ),
    pde(
        "Gabel et al. 5: u_t = exp(u_x) u_xx",
        "Derivative(u(x, t), t) - exp(Derivative(u(x, t), x))*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("x", "2*t", "u"),
            ("0", "t", "-x"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="replaces the nonlinear filtration equation of the CRC Handbook, Vol. 1, "
        "section 10.3, p. 129, which gives the full algebra",
    ),
    pde(
        "Gabel et al. 6: u_t = exp(3 atan(u_x)) u_xx / (u_x**2 + 1)",
        "Derivative(u(x, t), t) - exp(3*atan(Derivative(u(x, t), x)))*Derivative(u(x, t), (x, 2))/(Derivative(u(x, t), x)**2 + 1)",
        ("x", "t"),
        5,
        [
            ("0", "0", "1"),
            ("x", "2*t", "u"),
            ("u", "3*t", "-x"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.3 with n = 3",
    ),
    pde(
        "Gabel et al. 7: u_t = atan(u_xx)",
        "Derivative(u(x, t), t) - atan(Derivative(u(x, t), (x, 2)))",
        ("x", "t"),
        5,
        [
            ("0", "0", "1"),
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "2*t", "2*u"),
            ("0", "0", "x"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="the paper gives d/du; the other generators and the dimension are those of the CRC Handbook, Vol. 1, 10.4, for arbitrary K(u_xx), p. 131: its case 5, K = arctan(w_xx), adds only a contact symmetry (p. 132)",
    ),
    pde(
        "Gabel et al. 8: u_t = (exp(u) u_x)_x + exp(-2u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) - exp(-2*u(x, t))",
        ("x", "t"),
        3,
        [
            ("3*x/2", "2*t", "1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5",
    ),
    pde(
        "Gabel et al. 9: u_t = (exp(u) u_x)_x + exp(-u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) - exp(-u(x, t))",
        ("x", "t"),
        3,
        [
            ("x", "t", "1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5",
    ),
    pde(
        "Gabel et al. 10: u_t = (exp(u) u_x)_x - exp(u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) + exp(u(x, t))",
        ("x", "t"),
        3,
        [
            ("0", "t", "-1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5",
    ),
    pde(
        "Gabel et al. 11: u_t = (exp(u) u_x)_x - exp(2u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) + exp(2*u(x, t))",
        ("x", "t"),
        3,
        [
            ("x/2", "2*t", "-1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5",
    ),
    pde(
        "Gabel et al. 12: u_t = (exp(u) u_x)_x + 1",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) - 1",
        ("x", "t"),
        4,
        [
            ("x", "0", "2"),
            ("0", "exp(-t)", "exp(-t)"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5",
    ),
    pde(
        "Gabel et al. 13: u_t = (exp(u) u_x)_x - 1",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x) + 1",
        ("x", "t"),
        4,
        [
            ("x", "0", "2"),
            ("0", "exp(t)", "-exp(t)"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="CRC Vol. 1, 10.5; the paper prints exp(t) d/dt + exp(-t) d/du, which does not solve the determining equations: exp(t) (d/dt - d/du)",
    ),
    pde(
        "Gabel et al. 14: u_t = u_xx - exp(u)",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + exp(u(x, t))",
        ("x", "t"),
        3,
        [
            ("x", "2*t", "-2"),
        ],
        f"{GABEL_SOURCE}, table A1",
    ),
    pde(
        "Gabel et al. 15: u_t = u_xx + 1/u",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - 1/u(x, t)",
        ("x", "t"),
        3,
        [
            ("x", "2*t", "u"),
        ],
        f"{GABEL_SOURCE}, table A1",
    ),
    pde(
        "Gabel et al. 17: u_t = u_xx - u**2",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + u(x, t)**2",
        ("x", "t"),
        3,
        [
            ("x", "2*t", "-2*u"),
        ],
        f"{GABEL_SOURCE}, table A1",
    ),
    pde(
        "Gabel et al. 18: u_t = u_xx + u",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - u(x, t)",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "2*t*u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="u = exp(t) v, v a solution of the heat equation",
    ),
    pde(
        "Gabel et al. 19: u_t = u_xx - u",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + u(x, t)",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "-2*t*u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="u = exp(-t) v, v a solution of the heat equation",
    ),
    pde(
        "Gabel et al. 20: u_t = u_xx + 1",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - 1",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "2*t"),
            ("0", "0", "u - t"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="u = v + t, v a solution of the heat equation; the paper prints the scaling as 2t d/dt + x d/dx + 2tu d/du, which does not solve the determining equations: 2t d/du",
    ),
    pde(
        "Gabel et al. 21: u_t = u_xx - 1",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) + 1",
        ("x", "t"),
        INFINITE,
        [
            ("x", "2*t", "-2*t"),
            ("0", "0", "u + t"),
            ("2*t", "0", "-x*t - x*u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="u = v - t, v a solution of the heat equation; the paper prints the scaling as 2t d/dt + x d/dx - 2tu d/du, which does not solve the determining equations: -2t d/du",
    ),
    pde(
        "Gabel et al. 22: u_t = u u_x + u_xx",
        "Derivative(u(x, t), t) - u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("x", "2*t", "-u"),
            ("t", "0", "-1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="Burgers",
    ),
    pde(
        "Gabel et al. 23: u_t = u_xx + u_x**2",
        "Derivative(u(x, t), t) - Derivative(u(x, t), (x, 2)) - Derivative(u(x, t), x)**2",
        ("x", "t"),
        INFINITE,
        [
            ("0", "0", "1"),
            ("x", "2*t", "0"),
            ("2*t", "0", "-x"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="potential Burgers, linearizable to the heat equation by u = log(w)",
    ),
    pde(
        "Gabel et al. 24: u_t = (exp(u) u_x)_x - u u_x",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x)"
        " - Derivative(exp(u(x, t))*Derivative(u(x, t), x), x)",
        ("x", "t"),
        3,
        [
            ("0", "1", "0"),
            ("1", "0", "0"),
            ("t + x", "t", "1"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="generalized Hopf equation; replaces the CRC Handbook, Vol. 1, section 11.6, "
        "p. 185, which gives the full algebra",
    ),
    pde(
        "Gabel et al. 25: u_t = u u_x + u_txx",
        "Derivative(u(x, t), t) - u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t), t, (x, 2))",
        ("x", "t"),
        3,
        [
            ("0", "t", "-u"),
        ],
        f"{GABEL_SOURCE}, table A1",
        note="Benjamin-Bona-Mahony type",
    ),
]

# ODEBench (d'Ascoli et al., ODEFormer, ICLR 2024): 63 autonomous systems
# x' = f(x), mostly from Strogatz, with symbolic constants c_i (the benchmark's
# values in the notes); systems that differ only in the constants are one entry.
# First order: the algebras are infinite. The generators besides d/dt are the
# affine ones (translations, scalings, linear maps) that solve the linearized
# symmetry condition, checked against delierium's determining equations.
ODEBENCH = [
    ode(
        "ODEBench 1: RC-circuit (charging capacitor)",
        "Derivative(x0(t), t) - (c0 - x0(t)/c1)/c2",
        INFINITE,
        [("1", "0"), ("0", "-c0*c1 + x0")],
        f"{ODEBENCH_SOURCE}, strogatz p.20",
        note="ODEBench values 1: c0 = 0.7, c1 = 1.2, c2 = 2.31",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 2: Population growth (naive)",
        "-c0*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0"), ("0", "x0")],
        f"{ODEBENCH_SOURCE}, strogatz p.22",
        note="ODEBench values 2: c0 = 0.23",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 3: Population growth with carrying capacity",
        "-c0*(1 - x0(t)/c1)*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.22",
        note="ODEBench values 3: c0 = 0.79, c1 = 74.3",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 4: RC-circuit with non-linear resistor (charging capacitor)",
        "Derivative(x0(t), t) + 1/2 - 1/(exp(c0 - x0(t)/c1) + 1)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.38",
        note="ODEBench values 4: c0 = 0.5, c1 = 0.96",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 5: Velocity of a falling object with air resistance",
        "-c0 + c1*x0(t)**2 + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.38",
        note="ODEBench values 5: c0 = 9.81, c1 = 0.0021175",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 6, 12: Autocatalysis with one fixed abundant chemical",
        "-c0*x0(t) + c1*x0(t)**2 + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.39",
        note="ODEBench values 6: c0 = 2.1, c1 = 0.5; 12: c0 = 1.8, c1 = 0.1107",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 7: Gompertz law for tumor growth",
        "-c0*x0(t)*log(c1*x0(t)) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.39",
        note="ODEBench values 7: c0 = 0.032, c1 = 2.29",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 8: Logistic equation with Allee effect",
        "-c0*(-1 + x0(t)/c2)*(1 - x0(t)/c1)*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.39",
        note="ODEBench values 8: c0 = 0.14, c1 = 130.0, c2 = 4.4",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 9: Language death model for two languages",
        "-c0*(1 - x0(t)) + c1*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0"), ("0", "-c0/(c0 + c1) + x0")],
        f"{ODEBENCH_SOURCE}, strogatz p.40",
        note="ODEBench values 9: c0 = 0.32, c1 = 0.28",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 10: Refined language death model for two languages",
        "-c0*(1 - x0(t))*x0(t)**c1 + (1 - c0)*(1 - x0(t))**c1*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.40",
        note="ODEBench values 10: c0 = 0.2, c1 = 1.2",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 11: Naive critical slowing down (statistical mechanics)",
        "x0(t)**3 + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0"), ("-2*t", "x0")],
        f"{ODEBENCH_SOURCE}, strogatz p.41",
        note="",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 13: Overdamped bead on a rotating hoop",
        "-c0*(c1*cos(x0(t)) - 1)*sin(x0(t)) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.63",
        note="ODEBench values 13: c0 = 0.0981, c1 = 9.7",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 14: Budworm outbreak model with predation",
        "-c0*(1 - x0(t)/c1)*x0(t) + c3*x0(t)**2/(c2**2 + x0(t)**2) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.75",
        note="ODEBench values 14: c0 = 0.78, c1 = 81.0, c2 = 21.2, c3 = 0.9",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 15: Budworm outbreak with predation (dimensionless)",
        "-c0*(1 - x0(t)/c1)*x0(t) + Derivative(x0(t), t) + x0(t)**2/(x0(t)**2 + 1)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.76",
        note="ODEBench values 15: c0 = 0.4, c1 = 95.0",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 16: Landau equation (typical time scale tau = 1)",
        "-c0*x0(t) + c1*x0(t)**3 + c2*x0(t)**5 + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.87",
        note="ODEBench values 16: c0 = 0.1, c1 = -0.04, c2 = 0.001",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 17: Logistic equation with harvesting/fishing",
        "-c0*(1 - x0(t)/c1)*x0(t) + c2 + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.89",
        note="ODEBench values 17: c0 = 0.4, c1 = 100.0, c2 = 0.3",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 18: Improved logistic equation with harvesting/fishing",
        "-c0*(1 - x0(t)/c1)*x0(t) + c2*x0(t)/(c3 + x0(t)) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.90",
        note="ODEBench values 18: c0 = 0.4, c1 = 100.0, c2 = 0.24, c3 = 50.0",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 19: Improved logistic equation with harvesting/fishing (dimensionless)",
        "c0*x0(t)/(c1 + x0(t)) - (1 - x0(t))*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.90",
        note="ODEBench values 19: c0 = 0.08, c1 = 0.8",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 20: Autocatalytic gene switching (dimensionless)",
        "-c0 + c1*x0(t) + Derivative(x0(t), t) - x0(t)**2/(x0(t)**2 + 1)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.91",
        note="ODEBench values 20: c0 = 0.1, c1 = 0.55",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 21: Dimensionally reduced SIR infection model for dead people (dimensionless)",
        "-c0 + c1*x0(t) + Derivative(x0(t), t) + exp(-x0(t))",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.92",
        note="ODEBench values 21: c0 = 1.2, c1 = 0.2",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 22: Hysteretic activation of a protein expression (positive feedback, basal promoter expression)",
        "-c0 - c1*x0(t)**5/(c2 + x0(t)**5) + c3*x0(t) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.93",
        note="ODEBench values 22: c0 = 1.4, c1 = 0.4, c2 = 123.0, c3 = 0.89",
        x="t",
        y="x0",
    ),
    ode(
        "ODEBench 23: Overdamped pendulum with constant driving torque/fireflies/Josephson junction (dimensionless)",
        "-c0 + sin(x0(t)) + Derivative(x0(t), t)",
        INFINITE,
        [("1", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.104",
        note="ODEBench values 23: c0 = 0.21",
        x="t",
        y="x0",
    ),
    odes(
        "ODEBench 24: Harmonic oscillator without damping",
        ["-x1(t) + Derivative(x0(t), t)", "c0*x0(t) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0"), ("0", "-x1/c0", "x0"), ("0", "x0", "x1")],
        f"{ODEBENCH_SOURCE}, strogatz p.126",
        note="ODEBench values 24: c0 = 2.1",
    ),
    odes(
        "ODEBench 25: Harmonic oscillator with damping",
        ["-x1(t) + Derivative(x0(t), t)", "c0*x0(t) + c1*x1(t) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0"), ("0", "-c1*x0/c0 - x1/c0", "x0"), ("0", "x0", "x1")],
        f"{ODEBENCH_SOURCE}, strogatz p.144",
        note="ODEBench values 25: c0 = 4.5, c1 = 0.43",
    ),
    odes(
        "ODEBench 26: Lotka-Volterra competition model (Strogatz version with sheeps and rabbits)",
        [
            "-(c0 - c1*x1(t) - x0(t))*x0(t) + Derivative(x0(t), t)",
            "-(c2 - x0(t) - x1(t))*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.157",
        note="ODEBench values 26: c0 = 3.0, c1 = 2.0, c2 = 2.0",
    ),
    odes(
        "ODEBench 27: Lotka-Volterra simple (as on Wikipedia)",
        [
            "-(c0 - c1*x1(t))*x0(t) + Derivative(x0(t), t)",
            "(c2 - c3*x0(t))*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, https://en.wikipedia.org/wiki/Lotka-Volterra_equations",
        note="ODEBench values 27: c0 = 1.84, c1 = 1.45, c2 = 3.0, c3 = 1.62",
    ),
    odes(
        "ODEBench 28: Pendulum without friction",
        ["-x1(t) + Derivative(x0(t), t)", "c0*sin(x0(t)) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.169",
        note="ODEBench values 28: c0 = 0.9",
    ),
    odes(
        "ODEBench 29: Dipole fixed point",
        ["-c0*x0(t)*x1(t) + Derivative(x0(t), t)", "x0(t)**2 - x1(t)**2 + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0"), ("-t", "x0", "x1")],
        f"{ODEBENCH_SOURCE}, strogatz p.181",
        note="ODEBench values 29: c0 = 0.65",
    ),
    odes(
        "ODEBench 30: RNA molecules catalyzing each others replication",
        [
            "-(-c0*x0(t)*x1(t) + x1(t))*x0(t) + Derivative(x0(t), t)",
            "-(-c0*x0(t)*x1(t) + x0(t))*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.187",
        note="ODEBench values 30: c0 = 1.61",
    ),
    odes(
        "ODEBench 31: SIR infection model only for healthy and sick",
        [
            "c0*x0(t)*x1(t) + Derivative(x0(t), t)",
            "-c0*x0(t)*x1(t) + c1*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.188",
        note="ODEBench values 31: c0 = 0.4, c1 = 0.314",
    ),
    odes(
        "ODEBench 32: Damped double well oscillator",
        ["-x1(t) + Derivative(x0(t), t)", "c0*x1(t) + x0(t)**3 - x0(t) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.190",
        note="ODEBench values 32: c0 = 0.18",
    ),
    odes(
        "ODEBench 33: Glider (dimensionless)",
        [
            "c0*x0(t)**2 + sin(x1(t)) + Derivative(x0(t), t)",
            "-x0(t) + Derivative(x1(t), t) + cos(x1(t))/x0(t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.190",
        note="ODEBench values 33: c0 = 0.08",
    ),
    odes(
        "ODEBench 34: Frictionless bead on a rotating hoop (dimensionless)",
        ["-x1(t) + Derivative(x0(t), t)", "-(-c0 + cos(x0(t)))*sin(x0(t)) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.191",
        note="ODEBench values 34: c0 = 0.93",
    ),
    odes(
        "ODEBench 35: Rotational dynamics of an object in a shear flow",
        [
            "-cos(x0(t))*cot(x1(t)) + Derivative(x0(t), t)",
            "-(c0*sin(x1(t))**2 + cos(x1(t))**2)*sin(x0(t)) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.194",
        note="ODEBench values 35: c0 = 4.2",
    ),
    odes(
        "ODEBench 36: Pendulum with non-linear damping, no driving (dimensionless)",
        [
            "-x1(t) + Derivative(x0(t), t)",
            "c0*x1(t)*cos(x0(t)) + x1(t) + sin(x0(t)) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.195",
        note="ODEBench values 36: c0 = 0.07",
    ),
    odes(
        "ODEBench 37: Van der Pol oscillator (standard form)",
        ["-x1(t) + Derivative(x0(t), t)", "c0*(x0(t)**2 - 1)*x1(t) + x0(t) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.200",
        note="ODEBench values 37: c0 = 0.43",
    ),
    odes(
        "ODEBench 38: Van der Pol oscillator (simplified form from Strogatz)",
        [
            "-c0*(-x0(t)**3/3 + x0(t) + x1(t)) + Derivative(x0(t), t)",
            "Derivative(x1(t), t) + x0(t)/c0",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.214",
        note="ODEBench values 38: c0 = 3.37",
    ),
    odes(
        "ODEBench 39: Glycolytic oscillator, e.g., ADP and F6P in yeast (dimensionless)",
        [
            "-c0*x1(t) - x0(t)**2*x1(t) + x0(t) + Derivative(x0(t), t)",
            "c0*x0(t) - c1 + x0(t)**2*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.207",
        note="ODEBench values 39: c0 = 2.4, c1 = 0.07",
    ),
    odes(
        "ODEBench 40: Duffing equation (weakly non-linear oscillation)",
        [
            "-x1(t) + Derivative(x0(t), t)",
            "-c0*(1 - x0(t)**2)*x1(t) + x0(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.217",
        note="ODEBench values 40: c0 = 0.886",
    ),
    odes(
        "ODEBench 41: Cell cycle model by Tyson for interaction between protein cdc2 and cyclin (dimensionless)",
        [
            "-c0*(c1 + x0(t)**2)*(-x0(t) + x1(t)) + x0(t) + Derivative(x0(t), t)",
            "-c2 + x0(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.238",
        note="ODEBench values 41: c0 = 15.3, c1 = 0.001, c2 = 0.3",
    ),
    odes(
        "ODEBench 42: Reduced model for chlorine dioxide-iodine-malonic acid rection (dimensionless)",
        [
            "-c0 + c1*x0(t)*x1(t)/(x0(t)**2 + 1) + x0(t) + Derivative(x0(t), t)",
            "-c2*(1 - x1(t)/(x0(t)**2 + 1))*x0(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.260",
        note="ODEBench values 42: c0 = 8.9, c1 = 4.0, c2 = 1.4",
    ),
    odes(
        "ODEBench 43: Driven pendulum with linear damping / Josephson junction (dimensionless)",
        ["-x1(t) + Derivative(x0(t), t)", "-c0 + c1*x1(t) + sin(x0(t)) + Derivative(x1(t), t)"],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.269",
        note="ODEBench values 43: c0 = 1.67, c1 = 0.64",
    ),
    odes(
        "ODEBench 44: Driven pendulum with quadratic damping (dimensionless)",
        [
            "-x1(t) + Derivative(x0(t), t)",
            "-c0 + c1*x1(t)*Abs(x1(t)) + sin(x0(t)) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.300",
        note="ODEBench values 44: c0 = 1.67, c1 = 0.64",
    ),
    odes(
        "ODEBench 45: Isothermal autocatalytic reaction model by Gray and Scott 1985 (dimensionless)",
        [
            "-c0*(1 - x0(t)) + x0(t)*x1(t)**2 + Derivative(x0(t), t)",
            "c1*x1(t) - x0(t)*x1(t)**2 + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.288",
        note="ODEBench values 45: c0 = 0.5, c1 = 0.02",
    ),
    odes(
        "ODEBench 46: Interacting bar magnets",
        [
            "-c0*sin(x0(t) - x1(t)) + sin(x0(t)) + Derivative(x0(t), t)",
            "c0*sin(x0(t) - x1(t)) + sin(x1(t)) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.289",
        note="ODEBench values 46: c0 = 0.33",
    ),
    odes(
        "ODEBench 47: Binocular rivalry model (no oscillations)",
        [
            "x0(t) + Derivative(x0(t), t) - 1/(exp(c0*x1(t) - c1) + 1)",
            "x1(t) + Derivative(x1(t), t) - 1/(exp(c0*x0(t) - c1) + 1)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.290",
        note="ODEBench values 47: c0 = 4.89, c1 = 1.4",
    ),
    odes(
        "ODEBench 48: Bacterial respiration model for nutrients and oxygen levels",
        [
            "-c0 + x0(t) + Derivative(x0(t), t) + x0(t)*x1(t)/(c1*x0(t)**2 + 1)",
            "-c2 + Derivative(x1(t), t) + x0(t)*x1(t)/(c1*x0(t)**2 + 1)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.293",
        note="ODEBench values 48: c0 = 18.3, c1 = 0.48, c2 = 11.23",
    ),
    odes(
        "ODEBench 49: Brusselator: hypothetical chemical oscillation model (dimensionless)",
        [
            "-c1*x0(t)**2*x1(t) + (c0 + 1)*x0(t) + Derivative(x0(t), t) - 1",
            "-c0*x0(t) + c1*x0(t)**2*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.296",
        note="ODEBench values 49: c0 = 3.03, c1 = 3.1",
    ),
    odes(
        "ODEBench 50: Chemical oscillator model by Schnackenberg 1979 (dimensionless)",
        [
            "-c0 - x0(t)**2*x1(t) + x0(t) + Derivative(x0(t), t)",
            "-c1 + x0(t)**2*x1(t) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.296",
        note="ODEBench values 50: c0 = 0.24, c1 = 1.43",
    ),
    odes(
        "ODEBench 51: Oscillator death model by Ermentrout and Kopell 1990",
        [
            "-c0 - sin(x1(t))*cos(x0(t)) + Derivative(x0(t), t)",
            "-c1 - sin(x1(t))*cos(x0(t)) + Derivative(x1(t), t)",
        ],
        ("x0", "x1"),
        INFINITE,
        [("1", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.301",
        note="ODEBench values 51: c0 = 1.432, c1 = 0.972",
    ),
    odes(
        "ODEBench 52: Maxwell-Bloch equations (laser dynamics)",
        [
            "-c0*(-x0(t) + x1(t)) + Derivative(x0(t), t)",
            "-c1*(x0(t)*x2(t) - x1(t)) + Derivative(x1(t), t)",
            "-c2*(-c3*x0(t)*x1(t) + c3 - x2(t) + 1) + Derivative(x2(t), t)",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.82",
        note="ODEBench values 52: c0 = 0.1, c1 = 0.21, c2 = 0.34, c3 = 3.1",
    ),
    odes(
        "ODEBench 53: Model for apoptosis (cell death)",
        [
            "-c0 + c4*x0(t) + c5*x0(t)*x1(t)/(c9 + x0(t)) + Derivative(x0(t), t)",
            "-c1*(c8 + x1(t))*x2(t) + c2*x1(t)/(c6 + x1(t)) + c3*x0(t)*x1(t)/(c7 + x1(t)) + Derivative(x1(t), t)",
            "c1*(c8 + x1(t))*x2(t) - c2*x1(t)/(c6 + x1(t)) - c3*x0(t)*x1(t)/(c7 + x1(t)) + Derivative(x2(t), t)",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, https://epubs.siam.org/doi/10.1137/20M1318043",
        note="ODEBench values 53: c0 = 0.1, c1 = 0.6, c2 = 0.2, c3 = 7.95, c4 = 0.05, c5 = 0.4, c6 = 0.1, c7 = 2.0, c8 = 0.1, c9 = 0.1",
    ),
    odes(
        "ODEBench 54, 55, 56: Lorenz equations in well-behaved periodic regime",
        [
            "-c0*(-x0(t) + x1(t)) + Derivative(x0(t), t)",
            "-c1*x0(t) + x0(t)*x2(t) + x1(t) + Derivative(x1(t), t)",
            "c2*x2(t) - x0(t)*x1(t) + Derivative(x2(t), t)",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.319",
        note="ODEBench values 54: c0 = 5.1, c1 = 12.0, c2 = 1.67; 55: c0 = 10.0, c1 = 99.96, c2 = 2.6666666666666665; 56: c0 = 10.0, c1 = 28.0, c2 = 2.6666666666666665",
    ),
    odes(
        "ODEBench 57, 58, 59: R\u00f6ssler attractor (stable fixed point)",
        [
            "-c3*(-x1(t) - x2(t)) + Derivative(x0(t), t)",
            "-c3*(c0*x1(t) + x0(t)) + Derivative(x1(t), t)",
            "-c3*(c1 + (-c2 + x0(t))*x2(t)) + Derivative(x2(t), t)",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, https://en.wikipedia.org/wiki/Rössler_attractor",
        note="ODEBench values 57: c0 = -0.2, c1 = 0.2, c2 = 5.7, c3 = 5.0; 58: c0 = 0.1, c1 = 0.2, c2 = 5.7, c3 = 5.0; 59: c0 = 0.2, c1 = 0.2, c2 = 5.7, c3 = 5.0",
    ),
    odes(
        "ODEBench 60: Aizawa attractor (chaotic)",
        [
            "c3*x1(t) - (-c1 + x2(t))*x0(t) + Derivative(x0(t), t)",
            "-c3*x0(t) - (-c1 + x2(t))*x1(t) + Derivative(x1(t), t)",
            "-c0*x2(t) - c2 - c5*x0(t)**3*x2(t) + (c4*x2(t) + 1)*(x0(t)**2 + x1(t)**2) + x2(t)**3/3 + Derivative(x2(t), t)",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, https://analogparadigm.com/downloads/alpaca_17.pdf",
        note="ODEBench values 60: c0 = 0.95, c1 = 0.7, c2 = 0.65, c3 = 3.5, c4 = 0.25, c5 = 0.1",
    ),
    odes(
        "ODEBench 61: Chen-Lee attractor; system for gyro motion with feedback control of rigid body (chaotic)",
        [
            "-c0*x0(t) + x1(t)*x2(t) + Derivative(x0(t), t)",
            "-c1*x1(t) - x0(t)*x2(t) + Derivative(x1(t), t)",
            "-c2*x2(t) + Derivative(x2(t), t) - x0(t)*x1(t)/c3",
        ],
        ("x0", "x1", "x2"),
        INFINITE,
        [("1", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, https://doi.org/10.1016/j.chaos.2003.12.034",
        note="ODEBench values 61: c0 = 5.0, c1 = -10.0, c2 = -3.8, c3 = 3.0",
    ),
    odes(
        "ODEBench 62: Binocular rivalry model with adaptation (oscillations)",
        [
            "x0(t) + Derivative(x0(t), t) - 1/(exp(c0*x2(t) + c1*x1(t) - c2) + 1)",
            "-c3*(x0(t) - x1(t)) + Derivative(x1(t), t)",
            "x2(t) + Derivative(x2(t), t) - 1/(exp(c0*x0(t) + c1*x3(t) - c2) + 1)",
            "-c3*(x2(t) - x3(t)) + Derivative(x3(t), t)",
        ],
        ("x0", "x1", "x2", "x3"),
        INFINITE,
        [("1", "0", "0", "0", "0")],
        f"{ODEBENCH_SOURCE}, strogatz p.295",
        note="ODEBench values 62: c0 = 0.89, c1 = 0.4, c2 = 1.4, c3 = 1.0",
    ),
    odes(
        "ODEBench 63: SEIR infection model (proportions)",
        [
            "c1*x0(t)*x2(t) + Derivative(x0(t), t)",
            "c0*x1(t) - c1*x0(t)*x2(t) + Derivative(x1(t), t)",
            "-c0*x1(t) + c2*x2(t) + Derivative(x2(t), t)",
            "-c2*x2(t) + Derivative(x3(t), t)",
        ],
        ("x0", "x1", "x2", "x3"),
        INFINITE,
        [
            ("1", "0", "0", "0", "0"),
            ("0", "0", "0", "0", "x0 + x1 + x2 + x3"),
            ("0", "0", "0", "0", "1"),
        ],
        f"{ODEBENCH_SOURCE}, https://de.wikipedia.org/wiki/SEIR-Modell",
        note="ODEBench values 63: c0 = 0.47, c1 = 0.28, c2 = 0.3",
    ),
]

# Ko, Kim, Lee (2024), tables 4 and 5: PDEs whose symmetries a neural network
# learns from data. The paper lists only the symmetries of a periodic domain
# (no scalings): the dimensions and the other generators are delierium's (the
# fourth of cKdV from Baumann's cylindrical KdV). Its Kuramoto-Sivashinsky
# equation is the catalogue's.
KO_KIM_LEE = [
    pde(
        "Ko, Kim, Lee: KdV u_t + u u_x + u_xxx = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        4,
        [("0", "1", "0"), ("x", "3*t", "-2*u"), ("1", "0", "0"), ("t", "0", "1")],
        f"{KO_KIM_LEE_SOURCE}, tables 4 and 5",
        note="replaces the KdV equation of Arrigo, Example 3.17, (3.89), which gives the full "
        "algebra; the paper leaves out the scaling (periodic domain)",
    ),
    pde(
        "Ko, Kim, Lee: Burgers u_t + u u_x - nu u_xx = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - nu*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("t", "0", "1"),
            ("x", "2*t", "-u"),
            ("t*x", "t**2", "x - t*u"),
        ],
        f"{KO_KIM_LEE_SOURCE}, tables 4 and 5",
        note="the paper gives the translations and the Galilei boost",
    ),
    pde(
        "Ko, Kim, Lee: nKdV exp(-t/t0) u_t + u u_x + u_xxx = 0",
        "exp(-t/t0)*Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x)"
        " + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("0", "exp(-t/t0)", "0"),
            ("t0*(exp(t/t0) - 1)", "0", "1"),
            ("x", "3*t0*(1 - exp(-t/t0))", "-2*u"),
        ],
        f"{KO_KIM_LEE_SOURCE}, tables 4 and 5, appendix D.3",
        note="KdV after t -> t0 (exp(t/t0) - 1); appendix D.3, (31)-(33), has d/dt = exp(t/t0) "
        "d/dt-hat and the generator exp(t/t0) d/dt, which does not solve the determining "
        "equations: exp(-t/t0), as in table 4",
    ),
    pde(
        "Ko, Kim, Lee: cKdV u_t + u u_x + u_xxx + u/(2(t + 1)) = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))"
        " + u(x, t)/(2*(t + 1))",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("2*sqrt(t + 1)", "0", "1/sqrt(t + 1)"),
            ("x", "3*(t + 1)", "-2*u"),
            ("x*sqrt(t + 1)/2", "(t + 1)**(3/2)", "(x - 4*(t + 1)*u)/(4*sqrt(t + 1))"),
        ],
        f"{KO_KIM_LEE_SOURCE}, tables 4 and 5",
        note="the cylindrical KdV shifted to t + 1 (Baumann p. 297 with u -> 6u); the paper "
        "gives the first two",
    ),
]

# EqWorld (Polyanin, Zhurov, Levitin), exact solutions of nonlinear PDEs:
# eqworld.ipmnet.ru/en/solutions/npde, 64 pages. Left out: the Schrodinger
# equations (complex, systems: #21), 3.2.1, 3.2.3, 3.2.4 and 4.2.3 (arbitrary
# functions of x, y; the Janet basis did not finish in 3 min), 1.3.1 (Burgers,
# the same as Gabel et al. 22). The pages give exact solutions and some their
# invariance (noted); dimensions and the other generators are delierium's.
# The unknown is w as on the pages; lam, be, sig, mu, al stand for the Greek
# letters.
EQWORLD = [
    pde(
        "EqWorld 1.1.1: w_t = w_xx + a w (1 - w). Fisher equation",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) - a*w(x, t)*(1 - w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1101.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.1.2: w_t = w_xx + a w - b w**3. Newell-Whitehead equation",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) - a*w(x, t) + b*w(x, t)**3",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1102.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.1.3: w_t = w_xx - w (1 - w)(a - w). FitzHugh-Nagumo equation",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) + w(x, t)*(1 - w(x, t))*(a - w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1103.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.1.4: w_t = w_xx + a w + b w**m",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) - a*w(x, t) - b*w(x, t)**m",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1104.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.1.5: w_t = w_xx + a + b exp(lam w)",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) - a - b*exp(lam*w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1105.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.1.6: w_t = w_xx + a w ln w",
        "Derivative(w(x, t), t) - Derivative(w(x, t), (x, 2)) - a*w(x, t)*log(w(x, t))",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "exp(a*t)*w"),
            ("exp(a*t)", "0", "-a*x*exp(a*t)*w/2"),
        ],
        f"{EQWORLD_SOURCE}/npde1106.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.1: w_t = a (w**m w_x)_x. Heat equation with a power-law nonlinearity",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**m*Derivative(w(x, t), x), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "0"), ("m*x", "0", "2*w")],
        f"{EQWORLD_SOURCE}/npde1201.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.2: w_t = a (w**m w_x)_x + b w",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**m*Derivative(w(x, t), x), x) - b*w(x, t)",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("m*x", "0", "2*w"),
            ("0", "exp(-b*m*t)", "b*exp(-b*m*t)*w"),
        ],
        f"{EQWORLD_SOURCE}/npde1202.pdf",
        note="the fourth generator: w = exp(b t) v, tau = exp(b m t) gives v_tau = a (v**m v_x)_x",
        u="w",
    ),
    pde(
        "EqWorld 1.2.3: w_t = a (w**m w_x)_x + b w**(m + 1)",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**m*Derivative(w(x, t), x), x) - b*w(x, t)**(m + 1)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "-m*t", "w")],
        f"{EQWORLD_SOURCE}/npde1203.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.4: w_t = a (w**m w_x)_x + b w**(1 - m)",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**m*Derivative(w(x, t), x), x) - b*w(x, t)**(1 - m)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("m*x", "m*t", "w")],
        f"{EQWORLD_SOURCE}/npde1204.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.5: w_t = a (w**(2n) w_x)_x + b w**(1 - n)",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**(2*n)*Derivative(w(x, t), x), x) - b*w(x, t)**(1 - n)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("3*n*x", "2*n*t", "2*w")],
        f"{EQWORLD_SOURCE}/npde1205.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.6: w_t = a (w**n w_x)_x + b w + c1 w**m + c2 w**k",
        "Derivative(w(x, t), t) - a*Derivative(w(x, t)**n*Derivative(w(x, t), x), x) - b*w(x, t) - c1*w(x, t)**m - c2*w(x, t)**k",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1206.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.7: w_t = a (exp(lam w) w_x)_x. Heat equation with a exponential nonlinearity",
        "Derivative(w(x, t), t) - a*Derivative(exp(lam*w(x, t))*Derivative(w(x, t), x), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "0"), ("lam*x", "0", "2")],
        f"{EQWORLD_SOURCE}/npde1207.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.8: w_t = a (exp(lam w) w_x)_x + b + c1 exp(be w) + c2 exp(sig w)",
        "Derivative(w(x, t), t) - a*Derivative(exp(lam*w(x, t))*Derivative(w(x, t), x), x) - b - c1*exp(be*w(x, t)) - c2*exp(sig*w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1208.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.9: w_t = [f(w) w_x]_x. Nonlinear heat equation of general form",
        "Derivative(w(x, t), t) - Derivative(f(w(x, t))*Derivative(w(x, t), x), x)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "0")],
        f"{EQWORLD_SOURCE}/npde1209.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.2.10: w_t = [f(w) w_x]_x + g(w). Nonlinear heat equation with a source of general form",
        "Derivative(w(x, t), t) - Derivative(f(w(x, t))*Derivative(w(x, t), x), x) - g(w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1210.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.3.2: w_t + sig w w_x = a w_xx + b0 + b1 w + b2 w**2 + b3 w**3",
        "Derivative(w(x, t), t) + sig*w(x, t)*Derivative(w(x, t), x) - a*Derivative(w(x, t), (x, 2)) - b0 - b1*w(x, t) - b2*w(x, t)**2 - b3*w(x, t)**3",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1302.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.3.3: w_t = x**(-n)[x**n f(w) w_x]_x + g(w)",
        "Derivative(w(x, t), t) - x**(-n)*Derivative(x**n*f(w(x, t))*Derivative(w(x, t), x), x) - g(w(x, t))",
        ("x", "t"),
        1,
        [("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1303.pdf",
        u="w",
    ),
    pde(
        "EqWorld 1.3.4: w_t = [f(w)(w_x)**n]_x + g(w)",
        "Derivative(w(x, t), t) - Derivative(f(w(x, t))*Derivative(w(x, t), x)**n, x) - g(w(x, t))",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde1304.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.1.1: w_tt = a w_xx + a w + b w**n. Klein-Gordon equation with a power-law nonlinearity",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(w(x, t), (x, 2)) - a*w(x, t) - b*w(x, t)**n",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("a*t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2101.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.1.2: w_tt = w_xx + a w**n + b w**(2n - 1). Klein-Gordon equation with a power-law nonlinearity",
        "Derivative(w(x, t), (t, 2)) - Derivative(w(x, t), (x, 2)) - a*w(x, t)**n - b*w(x, t)**(2*n - 1)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2102.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.1.3: w_tt = a**2 w_xx + b exp(be w). Modified Liouville equation",
        "Derivative(w(x, t), (t, 2)) - a**2*Derivative(w(x, t), (x, 2)) - b*exp(be*w(x, t))",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("a**2*t", "x", "0"), ("x", "t", "-2/be")],
        f"{EQWORLD_SOURCE}/npde2103.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.1.4: w_tt = w_xx + a exp(be w) + b exp(2 be w). Klein-Gordon equation with a exponential nonlinearity",
        "Derivative(w(x, t), (t, 2)) - Derivative(w(x, t), (x, 2)) - a*exp(be*w(x, t)) - b*exp(2*be*w(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2104.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.1.5: w_tt = a w_xx + b sinh(lam w). Sinh-Gordon equation",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(w(x, t), (x, 2)) - b*sinh(lam*w(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("a*t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2105.pdf",
        note="sinh-Gordon",
        u="w",
    ),
    pde(
        "EqWorld 2.1.6: w_tt = a w_xx + b sin(lam w). Sine-Gordon equation",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(w(x, t), (x, 2)) - b*sin(lam*w(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("a*t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2106.pdf",
        note="sine-Gordon",
        u="w",
    ),
    pde(
        "EqWorld 2.1.7: w_tt = w_xx + f(w). Nonlinear Klein-Gordon equation",
        "Derivative(w(x, t), (t, 2)) - Derivative(w(x, t), (x, 2)) - f(w(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("t", "x", "0")],
        f"{EQWORLD_SOURCE}/npde2107.pdf",
        note="f arbitrary; EqWorld: w(+-x + C1, +-t + C2) and the Lorentz boost",
        u="w",
    ),
    pde(
        "EqWorld 2.2.1: w_tt = a (w w_x)_x",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(w(x, t)*Derivative(w(x, t), x), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "0", "2*w"), ("0", "t", "-2*w")],
        f"{EQWORLD_SOURCE}/npde2201.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.2: w_tt = a (w**n w_x)_x + b w**k",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(w(x, t)**n*Derivative(w(x, t), x), x) - b*w(x, t)**k",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("(n + 1 - k)*x", "(1 - k)*t", "2*w")],
        f"{EQWORLD_SOURCE}/npde2202.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.3: w_tt = a (exp(lam w) w_x)_x",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(exp(lam*w(x, t))*Derivative(w(x, t), x), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "t", "0"), ("lam*x", "0", "2")],
        f"{EQWORLD_SOURCE}/npde2203.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.4: w_tt = a x**(-n)(x**n w_x)_x + f(w)",
        "Derivative(w(x, t), (t, 2)) - a*x**(-n)*Derivative(x**n*Derivative(w(x, t), x), x) - f(w(x, t))",
        ("x", "t"),
        1,
        [("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde2204.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.5: w_tt = [a (x + b)**n w_x]_x + f(w)",
        "Derivative(w(x, t), (t, 2)) - Derivative(a*(x + b)**n*Derivative(w(x, t), x), x) - f(w(x, t))",
        ("x", "t"),
        1,
        [("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde2205.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.6: w_tt = a (exp(lam x) w_x)_x + f(w)",
        "Derivative(w(x, t), (t, 2)) - a*Derivative(exp(lam*x)*Derivative(w(x, t), x), x) - f(w(x, t))",
        ("x", "t"),
        1,
        [("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde2206.pdf",
        u="w",
    ),
    pde(
        "EqWorld 2.2.7: w_tt = [f(w) w_x]_x",
        "Derivative(w(x, t), (t, 2)) - Derivative(f(w(x, t))*Derivative(w(x, t), x), x)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "t", "0")],
        f"{EQWORLD_SOURCE}/npde2207.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.1: w_xx + w_yy = a w + b w**n",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*w(x, y) - b*w(x, y)**n",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3101.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.2: w_xx + w_yy = a w**n + b w**(2n - 1)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*w(x, y)**n - b*w(x, y)**(2*n - 1)",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3102.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.3: w_xx + w_yy = a exp(be w)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*exp(be*w(x, y))",
        ("x", "y"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0"), ("x", "y", "-2/be")],
        f"{EQWORLD_SOURCE}/npde3103.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.4: w_xx + w_yy = a exp(be w) + b exp(2 be w)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*exp(be*w(x, y)) - b*exp(2*be*w(x, y))",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3104.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.5: w_xx + w_yy = a w ln(be w)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*w(x, y)*log(be*w(x, y))",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3105.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.6: w_xx + w_yy = a sin(be w)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - a*sin(be*w(x, y))",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3106.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.1.7: w_xx + w_yy = f(w)",
        "Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2)) - f(w(x, y))",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde3107.pdf",
        note="f arbitrary; EqWorld: translations and rotations",
        u="w",
    ),
    pde(
        "EqWorld 3.2.2: a w_xx + (b exp(mu y) w_y)_y = f(w). Anisotropic heat (diffusion) equation",
        "a*Derivative(w(x, y), (x, 2)) + Derivative(b*exp(mu*y)*Derivative(w(x, y), y), y) - f(w(x, y))",
        ("x", "y"),
        1,
        [("1", "0", "0")],
        f"{EQWORLD_SOURCE}/npde3202.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.3.1: w_xx + [(al w + be) w_y]_y = 0. Stationary Khokhlov-Zabolotskaya equation",
        "Derivative(w(x, y), (x, 2)) + Derivative((al*w(x, y) + be)*Derivative(w(x, y), y), y)",
        ("x", "y"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "y", "0"), ("0", "y", "2*w + 2*be/al")],
        f"{EQWORLD_SOURCE}/npde3301.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.3.2: w_xx + (a exp(be w) w_y)_y = 0. Anisotropic heat (diffusion) equation",
        "Derivative(w(x, y), (x, 2)) + Derivative(a*exp(be*w(x, y))*Derivative(w(x, y), y), y)",
        ("x", "y"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "y", "0"), ("0", "y", "2/be")],
        f"{EQWORLD_SOURCE}/npde3302.pdf",
        u="w",
    ),
    pde(
        "EqWorld 3.3.3: [f(w) w_x]_x + [g(w) w_y]_y = 0. Anisotropic heat (diffusion) equation",
        "Derivative(f(w(x, y))*Derivative(w(x, y), x), x) + Derivative(g(w(x, y))*Derivative(w(x, y), y), y)",
        ("x", "y"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "y", "0")],
        f"{EQWORLD_SOURCE}/npde3303.pdf",
        u="w",
    ),
    pde(
        "EqWorld 4.1.1: a w_x w_xx + w_yy = 0. Equation of steady transonic gas flow",
        "a*Derivative(w(x, y), x)*Derivative(w(x, y), (x, 2)) + Derivative(w(x, y), (y, 2))",
        ("x", "y"),
        6,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("0", "0", "y"),
            ("x", "0", "3*w"),
            ("0", "y", "-2*w"),
        ],
        f"{EQWORLD_SOURCE}/npde4101.pdf",
        note="EqWorld: C1**(-3) C2**2 w(C1 x + C3, C2 y + C4) + C5 y + C6",
        u="w",
    ),
    pde(
        "EqWorld 4.1.2: w_yy + a y**(-1) w_y + b w_x w_xx = 0. Equation of steady transonic gas flow",
        "Derivative(w(x, y), (y, 2)) + a*Derivative(w(x, y), y)/y + b*Derivative(w(x, y), x)*Derivative(w(x, y), (x, 2))",
        ("x", "y"),
        5,
        [
            ("1", "0", "0"),
            ("0", "0", "1"),
            ("0", "0", "y**(1 - a)"),
            ("x", "0", "3*w"),
            ("0", "y", "-2*w"),
        ],
        f"{EQWORLD_SOURCE}/npde4102.pdf",
        note="EqWorld: C1**(-3) C2**2 w(C1 x + C3, C2 y) + C4 y**(1 - a) + C5",
        u="w",
    ),
    pde(
        "EqWorld 4.2.1: (w_xy)**2 - w_xx w_yy = 0. Homogeneous Monge-Ampere equation",
        "Derivative(w(x, y), x, y)**2 - Derivative(w(x, y), (x, 2))*Derivative(w(x, y), (y, 2))",
        ("x", "y"),
        15,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("x", "0", "0"),
            ("y", "0", "0"),
            ("w", "0", "0"),
            ("0", "x", "0"),
            ("0", "y", "0"),
            ("0", "w", "0"),
            ("0", "0", "x"),
            ("0", "0", "y"),
            ("0", "0", "w"),
            ("x**2", "x*y", "x*w"),
            ("x*y", "y**2", "y*w"),
            ("x*w", "y*w", "w**2"),
        ],
        f"{EQWORLD_SOURCE}/npde4201.pdf",
        note="the projective group of R**3",
        u="w",
    ),
    pde(
        "EqWorld 4.2.2: (w_xy)**2 - w_xx w_yy = A. Nonhomogeneous Monge-Ampere equation",
        "Derivative(w(x, y), x, y)**2 - Derivative(w(x, y), (x, 2))*Derivative(w(x, y), (y, 2)) - A",
        ("x", "y"),
        9,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "1"),
            ("0", "0", "x"),
            ("0", "0", "y"),
            ("x", "-y", "0"),
            ("y", "0", "0"),
            ("0", "x", "0"),
            ("x", "y", "2*w"),
        ],
        f"{EQWORLD_SOURCE}/npde4202.pdf",
        u="w",
    ),
    pde(
        "EqWorld 5.1.1: w_t + w_xxx - 6 w w_x = 0. Korteweg-de Vries equation",
        "Derivative(w(x, t), t) + Derivative(w(x, t), (x, 3)) - 6*w(x, t)*Derivative(w(x, t), x)",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "3*t", "-2*w"), ("-6*t", "0", "1")],
        f"{EQWORLD_SOURCE}/npde5101.pdf",
        note="EqWorld: C1**2 w(C1 x + 6 C1 C2 t + C3, C1**3 t + C4) + C2",
        u="w",
    ),
    pde(
        "EqWorld 5.1.2: w_t + w_xxx - 6 w w_x + (2 t)**(-1) w = 0. Cylindrical Korteweg-de Vries equation",
        "Derivative(w(x, t), t) + Derivative(w(x, t), (x, 3)) - 6*w(x, t)*Derivative(w(x, t), x) + w(x, t)/(2*t)",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("x", "3*t", "-2*w"),
            ("x*sqrt(t)/2", "t**(3/2)", "-(x + 24*t*w)/(24*sqrt(t))"),
            ("2*sqrt(t)", "0", "-1/(6*sqrt(t))"),
        ],
        f"{EQWORLD_SOURCE}/npde5102.pdf",
        note="the generators of Baumann's cylindrical KdV with w = -u",
        u="w",
    ),
    pde(
        "EqWorld 5.1.3: w_t + w_xxx + 6 sig w**2 w_x = 0. Modified Korteweg-de Vries equation",
        "Derivative(w(x, t), t) + Derivative(w(x, t), (x, 3)) + 6*sig*w(x, t)**2*Derivative(w(x, t), x)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "3*t", "-w")],
        f"{EQWORLD_SOURCE}/npde5103.pdf",
        u="w",
    ),
    pde(
        "EqWorld 5.1.4: w_t + w_xxx + f(w) w_x = 0. Generalized Korteweg-de Vries equation",
        "Derivative(w(x, t), t) + Derivative(w(x, t), (x, 3)) + f(w(x, t))*Derivative(w(x, t), x)",
        ("x", "t"),
        2,
        [("1", "0", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde5104.pdf",
        u="w",
    ),
    pde(
        "EqWorld 5.1.5: w_y w_xy - w_x w_yy = a w_yyy. Hydrodynamic boundary layer equation",
        "Derivative(w(x, y), y)*Derivative(w(x, y), x, y) - Derivative(w(x, y), x)*Derivative(w(x, y), (y, 2)) - a*Derivative(w(x, y), (y, 3))",
        ("x", "y"),
        INFINITE,
        [("1", "0", "0"), ("0", "0", "1"), ("0", "x**2", "0"), ("x", "y", "0"), ("0", "y", "-w")],
        f"{EQWORLD_SOURCE}/npde5105.pdf",
        note="EqWorld: C1 w(C2 x + C3, C1 C2 y + phi(x)) + C4, phi arbitrary; the entry has phi = x**2",
        u="w",
    ),
    pde(
        "EqWorld 5.1.6: w_y w_xy - w_x w_yy = a w_yyy + f(x). Boundary layer equation with pressure gradient",
        "Derivative(w(x, y), y)*Derivative(w(x, y), x, y) - Derivative(w(x, y), x)*Derivative(w(x, y), (y, 2)) - a*Derivative(w(x, y), (y, 3)) - f(x)",
        ("x", "y"),
        INFINITE,
        [("0", "0", "1"), ("0", "x**2", "0"), ("0", "1", "0")],
        f"{EQWORLD_SOURCE}/npde5106.pdf",
        note="f arbitrary; EqWorld: +-w(x, +-y + phi(x)) + C, phi arbitrary; the entry has phi = x**2 and 1",
        u="w",
    ),
    pde(
        "EqWorld 6.1.1: w_tt + (w w_x)_x + w_xxxx = 0. Boussinesq equation",
        "Derivative(w(x, t), (t, 2)) + Derivative(w(x, t)*Derivative(w(x, t), x), x) + Derivative(w(x, t), (x, 4))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "2*t", "-2*w")],
        f"{EQWORLD_SOURCE}/npde6101.pdf",
        note="EqWorld: C1**2 w(C1 x + C2, +-C1**2 t + C3). Replaces the Boussinesq equation of Arrigo, Example 3.18, (3.94)",
        u="w",
    ),
    pde(
        "EqWorld 6.1.2: w_y (Laplace w)_x - w_x (Laplace w)_y = a Laplace Laplace w. Equation of motion of viscous fluid; it is obtained from the Navier-Stokes equations",
        "Derivative(w(x, y), y)*(Derivative(w(x, y), (x, 3)) + Derivative(w(x, y), x, (y, 2))) - Derivative(w(x, y), x)*(Derivative(w(x, y), (x, 2), y) + Derivative(w(x, y), (y, 3))) - a*(Derivative(w(x, y), (x, 4)) + 2*Derivative(w(x, y), (x, 2), (y, 2)) + Derivative(w(x, y), (y, 4)))",
        ("x", "y"),
        5,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "1"), ("x", "y", "0"), ("y", "-x", "0")],
        f"{EQWORLD_SOURCE}/npde6102.pdf",
        note="stream function of the plane Navier-Stokes equations; EqWorld: scalings, translations, rotations and w + C4",
        u="w",
    ),
]

# Kahlmeyer, Merk, Giesen (AAAI 2025): systems y' = f(t, y) with a generator
# (0, eta) found by symbolic regression (github.com/kahlmeyer94/ODESym,
# ode_examples.py: load_examples and load_examples_indep). First order: the
# algebras are infinite.
ODESYM = [
    odes(
        "Kahlmeyer et al. example1: y' = (y0*(t + y1/y0)**2, t**2*y0)",
        [
            "-(t + y1(t)/y0(t))**2*y0(t) + Derivative(y0(t), t)",
            "-t**2*y0(t) + Derivative(y1(t), t)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "y0", "y1")],
        f"{ODESYM_SOURCE}, load_examples, example1",
    ),
    odes(
        "Kahlmeyer et al. example2: y' = (y0**2*y1*exp(1/y0), t*exp(-1/y0))",
        [
            "-y0(t)**2*y1(t)*exp(1/y0(t)) + Derivative(y0(t), t)",
            "-t*exp(-1/y0(t)) + Derivative(y1(t), t)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "y0**2", "y1")],
        f"{ODESYM_SOURCE}, load_examples, example2",
    ),
    odes(
        "Kahlmeyer et al. example3: y' = (t*y0*(y1 - log(y0)), t + y1 - log(y0))",
        [
            "-t*(y1(t) - log(y0(t)))*y0(t) + Derivative(y0(t), t)",
            "-t - y1(t) + log(y0(t)) + Derivative(y1(t), t)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "y0", "1")],
        f"{ODESYM_SOURCE}, load_examples, example3",
    ),
    odes(
        "Kahlmeyer et al. example4: y' = ((2*y0 + y1*exp(-y0/t**2))/t, y1)",
        [
            "Derivative(y0(t), t) - (2*y0(t) + y1(t)*exp(-y0(t)/t**2))/t",
            "-y1(t) + Derivative(y1(t), t)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "t**2", "y1")],
        f"{ODESYM_SOURCE}, load_examples, example4",
    ),
    odes(
        "Kahlmeyer et al. example5: y' = (y0*(t - log(y0)*tan(t)), -y1*log(y0)*tan(t) + y1)",
        [
            "-(t - log(y0(t))*tan(t))*y0(t) + Derivative(y0(t), t)",
            "y1(t)*log(y0(t))*tan(t) - y1(t) + Derivative(y1(t), t)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "y0*cos(t)", "y1*cos(t)")],
        f"{ODESYM_SOURCE}, load_examples, example5",
    ),
    odes(
        "Kahlmeyer et al. example6: y' = (y0*(t*y1/y0 + 2*log(y0)/t), 2*y1*log(y0)/t)",
        [
            "-(t*y1(t)/y0(t) + 2*log(y0(t))/t)*y0(t) + Derivative(y0(t), t)",
            "Derivative(y1(t), t) - 2*y1(t)*log(y0(t))/t",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "t**2*y0", "t**2*y1")],
        f"{ODESYM_SOURCE}, load_examples, example6",
    ),
    odes(
        "Kahlmeyer et al. example7: y' = (y1*exp(-y0**2/(2*t**2))/y0 + y0/(2*t), -y0**2*y1/(2*t**3))",
        [
            "Derivative(y0(t), t) - y1(t)*exp(-y0(t)**2/(2*t**2))/y0(t) - y0(t)/(2*t)",
            "Derivative(y1(t), t) + y0(t)**2*y1(t)/(2*t**3)",
        ],
        ("y0", "y1"),
        INFINITE,
        [("0", "t/y0", "y1/t")],
        f"{ODESYM_SOURCE}, load_examples, example7",
    ),
    odes(
        "Kahlmeyer et al. example8: y' = (exp(-t)*sin(y1), exp(-t)*sin(y0))",
        ["Derivative(y0(t), t) - exp(-t)*sin(y1(t))", "Derivative(y1(t), t) - exp(-t)*sin(y0(t))"],
        ("y0", "y1"),
        INFINITE,
        [("0", "sin(y1)", "sin(y0)")],
        f"{ODESYM_SOURCE}, load_examples, example8",
    ),
    odes(
        "Kahlmeyer et al. example9: y' = (t*y1*sin(y0), t*sin(y0))",
        ["-t*y1(t)*sin(y0(t)) + Derivative(y0(t), t)", "-t*sin(y0(t)) + Derivative(y1(t), t)"],
        ("y0", "y1"),
        INFINITE,
        [("0", "y1*sin(y0)", "sin(y0)")],
        f"{ODESYM_SOURCE}, load_examples, example9",
    ),
    odes(
        "Kahlmeyer et al. example10: y' = (t*log(y1), t*y0**2)",
        ["-t*log(y1(t)) + Derivative(y0(t), t)", "-t*y0(t)**2 + Derivative(y1(t), t)"],
        ("y0", "y1"),
        INFINITE,
        [("0", "log(y1)", "y0**2")],
        f"{ODESYM_SOURCE}, load_examples, example10",
    ),
    odes(
        "Kahlmeyer et al. example1 (independent): y' = (y1*log(t), y0*log(t))",
        ["-y1(t)*log(t) + Derivative(y0(t), t)", "-y0(t)*log(t) + Derivative(y1(t), t)"],
        ("y0", "y1"),
        INFINITE,
        [("0", "y1", "y0")],
        f"{ODESYM_SOURCE}, load_examples_indep, example1",
    ),
    odes(
        "Kahlmeyer et al. example2 (independent): y' = (t*sqrt(y0), t*y0*y1)",
        ["-t*sqrt(y0(t)) + Derivative(y0(t), t)", "-t*y0(t)*y1(t) + Derivative(y1(t), t)"],
        ("y0", "y1"),
        INFINITE,
        [("0", "sqrt(y0)", "y0*y1")],
        f"{ODESYM_SOURCE}, load_examples_indep, example2",
    ),
]

# PINNacle (Hao et al., NeurIPS 2024, github.com/i207M/PINNacle, src/pde/): the
# scalar PDEs with their default coefficients. Left out: coefficients from data
# files or piecewise (Heat2D_VaryingCoef, Wave2D_Heterogeneous,
# Poisson2D_ManyArea, Poisson3D_ComplexGeometry), Heat2D_ComplexGeometry (the
# heat equation in the plane), the inverse problems and the systems (Burgers2D,
# Gray-Scott, Navier-Stokes: #21). PINNacle gives no symmetries: dimensions and
# generators are delierium's.
PINNACLE = [
    ode(
        "PINNacle Poisson1D: u'' + sin(x) = 0",
        "Derivative(u(x), (x, 2)) + sin(x)",
        8,
        [
            ("1", "cos(x)"),
            ("0", "u - sin(x)"),
            ("0", "1"),
            ("0", "x"),
            ("x", "x*cos(x)"),
            ("u - sin(x)", "(u - sin(x))*cos(x)"),
            ("x**2", "x**2*cos(x) + x*(u - sin(x))"),
            ("x*(u - sin(x))", "x*(u - sin(x))*cos(x) + (u - sin(x))**2"),
        ],
        f"{PINNACLE_SOURCE}, poisson.py, a = 1",
        note="linear: v = u - sin(x) gives v'' = 0 and its 8 symmetries",
        y="u",
    ),
    pde(
        "PINNacle Burgers1D: u_t + u u_x = u_xx/(100 pi)",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t), (x, 2))/(100*pi)",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("t", "0", "1"),
            ("x", "2*t", "-u"),
            ("t*x", "t**2", "x - t*u"),
        ],
        f"{PINNACLE_SOURCE}, burgers.py, nu = 0.01/pi",
    ),
    pde(
        "PINNacle Poisson2D_Classic: Laplace u = 0",
        "Derivative(u(x, y), (x, 2)) + Derivative(u(x, y), (y, 2))",
        ("x", "y"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "y", "0"), ("y", "-x", "0"), ("0", "0", "u")],
        f"{PINNACLE_SOURCE}, poisson.py",
        note="replaces the Laplace equation of Arrigo, section 3.2.2, which gives the same generators",
    ),
    pde(
        "PINNacle PoissonBoltzmann2D: -Laplace u + 64 u = 10 (17 + x**2 + y**2) sin(pi x) sin(4 pi y)",
        "-Derivative(u(x, y), (x, 2)) - Derivative(u(x, y), (y, 2)) + 64*u(x, y) - 10*(17 + x**2 + y**2)*sin(pi*x)*sin(4*pi*y)",
        ("x", "y"),
        INFINITE,
        [("0", "0", "exp(8*x)"), ("0", "0", "exp(8*y)")],
        f"{PINNACLE_SOURCE}, poisson.py, k = 8, mu = (1, 4), A = 10",
        note="linear with a source: the superposition of solutions of -Laplace h + 64 h = 0",
    ),
    pde(
        "PINNacle Helmholtz2D: Laplace u + u = (1 - 32 pi**2) sin(4 pi x) sin(4 pi y)",
        "Derivative(u(x, y), (x, 2)) + Derivative(u(x, y), (y, 2)) + u(x, y) - sin(4*pi*x)*sin(4*pi*y)*(1 - 32*pi**2)",
        ("x", "y"),
        INFINITE,
        [("0", "0", "sin(x)"), ("0", "0", "cos(y)")],
        f"{PINNACLE_SOURCE}, helmholtz.py, A = (4, 4), k = 1",
        note="linear with a source: the superposition of solutions of Laplace h + h = 0",
    ),
    pde(
        "PINNacle Heat2D_Multiscale: u_t = u_xx/(500 pi)**2 + u_yy/pi**2",
        "Derivative(u(x, y, t), t) - Derivative(u(x, y, t), (x, 2))/(250000*pi**2) - Derivative(u(x, y, t), (y, 2))/pi**2",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "2*t", "0"),
            ("t/(125000*pi**2)", "0", "0", "-x*u"),
            ("0", "2*t/pi**2", "0", "-y*u"),
        ],
        f"{PINNACLE_SOURCE}, heat.py",
        note="the heat equation in the plane after scaling x and y",
    ),
    pde(
        "PINNacle Heat2D_LongTime: u_t = Laplace u/1000 + 5 sin(u**2)(1 + 2 sin(pi t/4)) sin(4 pi x) sin(2 pi y)",
        "Derivative(u(x, y, t), t) - (Derivative(u(x, y, t), (x, 2)) + Derivative(u(x, y, t), (y, 2)))/1000 - 5*sin(u(x, y, t)**2)*(1 + 2*sin(pi*t/4))*sin(4*pi*x)*sin(2*pi*y)",
        ("x", "y", "t"),
        0,
        [],
        f"{PINNACLE_SOURCE}, heat.py, k = 1, m1 = 4, m2 = 2",
        note="no continuous symmetries",
    ),
    pde(
        "PINNacle Wave1D: u_tt = 4 u_xx",
        "Derivative(u(x, t), (t, 2)) - 4*Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        INFINITE,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "u"), ("x", "t", "0"), ("4*t", "x", "0")],
        f"{PINNACLE_SOURCE}, wave.py, C = 2",
        note="linear: the superposition of solutions besides",
    ),
    pde(
        "PINNacle Wave2D_LongTime: u_tt = u_xx + 2 u_yy",
        "Derivative(u(x, y, t), (t, 2)) - Derivative(u(x, y, t), (x, 2)) - 2*Derivative(u(x, y, t), (y, 2))",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "u"),
            ("x", "y", "t", "0"),
            ("t", "0", "x", "0"),
            ("0", "2*t", "y", "0"),
            ("y", "-2*x", "0", "0"),
        ],
        f"{PINNACLE_SOURCE}, wave.py, a = sqrt(2)",
        note="the wave equation after scaling y; the superposition of solutions besides",
    ),
    pde(
        "PINNacle KuramotoSivashinskyEquation: u_t + 25/4 u u_x + 25/64 u_xx + 25/16384 u_xxxx = 0",
        "Derivative(u(x, t), t) + 25*u(x, t)*Derivative(u(x, t), x)/4 + 25*Derivative(u(x, t), (x, 2))/64 + 25*Derivative(u(x, t), (x, 4))/16384",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("25*t/4", "0", "1")],
        f"{PINNACLE_SOURCE}, chaotic.py, alpha = 100/16, beta = 100/16**2, gamma = 100/16**4",
    ),
    pde(
        "PINNacle PoissonND: Laplace u + pi**2/4 (sin(pi x1/2) + ... + sin(pi x5/2)) = 0 in 5D",
        "Derivative(u(x1, x2, x3, x4, x5), (x1, 2)) + Derivative(u(x1, x2, x3, x4, x5), (x2, 2)) + Derivative(u(x1, x2, x3, x4, x5), (x3, 2)) + Derivative(u(x1, x2, x3, x4, x5), (x4, 2)) + Derivative(u(x1, x2, x3, x4, x5), (x5, 2)) + pi**2/4*(sin(pi*x1/2) + sin(pi*x2/2) + sin(pi*x3/2) + sin(pi*x4/2) + sin(pi*x5/2))",
        ("x1", "x2", "x3", "x4", "x5"),
        INFINITE,
        [("0", "0", "0", "0", "0", "1"), ("0", "0", "0", "0", "0", "x1")],
        f"{PINNACLE_SOURCE}, poisson.py, dim = 5",
        note="linear with a source: the superposition of harmonic functions",
    ),
    pde(
        "PINNacle HeatND: u_t = Laplace u/5 - |x|**2/5 exp(|x|**2/2 + t) in 5D",
        "Derivative(u(x1, x2, x3, x4, x5, t), (x1, 2)) + Derivative(u(x1, x2, x3, x4, x5, t), (x2, 2)) + Derivative(u(x1, x2, x3, x4, x5, t), (x3, 2)) + Derivative(u(x1, x2, x3, x4, x5, t), (x4, 2)) + Derivative(u(x1, x2, x3, x4, x5, t), (x5, 2))/5 - (x1**2 + x2**2 + x3**2 + x4**2 + x5**2)/5*exp((x1**2 + x2**2 + x3**2 + x4**2 + x5**2)/2 + t) - Derivative(u(x1, x2, x3, x4, x5, t), t)",
        ("x1", "x2", "x3", "x4", "x5", "t"),
        INFINITE,
        [("0", "0", "0", "0", "0", "0", "1"), ("0", "0", "0", "0", "0", "0", "x1")],
        f"{PINNACLE_SOURCE}, heat.py, dim = 5",
        note="linear with a source: the superposition of solutions of h_t = Laplace h/5",
    ),
]

# PDE-FIND (Rudy, Brunton, Proctor, Kutz, Sci. Adv. 2017, table I and the
# example notebooks): the scalar real PDEs. Left out: Schrodinger with harmonic
# potential and NLS (complex: systems, #21), reaction-diffusion and
# Navier-Stokes (systems, #21), Kuramoto-Sivashinsky (the catalogue's) and the
# advection u_t + c u_x = 0 of the notebooks (PDEBench's). The paper gives no
# symmetries: dimensions and generators are delierium's.
PDEFIND = [
    pde(
        "PDE-FIND: KdV u_t + 6 u u_x + u_xxx = 0",
        "Derivative(u(x, t), t) + 6*u(x, t)*Derivative(u(x, t), x) + Derivative(u(x, t), (x, 3))",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("6*t", "0", "1"), ("x", "3*t", "-2*u")],
        f"{PDEFIND_SOURCE}, table I; Examples/TwoSolitonKDV.ipynb",
    ),
    pde(
        "PDE-FIND: Burgers u_t + u u_x - u_xx = 0",
        "Derivative(u(x, t), t) + u(x, t)*Derivative(u(x, t), x) - Derivative(u(x, t), (x, 2))",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("t", "0", "1"),
            ("x", "2*t", "-u"),
            ("t*x", "t**2", "x - t*u"),
        ],
        f"{PDEFIND_SOURCE}, table I; Examples/Burgers.ipynb; {HYDON}, Example 8.3",
    ),
    pde(
        "PDE-FIND: diffusion from a random walk f_t = f_xx/2",
        "Derivative(f(x, t), t) - Derivative(f(x, t), (x, 2))/2",
        ("x", "t"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("0", "0", "f"),
            ("x", "2*t", "0"),
            ("t", "0", "-x*f"),
            ("2*t*x", "2*t**2", "-(x**2 + t)*f"),
        ],
        f"{PDEFIND_SOURCE}; Examples/DiffusionFromRandomWalk.ipynb",
        note="Brownian motion: the density f of the position; the heat equation",
        u="f",
    ),
]

# Yang, Rao, Dehmamy, Walters, Yu, Symmetry-Informed Governing Equation Discovery
# (NeurIPS 2024): the ODE systems of the experiments with the default
# coefficients of github.com/Rose-STL-Lab/symmetry-ode-discovery, data_utils,
# and the symmetries the paper uses. First order: the algebras are infinite.
SYMMETRY_INFORMED = [
    odes(
        "Yang et al.: damped oscillator x1' = -x1/10 - x2, x2' = x1 - x2/10",
        ["Derivative(x1(t), t) + x1(t)/10 + x2(t)", "Derivative(x2(t), t) - x1(t) + x2(t)/10"],
        ("x1", "x2"),
        INFINITE,
        [("1", "0", "0"), ("0", "x2", "-x1"), ("0", "x1", "x2")],
        f"{SYMMETRY_INFORMED_SOURCE}, (13); data_utils/damped_oscillator.py",
        note="the paper's rotation x2 d/dx1 - x1 d/dx2; the scaling as for every linear system",
    ),
    odes(
        "Yang et al.: growth x1' = -3/10 x1 + x2**2/10, x2' = x2",
        ["Derivative(x1(t), t) + 3*x1(t)/10 - x2(t)**2/10", "Derivative(x2(t), t) - x2(t)"],
        ("x1", "x2"),
        INFINITE,
        [("1", "0", "0"), ("0", "2*x1", "x2")],
        f"{SYMMETRY_INFORMED_SOURCE}, (14); data_utils/growth.py",
        note="the paper's scaling (x1, x2) -> (a**2 x1, a x2)",
    ),
    odes(
        "Yang et al.: Lotka-Volterra in canonical coordinates x1' = 2/3 - 4/3 exp(x2), "
        "x2' = exp(x1) - 1",
        ["Derivative(x1(t), t) - 2/3 + 4*exp(x2(t))/3", "Derivative(x2(t), t) - exp(x1(t)) + 1"],
        ("x1", "x2"),
        INFINITE,
        [("1", "0", "0")],
        f"{SYMMETRY_INFORMED_SOURCE}, (15); data_utils/lotka.py",
        note="the paper learns its symmetry numerically",
    ),
    odes(
        "Yang et al.: glycolytic oscillator (Sel'kov) x1' = 3/4 - x1/10 - x1 x2**2, "
        "x2' = -x2 + x1/10 + x1 x2**2",
        [
            "Derivative(x1(t), t) - 3/4 + x1(t)/10 + x1(t)*x2(t)**2",
            "Derivative(x2(t), t) + x2(t) - x1(t)/10 - x1(t)*x2(t)**2",
        ],
        ("x1", "x2"),
        INFINITE,
        [("1", "0", "0")],
        f"{SYMMETRY_INFORMED_SOURCE}, (16); data_utils/selkov.py",
    ),
    odes(
        "Yang et al.: SEIR with reinfection",
        [
            "Derivative(S(t), t) - 3/20 + 3*S(t)*I(t)/5",
            "Derivative(E(t), t) - 3*S(t)*I(t)/5 + E(t)",
            "Derivative(I(t), t) - E(t) + I(t)/2",
            "Derivative(R(t), t) + 3/20 - I(t)/2",
        ],
        ("S", "E", "I", "R"),
        INFINITE,
        [
            ("1", "0", "0", "0", "0"),
            ("0", "0", "0", "0", "1"),
            ("0", "0", "0", "0", "S + E + I + R"),
        ],
        f"{SYMMETRY_INFORMED_SOURCE}, appendix C.1.2, (34)",
        note="the paper's (S + E + I + R) d/dR: the total population is conserved",
    ),
]

# The Well (Ohana et al., NeurIPS 2024, github.com/PolymathicAI/the_well,
# datasets/*/README.md): 16 data sets, all systems (#21) except the Helmholtz
# staircase: the wave equation with a point source and, in the frequency domain,
# the Helmholtz equation; the entries are their source-free forms.
THE_WELL = [
    pde(
        "The Well, helmholtz_staircase: Helmholtz equation Laplace u + omega**2 u = 0",
        "Derivative(u(x, y), (x, 2)) + Derivative(u(x, y), (y, 2)) + omega**2*u(x, y)",
        ("x", "y"),
        INFINITE,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("y", "-x", "0"),
            ("0", "0", "u"),
            ("0", "0", "sin(omega*x)"),
        ],
        f"{THE_WELL_SOURCE}, helmholtz_staircase",
        note="-(Laplace + omega**2) u = delta at the source; linear: the Euclidean motions and "
        "the superposition of solutions",
    ),
    pde(
        "The Well, helmholtz_staircase: wave equation U_tt = U_xx + U_yy",
        "Derivative(U(x, y, t), (t, 2)) - Derivative(U(x, y, t), (x, 2))"
        " - Derivative(U(x, y, t), (y, 2))",
        ("x", "y", "t"),
        INFINITE,
        [
            ("1", "0", "0", "0"),
            ("0", "1", "0", "0"),
            ("0", "0", "1", "0"),
            ("0", "0", "0", "U"),
            ("x", "y", "t", "0"),
            ("y", "-x", "0", "0"),
            ("t", "0", "x", "0"),
            ("0", "t", "y", "0"),
        ],
        f"{THE_WELL_SOURCE}, helmholtz_staircase",
        note="the time domain problem, source delta(t) delta(x - x0) left out; Poincare group, "
        "scaling, the superposition of solutions",
        u="U",
    ),
]

# Equations with symbolic powers of derivatives from the group classifications
# of gradient-dependent diffusion (#39): Cherniha, King, Kovalenko (2015),
# AIMS Mathematics (2026), Anco et al. (2016). Dimensions and generators as
# given there ("base" d/dt, d/dx); the e_i stand for the signs +-1.
SYMBOLIC_POWERS = [
    pde(
        "Cherniha, King, Kovalenko 3: u_t = u_x**k u_xx + e1 exp(-u)",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**k*Derivative(u(x, t), (x, 2)) - e1*exp(-u(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("x", "(k + 2)*t", "k + 2")],
        f"{CKK_SOURCE}, table 1, case 3",
    ),
    pde(
        "Cherniha, King, Kovalenko 4: u_t = u_x**k u_xx + e1 u**m",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**k*Derivative(u(x, t), (x, 2)) - e1*u(x, t)**m",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("(k + 1 - m)*x/(k + 2)", "(1 - m)*t", "u")],
        f"{CKK_SOURCE}, table 1, case 4; m != 1, 2",
    ),
    pde(
        "Cherniha, King, Kovalenko 5: u_t = u_x**k u_xx + e1 u**(k + 1) + e2 u",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**k*Derivative(u(x, t), (x, 2)) - e1*u(x, t)**(k + 1) - e2*u(x, t)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "exp(-k*e2*t)", "e2*exp(-k*e2*t)*u")],
        f"{CKK_SOURCE}, table 1, case 5; k != 1, -1",
    ),
    pde(
        "Cherniha, King, Kovalenko 10: u_t = u_x**k u_xx + e2 u",
        "Derivative(u(x, t), t) - Derivative(u(x, t), x)**k*Derivative(u(x, t), (x, 2)) - e2*u(x, t)",
        ("x", "t"),
        5,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("x", "0", "(1 + 2/k)*u"),
            ("0", "exp(-k*e2*t)", "e2*exp(-k*e2*t)*u"),
            ("0", "0", "exp(e2*t)"),
        ],
        f"{CKK_SOURCE}, table 1, case 10",
    ),
    pde(
        "AIMS 2026 I-(1): u_t = (u**m u_x**n)_x + e u**r",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**m*Derivative(u(x, t), x)**n, x) - (e*u(x, t)**r)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("(m + n - r)*x", "(1 - r)*(n + 1)*t", "(n + 1)*u")],
        f"{AIMS_SOURCE}, Theorem 1, case I-(1); r != 0, 1",
    ),
    pde(
        "AIMS 2026 I-(2): u_t = (u**m u_x**n)_x + e2 u**(m + n) - e3 u/(m + n - 1)",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**m*Derivative(u(x, t), x)**n, x) - (e2*u(x, t)**(m + n) - e3*u(x, t)/(m + n - 1))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "exp(e3*t)", "-e3*exp(e3*t)*u/(m + n - 1)")],
        f"{AIMS_SOURCE}, Theorem 1, case I-(2)",
    ),
    pde(
        "AIMS 2026 I-(3): u_t = (u**(1 - n) u_x**n)_x + e2 u log(u)",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**(1 - n)*Derivative(u(x, t), x)**n, x) - (e2*u(x, t)*log(u(x, t)))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "exp(e2*t)*u")],
        f"{AIMS_SOURCE}, Theorem 1, case I-(3), m = 1 - n",
    ),
    pde(
        "AIMS 2026 I-(4): u_t = (u**m u_x**n)_x + e2 u",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**m*Derivative(u(x, t), x)**n, x) - (e2*u(x, t))",
        ("x", "t"),
        4,
        [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("(m + n - 1)*x/(n + 1)", "0", "u"),
            ("0", "exp(e2*(1 - m - n)*t)", "e2*exp(e2*(1 - m - n)*t)*u"),
        ],
        f"{AIMS_SOURCE}, Theorem 1, case I-(4); m + n != 1",
    ),
    pde(
        "AIMS 2026 I-(5): u_t = (u**(1 - n) u_x**n)_x + e2 u",
        "Derivative(u(x, t), t) - Derivative(u(x, t)**(1 - n)*Derivative(u(x, t), x)**n, x) - (e2*u(x, t))",
        ("x", "t"),
        4,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "0", "u"), ("x", "(n + 1)*t", "e2*(n + 1)*t*u")],
        f"{AIMS_SOURCE}, Theorem 1, case I-(5), m = 1 - n",
    ),
    pde(
        "AIMS 2026 II-(1): u_t = (exp(u) u_x**n)_x + e2 exp(q u)",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x)**n, x) - (e2*exp(q*u(x, t)))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("(1 - q)*x/(n + 1)", "-q*t", "1")],
        f"{AIMS_SOURCE}, Theorem 1, case II-(1)",
    ),
    pde(
        "AIMS 2026 II-(2): u_t = (exp(u) u_x**n)_x + e2 exp(u) - e3",
        "Derivative(u(x, t), t) - Derivative(exp(u(x, t))*Derivative(u(x, t), x)**n, x) - (e2*exp(u(x, t)) - e3)",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("0", "exp(e3*t)", "-e3*exp(e3*t)")],
        f"{AIMS_SOURCE}, Theorem 1, case II-(2)",
    ),
    pde(
        "Anco et al.: u_t = -kappa p u_x**(p - 1) u_xx + c (a + u)**q",
        "Derivative(u(x, t), t) + kappa*p*Derivative(u(x, t), x)**(p - 1)*Derivative(u(x, t), (x, 2)) - c*(a + u(x, t))**q",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("(p - q)*x", "(p + 1)*(1 - q)*t", "(p + 1)*(a + u)")],
        f"{ANCO_SOURCE}, table 2, h = -kappa u_r**p, m = 0",
    ),
    pde(
        "Anco et al.: u_t = -kappa p u_x**(p - 1) u_xx + c exp(q u)",
        "Derivative(u(x, t), t) + kappa*p*Derivative(u(x, t), x)**(p - 1)*Derivative(u(x, t), (x, 2)) - c*exp(q*u(x, t))",
        ("x", "t"),
        3,
        [("1", "0", "0"), ("0", "1", "0"), ("q*x", "(p + 1)*q*t", "-(p + 1)")],
        f"{ANCO_SOURCE}, table 2, h = -kappa u_r**p, m = 0",
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

CATALOG = (
    CLASSICAL_ODES
    + FIRST_ORDER_ODES
    + ODE_SYSTEMS
    + PDES
    + BAUMANN_EXAMPLES
    + HYDON_EXAMPLES
    + HYDON_EXERCISES
    + BLUMAN_ANCO_EXAMPLES
    + CRC_VOL1
    + PDEBENCH
    + APEBENCH
    + GABEL
    + ODEBENCH
    + KO_KIM_LEE
    + EQWORLD
    + ODESYM
    + PINNACLE
    + PDEFIND
    + SYMMETRY_INFORMED
    + THE_WELL
    + SYMBOLIC_POWERS
    + KAMKE
)
