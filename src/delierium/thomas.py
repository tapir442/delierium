"""Algebraic Thomas decomposition: a system of polynomial equations and
inequations split into simple systems with disjoint solution sets (#58,
stage 2).

Bächler, Gerdt, Lange-Hegermann, Robertz, *Algorithmic Thomas
decomposition of algebraic and differential systems*, J. Symb. Comp. 47
(2012), arXiv:1108.0817, section 2; the algorithm numbers below are theirs.

The variables are ranked, the first being the highest. The leader of a
polynomial is its highest variable, its initial the leading coefficient in
the leader. A system is simple if it is triangular (at most one equation or
inequation per leader), its initials do not vanish and it is square-free in
each leader, all on the solutions of the lower part (Definition 2.2). Then
every solution of the lower part extends: the fibres have a constant number
of points. Solutions are complex; the decomposition computes no roots.

Internally the polynomials are sparse polynomials over the integers
(SymPy's PolyElement); expressions are converted at the interface only.
"""

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache
from typing import Any

from sympy import QQ, ZZ, Basic, Dummy, Expr, PolynomialError, S, Symbol, expand, groebner
from sympy import Poly as SPoly
from sympy.polys.matrices import DomainMatrix
from sympy.polys.rings import PolyRing

__all__ = ["SimpleSystem", "thomas_decomposition"]

# a polynomial of the ring ZZ[variables] (sympy.polys.rings.PolyElement)
Pol = Any


@dataclass
class SimpleSystem:
    """A simple system: equations (expr = 0) and inequations (expr != 0),
    highest leader first."""

    equations: list[Expr]
    inequations: list[Expr]
    variables: list[Symbol] = field(repr=False)

    def __str__(self) -> str:
        parts = [(e, "= 0") for e in self.equations] + [(e, "!= 0") for e in self.inequations]
        rank = {v: i for i, v in enumerate(self.variables)}
        parts.sort(key=lambda p: min((rank[v] for v in p[0].free_symbols), default=len(rank)))
        return "{" + ", ".join(f"{e} {r}" for e, r in parts) + "}"


def thomas_decomposition(
    equations: Iterable[Basic],
    inequations: Iterable[Basic] = (),
    variables: Sequence[Symbol] = (),
    factorize: bool = True,
) -> list[SimpleSystem]:
    """A Thomas decomposition of equations = 0 and inequations != 0 for the
    variables, ranked highest first (Algorithm 2.25, Decompose).

    With factorize (the default, as in the authors' implementation, §4.4),
    every polynomial is factored over the rationals and the system split on
    its factors: f*g = 0 into f = 0, and f != 0 with g = 0; f*g != 0 into
    f != 0 and g != 0. That keeps the polynomials small; without it they
    may grow quickly. The decomposition is finer then: Example 2.5 has the
    same four systems either way.

    Example 2.5 of Bächler et al.: a x**2 + b x + c with x > c > b > a.

    >>> from sympy import symbols
    >>> x, a, b, c = symbols("x a b c")
    >>> p = a * x**2 + b * x + c
    >>> for s in thomas_decomposition([p], variables=[x, c, b, a], factorize=False):
    ...     print(s)
    {a*x**2 + b*x + c = 0, 4*a*c - b**2 != 0, a != 0}
    {b*x + c = 0, b != 0, a = 0}
    {2*a*x + b = 0, 4*a*c - b**2 = 0, a != 0}
    {c = 0, b = 0, a = 0}
    """
    variables = list(variables)
    ring = _Ring(variables)
    start = _System({}, [])
    for e in equations:
        start.queue.append((ring.check(e), True))
    for e in inequations:
        start.queue.append((ring.check(e), False))
    systems = [s.normalized(ring) for s in _decompose(start, ring, factorize)]
    systems.sort(key=lambda s: _system_key(s, ring))
    return [
        SimpleSystem(
            [p.as_expr() for p, is_eq in s if is_eq],
            [p.as_expr() for p, is_eq in s if not is_eq],
            variables,
        )
        for s in systems
    ]


def _system_key(system: list[tuple[Pol, bool]], ring: "_Ring") -> tuple:
    """Generic systems first: fewer equations, then by leader and degree."""
    eqs = [p for p, is_eq in system if is_eq]
    return (
        len(eqs),
        [(ring.rank_key(p), ring.mdeg(p)) for p in eqs],
        [ring.sort_key(p) for p in eqs],
    )


class _Ring:
    """Leaders, initials and pseudo division with respect to the ranking."""

    def __init__(self, variables: list[Symbol]) -> None:
        self.variables = variables
        self.rank = {v: len(variables) - i for i, v in enumerate(variables)}
        self.ring = PolyRing(variables, ZZ) if variables else None
        self.gen = dict(zip(variables, self.ring.gens, strict=True)) if self.ring else {}
        # per instance: functools.cache on the method would keep every ring alive
        self._subresultant = cache(self._compute_subresultant)

    def check(self, e: Basic) -> Pol:
        e = expand(S(e))
        if not e.free_symbols <= set(self.rank):
            unknown = sorted(e.free_symbols - set(self.rank), key=str)
            raise ValueError(f"{e}: symbols {unknown} are not among the variables")
        if self.ring is None:
            raise ValueError("no variables")
        try:
            poly = SPoly(e, *self.variables, domain=QQ)
        except PolynomialError as error:
            raise ValueError(f"{e} is not a polynomial in {self.variables}") from error
        _, poly = poly.clear_denoms(convert=True)  # a/2 - 1: a - 2
        return self.primitive(self.ring.from_expr(poly.as_expr()))

    def ld(self, p: Pol) -> Symbol | None:
        """The leader, None for a constant."""
        for v in self.variables:
            if p.degree(self.gen[v]) > 0:
                return v
        return None

    def rank_key(self, p: Pol) -> int:
        x = self.ld(p)
        return self.rank[x] if x is not None else 0

    @staticmethod
    def sort_key(p: Pol) -> tuple:
        return tuple(p.terms())

    def mdeg(self, p: Pol, x: Symbol | None = None) -> int:
        x = x or self.ld(p)
        return max(p.degree(self.gen[x]), 0) if x is not None else 0

    def init(self, p: Pol, x: Symbol | None = None) -> Pol:
        x = x or self.ld(p)
        return p.coeff_wrt(self.gen[x], self.mdeg(p, x)) if x is not None else p

    def factors(self, p: Pol) -> list[Pol]:
        """The distinct irreducible nonconstant factors of p over the
        rationals, the lowest leader first (the content before the rest)."""
        distinct = {self.primitive(f) for f, _ in p.factor_list()[1]}
        return sorted(distinct, key=lambda f: (self.rank_key(f), self.mdeg(f), self.sort_key(f)))

    def primitive(self, p: Pol) -> Pol:
        """p without its integer content (same zeros), a nonzero constant 1."""
        if p.is_ground:
            return p.ring.one if p != 0 else p.ring.zero
        return p.primitive()[1]

    def prem(self, p: Pol, q: Pol, x: Symbol) -> Pol:
        return self.primitive(p.ring(p.prem(q, self.gen[x])))  # may be an int

    def pquo(self, p: Pol, q: Pol, x: Symbol) -> Pol:
        """The pseudo-quotient: init(q)**(deg p - deg q + 1) p = pquo q + prem.

        From prem and an exact division: SymPy's PolyElement.pquo (1.14) is
        wrong for every variable but the ring's first (pquo(a**2, a, a) gives
        a + 2)."""
        g = self.gen[x]
        m = self.init(q, x) ** (self.mdeg(p, x) - self.mdeg(q, x) + 1)
        return self.primitive((m * p - p.ring(p.prem(q, g))).exquo(q))

    def diff(self, p: Pol, x: Symbol) -> Pol:
        return self.primitive(p.diff(self.gen[x]))

    def without_leading_term(self, q: Pol, x: Symbol) -> Pol:
        return self.primitive(q - self.init(q, x) * self.gen[x] ** self.mdeg(q, x))

    def content_free(self, p: Pol, x: Symbol) -> Pol:
        """p divided by the gcd of its coefficients as a polynomial in x."""
        g = self.gen[x]
        content = p.ring.zero
        for d in range(self.mdeg(p, x) + 1):
            c = p.coeff_wrt(g, d)
            if c != 0:
                content = c if content == 0 else content.gcd(c)
        return self.primitive(p if content.is_ground else p.exquo(content))

    def prs(self, p: Pol, q: Pol, x: Symbol, i: int) -> tuple[Pol, Pol]:
        """(PRS_i, res_i) of p and q, deg p > deg q (Definition 2.13):
        PRS_i the regular subresultant of degree i (0 if there is none),
        res_i its initial, the principal subresultant coefficient."""
        dp, dq = self.mdeg(p, x), self.mdeg(q, x)
        zero = p.ring.zero
        if i == dp:
            return p, p.ring.one
        if i == dq:
            return q, self.init(q, x)
        if dq < i < dp:
            return zero, zero
        s = self._subresultant(p, q, x, i)
        res = s.coeff_wrt(self.gen[x], i)
        return (s, res) if res != 0 else (zero, zero)

    def _compute_subresultant(self, p: Pol, q: Pol, x: Symbol, j: int) -> Pol:
        """The j-th subresultant of p and q in x (j < deg q < deg p): the
        determinant of the Sylvester submatrix whose last column holds the
        polynomials x**k p, x**k q truncated above x**j (Mishra, ch. 7).

        Not SymPy's subresultants(): its subresultant PRS differs from the
        subresultants by polynomial factors where the sequence is defective
        (degree gaps), e.g. a spurious factor 9 z + 1 in the resultant of
        y**6 z**4 + ... - 27 z**3 and its derivative in y, which made the
        decomposition lose the solutions at z = -1/9."""
        g = self.gen[x]
        m, n = self.mdeg(p, x), self.mdeg(q, x)
        rows = [g**k * p for k in range(n - j - 1, -1, -1)]
        rows += [g**k * q for k in range(m - j - 1, -1, -1)]
        matrix = []
        for r in rows:
            coeffs = [r.coeff_wrt(g, d) for d in range(m + n - j - 1, j, -1)]
            tail = sum((r.coeff_wrt(g, d) * g**d for d in range(j + 1)), p.ring.zero)
            matrix.append([*coeffs, tail])
        size = len(matrix)
        return DomainMatrix(matrix, (size, size), p.ring.to_domain()).det()


class _System:
    """A candidate simple system (leader -> (polynomial, is equation)) and
    a queue of equations and inequations still to be treated."""

    def __init__(self, triangular: dict, queue: list) -> None:
        self.triangular: dict[Symbol, tuple[Pol, bool]] = triangular
        self.queue: list[tuple[Pol, bool]] = queue

    def copy(self) -> "_System":
        return _System(dict(self.triangular), list(self.queue))

    def equation(self, x: Symbol) -> Pol | None:
        entry = self.triangular.get(x)
        return entry[0] if entry and entry[1] else None

    def normalized(self, ring: _Ring) -> list[tuple[Pol, bool]]:
        """The (simple) system, highest leader first, each polynomial in
        normal form: reduced modulo a lex Groebner basis (over the
        rationals) of the lower equations, with the denominators cleared,
        without content and with a positive sign.

        The remainder differs from the polynomial by an element of the
        ideal of the lower equations, so it has the same values on their
        solutions: the same initial and square-freeness, the system stays
        simple. Unlike pseudo-reduction it is canonical and does not
        multiply by powers of the lower initials, whose coefficients would
        grow over the levels (1419 digits for a two-equation input). Where
        the initial is invertible modulo the lower equations, the polynomial
        is made monic first (25 digits instead of 1419 there)."""
        lowest_first = sorted(self.triangular, key=ring.rank.__getitem__)
        done: dict[Symbol, tuple[Pol, bool]] = {}
        equations: list[Expr] = []  # the normalized equations below the current leader
        for x in lowest_first:
            p, is_equation = self.triangular[x]
            if equations:
                p = _monic_normal_form(p, x, equations, ring)
            p = ring.content_free(p, x)
            # the sign of the initial's leading term: x**2 - a, not a - x**2
            p = -p if ring.init(p, x).LC < 0 else p
            done[x] = (p, is_equation)
            if is_equation:
                equations.append(p.as_expr())
        return [done[x] for x in reversed(lowest_first)]


def _monic_normal_form(p: Pol, x: Symbol, equations: list[Expr], ring: _Ring) -> Pol:
    """p reduced modulo a lex Groebner basis of the lower equations, made
    monic in x first if its initial has an inverse f modulo them (an element
    t - f of the basis of the equations and t init - 1), the denominators
    cleared. f init = 1 on the solutions of the lower equations, so f does
    not vanish there: the zeros, the initial and square-freeness stay."""
    variables = ring.variables
    expr = p.as_expr()
    init = ring.init(p, x).as_expr()
    if not init.is_number:
        t = Dummy("t")
        with_inverse = groebner([*equations, t * init - 1], t, *variables, order="lex", domain=QQ)
        inverse = [g for g in with_inverse.exprs if SPoly(g, t).degree() == 1]
        if inverse:
            g = SPoly(inverse[-1], t)
            a, b = g.all_coeffs()
            if a.is_number:  # t - f: f = -b/a
                expr = expand(expr * (-b / a))
    remainder = groebner(equations, *variables, order="lex", domain=QQ).reduce(expr)[1]
    _, cleared = SPoly(remainder, *variables).clear_denoms(convert=True)
    assert ring.ring is not None
    return ring.ring.from_expr(cleared.as_expr())


def _reduce(system: _System, p: Pol, ring: _Ring) -> Pol:
    """p pseudo-reduced modulo the equations of the candidate simple
    system, with an initial that does not reduce to 0 (Algorithm 2.6)."""
    q = p
    x = ring.ld(q)
    while (
        x is not None
        and (e := system.equation(x)) is not None
        and ring.mdeg(q, x) >= ring.mdeg(e, x)
    ):
        q = ring.prem(q, e, x)
        x = ring.ld(q)
    if x is not None and _reduce(system, ring.init(q, x), ring) == 0:
        return _reduce(system, ring.without_leading_term(q, x), ring)
    return q


def _reduce_fully(system: _System, p: Pol, ring: _Ring) -> Pol:
    """Reduce, then also the coefficients modulo the lower equations of the
    candidate simple system (the authors' implementation, §4.2): each a
    pseudo-reduction of the whole polynomial, i.e. a multiplication by a
    power of an initial, which does not vanish on the solutions, and the
    subtraction of a multiple of the equation. Without it the coefficients
    grow with every step (degree 500 in z modulo 9 z + 1 = 0)."""
    q = _reduce(system, p, ring)
    x = ring.ld(q)
    if x is None:
        return q
    lower = sorted(
        (y for y in system.triangular if ring.rank[y] < ring.rank[x]),
        key=ring.rank.__getitem__,
        reverse=True,
    )
    changed = False
    for y in lower:
        e = system.equation(y)
        if e is not None and ring.mdeg(q, y) >= ring.mdeg(e, y):
            q = ring.prem(q, e, y)
            changed = True
    return _reduce(system, q, ring) if changed else q


def _split(system: _System, p: Pol) -> tuple[_System, _System]:
    """(system with p != 0, system with p = 0) (Algorithm 2.11); the first
    is system itself."""
    other = system.copy()
    system.queue.append((p, False))
    other.queue.append((p, True))
    return system, other


def _init_split(system: _System, q: tuple[Pol, bool], ring: _Ring) -> _System:
    """Algorithm 2.12: system gets init(q) != 0; returned the system with
    init(q) = 0 and q back in its queue."""
    _, other = _split(system, ring.init(q[0]))
    other.queue.append(q)
    return other


def _res_split(system: _System, p: Pol, q: Pol, x: Symbol, ring: _Ring) -> tuple[int, _System]:
    """Algorithm 2.18: the quasi fibre cardinality i of p and q (deg p >
    deg q) and the i-th fibration split (system gets res_i != 0)."""
    i = 0
    while True:
        _, res = ring.prs(p, q, x, i)
        if _reduce(system, res, ring) != 0:
            _, other = _split(system, ring.primitive(res))
            return i, other
        i += 1


def _res_split_gcd(system: _System, q: Pol, x: Symbol, ring: _Ring) -> tuple[_System, Pol]:
    """Algorithm 2.19: the conditional gcd of the equation of leader x
    and the equation q."""
    p = system.equation(x)
    assert p is not None
    i, other = _res_split(system, p, q, x, ring)
    other.queue.append((q, True))
    return other, ring.primitive(ring.prs(p, q, x, i)[0])


def _res_split_divide(
    system: _System, p: Pol, q: tuple[Pol, bool], x: Symbol, ring: _Ring
) -> tuple[_System, Pol]:
    """Algorithm 2.20: p divided by its conditional gcd with q.

    If deg p <= deg q, the gcd is that of p and prem(q, p); but the system
    split off gets q itself back, not prem(q, p) as in the paper: the two
    are equivalent where p = 0, not where p is an inequation (Decompose,
    line 35: x - y != 0, x - 1 != 0 would lose y = 1)."""
    reduced = q[0]
    if ring.mdeg(p, x) <= ring.mdeg(reduced, x):
        reduced = ring.prem(reduced, p, x)
    i, other = _res_split(system, p, reduced, x, ring)
    quotient = ring.pquo(p, ring.prs(p, reduced, x, i)[0], x) if i > 0 else p
    other.queue.append(q)
    return other, quotient


def _res_split_square_free(
    system: _System, p: tuple[Pol, bool], x: Symbol, ring: _Ring
) -> tuple[_System, Pol]:
    """Algorithm 2.21: the conditional square-free part of p."""
    derivative = ring.diff(p[0], x)
    i, other = _res_split(system, p[0], derivative, x, ring)
    part = ring.pquo(p[0], ring.prs(p[0], derivative, x, i)[0], x) if i > 0 else p[0]
    other.queue.append(p)
    return other, part


def _select(queue: list[tuple[Pol, bool]], ring: _Ring) -> tuple[Pol, bool]:
    """Equations first, the lowest leader first; an inequation only if no
    equation of the same or a lower leader waits (Definition 2.22)."""
    equations = [q for q in queue if q[1]]
    candidates = equations or queue
    chosen = min(candidates, key=lambda q: (ring.rank_key(q[0]), ring.sort_key(q[0])))
    queue.remove(chosen)
    return chosen


def _decompose(start: _System, ring: _Ring, factorize: bool) -> list[_System]:
    """Algorithm 2.25 (Decompose), optionally splitting on the factors of
    each polynomial taken from the queue."""
    pending = [start]
    result = []
    while pending:
        system = pending.pop()
        if not system.queue:
            result.append(system)
            continue
        q, is_equation = _select(system.queue, ring)
        q = _reduce_fully(system, q, ring)
        if (is_equation and q != 0 and q.is_ground) or (not is_equation and q == 0):
            continue  # inconsistent
        x = ring.ld(q)
        if factorize and x is not None and len(factors := ring.factors(q)) > 1:
            pending += _split_factors(system, factors, is_equation)
        elif x is not None:
            if factorize:
                q = factors[0]  # without repeated factors
            insert = _insert_equation if is_equation else _insert_inequation
            pending += insert(system, q, x, ring)
        pending.append(system)
    return result


def _split_factors(system: _System, factors: list[Pol], is_equation: bool) -> list[_System]:
    """The factors f1, ..., fk of an equation or inequation into the queue:
    for an inequation all fi != 0; for an equation the disjoint cases f1 = 0,
    f1 != 0 and f2 = 0, ...; system takes the first, the others are
    returned."""
    if not is_equation:
        system.queue += [(f, False) for f in factors]
        return []
    others = []
    for k in range(1, len(factors)):
        other = system.copy()
        other.queue += [(f, False) for f in factors[:k]] + [(factors[k], True)]
        others.append(other)
    system.queue.append((factors[0], True))
    return others


def _insert_equation(system: _System, q: Pol, x: Symbol, ring: _Ring) -> list[_System]:
    """Lines 11-26 of Decompose: the reduced equation q of leader x into the
    candidate simple system; returns the systems split off."""
    entry = system.triangular.get(x)
    if entry is not None and entry[1]:
        _, res0 = ring.prs(entry[0], q, x, 0)
        if _reduce(system, res0, ring) != 0:
            # a common root needs res0 = 0: add it, then try again
            system.queue += [(q, True), (ring.primitive(res0), True)]
            return []
        other, p = _res_split_gcd(system, q, x, ring)
        system.triangular[x] = (p, True)
        return [other]
    if entry is not None:  # an inequation: treated again later
        system.queue.append(entry)
        del system.triangular[x]
    split = [_init_split(system, (q, True), ring)]
    other, p = _res_split_square_free(system, (q, True), x, ring)
    system.triangular[x] = (p, True)
    return [*split, other]


def _insert_inequation(system: _System, q: Pol, x: Symbol, ring: _Ring) -> list[_System]:
    """Lines 27-40 of Decompose: the reduced inequation q of leader x."""
    entry = system.triangular.get(x)
    if entry is not None and entry[1]:
        other, p = _res_split_divide(system, entry[0], (q, False), x, ring)
        system.triangular[x] = (p, True)
        return [other]
    split = [_init_split(system, (q, False), ring)]
    other, p = _res_split_square_free(system, (q, False), x, ring)
    split.append(other)
    if entry is not None:
        other, r = _res_split_divide(system, entry[0], (p, False), x, ring)
        split.append(other)
        p = ring.primitive(r * p)  # the lcm of both inequations
    system.triangular[x] = (p, False)
    return split
