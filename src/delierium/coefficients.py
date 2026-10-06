"""Coefficients of linear differential polynomials.

The coefficients are rational functions of the independent variables and
parameters. Kept as SymPy expressions, every step of the reduction had to
bring them into canonical form with ``cancel``, which expands the
expression from scratch and converts it into polynomials and back; that was
almost all of the running time. A :class:`Coeff` keeps them instead as
elements of SymPy's rational function field (``FracField``): numerator and
denominator are expanded, coprime polynomials, so equality and the zero test
are structural and the arithmetic never leaves the polynomials.

Generators of the field are the symbols and the non-rational atoms of the
coefficients (``exp(x)``, ``y**n``, ``f(x)``, ...). They are chosen so that
the field does not miss a relation between them: ``x``, ``sqrt(x)`` and
``1/x**(3/2)`` are all powers of the one generator ``sqrt(x)``, ``exp(2*x)``
is ``exp(x)**2``, and ``y**(n - 1)`` is ``y**n/y``. Trigonometric and hyperbolic
functions are written in ``sin``, ``cos`` (``sinh``, ``cosh``) of one argument
(``sin(2*x)`` is ``2*sin(x)*cos(x)``, ``tan`` is ``sin/cos``), and where the field
has both of a pair, the zero test and comparisons reduce modulo
``cos**2 + sin**2 - 1`` (``cosh**2 - sinh**2 - 1``): a normal form, so that they
are exact (#61). A float is taken for the
decimal it prints as: ``0.25`` is ``1/4``, ``0.1`` is ``1/10``. A coefficient
containing an algebraic element the field cannot represent faithfully
(``sqrt(2)``, ``I``, ``sqrt(x + 1)``) stays a canonical SymPy expression, as
before.

Each computation has its own field (:func:`fresh_field`; a Janet basis
opens one), which only grows while it runs: a new generator gives a new
field, and older elements are lifted into it when they are used. Outside
such a computation a default field is used. A coefficient that meets one of
another field is converted into the current one, so mixing them is correct,
only slower.

>>> from sympy import symbols, exp, sqrt
>>> x, y, n = symbols("x y n")
>>> c = Coeff(x / (x**2 + x))
>>> c
1/(x + 1)
>>> c.diff(x)
-1/(x**2 + 2*x + 1)
>>> Coeff(sqrt(x)) * Coeff(sqrt(x)) == Coeff(x)
True
>>> Coeff(exp(2 * x)) - Coeff(exp(x)) ** 2
0
>>> Coeff(y**n).diff(y) == Coeff(n * y ** (n - 1))
True
>>> Coeff(sqrt(x + 1)).is_field
False
>>> Coeff(0.1 * x + 0.25)
x/10 + 1/4
>>> from sympy import sin, cos
>>> Coeff(sin(2 * x)) == Coeff(2 * sin(x) * cos(x))
True
>>> Coeff(sin(x) ** 2 + cos(x) ** 2 - 1) == Coeff(0)
True
"""

# Coeff's private helpers are applied to other Coeff instances as well
# pylint: disable=protected-access

import operator
from collections.abc import Callable, Iterable, Iterator, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from math import comb, gcd, lcm
from typing import Any

from sympy import (
    Basic,
    Derivative,
    Dummy,
    Expr,
    Float,
    Pow,
    Rational,
    S,
    Symbol,
    cancel,
    default_sort_key,
    expand_power_exp,
    expand_trig,
    nsimplify,
    sympify,
)
from sympy.core.function import AppliedUndef, Function
from sympy.functions.elementary.exponential import ExpBase
from sympy.functions.elementary.hyperbolic import cosh, coth, csch, sech, sinh, tanh
from sympy.functions.elementary.trigonometric import cos, cot, csc, sec, sin, tan
from sympy.polys.domains import ZZ
from sympy.polys.fields import FracElement, FracField

from delierium.helpers import profile_if_enabled

__all__ = [
    "Coeff",
    "fresh_field",
]

# (b, rest): the base and the symbolic part of the exponent of an atom
AtomKey = tuple[Basic, Basic]
# what a Coeff is made from and combined with
type CoeffLike = Coeff | Basic | int


class _UnsupportedError(Exception):
    """The expression contains an atom the field cannot represent."""


class _FieldState:
    """A field and the generators it is built from.

    A generator stands for all powers b**(c*rest) with rational c of a base b
    and a symbolic part rest of the exponent (rest = 1 for a plain atom): the
    generator is b**(rest/L), L the common denominator of all c seen so far,
    and b**(c*rest) is its (c*L)-th power.
    """

    def __init__(self) -> None:
        self.keys: dict[AtomKey, int] = {}  # (b, rest) -> L
        self.symbols: tuple = ()  # the generators as expressions, in field order
        self.field = FracField((Symbol("_delierium_dummy"),), ZZ)
        self.index: dict[Basic, int] = {}  # generator expression -> index
        # (generator expression, variable) -> Coeff
        self.dgen: dict[tuple[Basic, Basic], Coeff] = {}
        # cos**2 + sin**2 - 1, cosh**2 - sinh**2 - 1 of the pairs among the
        # generators, as (index of cos, index of sin, sign): cos**2 = 1 - sign*sin**2
        self.relations: list[tuple[int, int, int]] = []
        # (sin or sinh, u) -> g: sin(k u), cos(k u) are written in sin(g u),
        # cos(g u), g the greatest common divisor of the multiples k seen
        self.trig_base: dict[tuple[Any, Basic], Rational] = {}

    @staticmethod
    def generator(key: AtomKey, L: int) -> Expr:
        base, rest = key
        return Pow(base, rest / L)

    def element_of(self, key: AtomKey, c: Rational) -> FracElement:
        """The atom b**(c*rest) as an element of the current field."""
        L = self.keys[key]
        g = self.field.gens[self.index[self.generator(key, L)]]
        return g ** int(c * L)

    def extend(self, atoms: Iterable[tuple[AtomKey, Rational]]) -> bool:
        """Make every (key, c) in atoms representable; True if the field changed."""
        changed = False
        # in a fixed order: the order of the generators is the variable order
        # of the polynomial ring, and the cost of the gcds depends on it (a
        # set's order changed with the hash seed: one Janet basis took 8 s to
        # 450 s)
        for key, c in sorted(atoms, key=lambda a: (default_sort_key(a[0]), a[1])):
            L = self.keys.get(key)
            q = Rational(c).q
            if L is None:
                self.keys[key] = q
                changed = True
            elif L % q:
                self.keys[key] = lcm(L, q)
                changed = True
        if changed:
            self._rebuild()
        return changed

    def _rebuild(self) -> None:
        """The generators, the field and the relations from self.keys."""
        self.symbols = tuple(self.generator(k, L) for k, L in self.keys.items())
        self.index = {g: i for i, g in enumerate(self.symbols)}
        self.field = FracField(self.symbols or (Symbol("_delierium_dummy"),), ZZ)
        self.relations = self._relations()

    def drop_generators(self, generators: Iterable[Expr]) -> None:
        """Remove generators replaced by others (a finer trigonometric base):
        the elements that contain them are converted again when lifted."""
        gone = {(g, S.One) for g in generators} & set(self.keys)
        if not gone:
            return
        for key in gone:
            del self.keys[key]
        self._rebuild()
        self.dgen = {k: v for k, v in self.dgen.items() if (k[0], S.One) not in gone}

    def _relations(self) -> list[tuple[int, int, int]]:
        relations = []
        for g, i in self.index.items():
            for c, s, sign in ((cos, sin, 1), (cosh, sinh, -1)):
                if isinstance(g, c) and s(g.args[0]) in self.index:
                    relations.append((i, self.index[s(g.args[0])], sign))
        return relations

    def reduce_numerator(self, f: FracElement) -> Any:
        """The numerator of f in normal form modulo the relations, every
        cos**(2q + r) written as cos**r (1 - sign*sin**2)**q (unique: the
        relations are a Groebner basis, the pairs being disjoint): 0 iff f is.
        Directly on the terms: PolyElement.rem searches the leading term anew
        for every step, quadratic in the number of terms (#61)."""
        numer = f.numer
        if not self.relations or f.field is not self.field:
            return numer
        terms = dict(numer)
        for i, j, sign in self.relations:
            if all(e[i] < 2 for e in terms):
                continue
            reduced: dict[tuple[int, ...], Any] = {}
            for e, c in terms.items():
                q, r = divmod(e[i], 2)
                m = list(e)
                m[i] = r
                for k in range(q + 1):
                    t = tuple(m)
                    reduced[t] = reduced.get(t, 0) + c * comb(q, k) * (-sign) ** k
                    m[j] += 2
            terms = {e: c for e, c in reduced.items() if c}
        return numer.ring.from_dict(terms)


# the field outside of any fresh_field(), shared by all threads
_default = _FieldState()
_current: ContextVar[_FieldState | None] = ContextVar("delierium_coefficient_field", default=None)


def _state() -> _FieldState:
    """The field of the running computation."""
    return _current.get() or _default


@contextmanager
def fresh_field() -> Iterator[None]:
    """Run a computation in a field of its own.

    Without it, all computations of a process would share one field that
    only grows: arithmetic gets slower with every generator another
    computation added (the catalogue: 90 s shared, 70 s with a field per
    Janet basis), and the order of the generators depends on the history.
    Nested uses and threads each get their own field.

    >>> from sympy import symbols, exp
    >>> x = symbols("x")
    >>> with fresh_field():
    ...     c = Coeff(exp(x))
    ...     print(c.f.field.symbols)
    (exp(x),)
    >>> c * Coeff(x) == Coeff(x * exp(x))  # used outside its field
    True
    """
    token = _current.set(_FieldState())
    try:
        yield
    finally:
        _current.reset(token)


def _is_transcendental_atom(e: Basic) -> bool:
    """Symbols, E, pi and applied functions: no algebraic relation with
    anything else the field contains."""
    return (
        e.is_Symbol
        or e in (S.Exp1, S.Pi)
        or isinstance(e, (AppliedUndef, Derivative))
        or (isinstance(e, Function) and not isinstance(e, ExpBase))
    )


def _atom_key(e: Basic) -> tuple[AtomKey, Rational]:
    """(key, c) with e == b**(c*rest) for key == (b, rest), or _UnsupportedError."""
    if isinstance(e, (Pow, ExpBase)):
        base, exp = e.as_base_exp()
        c, rest = exp.as_coeff_Mul(rational=True)
        if rest == 1:
            # a rational power: a root of a transcendental atom only
            if not _is_transcendental_atom(base):
                raise _UnsupportedError(e)
        elif not (_is_transcendental_atom(base) or (base.is_Integer and base > 1) or base.is_Add):
            raise _UnsupportedError(e)
        return (base, rest), c
    if _is_transcendental_atom(e):
        return (e, S.One), S.One
    raise _UnsupportedError(e)


def _split_exponent(e: Basic) -> list[Expr] | None:
    """b**(e1 + e2 + ...) as the factors b**e1, b**e2, ..., or None."""
    if isinstance(e, (Pow, ExpBase)):
        base, exp = e.as_base_exp()
        if exp.is_Add:
            return [Pow(base, a, evaluate=False) for a in exp.args]
    return None


def _collect_atoms(e: Basic, atoms: set[tuple[AtomKey, Rational]]) -> None:
    if e.is_Rational:
        return
    factors = _split_exponent(e)
    if factors is not None:
        for a in factors:
            _collect_atoms(a, atoms)
        return
    if e.is_Add or e.is_Mul:
        for a in e.args:
            _collect_atoms(a, atoms)
    elif e.is_Pow and e.exp.is_Integer:
        _collect_atoms(e.base, atoms)
    else:
        atoms.add(_atom_key(e))


def _convert(e: Basic, field: FracField) -> FracElement:  # pylint: disable=too-many-return-statements
    if e.is_Integer:
        return field(int(e))
    if e.is_Rational:
        return field(int(e.p)) / int(e.q)
    if e.is_Add:
        result = field.zero
        for a in e.args:
            result += _convert(a, field)
        return result
    if e.is_Mul:
        result = field.one
        for a in e.args:
            result *= _convert(a, field)
        return result
    if e.is_Pow and e.exp.is_Integer:
        return _convert(e.base, field) ** int(e.exp)
    factors = _split_exponent(e)
    if factors is not None:
        result = field.one
        for a in factors:
            result *= _convert(a, field)
        return result
    return _state().element_of(*_atom_key(e))


# tan, cot, ... in terms of sin and cos (sinh and cosh)
_QUOTIENTS: dict[Any, Callable[[Expr], Expr]] = {
    tan: lambda u: sin(u) / cos(u),
    cot: lambda u: cos(u) / sin(u),
    sec: lambda u: 1 / cos(u),
    csc: lambda u: 1 / sin(u),
    tanh: lambda u: sinh(u) / cosh(u),
    coth: lambda u: cosh(u) / sinh(u),
    sech: lambda u: 1 / cosh(u),
    csch: lambda u: 1 / sinh(u),
}


def _rational_gcd(a: Rational, b: Rational) -> Rational:
    return Rational(gcd(a.p * b.q, b.p * a.q), a.q * b.q)


def _trigonometric_normal(e: Expr) -> Expr:
    """tan, cot, sec, csc (and the hyperbolic ones) in sin and cos; sin(k u),
    cos(k u) in sin(g u), cos(g u) (expand_trig), g the greatest common
    divisor of all multiples k of u the field has seen. So sin(2 x) and
    sin(x) cos(x) are in the same generators, related by cos**2 + sin**2 = 1,
    while sin(4 pi x) alone stays one generator. A finer g drops the old
    generators from the field; elements containing them are converted again."""
    e = e.replace(lambda f: type(f) in _QUOTIENTS, lambda f: _QUOTIENTS[type(f)](f.args[0]))
    state = _state()
    atoms = []
    for f in e.atoms(sin, cos, sinh, cosh):
        k, u = f.args[0].as_coeff_Mul(rational=True)
        family = sin if isinstance(f, (sin, cos)) else sinh
        atoms.append((f, family, k, u))
        key = (family, u)
        old = state.trig_base.get(key)
        g = abs(k) if old is None else _rational_gcd(old, k)
        if old is not None and g != old:
            pair = (sin, cos) if family is sin else (sinh, cosh)
            state.drop_generators(p(old * u) for p in pair)
        state.trig_base[key] = g
    rule = {}
    for f, family, k, u in atoms:
        m = k / state.trig_base[(family, u)]
        if m != 1:
            d = Dummy()
            rule[f] = expand_trig(type(f)(m * d)).xreplace({d: state.trig_base[(family, u)] * u})
    return e.xreplace(rule) if rule else e


def _prepare(e: Any) -> Expr:
    # b**(n - 1) -> b**n/b, exp(x + 1) -> E*exp(x), so that the field sees
    # the same generators whatever form the powers come in
    e = sympify(e)
    # a float is taken for the simplest rational within its precision (0.1
    # -> 1/10, not the binary approximation; 1.66666666666667 -> 5/3): the
    # field cannot represent floats, and as expressions they make every
    # comparison slow (Kamke 3.51: 124 s)
    floats = e.atoms(Float)
    if floats:
        e = e.xreplace({f: nsimplify(f, rational=True) for f in floats})
    if e.has(sin, cos, tan, cot, sec, csc, sinh, cosh, tanh, coth, sech, csch):
        e = _trigonometric_normal(e)
    return expand_power_exp(e)


@profile_if_enabled
def _to_field(e: Expr) -> FracElement:
    """e (prepared) as an element of the current field, or _UnsupportedError."""
    atoms: set[tuple[AtomKey, Rational]] = set()
    _collect_atoms(e, atoms)
    state = _state()
    state.extend(atoms)
    return _convert(e, state.field)


def _lift(f: FracElement) -> FracElement:
    """f as an element of the current field."""
    field = _state().field
    if f.field is field:
        return f
    old = f.field.symbols
    if field.symbols[: len(old)] == old:
        # the field has only been extended: pad the monomials with zeros
        ring = field.ring
        pad = (0,) * (ring.ngens - len(old))

        def padded(p: Any) -> Any:
            return ring.from_dict({m + pad: c for m, c in p.items()})

        return field.raw_new(padded(f.numer), padded(f.denom))
    # a generator has been replaced by a root of it, or f is of another field
    return _to_field(_prepare(f.as_expr()))


class Coeff:
    """A coefficient: an element of the current rational function field, or,
    if the field cannot represent it, a SymPy expression. As before this
    module, such an expression is brought into canonical form (``cancel``)
    only when needed: for the zero test, a comparison, and by canonical()."""

    __slots__ = ("_canonical", "_expr", "f")
    f: Any  # the field element, or None
    _expr: Any  # the SymPy expression if f is None
    _canonical: bool

    def __init__(self, e: "Coeff | Basic | int" = 0) -> None:
        if isinstance(e, Coeff):
            self.f, self._expr, self._canonical = e.f, e._expr, e._canonical
            return
        e = _prepare(e)
        try:
            self.f = _to_field(e)
            self._expr = None
        except _UnsupportedError:
            self.f = None
            self._expr = e
        self._canonical = self.f is not None

    @classmethod
    def _new(cls, f: FracElement | None = None, expr: Expr | None = None) -> "Coeff":
        new = object.__new__(cls)
        new.f = f
        new._expr = expr
        new._canonical = f is not None
        return new

    def canonical(self) -> "Coeff":
        """self, with an expression brought into canonical form."""
        if not self._canonical:
            self._expr = cancel(self._expr)
            self._canonical = True
        return self

    @property
    def is_field(self) -> bool:
        return self.f is not None

    def as_expr(self) -> Expr:
        if self._expr is None:
            self._expr = self.f.as_expr()
        return self._expr

    def _field_element(self) -> FracElement:
        f = self.f = _lift(self.f)
        return f

    def _common_field_elements(self, other: "Coeff") -> tuple[FracElement, FracElement]:
        """self and other as elements of the same (current) field."""
        a = self._field_element()
        b = other._field_element()
        if a.field is not b.field:  # lifting b has grown the field
            a = self._field_element()
        return a, b

    def _binary(self, other: CoeffLike, op: Callable[[Any, Any], Any]) -> "Coeff":
        if not isinstance(other, Coeff):
            other = Coeff(other)
        if self.f is not None and other.f is not None:
            return Coeff._new(f=op(*self._common_field_elements(other)))
        return Coeff._new(expr=op(self.as_expr(), other.as_expr()))

    def __add__(self, other: CoeffLike) -> "Coeff":
        return self._binary(other, operator.add)

    __radd__ = __add__

    def __sub__(self, other: CoeffLike) -> "Coeff":
        return self._binary(other, operator.sub)

    def __rsub__(self, other: CoeffLike) -> "Coeff":
        return self._binary(other, lambda a, b: b - a)

    def __mul__(self, other: CoeffLike) -> "Coeff":
        return self._binary(other, operator.mul)

    __rmul__ = __mul__

    def __truediv__(self, other: CoeffLike) -> "Coeff":
        return self._binary(other, operator.truediv)

    def __pow__(self, n: int) -> "Coeff":
        if self.f is not None:
            return Coeff._new(f=self._field_element() ** n)
        return Coeff._new(expr=self._expr**n)

    def __neg__(self) -> "Coeff":
        if self.f is not None:
            return Coeff._new(f=-self.f)
        return Coeff._new(expr=-self._expr)

    def __bool__(self) -> bool:
        if self.f is not None:
            # zero modulo cos**2 + sin**2 - 1 is zero (#61): only here and in
            # comparisons, the arithmetic stays in the field (reducing every
            # result would prevent cancellations: cos**2/cos)
            return bool(_state().reduce_numerator(self._field_element()))
        return self.canonical()._expr != 0

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Coeff):
            if isinstance(other, int) and self.f is not None:
                f = self.f
                if f.denom == 1 and f.numer == other:
                    return True
                if not _state().relations:
                    return False
            other = Coeff(other)
        if self.f is not None and other.f is not None:
            # field elements are canonical (coprime, normalized sign), so
            # compare them structurally: subtracting would need a gcd
            a, b = self._common_field_elements(other)
            if a == b:
                return True
            return bool(_state().relations) and not _state().reduce_numerator(a - b)
        return not self - other

    def __hash__(self) -> int:
        return hash(self.canonical().as_expr())

    def __str__(self) -> str:
        return str(self.as_expr())

    __repr__ = __str__

    @profile_if_enabled
    def diff(self, *variables: Basic) -> "Coeff":
        result = self
        for v in variables:
            result = result._diff(v)
        return result

    def _diff(self, v: Basic) -> "Coeff":
        if self.f is None:
            return Coeff._new(expr=self._expr.diff(v))
        f = self._field_element()
        # the derivatives of the generators depending on v; computing them
        # may add generators, so f is lifted afterwards
        state = _state()
        dgens: list[tuple[Basic, Coeff | None]] = []
        occurring = [
            g
            for g, dn, dd in zip(f.field.symbols, f.numer.degrees(), f.denom.degrees(), strict=True)
            if dn > 0 or dd > 0
        ]
        for g in occurring:
            if g == v:
                dgens.append((g, None))
            elif not g.is_Symbol and v in g.free_symbols:
                d = state.dgen.get((g, v))
                if d is None:
                    d = state.dgen[(g, v)] = Coeff(g.diff(v))
                if d.f is None:
                    return Coeff._new(expr=self.as_expr().diff(v))
                dgens.append((g, d))
        f = self._field_element()
        field = f.field
        result = field.zero
        for g, d in dgens:
            partial = f.diff(field.gens[state.index[g]])
            result += partial if d is None else partial * d._field_element()
        return Coeff._new(f=result)

    def xreplace(self, rule: dict) -> Expr:
        return self.as_expr().xreplace(rule)


def primitive(coeffs: Sequence[Coeff]) -> list[Coeff] | None:
    """coeffs times a common factor: coprime polynomials, the first one with
    a positive leading coefficient, so that proportional lists give the same
    result. None unless all of them are field elements.

    >>> from sympy import symbols
    >>> x, a = symbols("x a")
    >>> primitive([Coeff(-2 * x / (a + 1)), Coeff(4 / (a + 1)), Coeff(6 * x**2)])
    [x, -2, -3*a*x**2 - 3*x**2]
    """
    if any(c.f is None for c in coeffs):
        return None
    fs = [c._field_element() for c in coeffs]
    field = _state().field
    fs = [_lift(f) for f in fs]  # a later lift may have grown the field
    ring = field.ring
    den = ring.one
    for f in fs:
        if f.denom != ring.one:
            den = den.lcm(f.denom)
    nums = [f.numer * den.exquo(f.denom) for f in fs]
    content = ring.zero
    for n in nums:
        content = content.gcd(n)
        if content == ring.one:
            break
    if content != ring.one:
        nums = [n.exquo(content) for n in nums]
    if ring.domain.is_negative(nums[0].LC):
        nums = [-n for n in nums]
    return [Coeff._new(f=field.raw_new(n, ring.one)) for n in nums]


ONE = Coeff(1)
