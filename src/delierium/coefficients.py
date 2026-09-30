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
is ``exp(x)**2``, and ``y**(n - 1)`` is ``y**n/y``. A float is taken for the
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
"""

# Coeff's private helpers are applied to other Coeff instances as well
# pylint: disable=protected-access

from contextlib import contextmanager
from contextvars import ContextVar
from math import lcm
from typing import Any

from sympy import (
    Derivative,
    Float,
    Pow,
    Rational,
    S,
    Symbol,
    cancel,
    expand_power_exp,
    sympify,
)
from sympy.core.function import AppliedUndef, Function
from sympy.functions.elementary.exponential import ExpBase
from sympy.polys.domains import ZZ
from sympy.polys.fields import FracField

from delierium.helpers import profile_if_enabled

__all__ = [
    "Coeff",
    "fresh_field",
]


class _UnsupportedError(Exception):
    """The expression contains an atom the field cannot represent."""


class _FieldState:
    """A field and the generators it is built from.

    A generator stands for all powers b**(c*rest) with rational c of a base b
    and a symbolic part rest of the exponent (rest = 1 for a plain atom): the
    generator is b**(rest/L), L the common denominator of all c seen so far,
    and b**(c*rest) is its (c*L)-th power.
    """

    def __init__(self):
        self.keys = {}  # (b, rest) -> L
        self.symbols: tuple = ()  # the generators as expressions, in field order
        self.field = FracField((Symbol("_delierium_dummy"),), ZZ)
        self.index = {}  # generator expression -> index
        self.dgen = {}  # (generator expression, variable) -> Coeff

    @staticmethod
    def generator(key, L):
        base, rest = key
        return Pow(base, rest / L)

    def element_of(self, key, c):
        """The atom b**(c*rest) as an element of the current field."""
        L = self.keys[key]
        g = self.field.gens[self.index[self.generator(key, L)]]
        return g ** int(c * L)

    def extend(self, atoms):
        """Make every (key, c) in atoms representable; True if the field changed."""
        changed = False
        for key, c in atoms:
            L = self.keys.get(key)
            q = Rational(c).q
            if L is None:
                self.keys[key] = q
                changed = True
            elif L % q:
                self.keys[key] = lcm(L, q)
                changed = True
        if changed:
            self.symbols = tuple(self.generator(k, L) for k, L in self.keys.items())
            self.index = {g: i for i, g in enumerate(self.symbols)}
            self.field = FracField(self.symbols, ZZ)
        return changed


# the field outside of any fresh_field(), shared by all threads
_default = _FieldState()
_current: ContextVar[_FieldState | None] = ContextVar("delierium_coefficient_field", default=None)


def _state():
    """The field of the running computation."""
    return _current.get() or _default


@contextmanager
def fresh_field():
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


def _is_transcendental_atom(e):
    """Symbols, E, pi and applied functions: no algebraic relation with
    anything else the field contains."""
    return (
        e.is_Symbol
        or e in (S.Exp1, S.Pi)
        or isinstance(e, (AppliedUndef, Derivative))
        or (isinstance(e, Function) and not isinstance(e, ExpBase))
    )


def _atom_key(e):
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


def _split_exponent(e):
    """b**(e1 + e2 + ...) as the factors b**e1, b**e2, ..., or None."""
    if isinstance(e, (Pow, ExpBase)):
        base, exp = e.as_base_exp()
        if exp.is_Add:
            return [Pow(base, a, evaluate=False) for a in exp.args]
    return None


def _collect_atoms(e, atoms):
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


def _convert(e, field):  # pylint: disable=too-many-return-statements
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


def _prepare(e):
    # b**(n - 1) -> b**n/b, exp(x + 1) -> E*exp(x), so that the field sees
    # the same generators whatever form the powers come in
    e = sympify(e)
    # a float is taken for the decimal it prints as (0.1 -> 1/10, not the
    # binary approximation): the field cannot represent floats, and as
    # expressions they make every comparison slow (Kamke 3.51: 124 s)
    floats = e.atoms(Float)
    if floats:
        e = e.xreplace({f: Rational(str(f)) for f in floats})
    return expand_power_exp(e)


@profile_if_enabled
def _to_field(e):
    """e (prepared) as an element of the current field, or _UnsupportedError."""
    atoms: set = set()
    _collect_atoms(e, atoms)
    state = _state()
    state.extend(atoms)
    return _convert(e, state.field)


def _lift(f):
    """f as an element of the current field."""
    field = _state().field
    if f.field is field:
        return f
    old = f.field.symbols
    if field.symbols[: len(old)] == old:
        # the field has only been extended: pad the monomials with zeros
        ring = field.ring
        pad = (0,) * (ring.ngens - len(old))

        def padded(p):
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

    def __init__(self, e=0):
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
    def _new(cls, f=None, expr=None):
        new = object.__new__(cls)
        new.f = f
        new._expr = expr
        new._canonical = f is not None
        return new

    def canonical(self):
        """self, with an expression brought into canonical form."""
        if not self._canonical:
            self._expr = cancel(self._expr)
            self._canonical = True
        return self

    @property
    def is_field(self):
        return self.f is not None

    def as_expr(self):
        if self._expr is None:
            self._expr = self.f.as_expr()
        return self._expr

    def _field_element(self):
        f = self.f = _lift(self.f)
        return f

    def _binary(self, other, op):
        if not isinstance(other, Coeff):
            other = Coeff(other)
        if self.f is not None and other.f is not None:
            a = self._field_element()
            b = other._field_element()
            if a.field is not b.field:  # lifting b has grown the field
                a = self._field_element()
            return Coeff._new(f=op(a, b))
        return Coeff._new(expr=op(self.as_expr(), other.as_expr()))

    def __add__(self, other):
        return self._binary(other, lambda a, b: a + b)

    __radd__ = __add__

    def __sub__(self, other):
        return self._binary(other, lambda a, b: a - b)

    def __rsub__(self, other):
        return self._binary(other, lambda a, b: b - a)

    def __mul__(self, other):
        return self._binary(other, lambda a, b: a * b)

    __rmul__ = __mul__

    def __truediv__(self, other):
        return self._binary(other, lambda a, b: a / b)

    def __pow__(self, n):
        if self.f is not None:
            return Coeff._new(f=self._field_element() ** n)
        return Coeff._new(expr=self._expr**n)

    def __neg__(self):
        if self.f is not None:
            return Coeff._new(f=-self.f)
        return Coeff._new(expr=-self._expr)

    def __bool__(self):
        if self.f is not None:
            return bool(self.f.numer)
        return self.canonical()._expr != 0

    def __eq__(self, other):
        if not isinstance(other, Coeff):
            if isinstance(other, int) and self.f is not None:
                f = self.f
                return f.denom == 1 and f.numer == other
            other = Coeff(other)
        if self.f is not None and other.f is not None:
            # field elements are canonical (coprime, normalized sign), so
            # compare them structurally: subtracting would need a gcd
            a = self._field_element()
            b = other._field_element()
            if a.field is not b.field:  # lifting b has grown the field
                a = self._field_element()
            return a == b
        return not self - other

    def __hash__(self):
        return hash(self.canonical().as_expr())

    def __str__(self):
        return str(self.as_expr())

    __repr__ = __str__

    @profile_if_enabled
    def diff(self, *variables):
        result = self
        for v in variables:
            result = result._diff(v)
        return result

    def _diff(self, v):
        if self.f is None:
            return Coeff._new(expr=self._expr.diff(v))
        f = self._field_element()
        # the derivatives of the generators depending on v; computing them
        # may add generators, so f is lifted afterwards
        state = _state()
        dgens = []
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

    def xreplace(self, rule):
        return self.as_expr().xreplace(rule)


def primitive(coeffs):
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
