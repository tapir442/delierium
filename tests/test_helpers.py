"""Tests for delierium.helpers"""

from sympy import *

from delierium.helpers import is_function, pairs_exclude_diagonal


def test_pairs_exclude_diagonal():
    it = range(5)
    for x, y in pairs_exclude_diagonal(it):
        assert x != y


def test_pairs_exclude_diagonal_empty_output():
    it = range(1)
    for _ in pairs_exclude_diagonal(it):
        # shouldn't happen
        assert False


def test_is_function():
    x = Symbol('x')
    f = Function('f')(x)
    assert is_function(f)
    assert not is_function(diff(f, x))
    assert not is_function(x * diff(f, x))
    assert not is_function(x * f)
    g = Function('g')
    assert is_function(g)


def test_cached_property_survives_id_reuse():
    # The cache used to be keyed by id(expr). Once an expression is garbage
    # collected, a new one may get the same id and, from such a cache, the
    # free symbols of the old one. Create and drop many expressions and
    # compare each cached value with the uncached one.
    from sympy import Basic

    from delierium.helpers import clear_property_cache, make_cached_property

    clear_property_cache()
    getter = Basic.free_symbols.fget
    free_symbols = make_cached_property(Basic.free_symbols)
    for i in range(20000):
        e = Symbol(f's{i}') + i
        assert free_symbols.fget(e) == getter(e)
        del e
    clear_property_cache()


def test_derivative_patch_keeps_sympy_behaviour():
    # delierium replaces Derivative.__new__ for the whole process; diff
    # without a variable must still infer it (it used to return x**2)
    import pytest

    import delierium.helpers

    x, y = symbols('x y')
    assert diff(x**2) == 2 * x
    assert diff(sin(x) * x) == x * cos(x) + sin(x)
    assert diff(Integer(3)) == 0
    with pytest.raises(ValueError, match="more than one variable"):
        diff(x * y)
    with pytest.raises(ValueError, match="Can't calculate derivative wrt"):
        Derivative(x, 1 + x)
