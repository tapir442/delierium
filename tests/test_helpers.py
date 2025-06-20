"""Tests for delierium.helpers"""

import sage.all
from delierium.helpers import is_function, pairs_exclude_diagonal, compactify
from sage.calculus.functional import diff
from sage.calculus.var import function, var


def test_pairs_exclude_diagonal():
    it = range(5)
    for x, y in pairs_exclude_diagonal(it):
        assert x != y

def test_pairs_exclude_diagonal_empty_output():
    it = range(1)
    for x, y in pairs_exclude_diagonal(it):
        # shouldn't happen
        assert False

def test_is_function():
    x = var('x')
    f = function('f')(x)
    assert is_function(f)
    assert not is_function(diff(f, x))
    assert not is_function(x*diff(f, x))
    assert not is_function(x*f)
    g = function('g')
    # XXX: this because g has no parameters
    assert not is_function(g)
