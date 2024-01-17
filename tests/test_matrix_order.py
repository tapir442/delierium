"""Tests for delierium.Matrix_Order"""

import sage.all
from delierium.helpers import is_function, pairs_exclude_diagonal, compactify
from sage.calculus.functional import diff
from sage.calculus.var import function, var
from delierium.MatrixOrder import insert_row

from sage.matrix.constructor import identity_matrix, matrix, Matrix

def test_insert_row():
    assert 1
