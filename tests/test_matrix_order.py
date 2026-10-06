"""Tests for delierium.Matrix_Order"""

from sympy import Matrix, symbols

from delierium.matrix_order import insert_row


def test_insert_row():
    x, y = symbols("x y")
    m = Matrix([[1, 2], [3, 4]])
    assert insert_row(m, 0, [x, y]) == Matrix([[x, y], [1, 2], [3, 4]])
    assert insert_row(m, 1, Matrix([[x, y]])) == Matrix([[1, 2], [x, y], [3, 4]])
    assert insert_row(m, 2, [x, y]) == Matrix([[1, 2], [3, 4], [x, y]])
