"""Tests for delierium.Matrix_Order"""

import pytest
import sage.all
from delierium.MatrixOrder import insert_row
from sage.calculus.functional import diff
from sage.calculus.var import function, var
from sage.matrix.constructor import Matrix, identity_matrix, matrix


@pytest.mark.parametrize("no_vars, expected",
                         [(1, matrix([[4], [1]])),
                          (2, matrix([[4, 4],
                                      [1, 0],
                                      [0, 1]])),
                          (3, matrix([[4, 4, 4],
                                      [1, 0, 0],
                                      [0, 1, 0],
                                      [0,0,1]]
                                     )
                           )
                          ]
                         )
def test_insert_row(no_vars, expected):
    """test for 'insert_row'

    Args:
        no_vars: size of matrix
        expected: expected values
    """
    im = identity_matrix(no_vars)
    i = insert_row(im, 0, [4]*no_vars)
    assert i == expected



def test_mlex(context_x_y_z_u_v_w_mlex):
    print(context_x_y_z_u_v_w_mlex)
#    assert context_x_y_z_u_v_w_mlex.independent == [x,y,z]
#    assert context_x_y_z_u_v_w_mlex.dependent == [u,v,w]
    print(dir(context_x_y_z_u_v_w_mlex.weight))
    assert context_x_y_z_u_v_w_mlex.weight == matrix\
        ([[0, 0, 0, 3, 2, 1],
          [1, 0, 0, 0, 0, 0],
          [0, 1, 0, 0, 0, 0],
          [0, 0, 1, 0, 0, 0]])
