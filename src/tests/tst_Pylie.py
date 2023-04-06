import sage
from sage.all import *

import sys
from pprint import pprint
with open ("/home/tapir/mausi.txt", "w") as f:
    f.write("%s" % sys.path)


def testDelieriumFunction():
    var('x')
    u = function ("u")(x)
    d = diff (u,x)
    assert is_derivative (d)
    assert not is_derivative (u)
