import os
with open("/home/tapir/hansi2.txt", "w") as f:
    f.write(f"{os.environ}")

import sage.all
from delierium.helpers import pairs_exclude_diagonal

def test_pairs_exclude_diagonal():
    it = range(5)
    for x, y in pairs_exclude_diagonal(it):
        assert x != y
