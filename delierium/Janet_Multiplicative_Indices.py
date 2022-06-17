# -*- coding: utf-8 -*-
"""

"""

import more_itertools
from IPython.core.debugger import set_trace

l = [[2,3,3],[1,3,3],[0,3,3],[1,0,3],[1,2,1],[4,2,0],[2,2,0],[0,2,0]]

def Janet_Multiplicative_Indices(B: list)->list:
    # XXX Fix SSorting
    #B = sorted(B, reverse = True)
    ny = B[0]
    # Attention, postfence
    p1 = len(ny) - 1
    # Attention, postfence
    I  = set(range(p1+1))
    M  = [list(I)]
   # #import pdb; pdb.set_trace()
    for k in range(1,len(B)):
        dif = [a - b for a,b in zip(ny, B[k])]
        p2  = max(more_itertools.locate(dif, lambda _: _ > 0))
        I.discard(p2)
        if p1 < p2:
            I |= set(range(p1, p2))
        M.append(list(I))
        ny = B[k]
        p1 = p2
    return M


res = Janet_Multiplicative_Indices(l)
from pprint import pprint
pprint(res)

#def Involutive_Basis(B):
#    Bbar = B[:]
#    while 1:
#        S = [ny + [0,0,1] for
#             ny in Bbar for j in Nlbm if v+[0,0,1] not in BbasrL]
#        if not S:
#            return Bbar
#        choess my
#        Bbar != my

#pprint(Janet_Multiplicative_Indices([[1,1,3],[3,0,3] ,[3,2,2],[1,1,0]]))

print("A")

pprint(Janet_Multiplicative_Indices([[2,2,3],[3,0,3],[3,1,1],[0,1,1]]))

def divides(u,w):
    #return all(_[0] <= _[1] for _ in zip(u,w))
    # this is much faster than functional approach
    for _ in zip(u,w):
        if _[0] > _[1]:
            return False
    return True

def Ldivisor(u,v):
    return True


#%timeit divides([0,0,0,0,0,0,0], [1,0,0,0,0,0,1])
#%timeit divides([3,0,0,0,0,0,0], [2,0,0,0,0,0,1])
#print(divides([0,0,0,0,0,0,0], [1,0,0,0,0,0,1]))
#print(divides([3,0,0,0,0,0,0], [2,0,0,0,0,0,1]))

if divides([0,0,0,0,0,0,0], [1,0,0,0,0,0,1]):
    print ("A")
if divides([3,0,0,0,0,0,0], [2,0,0,0,0,0,1]):
    print("B")

# Example from "Construction of Janet Bases, I. Monomial Bases, Example 1"
l = [[0,1,2],[1,0,1],[0,2,0],[1,1,0],[2,0,0]]
pprint(Janet_Multiplicative_Indices(l))
l = [[2,1,0],[1,0,1],[0,2,0],[0,1,1],[0,0,2]]
pprint(Janet_Multiplicative_Indices(l))


class Node:
    def __init__(self, data):
        self._data = data
        self._ndg  = None # left
        self._nvr  = None # right
##mon(v) = u is the monomial assigned to v,
#ndg(v) = nd is the pointer to the next node in degree,
#nvr(v) = nv is the pointer to the next node in variable.
    def mon(self):
        return self._data
    @property
    def nvr(self):
        return self._nvr
    @nvr.setter
    def nvr(self, v):
        self._nvr = v
    @property
    def ndg(self):
        return self._ndg
    @ndg.setter
    def ndg(self, v):
        self._ndg = v
    def __str__ (self):
        return "%s" % [self._data, self.ndg, self.nvr]
    def __lt__ (self, other):
        return self.data < other
    def __eq__(self, other):
        return self._data == other._data

class Janet_Tree:
    def __init__(self, root):
        self._root = root

    def insert (self, u):
        pass

    def root(self):
        return self._root

class Monomial:
    def __init__(self, l):
        self._l = l[:]
    def __hash__(self):
        return hash("%s" % self._l)
    def __eq__(self, other):
        return self._l == other._l
    def __lt__(self, other):
        pass
    def __mul__(self, i):
        s = self._l[:]
        s[i] = s[i] + 1
        return Monomial(s)
    def deg(self, i):
        return self._data[i]
    def divides(self, other):
        #return all(_[0] <= _[1] for _ in zip(self.data,w.data))
        # this is much faster than functional approach
        for _ in zip(self._data, other._data):
            if _[0] > _[1]:
                return False
        return True
    def __len__ (self):
        return len(self._data)


class Janet_Node(Node, Monomial):
    def __str__(self):
        return "[%s], L:%s, R:%s]" % (self._data, self.ndg, self.nvr)
#    def __repr__(self):
#        return self.__str__()
    def __mul__(self, i):
        d = self._data[:]
        d[i] += 1
        return Janet_Node(d)
    def __eq__(self, other):
        return self._data == other._data
def JDivisor(JT, w):
    v = JT.root()
    n = len(v._data)
    while v.divides(w):
        while v.ndg and v.ndg.divides (w):
            v = v.ndg
        if v.nvr:
            v = v.nvr
        elif v.ndg:
            return None
        else:
            # for the algorithm from the paper this would not
            # work as for the tree only containing the root we
            # will always return the root as a leave. So we need that
            # extra check for the root
            if v._data == [0]*n:
                return None
            else:
                return v._data

def OneleafTree(u, i, w):
    v    = w
    tree = [v]
    _w   = w
    n    = len(v)
    while u != _w and i < n:
        while 1:
            _w = _w * i
            if _w.divides(u):
                v.ndg = _w
                v     = v.ndg
#                tree.append(v)
            else:
                # XXX: this is not nice :(.
                # we are one too far
                #_w._data[i] -= 1
                break
        if u != _w:
            v.nvr = _w
            v     = v.nvr
 #           tree.append(v)
            i    += 1
#    return tree

def JProlong(jt, i, V):
    v = jt
    while v.ndg:
        if v.nvr:
            JProlong(v, i, V)
        v = v.ndg
    if v.nvr:
        JProlong(v, i, V)
    else:
        V.append(v*i)
    return V


def JInsert(JT, u, V):
    i     = 0
    JTree = JT
    v     = JTree.root()
    n     = len(v)
    while i < n:
        # make this indexing into a method named 'deg'
        while v.deg(i) < u.deg(i) and v.ndg:
            v = v.ndg
        if v.deg(i) < u.deg(i):
            JProlong(v,i,V)
            #jtree  = OneleafTree(u, i, v*i)
            OneleafTree(u, i, v*i)
#            set_trace()
#            v.ndg  = jtree[0]
            # strange stop criterion
            i = n + 1
        else:
            if v.ndg:
                V.append(u*i)
            if v.nvr:
                i += 1
                v  = v.nvr
            else:
                if i < n-1:
                    #jtree = OneleafTree(u, i + 1, v)
                    OneleafTree(u, i + 1, v)
#                    set_trace()
                    #v.ndg = jtree[0]
                    i = n + 1
    return JTree, V

def MonomialJanetBasis(U):
    def choose(l):
        """
        choose u in l without divisor in V \ {u}

        Parameters
        ----------
        l : TYPE
            list of monomials

        Returns
        -------
        TYPE
            monomial

        """
        if len(l) == 1:
            return l[0]
        for i in range(len(l)):
            for j in range(i+1, len(l)):
                div = [_[0] - _[1] for _ in zip(l[i]._data, l[j]._data)]
                if Janet_Node(div) not in V:
                    return l[i]
    unit_monomial = Janet_Node([0]*len(U[0]))
    tree = Janet_Tree(unit_monomial)
    V    = [Janet_Node(u) for u in U]
    if unit_monomial in V:
        Ubar = [unit_monomial]
    else:
        Ubar = []
        while V:
            u = choose(V)
            V.remove(u)
            set_trace()
            if JDivisor(tree, u) is None:
                Ubar.append(u)
                JInsert(tree, u, V)
    return Ubar

mausi = MonomialJanetBasis(l)

pprint(mausi)

# =============================================================================
#
# 1: i:= 1
# 2: JTree:= JT
# 3: v:= root(JTree)
# 4: while i ::; n do
# 5:   while deg i (mon(v» < degi(u) and ndg(v) do
# 6:     v := ndg(v)
# 7:   od
# 8:   if degi(mon(v» < degi(u) then
# 9:     J-prolong(jst(v), i, V)
# 10:    jtree :=OneleafTree(u, i, mon(v)· Xi)
# 11:   ndg(v) := root(jtree)
# 12:
#  JTree := JTree U jtree
# 13:
#  i:= n + 1
# 14:
#  else
# 15:
#  if ndg(v) then
# 16:
#  V := V U {u . xd
# 17:
#  fi
# 18:
#  if nvr(v) then
# 19:
#  i := i + 1
# 20:
#  v := nvr(v)
# 21:
#  else
# 22:
#  if i < n then
# 23:
#  jtree :=OneleafTree(u, i + 1, mon(v»
# 24:
#  ndg(v) := root(jtree)
# 25:
#  JTree := JTree U jtree
# 26:
#  i := n + 1
# 27:
#  fi
# 28:
#  fi
# 29:
#  fi
# 30: od
# 31: return JTree, V
# =============================================================================
# =============================================================================
# Input: U, a finite set of distinct monomials
# Output: U, the minimal Janet basis of ideal I d(U)
# 1: JT:= {{I, nil, nil}}
# 2: V:= U
# 3: if 1 E V then
# 4:
#  U:={I}
# 5: else
# 6:
#  U:= 0
# 7:
#  while V i= 0 do
# 8:
#  choose u E V without divisor in V \ {u}
# 9:
#  V:=V\{u}
# 10:
#  if J-divisor(JT, u) = nil then
# 11:
#  U:=UU{u}
# 12:
#  J-insert(JT, u, V)
# 13:
#  fi
# 14:
#  od
# 15: fi
# 16: return U
#
# =============================================================================

class Janet_Tree:
    def __init__(self, monomials):
        pass
