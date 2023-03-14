#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Nov 10 11:10:23 2021

@author: tapir

Factored out from JanetBasis.py, for ease of debugging and extending

Holds everything for monomial involution stuff,like multipliers, divisions, etc.
"""
import itertools

def vec_degree(v, m):
    return m[v]

class Multipliers:
    """multipliers and nonmultipliers for differential vectors aka tuples

    m   : a tuple representing a differential vector
    M   : the complete set of differential vectors
    Vars: a tuple representing the order of indizes in m
          Examples:
              (0,1,2) means first index in m represents the highest variable
              (2,1,0) means last index in m represents the highest variable
    """
    def __init__(self, m, M, Vars):
        """
        The doctest example is from Schwarz, Example C.1, p. 384
        This example is in on variables x1,x2,x3, with x3 the highest rated variable.
        So we have to specify (2,1,0) to represent this

        >>> M = [(2,2,3), (3,0,3), (3,1,1), (0,1,1)]
        >>> r = Multipliers (M[0],M, (2,1,0))
        >>> print(M[0], r.multipliers, r.nonmultipliers)
        (2, 2, 3) [2, 1, 0] []
        >>> r = Multipliers (M[1],M, (2,1,0))
        >>> print (M[1], r.multipliers, r.nonmultipliers)
        (3, 0, 3) [2, 0] [1]
        >>> r = Multipliers (M[2],M, (2,1,0))
        >>> print (M[2], r.multipliers, r.nonmultipliers)
        (3, 1, 1) [1, 0] [2]
        >>> r = Multipliers (M[3],M, (2,1,0))
        >>> print (M[3], r.multipliers, r.nonmultipliers)
        (0, 1, 1) [1] [0, 2]
        >>> N=[[0,2], [2,0], [1,1]]
        >>> r =Multipliers(N[0], N,  (0,1))
        >>> print(r.multipliers, r.nonmultipliers)
        [1] [0]
        >>> r =Multipliers(N[1], N,  (0,1))
        >>> print(r.multipliers, r.nonmultipliers)
        [0, 1] []
        >>> r =Multipliers(N[2], N,  (0,1))
        >>> print(r.multipliers, r.nonmultipliers)
        [1] [0]
        >>> r =Multipliers(N[0], N,  (1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [1, 0] []
        >>> r =Multipliers(N[1], N,  (1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [0] [1]
        >>> r =Multipliers(N[2], N,  (1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [0] [1]
        >>> # next example form Gertd/Blinkov: Janet-like monomial divisiom, Table1
        >>> # x1 -> Index 2
        >>> # x2 -> Index 1 (this is easy)
        >>> # x3 -> Index 0
        >>> U = [[0,0,5], [1,2,2],[2,0,2], [1,4,0],[2,1,0],[5,0,0]]
        >>> r = Multipliers(U[0], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [2, 1, 0] []
        >>> r = Multipliers(U[1], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [1, 0] [2]
        >>> r = Multipliers(U[2], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [0] [1, 2]
        >>> r = Multipliers(U[3], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [1, 0] [2]
        >>> r = Multipliers(U[4], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [0] [1, 2]
        >>> r = Multipliers(U[5], U, (2,1,0))
        >>> print(r.multipliers, r.nonmultipliers)
        [0] [1, 2]
        >>> M = [(1,0), (0,3)]
        >>> r = Multipliers(M[0], M, (0,1))
        >>> print(r.multipliers, r.nonmultipliers)
        [1] [0]
        >>> print(r.multipliers, r.nonmultipliers)
        [1] [0]
        
        """
        d = max((vec_degree(v, u) for u in M for v in Vars), default=0)
        mult = []
        if vec_degree(Vars[0], m) == d:
            mult.append(Vars[0])
        for j in range(1, len(Vars)):
            v = Vars[j]
            dd = list(map(lambda x: vec_degree(x, m), Vars[:j]))
            V = []
            for _u in M:
                if [vec_degree(_v, _u) for _v in Vars[:j]] == dd:
                    V.append(_u)
            if vec_degree(v, m) == max((vec_degree(v, _u) for _u in V), default=0):
                mult.append(v)
        self.multipliers    = mult
        self.nonmultipliers = list(sorted(set(Vars) - set(mult)))

def complete(S):
    # S: list of monomial tuples. Highest variable ist the last index 
    result = list(S)
    if len(result) == 1:
        return result
    vars = list(range(len(context._independent)))
    def map_old_to_new(v):
        return context._independent[vars.index(v)]
    while 1:
        # XXX put that line on top, then call 'complete' from Involution
        monomials = [(_, derivative_to_vec(_.Lder(), context)) for _ in result]
        ms        = tuple([_[1] for _ in monomials])
        m0 = []

        # multiplier-collection is our M
        multiplier_collection = []
        for dp, monom in monomials:
            # S1
            division = Multipliers(monom, ms, vars)
            _multipliers, _nonmultipliers = division.multipliers, division.nonmultipliers
            multiplier_collection.append((monom, dp, _multipliers, _nonmultipliers))
        for monom, dp, _multipliers, _nonmultipliers in multiplier_collection:
            if not _nonmultipliers:
                m0.append((monom, None, dp))
            else:
                # todo: do we need subsets or is a multiplication by only one
                # nonmultiplier one after the other enough ?
                for n in _nonmultipliers:
                    _m0 = list(monom)
                    _m0[n] += 1
                    m0.append((_m0, n, dp))
        to_remove = []
        for _m0 in m0:
            # S3: check whether in class of any of the monomials
            for monomial, _, _multipliers, _nonmultipliers in multiplier_collection:
                if all(_m0[0][x] >= monomial[x] for x in _multipliers) and \
                   all(_m0[0][x] == monomial[x] for x in _nonmultipliers):
                    # this is in _m0's class
                    to_remove.append(_m0)
        for _to in to_remove:
            try:
                m0.remove(_to)
            except:
                pass
        if not m0:
            # XXX create the _Differntial Polynomials here
            return result
        else:
            for _m0 in m0:
                # XXX don't create the polynomials, just the monomial tuples
                dp = _Differential_Polynomial(_m0[2].diff(map_old_to_new(_m0[1])).expression(), context)
                if dp not in result:
                    result.append(dp)
        result = Reorder(result, context, ascending=False)        
        
        
        
#def complete(S):
#    # S: list of monomial tuples. Highest variable ist the last index 
#    # highest index is most important, we, have xn >...> x1
#    from IPython.core.debugger import set_trace
#    monomials = S[:]
#    result = []
#    all_vars = set([_ for _ in range(len(monomials[0]))])
#    while 1:
#        m0 = []
#        # multiplier-collection is our M
#        multiplier_collection = []
#        division = My_Multiplier(monomials)
#        multiplier_collection = [(v, all_vars - v, k) for k, v in division.mults.items()]
#        for mult, nonmult, monom, in multiplier_collection:
#            for n in nonmult:
#                _m0 = list(monom)
#                _m0[n] += 1
#                m0.append((_m0, n, monom))
#        to_remove = []
#        #set_trace()
#        for _m0 in m0:
#            # S3: check whether in class of any of the monomials
#            for mult, nonmult, monom in multiplier_collection:
#                s1 = [_m0[0][x] >= monom[x] for x in mult]
#                s2 = [_m0[0][x] == monom[x] for x in nonmult]
#                if all(s1) and all(s2):
#                    # this is in _m0's class
#                    to_remove.append(_m0)
#                    break
#                    
#        for _to in to_remove:
#            try:
#                m0.remove(_to)
#            except:
#                pass
#        if not m0:
#            # XXX create the _Differntial Polynomials here
#            return result
#        else:
#            result.extend(m0)
#            monomials.extend([tuple(_[0]) for _ in m0])
        
        
        
        # https://amirhashemi.iut.ac.ir/sites/amirhashemi.iut.ac.ir/files//file_basepage/invbasis.txt#overlay-context=contents
#Janet:=proc(u,U,Vars)
#local n,m,d,L,i,j,dd,V,v,Mult;
#option trace;
#if degree(u)=0 then RETURN(Vars); fi;
#n:=nops(Vars);
#m:=ArrayNumElems(U);
#d:=[seq(max(seq(degree(U[j],Vars[i]),j=1..m)),i=1..n)];
#Mult:=NULL;
#    if degree(u,Vars[1])=d[1] then
#      Mult:=Mult,Vars[1];
#     fi:
#for j from 2 to n do
#    dd:=[seq(degree(u,Vars[l]),l=1..j-1)];
#    V:=NULL:
#    for v in U do
#       if [seq(degree(v,Vars[l]),l=1..j-1)]=dd then
#          V:=V,v:
#       fi:
#    od:
#    if degree(u,Vars[j])=max(seq(degree(v,Vars[j]), v in [V])) then
#       Mult:=Mult,Vars[j];
#    fi:
#od:
#RETURN([Mult]);
#end:

def degree_of_set(j, U):
    return max(u[j] for u in U)
    
def degree(j):
    return u[j]

class My_Multiplier:
    def __init__(self, M):
        self.degrees = {}
        # no of variables
        n = len(M[0])
        for i in range(n):
            self.degrees[i] = 0
            for m in M:
                self.degrees[i] = max(self.degrees[i], m[i])
        self.max_degree = max (self.degrees.values())
        self.mults = {}
        for m in M:
            self.mults[tuple(m)] = set()
        self.alphas = {}
        for m in M:
            if m[n-1] == self.degrees[n-1]:
                self.mults[m].add(n-1)
        tuples = [ele for ele in itertools.product(range(0, self.max_degree+1), repeat = 1)]
        self.alphas = {}
        for t in tuples:
            self.alphas[t] = set([m for m in M if all(m[n-1] == _t for _t in t)])
        to_delete = [_ for _ in self.alphas if not self.alphas[_]]
        for t in to_delete:
            del self.alphas[t]

        for j in reversed(range(n-1)):
            for m in M:
                if m[j] == self.degrees[j]:
                    self.mults[m].add(j)
            for m in M:
                for a in self.alphas:
                    if m in self.alphas[a] and m[j] == degree_of_set(j, self.alphas[a]):
                        self.mults[m].add(j)
            if n != 0:
                tuples = [ele for ele in itertools.product(range(0, self.max_degree+1), repeat = n - j)]       
                self.alphas = {}
                for t in tuples:
                    self.alphas[t] = set(m for m in M if list(m[j:]) == list(t))
                to_delete = [_ for _ in self.alphas if not self.alphas[_]]                    
                for t in to_delete:
                    del self.alphas[t]