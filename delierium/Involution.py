#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Nov 10 11:10:23 2021

@author: tapir

Factored out from JanetBasis.py, for ease of debugging and extending

Holds everything for monomial involution stuff,like multipliers, divisions, etc.
"""

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