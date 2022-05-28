#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jan 22 07:46:07 2022

@author: tapir
"""



# from https://ask.sagemath.org/question/7929/computing-variational-derivatives/
from sage.all import *
import sage.symbolic.operators
from IPython.core.debugger import set_trace
from delierium.helpers import is_derivative, is_function


def analyze_term (term, pattern = None):
    operands = term.operands()
    for operand in operands:
        print (operand)


x,y,z=var('x y z')

f = function("f")
g= function("g")

def analyze_term (term, pattern = None):
    operands = term.operands()
    print (term.collect(g(x,y)))
    print (term.degree(g(x,y)))
#    for operand in operands:
#        print("..............")
#        print (operand)
#        print(operand.operator(), operand.operands())
#        set_trace ()
#        if operand.operator() == pow:
#            print ("================================>", operand.operator()[-1])


l = (x*y**2-sin(z))*diff(f(x,y),x,y)*(f(x,y)**2)*(g(x,y)**3)
print(l)
analyze_term(l)

l = (x*y**2-sin(z))*diff(f(x,y),x,y)*(f(x,y)**2)
print(l)
analyze_term(l)
