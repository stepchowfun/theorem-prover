#!/usr/bin/python -O
# -*- coding: utf-8 -*-

# 2014 Stephan Boyer

from language import *

##############################################################################
# Axioms
##############################################################################

zero = Function("zero", [])
succ = lambda x:    Function("succ", [x])
add  = lambda x, y: Function("add", [x, y])
mul  = lambda x, y: Function("mul", [x, y])
eq   = lambda x, y: Predicate("Eq", [x, y])
x    = Variable("x")
y    = Variable("y")
z    = Variable("z")

axioms = {
  ForAll(x, eq(x, x)),
  ForAll(x, ForAll(y, Implies(eq(x, y), eq(y, x)))),
  ForAll(x, ForAll(y, ForAll(z, Implies(And(eq(x, y), eq(y, z)), eq(x, z))))),
  ForAll(x, Not(eq(zero, succ(x)))),
  ForAll(x, ForAll(y, Implies(eq(succ(x), succ(y)), eq(x, y)))),
  ForAll(x, eq(add(zero, x), x)),
  ForAll(x, eq(mul(zero, x), zero)),
  ForAll(x, ForAll(y, eq(add(x, succ(y)), succ(add(x, y))))),
  ForAll(x, ForAll(y, eq(mul(x, succ(y)), add(mul(x, y), y))))
}
