#!/usr/bin/python -O
# -*- coding: utf-8 -*-

from axioms import *

##############################################################################
# Sequents
##############################################################################

class Sequent:
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def fv(self):
    result = set()
    for formula in self.left:
      result |= formula.fv()
    for formula in self.right:
      result |= formula.fv()
    return result

  def isAxiomaticallyTrue(self):
    # TODO: check up to unification
    if len(self.left & self.right) > 0:
      return True
    return False

##############################################################################
# Proof search
##############################################################################

class SearchResult(Exception):
  def __init__(self, result):
    self.result = result

# returns True if a proof was found
# returns False if not provable
def proofGenerator(sequent):
  frontier = [sequent]
  while len(frontier) > 0:
    # get the next sequent
    old_sequent = frontier.pop(0)
    if old_sequent.isAxiomaticallyTrue():
      continue
    
    # attempt to reduce a formula in the sequent
    reduced = False

    # left side
    for formula in old_sequent.left:
      yield
      if isinstance(formula, Variable):
        continue
      if isinstance(formula, Function):
        continue
      if isinstance(formula, Predicate):
        continue
      if isinstance(formula, Not):
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.left.remove(formula)
        new_sequent.right.add(formula.formula)
        frontier.append(new_sequent)
        reduced = True
        break
      if isinstance(formula, And):
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.left.remove(formula)
        new_sequent.left.add(formula.formula_a)
        new_sequent.left.add(formula.formula_b)
        frontier.append(new_sequent)
        reduced = True
        break
      if isinstance(formula, Or):
        new_sequent_a = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_b = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_a.left.remove(formula)
        new_sequent_b.left.remove(formula)
        new_sequent_a.left.add(formula.formula_a)
        new_sequent_b.left.add(formula.formula_b)
        frontier.append(new_sequent_a)
        frontier.append(new_sequent_b)
        reduced = True
        break
      if isinstance(formula, Implies):
        new_sequent_a = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_b = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_a.left.remove(formula)
        new_sequent_b.left.remove(formula)
        new_sequent_a.right.add(formula.formula_a)
        new_sequent_b.left.add(formula.formula_b)
        frontier.append(new_sequent_a)
        frontier.append(new_sequent_b)
        reduced = True
        break
    if reduced:
      continue
    for formula in old_sequent.left:
      yield
      if isinstance(formula, ThereExists):
        fv = old_sequent.fv()
        index = 1
        name = "var" + str(index)
        while name in fv:
          index += 1
          name = "var" + str(index)
        variable = Variable(name)
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.left.add(formula.formula.replace(formula.variable, variable))
        frontier.append(new_sequent)
        reduced = True
        break
    if reduced:
      continue
    for formula in old_sequent.left:
      yield
      if isinstance(formula, ForAll):
        raise NotImplementedError()
    if reduced:
      continue

    # right side
    for formula in old_sequent.right:
      yield
      if isinstance(formula, Variable):
        continue
      if isinstance(formula, Function):
        continue
      if isinstance(formula, Predicate):
        continue
      if isinstance(formula, Not):
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.right.remove(formula)
        new_sequent.left.add(formula.formula)
        frontier.append(new_sequent)
        reduced = True
        break
      if isinstance(formula, And):
        new_sequent_a = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_b = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent_a.right.remove(formula)
        new_sequent_b.right.remove(formula)
        new_sequent_a.right.add(formula.formula_a)
        new_sequent_b.right.add(formula.formula_b)
        frontier.append(new_sequent_a)
        frontier.append(new_sequent_b)
        reduced = True
        break
      if isinstance(formula, Or):
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.right.remove(formula)
        new_sequent.right.add(formula.formula_a)
        new_sequent.right.add(formula.formula_b)
        frontier.append(new_sequent)
        reduced = True
        break
      if isinstance(formula, Implies):
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.right.remove(formula)
        new_sequent.left.add(formula.formula_a)
        new_sequent.right.add(formula.formula_b)
        frontier.append(new_sequent)
        reduced = True
        break
    if reduced:
      continue
    for formula in old_sequent.right:
      yield
      if isinstance(formula, ForAll):
        fv = old_sequent.fv()
        index = 1
        name = "var" + str(index)
        while name in fv:
          index += 1
          name = "var" + str(index)
        variable = Variable(name)
        new_sequent = Sequent(old_sequent.left.copy(), old_sequent.right.copy())
        new_sequent.right.add(formula.formula.replace(formula.variable, variable))
        frontier.append(new_sequent)
        reduced = True
        break
    if reduced:
      continue
    for formula in old_sequent.right:
      yield
      if isinstance(formula, ThereExists):
        raise NotImplementedError()
    if not reduced:
      raise SearchResult(False)

  # no more sequents to prove
  raise SearchResult(True)

# returns True if the sequent is provable
# returns False if the sequent is not provable
def proveSequent(sequent):
  g = proofGenerator(sequent)
  while True:
    try:
      g.next()
    except SearchResult as r:
      return r.result

# returns True if the formula is provable
# returns False if the formula is not provable
def proveFormula(formula):
  return proveSequent(Sequent(axioms, formula))

# returns True if the formula is provable
# returns False if its inverse is provable
# returns None if its veracity is independent of the axioms
def proveOrDisproveFormula(formula):
  g = proofGenerator(proveSequent(Sequent(axioms, formula)))
  h = proofGenerator(proveSequent(Sequent(axioms, Not(formula))))
  while g is not None or h is not None:
    if g is not None:
      try:
        g.next()
      except SearchResult as r:
        if r.result:
          return True
        else:
          g = None
    if h is not None:
      try:
        h.next()
      except SearchResult as r:
        if r.result:
          return False
        else:
          h = None
  return None