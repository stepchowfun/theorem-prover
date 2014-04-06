#!/usr/bin/python -O
# -*- coding: utf-8 -*-

# 2014 Stephan Boyer

from language import *

##############################################################################
# Unification
##############################################################################

# solve a single equation
def unify(term_a, term_b):
  if isinstance(term_a, UnificationTerm):
    if term_b.occurs(term_a) or term_b.time > term_a.time:
      return None
    return { term_a: term_b }
  if isinstance(term_b, UnificationTerm):
    if term_a.occurs(term_b) or term_a.time > term_b.time:
      return None
    return { term_b: term_a }
  if isinstance(term_a, Variable) and isinstance(term_b, Variable):
    if term_a == term_b:
      return { }
    return None
  if (isinstance(term_a, Function) and isinstance(term_b, Function)) or \
     (isinstance(term_a, Predicate) and isinstance(term_b, Predicate)):
    if term_a.name != term_b.name:
      return None
    if len(term_a.terms) != len(term_b.terms):
      return None
    substitution = { }
    for i in range(len(term_a.terms)):
      a = term_a.terms[i]
      b = term_b.terms[i]
      for k, v in substitution.items():
        a = a.replace(k, v)
        b = b.replace(k, v)
      sub = unify(a, b)
      if sub == None:
        return None
      for k, v in sub.items():
        substitution[k] = v
    return substitution
  return None

# solve a list of equations
def unify_list(pairs):
  substitution = { }
  for term_a, term_b in pairs:
    a = term_a
    b = term_b
    for k, v in substitution.items():
      a = a.replace(k, v)
      b = b.replace(k, v)
    sub = unify(a, b)
    if sub == None:
      return None
    for k, v in sub.items():
      substitution[k] = v
  return substitution

##############################################################################
# Sequents
##############################################################################

class Sequent:
  def __init__(self, left, right, siblings, depth):
    self.left = left
    self.right = right
    self.siblings = siblings
    self.depth = depth

  def freeVariables(self):
    result = set()
    for formula in self.left:
      result |= formula.freeVariables()
    for formula in self.right:
      result |= formula.freeVariables()
    return result

  def freeUnificationTerms(self):
    result = set()
    for formula in self.left:
      result |= formula.freeUnificationTerms()
    for formula in self.right:
      result |= formula.freeUnificationTerms()
    return result

  def getVariableName(self, prefix):
    fv = self.freeVariables() | self.freeUnificationTerms()
    index = 1
    name = prefix + str(index)
    while Variable(name) in fv or UnificationTerm(name) in fv:
      index += 1
      name = prefix + str(index)
    return name

  def getUnifiablePairs(self):
    pairs = []
    for formula_left in self.left:
      for formula_right in self.right:
        if unify(formula_left, formula_right) is not None:
          pairs.append((formula_left, formula_right))
    return pairs

  def __eq__(self, other):
    for formula in self.left:
      if formula not in other.left:
        return False
    for formula in other.left:
      if formula not in self.left:
        return False
    for formula in self.right:
      if formula not in other.right:
        return False
    for formula in other.right:
      if formula not in self.right:
        return False
    return True

  def __str__(self):
    left_part = ", ".join([str(formula) for formula in self.left])
    right_part = ", ".join([str(formula) for formula in self.right])
    if left_part != "":
      left_part = left_part + " "
    if right_part != "":
      right_part = " " + right_part
    return left_part + "⊢" + right_part

  def __hash__(self):
    return hash(str(self))

##############################################################################
# Proof search
##############################################################################

# returns True if the sequent is provable
# returns False or loops forever if the sequent is not provable
def proveSequent(sequent):
  # reset the time for each formula in the sequent
  for formula in sequent.left:
    formula.setInstantiationTime(0)
  for formula in sequent.right:
    formula.setInstantiationTime(0)

  # sequents to be proven
  frontier = [sequent]

  # sequents which have been proven
  proven = { sequent }

  while True:
    # get the next sequent
    old_sequent = None
    while len(frontier) > 0 and (old_sequent is None or old_sequent in proven):
      old_sequent = frontier.pop(0)
    if old_sequent is None:
      break
    print "%s. %s" % (old_sequent.depth, old_sequent)

    # check if this sequent is axiomatically true without unification
    if len(set(old_sequent.left.keys()) & set(old_sequent.right.keys())) > 0:
      proven.add(old_sequent)
      continue

    # check if this sequent has unification terms
    if old_sequent.siblings is not None:
      # get the unifiable pairs for each sibling
      sibling_pair_lists = [sequent.getUnifiablePairs()
        for sequent in old_sequent.siblings]

      # check if there is a unifiable pair for each sibling
      if all([len(pair_list) > 0 for pair_list in sibling_pair_lists]):
        # iterate through all simultaneous choices of pairs from each sibling
        substitution = None
        index = [0] * len(sibling_pair_lists)
        while True:
          # attempt to unify at the index
          substitution = unify_list([sibling_pair_lists[i][index[i]]
            for i in range(len(sibling_pair_lists))])
          if substitution is not None:
            break

          # increment the index
          pos = len(sibling_pair_lists) - 1
          while pos >= 0:
            index[pos] += 1
            if index[pos] < len(sibling_pair_lists[pos]):
              break
            index[pos] = 0
            pos -= 1
          if pos < 0:
            break
        if substitution is not None:
          for sequent in old_sequent.siblings:
            if sequent != old_sequent:
              print "%s. %s" % (sequent.depth, sequent)
          for k, v in substitution.items():
            print "  %s = %s" % (k, v)
          proven |= old_sequent.siblings
          frontier = [sequent for sequent in frontier
            if sequent not in old_sequent.siblings]
          continue
      else:
        # unlink this sequent
        old_sequent.siblings.remove(old_sequent)

    while True:
      # determine which formula to expand
      left_formula = None
      left_depth = None
      for formula, depth in old_sequent.left.items():
        if left_depth is None or left_depth > depth:
          if not isinstance(formula, Predicate):
            left_formula = formula
            left_depth = depth
      right_formula = None
      right_depth = None
      for formula, depth in old_sequent.right.items():
        if right_depth is None or right_depth > depth:
          if not isinstance(formula, Predicate):
            right_formula = formula
            right_depth = depth
      apply_left = False
      apply_right = False
      if left_formula is not None and right_formula is None:
        apply_left = True
      if left_formula is None and right_formula is not None:
        apply_right = True
      if left_formula is not None and right_formula is not None:
        if left_depth < right_depth:
          apply_left = True
        else:
          apply_right = True
      if left_formula is None and right_formula is None:
        return False

      # apply a left rule
      if apply_left:
        print left_formula
        if isinstance(left_formula, Not):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.left[left_formula]
          new_sequent.right[left_formula.formula] = \
          old_sequent.left[left_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(left_formula, And):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.left[left_formula]
          new_sequent.left[left_formula.formula_a] = \
            old_sequent.left[left_formula] + 1
          new_sequent.left[left_formula.formula_b] = \
          old_sequent.left[left_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(left_formula, Or):
          new_sequent_a = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          new_sequent_b = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent_a.left[left_formula]
          del new_sequent_b.left[left_formula]
          new_sequent_a.left[left_formula.formula_a] = \
            old_sequent.left[left_formula] + 1
          new_sequent_b.left[left_formula.formula_b] = \
          old_sequent.left[left_formula] + 1
          if new_sequent_a.siblings is not None:
            new_sequent_a.siblings.add(new_sequent_a)
          frontier.append(new_sequent_a)
          if new_sequent_b.siblings is not None:
            new_sequent_b.siblings.add(new_sequent_b)
          frontier.append(new_sequent_b)
          break
        if isinstance(left_formula, Implies):
          new_sequent_a = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          new_sequent_b = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent_a.left[left_formula]
          del new_sequent_b.left[left_formula]
          new_sequent_a.right[left_formula.formula_a] = \
            old_sequent.left[left_formula] + 1
          new_sequent_b.left[left_formula.formula_b] = \
          old_sequent.left[left_formula] + 1
          if new_sequent_a.siblings is not None:
            new_sequent_a.siblings.add(new_sequent_a)
          frontier.append(new_sequent_a)
          if new_sequent_b.siblings is not None:
            new_sequent_b.siblings.add(new_sequent_b)
          frontier.append(new_sequent_b)
          break
        if isinstance(left_formula, ForAll):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings or set(),
            old_sequent.depth + 1
          )
          new_sequent.left[left_formula] += 1
          formula = left_formula.formula.replace(
            left_formula.variable,
            UnificationTerm(old_sequent.getVariableName("t"))
          )
          formula.setInstantiationTime(old_sequent.depth + 1)
          if formula not in new_sequent.left:
            new_sequent.left[formula] = new_sequent.left[left_formula]
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(left_formula, ThereExists):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.left[left_formula]
          variable = Variable(old_sequent.getVariableName("v"))
          formula = left_formula.formula.replace(left_formula.variable,
            variable)
          formula.setInstantiationTime(old_sequent.depth + 1)
          new_sequent.left[formula] = old_sequent.left[left_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break

      # apply a right rule
      if apply_right:
        print right_formula
        if isinstance(right_formula, Not):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.right[right_formula]
          new_sequent.left[right_formula.formula] = \
          old_sequent.right[right_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(right_formula, And):
          new_sequent_a = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          new_sequent_b = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent_a.right[right_formula]
          del new_sequent_b.right[right_formula]
          new_sequent_a.right[right_formula.formula_a] = \
            old_sequent.right[right_formula] + 1
          new_sequent_b.right[right_formula.formula_b] = \
          old_sequent.right[right_formula] + 1
          if new_sequent_a.siblings is not None:
            new_sequent_a.siblings.add(new_sequent_a)
          frontier.append(new_sequent_a)
          if new_sequent_b.siblings is not None:
            new_sequent_b.siblings.add(new_sequent_b)
          frontier.append(new_sequent_b)
          break
        if isinstance(right_formula, Or):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.right[right_formula]
          new_sequent.right[right_formula.formula_a] = \
            old_sequent.right[right_formula] + 1
          new_sequent.right[right_formula.formula_b] = \
            old_sequent.right[right_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(right_formula, Implies):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.right[right_formula]
          new_sequent.left[right_formula.formula_a] = \
            old_sequent.right[right_formula] + 1
          new_sequent.right[right_formula.formula_b] = \
            old_sequent.right[right_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(right_formula, ForAll):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings,
            old_sequent.depth + 1
          )
          del new_sequent.right[right_formula]
          variable = Variable(old_sequent.getVariableName("v"))
          formula = right_formula.formula.replace(right_formula.variable,
            variable)
          formula.setInstantiationTime(old_sequent.depth + 1)
          new_sequent.right[formula] = old_sequent.right[right_formula] + 1
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break
        if isinstance(right_formula, ThereExists):
          new_sequent = Sequent(
            old_sequent.left.copy(),
            old_sequent.right.copy(),
            old_sequent.siblings or set(),
            old_sequent.depth + 1
          )
          new_sequent.right[right_formula] += 1
          formula = right_formula.formula.replace(
            right_formula.variable,
            UnificationTerm(old_sequent.getVariableName("t"))
          )
          formula.setInstantiationTime(old_sequent.depth + 1)
          if formula not in new_sequent.right:
            new_sequent.right[formula] = new_sequent.right[right_formula]
          if new_sequent.siblings is not None:
            new_sequent.siblings.add(new_sequent)
          frontier.append(new_sequent)
          break

  # no more sequents to prove
  return True

# returns True if the formula is provable
# returns False or loops forever if the formula is not provable
def proveFormula(axioms, formula):
  return proveSequent(Sequent(
    { axiom: 0 for axiom in axioms },
    { formula: 0 },
    None,
    0
  ))
