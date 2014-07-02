#!/usr/bin/python -O
# -*- coding: utf-8 -*-

# 2014 Stephan Boyer

##############################################################################
# Terms
##############################################################################

class Variable:
  def __init__(self, name):
    self.name = name
    self.time = 0

  def freeVariables(self):
    return { self }

  def freeUnificationTerms(self):
    return set()

  def replace(self, old, new):
    if self == old:
      return new
    return self

  def occurs(self, unification_term):
    return False

  def setInstantiationTime(self, time):
    self.time = time

  def __eq__(self, other):
    if not isinstance(other, Variable):
      return False
    return self.name == other.name

  def __str__(self):
    return self.name

  def __hash__(self):
    return hash(str(self))

class UnificationTerm:
  def __init__(self, name):
    self.name = name
    self.time = 0

  def freeVariables(self):
    return set()

  def freeUnificationTerms(self):
    return { self }

  def replace(self, old, new):
    if self == old:
      return new
    return self

  def occurs(self, unification_term):
    return self == unification_term

  def setInstantiationTime(self, time):
    self.time = time

  def __eq__(self, other):
    if not isinstance(other, UnificationTerm):
      return False
    return self.name == other.name

  def __str__(self):
    return self.name

  def __hash__(self):
    return hash(str(self))

class Function:
  def __init__(self, name, terms):
    self.name = name
    self.terms = terms
    self.time = 0

  def freeVariables(self):
    if len(self.terms) == 0:
      return set()
    return reduce((lambda x, y: x | y),
      [term.freeVariables() for term in self.terms])

  def freeUnificationTerms(self):
    if len(self.terms) == 0:
      return set()
    return reduce((lambda x, y: x | y),
      [term.freeUnificationTerms() for term in self.terms])

  def replace(self, old, new):
    if self == old:
      return new
    return Function(self.name,
      [term.replace(old, new) for term in self.terms]
    )

  def occurs(self, unification_term):
    return any([term.occurs(unification_term) for term in self.terms])

  def setInstantiationTime(self, time):
    self.time = time
    for term in self.terms:
      term.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, Function):
      return False
    if self.name != other.name:
      return False
    if len(self.terms) != len(other.terms):
      return False
    return all(
      [self.terms[i] == other.terms[i] for i in range(len(self.terms))]
    )

  def __str__(self):
    if len(self.terms) == 0:
      return self.name
    return self.name + '(' + ', '.join(
      [str(term) for term in self.terms]
    ) + ')'

  def __hash__(self):
    return hash(str(self))

##############################################################################
# Formulae
##############################################################################

class Predicate:
  def __init__(self, name, terms):
    self.name = name
    self.terms = terms

  def freeVariables(self):
    if len(self.terms) == 0:
      return set()
    return reduce((lambda x, y: x | y),
      [term.freeVariables() for term in self.terms])

  def freeUnificationTerms(self):
    if len(self.terms) == 0:
      return set()
    return reduce((lambda x, y: x | y),
      [term.freeUnificationTerms() for term in self.terms])

  def replace(self, old, new):
    if self == old:
      return new
    return Predicate(self.name,
      [term.replace(old, new) for term in self.terms]
    )

  def occurs(self, unification_term):
    return any([term.occurs(unification_term) for term in self.terms])

  def __eq__(self, other):
    if not isinstance(other, Predicate):
      return False
    if self.name != other.name:
      return False
    if len(self.terms) != len(other.terms):
      return False
    return all(
      [self.terms[i] == other.terms[i] for i in range(len(self.terms))]
    )

  def setInstantiationTime(self, time):
    for term in self.terms:
      term.setInstantiationTime(time)

  def __str__(self):
    if len(self.terms) == 0:
      return self.name
    return self.name + '(' + ', '.join(
      [str(term) for term in self.terms]
    ) + ')'

  def __hash__(self):
    return hash(str(self))

class Not:
  def __init__(self, formula):
    self.formula = formula

  def freeVariables(self):
    return self.formula.freeVariables()

  def freeUnificationTerms(self):
    return self.formula.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return Not(self.formula.replace(old, new))

  def occurs(self, unification_term):
    return self.formula.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.formula.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, Not):
      return False
    return self.formula == other.formula

  def __str__(self):
    return '¬' + str(self.formula)

  def __hash__(self):
    return hash(str(self))

class And:
  def __init__(self, formula_a, formula_b):
    self.formula_a = formula_a
    self.formula_b = formula_b

  def freeVariables(self):
    return self.formula_a.freeVariables() | \
      self.formula_b.freeVariables()

  def freeUnificationTerms(self):
    return self.formula_a.freeUnificationTerms() | \
      self.formula_b.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return And(
      self.formula_a.replace(old, new),
      self.formula_b.replace(old, new)
    )

  def occurs(self, unification_term):
    return self.formula_a.occurs(unification_term) or \
      self.formula_b.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.formula_a.setInstantiationTime(time)
    self.formula_b.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, And):
      return False
    return self.formula_a == other.formula_a and \
      self.formula_b == other.formula_b

  def __str__(self):
    return '(%s ∧ %s)' % (self.formula_a, self.formula_b)

  def __hash__(self):
    return hash(str(self))

class Or:
  def __init__(self, formula_a, formula_b):
    self.formula_a = formula_a
    self.formula_b = formula_b

  def freeVariables(self):
    return self.formula_a.freeVariables() | \
      self.formula_b.freeVariables()

  def freeUnificationTerms(self):
    return self.formula_a.freeUnificationTerms() | \
      self.formula_b.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return Or(
      self.formula_a.replace(old, new),
      self.formula_b.replace(old, new)
    )

  def occurs(self, unification_term):
    return self.formula_a.occurs(unification_term) or \
      self.formula_b.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.formula_a.setInstantiationTime(time)
    self.formula_b.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, Or):
      return False
    return self.formula_a == other.formula_a and \
      self.formula_b == other.formula_b

  def __str__(self):
    return '(%s ∨ %s)' % (self.formula_a, self.formula_b)

  def __hash__(self):
    return hash(str(self))

class Implies:
  def __init__(self, formula_a, formula_b):
    self.formula_a = formula_a
    self.formula_b = formula_b

  def freeVariables(self):
    return self.formula_a.freeVariables() | \
      self.formula_b.freeVariables()

  def freeUnificationTerms(self):
    return self.formula_a.freeUnificationTerms() | \
      self.formula_b.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return Implies(
      self.formula_a.replace(old, new),
      self.formula_b.replace(old, new)
    )

  def occurs(self, unification_term):
    return self.formula_a.occurs(unification_term) or \
      self.formula_b.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.formula_a.setInstantiationTime(time)
    self.formula_b.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, Implies):
      return False
    return self.formula_a == other.formula_a and \
      self.formula_b == other.formula_b

  def __str__(self):
    return '(%s → %s)' % (self.formula_a, self.formula_b)

  def __hash__(self):
    return hash(str(self))

class ForAll:
  def __init__(self, variable, formula):
    self.variable = variable
    self.formula = formula

  def freeVariables(self):
    return self.formula.freeVariables() - { self.variable }

  def freeUnificationTerms(self):
    return self.formula.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return ForAll(
      self.variable.replace(old, new),
      self.formula.replace(old, new)
    )

  def occurs(self, unification_term):
    return self.formula.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.variable.setInstantiationTime(time)
    self.formula.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, ForAll):
      return False
    return self.variable == other.variable and \
      self.formula == other.formula

  def __str__(self):
    return '(∀%s. %s)' % (self.variable, self.formula)

  def __hash__(self):
    return hash(str(self))

class ThereExists:
  def __init__(self, variable, formula):
    self.variable = variable
    self.formula = formula

  def freeVariables(self):
    return self.formula.freeVariables() - { self.variable }

  def freeUnificationTerms(self):
    return self.formula.freeUnificationTerms()

  def replace(self, old, new):
    if self == old:
      return new
    return ThereExists(
      self.variable.replace(old, new),
      self.formula.replace(old, new)
    )

  def occurs(self, unification_term):
    return self.formula.occurs(unification_term)

  def setInstantiationTime(self, time):
    self.variable.setInstantiationTime(time)
    self.formula.setInstantiationTime(time)

  def __eq__(self, other):
    if not isinstance(other, ThereExists):
      return False
    return self.variable == other.variable and \
      self.formula == other.formula

  def __str__(self):
    return '(∃%s. %s)' % (self.variable, self.formula)

  def __hash__(self):
    return hash(str(self))
