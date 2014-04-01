#!/usr/bin/python -O
# -*- coding: utf-8 -*-

# 2014 Stephan Boyer

import sys
from rules import *
try:
  import readline
except ImportError:
  pass

##############################################################################
# Command-line interface
##############################################################################

class Error(Exception):
  def __init__(self, message):
    self.message = message

def lexer(inp):
  # perform a lexical analysis
  tokens = []
  pos = 0
  while pos < len(inp):
    # skip whitespace
    if inp[pos] == " ":
      pos += 1
      continue

    # identifiers
    identifier = ""
    while pos < len(inp) and inp[pos].isalnum():
      identifier += inp[pos]
      pos += 1
    if len(identifier) > 0:
      tokens.append(identifier)
      continue

    # symbols
    tokens.append(inp[pos])
    pos += 1

  # return the tokens
  return tokens

def parse(tokens):
  # keywords
  keywords = ["not", "implies", "and", "or", "forall", "forsome"]

  # empty formula
  if len(tokens) == 0:
    raise Error("Empty formula.")

  # Implies
  implies_pos = None
  depth = 0
  for i in range(len(tokens)):
    if tokens[i] == "(":
      depth += 1
      continue
    if tokens[i] == ")":
      depth -= 1
      continue
    if depth == 0 and tokens[i].lower() == "implies":
      implies_pos = i
      break
  if implies_pos is not None:
    if implies_pos == 0 or implies_pos == len(tokens) - 1:
      raise Error("Missing formula in IMPLIES connective.")
    return Implies(parse(tokens[0:implies_pos]),
      parse(tokens[implies_pos+1:]))

  # Or
  or_pos = None
  depth = 0
  for i in range(len(tokens)):
    if tokens[i] == "(":
      depth += 1
      continue
    if tokens[i] == ")":
      depth -= 1
      continue
    if depth == 0 and tokens[i].lower() == "or":
      or_pos = i
      break
  if or_pos is not None:
    if or_pos == 0 or or_pos == len(tokens) - 1:
      raise Error("Missing formula in OR connective.")
    return Or(parse(tokens[0:or_pos]), parse(tokens[or_pos+1:]))

  # And
  and_pos = None
  depth = 0
  for i in range(len(tokens)):
    if tokens[i] == "(":
      depth += 1
      continue
    if tokens[i] == ")":
      depth -= 1
      continue
    if depth == 0 and tokens[i].lower() == "and":
      and_pos = i
      break
  if and_pos is not None:
    if and_pos == 0 or and_pos == len(tokens) - 1:
      raise Error("Missing formula in AND connective.")
    return And(parse(tokens[0:and_pos]), parse(tokens[and_pos+1:]))

  # Not
  if tokens[0] == "not":
    if len(tokens) < 2:
      raise Error("Missing formula in NOT connective.")
    return Not(parse(tokens[1:]))

  # ForAll
  if tokens[0] == "forall":
    if len(tokens) < 2:
      raise Error("Missing bound variable in FORALL quantifier.")
    if len(tokens) < 3 or tokens[2] != ".":
      raise Error("Missing '.' in FORALL quantifier.")
    if len(tokens) < 4:
      raise Error("Missing formula in FORALL quantifier.")
    return ForAll(parse(tokens[1:2]), parse(tokens[3:]))

  # ThereExists
  if tokens[0] == "forsome":
    if len(tokens) < 2:
      raise Error("Missing bound variable in FORSOME quantifier.")
    if len(tokens) < 3 or tokens[2] != ".":
      raise Error("Missing '.' in FORSOME quantifier.")
    if len(tokens) < 4:
      raise Error("Missing formula in FORSOME quantifier.")
    return ThereExists(parse(tokens[1:2]), parse(tokens[3:]))

  # Function
  if tokens[0].isalnum() and tokens[0] not in keywords and \
    len(tokens) > 1 and not any([c.isupper() for c in tokens[0]]):
    if len(tokens) < 3 or tokens[1] != "(":
      raise Error("Missing function argument list.")
    if tokens[-1] != ")":
      raise Error("Missing ')' after function argument list.")
    name = tokens[0]
    args = []
    i = 2
    while i < len(tokens) - 1:
      end = len(tokens) - 1
      depth = 0
      for j in range(i + 1, len(tokens) - 1):
        if tokens[j] == "(":
          depth += 1
          continue
        if tokens[j] == ")":
          depth -= 1
          continue
        if depth == 0 and tokens[j] == ",":
          end = j
          break
      if i == end:
        raise Error("Missing function argument.")
      args.append(parse(tokens[i:end]))
      i = end + 1
    return Function(name, args)

  # Predicate
  if tokens[0].isalnum() and tokens[0] not in keywords and \
    len(tokens) == 1 and any([c.isupper() for c in tokens[0]]):
    return Predicate(tokens[0], [])
  if tokens[0].isalnum() and tokens[0] not in keywords and \
    len(tokens) > 1 and any([c.isupper() for c in tokens[0]]):
    if len(tokens) < 3 or tokens[1] != "(":
      raise Error("Missing predicate argument list.")
    if tokens[-1] != ")":
      raise Error("Missing ')' after predicate argument list.")
    name = tokens[0]
    args = []
    i = 2
    while i < len(tokens) - 1:
      end = len(tokens) - 1
      depth = 0
      for j in range(i + 1, len(tokens) - 1):
        if tokens[j] == "(":
          depth += 1
          continue
        if tokens[j] == ")":
          depth -= 1
          continue
        if depth == 0 and tokens[j] == ",":
          end = j
          break
      if i == end:
        raise Error("Missing predicate argument.")
      args.append(parse(tokens[i:end]))
      i = end + 1
    return Predicate(name, args)

  # Variable
  if tokens[0].isalnum() and tokens[0] not in keywords and \
    len(tokens) == 1 and not any([c.isupper() for c in tokens[0]]):
    return Variable(tokens[0])

  # Group
  if tokens[0] == "(":
    if tokens[-1] != ")":
      raise Error("Missing ')'.")
    if len(tokens) == 2:
      raise Error("Missing formula in parenthetical group.")
    return parse(tokens[1:-1])

def typecheck_term(term):
  if isinstance(term, Variable):
    return
  if isinstance(term, Function):
    for subterm in term.terms:
      typecheck_term(subterm)
    return
  raise Error("Invalid term: " + str(term) + ".")

def typecheck_formula(formula):
  if isinstance(formula, Predicate):
    for term in formula.terms:
      typecheck_term(term)
    return
  if isinstance(formula, Not):
    typecheck_formula(formula.formula)
    return
  if isinstance(formula, And):
    typecheck_formula(formula.formula_a)
    typecheck_formula(formula.formula_b)
    return
  if isinstance(formula, Or):
    typecheck_formula(formula.formula_a)
    typecheck_formula(formula.formula_b)
    return
  if isinstance(formula, Implies):
    typecheck_formula(formula.formula_a)
    typecheck_formula(formula.formula_b)
    return
  if isinstance(formula, ForAll):
    if not isinstance(formula.variable, Variable):
      raise Error("Invalid bound variable in FORALL quantifier: " +
        str(formula.variable) + ".")
    typecheck_formula(formula.formula)
    return
  if isinstance(formula, ThereExists):
    if not isinstance(formula.variable, Variable):
      raise Error("Invalid bound variable in FORSOME quantifier: " +
        str(formula.variable) + ".")
    typecheck_formula(formula.formula)
    return
  raise Error("Invalid formula: " + str(formula) + ".")

def main():
  print "  Terms:"
  print "    x"
  print "    f(x)"
  print ""
  print "  Formulae:"
  print "    P(x)"
  print "    not P"
  print "    P or Q"
  print "    P and Q"
  print "    P implies Q"
  print "    forall x. P(x)"
  print "    forsome x. P(x)"
  print ""
  print "Enter formulae at the prompt."

  while True:
    try:
      inp = raw_input("\n> ")
      tokens = lexer(inp)
      formula = parse(tokens)
      try:
        typecheck_formula(formula)
      except Error as formula_error:
        try:
          typecheck_term(formula)
        except Error as term_error:
          raise formula_error
        else:
          raise Error("Enter a formula, not a term.")
      result = proveOrDisproveFormula(formula)
      if result == True:
        print "Formula proven: " + str(formula) + "."
      if result == False:
        print "Formula disproven: " + str(formula) + "."
      if result is None:
        print "Formula neither provable nor disprovable: " + str(formula) + "."
    except Error as e:
      print e.message
    except KeyboardInterrupt:
      pass
    except EOFError:
      print ""
      break

if __name__ == "__main__":
  main()
