An automated theorem prover for first-order logic.

To get started, run `cli.py`:

    $ ./cli.py
    First-Order Logic Theorem Prover
    2014 Stephan Boyer

    Terms:

      x       (variable)
      f(x)    (function)

    Formulae:

      P(term)        (predicate)
      not P          (complement)
      P or Q         (disjunction)
      P and Q        (conjunction)
      P implies Q    (implication)
      forall x. P    (universal quantification)
      forsome x. P   (existential quantification)

    Enter formulae at the prompt. The following commands are also available for manipulating axioms:

      axioms              (list axioms)
      add <formula>       (add an axiom)
      remove <formula>    (remove an axiom)
      reset               (remove all axioms)

    >

Example session:

    > P or not P
    Formula proven: (P ∨ ¬P).

    > P and not P
    Formula disproven: (P ∧ ¬P).

    > P(x, y)
    Formula neither provable nor disprovable: P(x, y).

    > forall x. P(x) implies (Q(x) implies P(x))
    Formula proven: (∀x. (P(x) → (Q(x) → P(x)))).

    > add forall x. Equals(x, x)    
    Axiom added: (∀x. Equals(x, x)).

    > Equals(a, a)
    Formula proven: Equals(a, a).

Copyright (C) 2014 Stephan Boyer

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.