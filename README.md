An automated theorem prover for first-order logic. For any provable formula, this program is guaranteed to find the proof (eventually). However, as a consequence of the negative answer to Hilbert's *Entscheidungsproblem*, there are some unprovable formulae that will cause this program to loop forever.

Some notes:

* The proof steps are shown as [sequents](http://en.wikipedia.org/wiki/Sequent).
* The actual theorem prover is in `prover.py`. The command-line interface (including the parser) is in `main.py`. `language.py` contains boilerplate classes used to represent logical formulae.
* The system will not accept a lemma unless it can be proven. An axiom is admitted without proof.
* This is only a pedagogical tool. It is too slow to be used for anything practical.

To get started, run `main.py`:

    $ ./main.py
    First-Order Logic Theorem Prover
    2014 Stephan Boyer

    Terms:

      x               (variable)
      f(term, ...)    (function)

    Formulae:

      P(term)        (predicate)
      not P          (complement)
      P or Q         (disjunction)
      P and Q        (conjunction)
      P implies Q    (implication)
      forall x. P    (universal quantification)
      exists x. P    (existential quantification)

    Enter formulae at the prompt. The following commands are also available for manipulating axioms:

      axioms              (list axioms)
      lemmas              (list lemmas)
      axiom <formula>     (add an axiom)
      lemma <formula>     (prove and add a lemma)
      remove <formula>    (remove an axiom or lemma)
      reset               (remove all axioms and lemmas)

    >

Example session:

    > P or not P
    0. ⊢ (P ∨ ¬P)
    1. ⊢ P, ¬P
    2. P ⊢ P
    Formula proven: (P ∨ ¬P).

    > P and not P
    0. ⊢ (P ∧ ¬P)
    1. ⊢ P
    Formula unprovable: (P ∧ ¬P).

    > forall x. P(x) implies (Q(x) implies P(x))
    0. ⊢ (∀x. (P(x) → (Q(x) → P(x))))
    1. ⊢ (P(v1) → (Q(v1) → P(v1)))
    2. P(v1) ⊢ (Q(v1) → P(v1))
    3. Q(v1), P(v1) ⊢ P(v1)
    Formula proven: (∀x. (P(x) → (Q(x) → P(x)))).

    > exists x. (P(x) implies forall y. P(y))
    0. ⊢ (∃x. (P(x) → (∀y. P(y))))
    1. ⊢ (P(t1) → (∀y. P(y))), (∃x. (P(x) → (∀y. P(y))))
    2. P(t1) ⊢ (∀y. P(y)), (∃x. (P(x) → (∀y. P(y))))
    3. P(t1) ⊢ (∀y. P(y)), (P(t2) → (∀y. P(y))), (∃x. (P(x) → (∀y. P(y))))
    4. P(t1) ⊢ (P(t2) → (∀y. P(y))), (∃x. (P(x) → (∀y. P(y)))), P(v1)
    5. P(t1), P(t2) ⊢ (∀y. P(y)), (∃x. (P(x) → (∀y. P(y)))), P(v1)
    6. P(t1), P(t2) ⊢ (∀y. P(y)), (P(t3) → (∀y. P(y))), (∃x. (P(x) → (∀y. P(y)))), P(v1)
    7. P(t1), P(t2) ⊢ (P(t3) → (∀y. P(y))), P(v2), (∃x. (P(x) → (∀y. P(y)))), P(v1)
    8. P(t3), P(t1), P(t2) ⊢ (∀y. P(y)), P(v2), (∃x. (P(x) → (∀y. P(y)))), P(v1)
      t3 = v1
    Formula proven: (∃x. (P(x) → (∀y. P(y)))).

    > axiom forall x. Equals(x, x)
    Axiom added: (∀x. Equals(x, x)).

    > axioms
    (∀x. Equals(x, x))

    > lemma Equals(a, a)
    0. (∀x. Equals(x, x)) ⊢ Equals(a, a)
    1. Equals(t1, t1), (∀x. Equals(x, x)) ⊢ Equals(a, a)
      t1 = a
    Lemma proven: Equals(a, a).

    > lemmas
    Equals(a, a)

    > remove forall x. Equals(x, x)
    Axiom removed: (∀x. Equals(x, x)).
    This lemma was proven using that axiom and was also removed:
      Equals(a, a)

Copyright (C) 2014 Stephan Boyer

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.