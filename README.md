Ponentis
========

Ponentis is a small formal logic system right now with the goal of eventually being an educationally-oriented proof checker. As of right now, Ponentis can automatically generate certain kinds of proofs, although it is not very good at it.

The following are goals for this project:

  - A good enough ATP to recognize as correct:
    - any line in a proof that should be obvious as formally valid to an untrained reader,
    - fast enough that a student won't get frustrated when they have to recompile a proof that had a bug.
  - An interactive rendering system that can render only parts of proofs but expand when necessary, so that you can "explore" parts of summarized proofs you want to formalized or don't understand.
  - Readable, "literate" input style a la [knuth](http://www-cs-faculty.stanford.edu/~knuth/lp.html)
  - Output to at least one of the several functional formal proof languages (scheme/haskell/etc.)
  - Output to a human-readable, natural language but fully formalized proof
  - Runnable in the browser (will compile with [Skulpt](http://www.skulpt.org/))

The following are not goals for this project:

  - To be a good ATP.
    - In fact, it should in some cases be intentionally *not* good so as not to approve a proof whose logic isn't obvious to an untrained human reader
    - The point is to give students a runtime for their proofs without them having to learn programming; the point is not to generate proofs.

There is currently no input parser, but the goal is for input to eventually look like this:

```
TERMS
    =, *, + (binary infix)
    0 (atom)
AXIOMS
    a = a 'the reflexive property of equality
    (a = b) => (b = a) 'the commutative property of equality
    (a = b and b = c) => (a = c) 'the transitive property of equality

    a + 0 = 0 'the definition of the additive identity
    a + b = b + a 'the commutative property of addition
    (a + b) + c = a + (b + c) 'the associatve property of addition
    a = b => a + c = b + c 'the substitution law for addition
    a + c = b + c => 'the cancellation law for addition

    a * b = b * a 'the commutative property of multiplication
    (a * b) * c = a * (b * c) 'the associatve property of multiplication
    a = b => a * c = b * c 'the substitution law for multiplication
    a * c = b * c => 'the cancellation law for multiplication
    a * (b + c) = a * b + a * c 'the distributive law of addition over multiplication

THEOREM a * 0 = 0
    The trick for this proof is to expand a * (a + 0) in two different ways.
    The first way uses the definition of the additive identity:
        a * (a + 0) = 0 + a * (a + 0)
        a * (a + 0) = 0 + a * a

    The second way uses the distributive law:
        a * (a + 0) = a * 0 + a * a

    Then we have:
        a * 0 + a * a = 0 + a * a
        a * 0 = 0 QED
```


The current output for the equivalent of the above input looks like this, which is close to the goal for the final bullet point.
```
By the commutative property of addition we have:
  ((0 + (a * (a + 0))) = ((a * (a + 0)) + 0))
Then by the definition of the additive identity we have:
  ((0 + (a * (a + 0))) = ((a * (a + 0)) + 0)) ∧ (((a * (a + 0)) + 0) = (a * (a + 0)))
Then by the transitive property of equality we have:
  ((0 + (a * (a + 0))) = (a * (a + 0)))
Then by the commutative property of equality we have:
  ((a * (a + 0)) = (0 + (a * (a + 0)))) [0]

By the definition of the additive identity we have:
  ((a + 0) = a)
Then by the substitution law for multiplication we have:
  ((a * (a + 0)) = (a * a))
Then by the substitution law for addition we have:
  ((0 + (a * (a + 0))) = (0 + (a * a)))
Then by [0] we have:
  ((0 + (a * (a + 0))) = (0 + (a * a))) ∧ ((a * (a + 0)) = (0 + (a * (a + 0))))
Then by the transitive property of equality we have:
  ((a * (a + 0)) = (0 + (a * a))) [1]

By the distributive law for multiplication over addition we have:
  (((a + 0) * a) = ((a * 0) + (a * a)))
Then by the commutative property of multiplication we have:
  ((a * (a + 0)) = ((a + 0) * a)) ∧ (((a + 0) * a) = ((a * 0) + (a * a)))
Then by the transitive property of equality we have:
  ((a * (a + 0)) = ((a * 0) + (a * a))) [2]

By [2] we have:
  ((a * (a + 0)) = ((a * 0) + (a * a)))
Then by [1] we have:
  ((a * (a + 0)) = (0 + (a * a))) ∧ ((a * (a + 0)) = ((a * 0) + (a * a)))
Then by the commutative property of equality we have:
  ((0 + (a * a)) = (a * (a + 0))) ∧ ((a * (a + 0)) = ((a * 0) + (a * a)))
Then by the transitive property of equality we have:
  ((0 + (a * a)) = ((a * 0) + (a * a))) [3]

By [3] we have:
  ((0 + (a * a)) = ((a * 0) + (a * a)))
Then by the commutative property of addition we have:
  (((a * 0) + a) = ((a * a) + (a * 0))) ∧ ((0 + (a * a)) = ((a * 0) + a))
Then by the transitive property of equality we have:
  ((0 + (a * a)) = ((a * a) + (a * 0)))
Then by the commutative property of addition we have:
  (((a * a) + 0) = (0 + a)) ∧ ((0 + a) = ((a * a) + (a * 0)))
Then by the transitive property of equality we have:
  (((a * a) + 0) = ((a * a) + (a * 0)))
Then by the cancellation law for addition we have:
  (0 = (a * 0)) [4]
QED
```
