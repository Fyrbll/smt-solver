Project for Advanced Functional Programming, Fall 2022
======================================================

Dependencies
------------

I'm using the following Racket modules. I believe they're included in a standard
installation of Racket so you shouldn't need to use `raco` at all.

- racket/list
- racket/match
- racket/function
- racket/set
- racket/syntax
- racket/string

Usage
-----

### Using the SMT Solver

1. Load `dpllt.rkt` in the Racket REPL.
2. Call the function `main` with the path to an input file.

```
$ racket -I racket/repl

Welcome to Racket v8.7.0.6 [cs].

> ,enter "dpllt.rkt"

"dpllt.rkt"> (main "./input-1.smt2")
(list (cons 'b (set 1))
      (cons '(f a b) (set 2))
      (cons '(f (f a b) b) (set 0 3))
      (cons 'a (set 0 3)))

"dpllt.rkt"> (main "./input-2.smt2")
#f
```

**Writing Inputs**

Pick a problem in the theory of uninterpreted functions with equality. Let's
start with an easy one. Say we want to prove

$$(f(x) = y ∧ f(y) = z ∧ f(z) = x) ⇒ f(f(f(f(f(f(x)))))) = x$$

Put the following input in a file called `input.smt2` (you can call it whatever
you want.) It's the negation of what we want to prove. We want the solver to
state that there are no counterexamples to the statement.

```
(assert (= (f x) y))
(assert (= (f y) z))
(assert (= (f z) x))
(assert (not (= (f (f (f (f (f (f x)))))) x)))
```

The solver actually converts formulas to CNF so we don't need to perform the
negation ourselves. We can express the problem in a single assertion too.

```
(assert (not 
  (=> (and (= (f x) y)
           (= (f y) z)
           (= (f z) x))
      (= (f (f (f (f (f (f x)))))) x))))
```

Anyway, assuming the input has been placed in `input.smt2`, we can run the
solver from the REPL.

```
$ racket -I racket/repl
Welcome to Racket v8.7.0.6 [cs].
> ,enter "dpllt.rkt"
"dpllt.rkt"> (main "./input.smt2")
#f
```

The `#f` here means the input is unsatisfiable.

Now consider a new formula that is satisfiable. Suppose we erroneously believe
that

$$(f(x) = y ∧ f(y) = z ∧ f(z) = x) ⇒ f(f(f(x))) = y$$

and we make a file `input.smt2` asserting the negation of this statement.

```
(assert (not
  (=> (and (= (f x) y)
           (= (f y) z)
           (= (f z) x))
      (= (f (f (f x))) y))))
```

We run the solver from the Racket REPL.

```
$ racket -I racket/repl
Welcome to Racket v8.7.0.6 [cs].
> ,enter "dpllt.rkt"
"dpllt.rkt"> (main "./input.smt2")
(list (cons '(f z) (set 1 2 7))
      (cons 'x (set 1 2 7))
      (cons '(f (f x)) (set 0 4 6))
      (cons '(f x) (set 3 5))
      (cons 'z (set 0 4 6))
      (cons '(f (f (f x))) (set 1 2 7))
      (cons '(f y) (set 0 4 6))
      (cons 'y (set 3 5)))
```

Here the solver has deemed the theory satisfiable and has produced a mapping of
subterms in the input to sets of natural numbers. The idea is that the sets here
are equivalence classes of subterms. In practice, two subterms are equal in the
model if they map to the same equivalence class.

What should we take away from this? Well the solver is telling us that there is
a counterexample to our erroneous claim. It's saying that there is some
uninterpreted sort with at least three distinct elements
$x = \\{1,2,7\\}, y = \\{3,5\\}, z = \\{0,4,6\\}$ and a unary function $f$ such that
the premises $f(x) = y, f(y) = z,$ and $f(z) = x$ are satisfied however the
conclusion $f^3(x) = y$ does not hold. From the model, we can read off that
$x = f(z) = f(f(f(x))), y = f(x), z = f(y) = f(f(x))$

Implementation Walkthrough
--------------------------

Here is a description of the implementation.

1. Assertions are read from the input file. The input file has the grammar

```
INPUT ::= ASSERTION*

ASSERTION ::= (assert FORMULA)

FORMULA ::= (= TERM TERM)
          | (and FORMULA FORMULA+)
          | (or FORMULA FORMULA+)
          | (not FORMULA FORMULA+)
          | (=> FORMULA FORMULA+)

TERM ::= VARIABLE
       | (VARIABLE TERM+)
```

2. The program produces a bijection from a subset of the natural numbers greater
than 0 to equalities. So, if the program contains just the equalities
$f(a,b) = a$ and $f(f(a,b),b) = a$, then the program will produce two hash
tables.

$$\text{literal\\_to\\_term}\ = \\{ 1 \mapsto (f(a,b) = a), 2 \mapsto (f(f(a,b),b) = a) \\}$$

$$\text{term\\_to\\_literal}\ = \\{ (f(a,b) = a) \mapsto 1, (f(f(a,b),b) = a) \mapsto 2 \\}$$

Observe that I used the word 'literal' in the names of the hash tables. This is
because each non-zero integer can be treated as a positive or negative boolean
literal for the purposes of boolean satisfiability.

3. The program replaces all the equalities with their corresponding boolean
literals and also converts the formula to CNF. Note that this means we
temporarily "forget" that the original problem was in the theory of
uninterpreted functions.

Say the original problem was

$$(f(a,b) = a) \wedge (f(f(a,b),b) \neq a)$$

it is transformed into the CNF satsifiability problem

$$1 \wedge -2$$

4. The program runs the SAT solver on this CNF formula. Once it generates a
model, the model is transformed back into a conjunction of equalities and
inequalities using the 'term_to_literal' hash table. The conjunction is run
through the theory solver to check its consistency with respect to the theory of
uninterpreted functions. If the model is theory-consistent, it is returned. If
the model is not theory-consistent, a new clause (a disjunction of literals) is
added to the formula based on the conflict. The SAT solver is then restarted.

The following diagram presents the relationship between different functions in
the solver. I have also mentioned which file is home to each function.

The label "Yes" in most situations means "this transition rule applies to the
state." In other situations it means "true." On the other hand "No" in most
situations means "this transition rule does not apply," or it means "false." The
meaning should be clear from context.

The steps `pure-literal`, `unit-propagate`, `decide`, `tlearn`, `backtrack`,
`backjump`, and `fail` are explained in sections 2 and 3 of the
"Solving SAT and SAT Modulo Theories" paper.

```
              (dpllt) main
    after preparing 'term->literal' and
    'literal->term', and calling 'cnf'
                        |
                        V                  output #f, "unsat"
          ---------> get-model                 ^
         /      (dpllt) |                      | Yes
         |              V                No    |
         |           pure-literal     -------fail (dpll)
         |       (dpll) |            /         ^
         |              V           V          | No
         |           get-model-guess           |
         |      (dpllt) |               backjump/backtrack (dpll)
         |              |                      ^  |
         |              |                      |  | Yes
         |              V           Yes        |  V
         |           unit-propagate ---> get-model-check
         |       (dpll) |                ^  (dpllt)
         |              | No        Yes /
         |              V              / 
      tlearn         decide ----------/
 (dpllt) ^       (dpll) |
         |              | No
         \     No       V           Yes
          \--------- consistent? --------> output model, "sat"
                      (euf)
```

A Closer Look
-------------

If you want to see exactly which transition rules are fired and how they change
the model, change the value of `debug` in `dpll.rkt` to `#t`

```
#lang racket/base

(require racket/match racket/set racket/function racket/list racket/string)
(provide (all-defined-out))

(define debug #t)

;; ...
```

```
Welcome to Racket v8.7.0.6 [cs].

> ,enter "dpllt.rkt"

"dpllt.rkt"> (main "./input-7.smt2")
((1 <=> (= (f x) y))
 (2 <=> (= (f y) z))
 (3 <=> (= (f z) x))
 (4 <=> (= (f (f (f (f (f (f x)))))) x)))
__initial__        ()
__pure-literal__   -4 3 2 1
__tlearn__         (4 -3 -2 -1)
__restart__
__initial__        ()
__unit-propagate__ 1
__unit-propagate__ 2 1
__unit-propagate__ 3 2 1
__unit-propagate__ 4 3 2 1
#f
```

Helpful and Limiting Aspects of Functional Programming 
------------------------------------------------------

1. I did not write the code in Haskell because I wanted to write a working
solver first and *then* worry about the types. With code that involves state,
especially code where you don't know exactly what information you should include
in your state datatype, I think it's best to start with an approach that
leverages global mutable state. When you're happy with the result, you can
package all the necessary information into a type-safe struct. If I had more
time to spend on the project I would add types gradually.

2. I think immutable data structures might not be the right choice for fast SAT
solving. My theory solver (in `euf.rkt`) mostly uses mutable state, while my SAT
solver (in `dpll.rkt`) explicitly passes around an immutable state struct.
Still, I think I perform a lot of expensive operations on immutable graphs to
implement backjumping in my SAT solver. Specifically when I roll back a decision
and the unit propagations associated with that level, I also roll back changes
to my unit propagation graph. I ought to formally profile my tool to see where
it spends the most time.

References
----------

1. *Conversion to CNF.* [Wikipedia article on conjunctive normal form][1]

2. *DPLL and DPLL(T).* [Solving SAT and SAT Modulo Theories: from an Abstract Davis-Putnam-Logemann-Loveland Procedure to DPLL(T)][2]
by Robert Nieuwenhuis, Albert Oliveras, and Cesare Tinelli.

3. *Theory solver for uninterpreted functions.*
[Fast Decision Procedures Based on Congruence Closure][3] by Greg Nelson and
Derek C. Oppen.

[1]:https://en.wikipedia.org/wiki/Conjunctive_normal_form
[2]:https://dl.acm.org/doi/pdf/10.1145/1217856.1217859
[3]:https://web.eecs.umich.edu/~weimerw/2011-6610/reading/nelson-oppen-congruence.pdf