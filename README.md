Project for Advanced Functional Programming, Fall 2022
======================================================

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

2. The program produces a bijection from a subset of the natural numbers to
equalities. So, if the program contains just the equalities $f(a,b) = a$ and
$f(f(a,b),b) = a$, then the program will produce two hash tables.

$$\text{literal\\_to\\_term}\ = \\{ 1 \mapsto (f(a,b) = a), 2 \mapsto (f(f(a,b),b) = a) \\}$$

$$\text{term\\_to\\_literal}\ = \\{ (f(a,b) = a) \mapsto 1, (f(f(a,b),b) = a) \mapsto 2 \\}$$

Here is a commented version of the function `main` from `dpllt.rkt`, which is
the entry point to the solver.

```
(define (main path)
  (let* (
         ;; the following three lines read all the s-expressions in the input
         ;; file and store them in the variable 'assertions'
         (in-port (open-input-file path))
         (assertions (port->list read in-port))
         (_ (close-input-port in-port))

         ;; we remove the 'assert' enclosing each assertion in 'assertions'
         ;; e.g. (assert (= x y)) --> (= x y)
         ;; the results are stored in 'formulas'
         (formulas (map (match-lambda
                          ((list 'assert formula)
                           formula)) assertions))


         ;; 'terms' is the list of terms present across all the formulas
         ;; mentioned in 'formulas,' how
         (terms (append-map (lambda (formula)
                              (collect-terms formula)) formulas))


         ;; 
         (term->literal (make-term->literal terms))

         ;; since 'term->literal' is a one-to-one hash table, we can compute its
         ;; inverse hash table
         (literal->term (hash-invert term->literal))


         (formulas (map (lambda (formula)
                          (replace term->literal formula)) formulas))


         (formula (if (> (length formulas) 1)
                      (cons 'and formulas)
                      (first formulas)))


         (formula (cnf formula)))

    ;; please ignore this it's for debugging purposes
    (log (hash-map literal->term (lambda (literal term)
                                   (list literal '<=> term))))

    (get-model^ term->literal literal->term formula #t)))
```

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

<!--
(time (main "./input-5.smt2") (void))
cpu time: 486906 real time: 496929 gc time: 2215
-->