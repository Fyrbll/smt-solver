#lang racket/base

(require racket/match racket/set racket/function racket/list racket/string)
(provide (all-defined-out))

(define debug #f)

(define (log s)
  (when debug (displayln s)))

(define (list-singleton element) 
  (list element))

(define (snoc lst element)
  (append lst (list element)))

(define (list-member? lst element)
  (member element lst))

(define (list-remove-where lst predicate)
  (remf predicate lst))

(define (list-remove lst element)
  (remf (curry equal? element) lst))

;; Model = Setof Literal

;; stack : Listof Literal
;; decision : Setof Literal
;; edges : Immutable-HashTable Literal (Setof Literal)
;; model : Model
;; formula : Formula
(struct State (stack decision edges model formula) #:transparent)

;; pretty-state : State → String
(define (pretty-state state)
  (match-let (((State stack decision _ _ _) state))
    (string-join
     (map
      (lambda (literal)
        (if (set-member? decision literal)
            (format "~v*" literal)
            (format "~v" literal)))
      stack)
     " ")))

;; Literal = Integer
(define literal? integer?)

;; Clause = Listof Literal
(define (clause? clause-or-formula)
  (andmap literal? clause-or-formula))

;; Formula = Listof Clause
(define (formula? clause-or-formula)
  (andmap clause? clause-or-formula))

;; negate : (Literal → Literal) ∩ (Clause → Formula)
(define (negate literal-or-clause)
  (if (literal? literal-or-clause)
      (let ((literal literal-or-clause))
        (- literal))
      (let ((clause literal-or-clause))
        (map (compose list-singleton negate) clause))))

;; entails-clause : Model → Clause → Boolean
(define (entails-clause model clause)
  (ormap (curry set-member? model) clause))

;; entails-formula : Model → Formula → Boolean
(define (entails-formula model formula)
  (andmap (curry entails-clause model) formula))

;; defined : Setof Literal → Literal → Boolean
(define (defined model literal)
  (or (set-member? model literal)
      (set-member? model (negate literal))))

;; unit-propagate-clause : State → Clause → Clause → Option State
(define (unit-propagate-clause state left-clause right-clause)
  (match right-clause
    (`(,literal . ,new-right-clause)
     (match-let (((State stack decision edges model formula) state)
                 (new-left-clause (snoc left-clause literal)))
       (if (not (defined model literal))
           (let ((clause-w/o-literal (append left-clause new-right-clause)))
             (if (entails-formula model (negate clause-w/o-literal))
                 (let ((new-stack (cons literal stack))
                       (new-edges (foldl
                                   (lambda (model-literal edges)
                                     (hash-update edges model-literal
                                                  (curryr set-add literal)))
                                   (hash-set edges literal (set))
                                   (map negate clause-w/o-literal)))
                       (new-model (set-add model literal)))
                   (State new-stack decision new-edges new-model formula))
                 (unit-propagate-clause state new-left-clause
                                        new-right-clause)))
           (unit-propagate-clause state new-left-clause new-right-clause))))
    ('()
     #f)))

;; unit-propagate-formula : State → Formula → Option State
(define (unit-propagate-formula state formula)
  (match formula
    (`(,clause . ,clauses)
     (or (unit-propagate-clause state '() clause)
         (unit-propagate-formula state clauses)))
    ('()
     #f)))

;; unit-propagate : State → Option State
(define (unit-propagate state)
  (unit-propagate-formula state (State-formula state)))

;; sanity-check-1 : → Void
(define (sanity-check-1)
  (println (unit-propagate (State '() (set) (hash) (set) '((1))))))

;; sanity-check-2 : → Void
(define (sanity-check-2)
  (println (unit-propagate (State '(1) (set 1) (hash 1 (set)) (set) 
                                  `((,(- 1) 2))))))

;;                                      - remove ¬l from pure
;;                   move along         - add ¬l to impure
;;                  /                   - add l to impure
;; is l pure so far?                    - move along
;;                  \                  /
;;                   is ¬l pure so far?                     move along
;;                                     \                   /
;;                                      is l impure so far?
;;                                                         \
;;                                                          - add l to pure
;;                                                          - move along
;;
;; pure-literal-formula : Setof Literal → Setof Literal → Formula →
;;                        Setof Literal
(define (pure-literal-formula pure impure formula)
  (match formula
    (`((,literal . ,clause) . ,clauses)
     (let ((new-formula `(,clause . ,clauses)))
       (if (set-member? pure literal)
           (pure-literal-formula pure impure new-formula)
           (let ((not-literal (negate literal)))
             (if (set-member? pure not-literal)
                 (let ((new-pure (set-remove pure not-literal))
                       (new-impure (set-add (set-add impure literal)
                                            not-literal)))
                   (pure-literal-formula new-pure new-impure new-formula))
                 (if (set-member? impure literal)
                     (pure-literal-formula pure impure new-formula)
                     (let ((new-pure (set-add pure literal)))
                       (pure-literal-formula new-pure impure 
                                             new-formula))))))))
    (`(() . ,new-formula)
     (pure-literal-formula pure impure new-formula))
    ('()
     pure)))

;; pure-literal : State → Option State
(define (pure-literal state)
  (match-let*
      (((State stack decision edges model formula) state)
       (setof-pure-literal (pure-literal-formula (set) (set) formula)))
    (and (not (set-empty? setof-pure-literal))
         (let* ((listof-pure-literal (set->list setof-pure-literal))
                (new-stack (append listof-pure-literal stack))
                (new-edges (foldr (lambda (literal edges)
                                    (hash-set edges literal (set))) edges
                                  listof-pure-literal))
                (new-model (foldr (lambda (literal model)
                                    (set-add model literal)) model
                                  listof-pure-literal)))
           (State new-stack decision new-edges new-model formula)))))

;; sanity-check-3 : → Void
(define (sanity-check-3)
  (println (pure-literal (State '() (set) (hash) (set) 
                                `((1) (2 ,(- 3)) (,(- 2)))))))

;; sanity-check-4 : → Void
(define (sanity-check-4)
  (println (pure-literal (State '() (set) (hash) (set) 
                                `((1 2) (,(- 2) ,(- 1)))))))

;; decide-formula : Model → Formula → Option Literal
(define (decide-formula model formula)
  (match formula
    (`((,literal . ,clause) . ,clauses)
     (if (not (defined model literal))
         literal
         (decide-formula model `(,clause . ,clauses))))
    (`(() . ,new-formula)
     (decide-formula model new-formula))
    ('()
     #f)))

;; decide : State → Option State
(define (decide state)
  (match-let* (((State stack decision edges model formula) state)
               (maybe-literal (decide-formula model formula)))
    (and maybe-literal
         (let* ((literal maybe-literal)
                (new-stack (cons literal stack))
                (new-decision (set-add decision literal))
                (new-edges (hash-set edges literal (set)))
                (new-model (set-add model literal)))
           (State new-stack new-decision new-edges new-model formula)))))

;; sanity-check-5 : → Void
(define (sanity-check-5)
  (println (decide (State '() (set) (hash) (set)
                          '((1 2) (-1 3) (-1 -2) (-3 2) (1 3))))))

;; sanity-check-6 : → Void
(define (sanity-check-6)
  (println (decide (State '(1 2 3) (set 1 2 3) (hash 1 (set) 2 (set) 3 (set))
                          (set 1 2 3) '((1 2) (-1 3) (-1 -2) (-3 2) (1 3))))))

;; conflict : State → Boolean
(define (conflict state)
  (match-let (((State _ decision _ model formula) state))
    (ormap (compose (curry entails-formula model) negate) formula)))

;; fail : State → Option State
(define (fail state)
  (and (conflict state) (set-empty? (State-decision state)) state))

;; sanity-check-7 : → Void
(define (sanity-check-7)
  (println (fail (State '(1 -2) (set) (hash 1 (set) -2 (set)) (set -2 1)
                        '((-1 2))))))

;; sanity-check-8 : → Void
(define (sanity-check-8)
  (println (fail (State '(1 -2) (set -2) (hash 1 (set) -2 (set 1)) (set -2 1)
                        '((-1 2))))))

;; backtrack-helper : Clause → State → State
(define (backtrack-helper clause state)
  (match-let (((State stack decision edges model formula) state))
    (match stack
      (`(,literal . ,new-stack)
       (let* ((new-model (set-remove model literal))
              (new-edges (foldl
                          (lambda (model-literal edges)
                            (hash-update edges model-literal
                                         (curryr set-remove literal)))
                          (hash-remove edges literal)
                          (set->list new-model)))
              (new-state (State new-stack decision new-edges new-model 
                                formula)))
         (if (set-member? decision literal)
             (let* ((not-literal (negate literal))
                    (newer-stack (cons not-literal new-stack))
                    (newer-decision (set-remove decision literal))
                    (newer-model (set-add new-model not-literal))
                    (newer-edges (foldl
                                  (lambda (clause-literal edges)
                                    (let ((not-clause-literal 
                                           (negate clause-literal)))
                                      (if (set-member? new-model 
                                                       not-clause-literal)
                                          (hash-update 
                                           edges not-clause-literal
                                           (curryr set-add not-literal))
                                          edges)))
                                  (hash-set new-edges not-literal (set))
                                  clause)))
               (State newer-stack newer-decision newer-edges newer-model 
                      formula))
             (backtrack-helper clause new-state))))
      ('()
       (error "backtrack-helper: impossible")))))

;; backtrack-formula : State → Formula → State
(define (backtrack-formula state clauses)
  (match-let (((State stack decision edges model formula) state))
    (match clauses
      (`(,clause . ,new-clauses)
       (if (entails-formula model (negate clause))
           (backtrack-helper clause state)
           (backtrack-formula state new-clauses)))
      ('()
       (error "backtrack-formula: impossible")))))

;; backtrack : State → Option State
(define (backtrack state)
  (and (conflict state) (not (set-empty? (State-decision state)))
       (backtrack-formula state (State-formula state))))

;; sanity-check-9 : → Void
(define (sanity-check-9)
  (println
   (backtrack
    (State '(-2 3 1) (set 1) (hash 1 (set -2 3) -2 (set) 3 (set)) (set 1 -2 3)
           '((1 2) (-1 3) (-1 -2) (-3 2) (-1 -3))))))

;; sanity-check-10 : → Void
(define (sanity-check-10)
  (println
   (backtrack
    (State '(-2 3 1 4) (set 1 4) (hash 1 (set -2 3) -2 (set) 3 (set) 4 (set)) 
           (set 1 -2 3 4) '((1 2) (-1 3) (-1 -2) (-3 2 -4) (-1 -3))))))

(define (backjump-subgraph decision-level listof-edges subgraph frontier)
  (match frontier
    (`(,literal . ,new-frontier)
     (if (list-member? decision-level literal)
         (let* ((predecessors (map car
                                   (filter (compose (curryr set-member? literal)
                                                    cdr)
                                           listof-edges)))
                (newer-frontier (append predecessors new-frontier))
                (new-subgraph (foldl (lambda (predecessor subgraph)
                                       (hash-update subgraph predecessor
                                                    (curryr set-add literal)
                                                    (set)))
                                     subgraph predecessors)))
           (backjump-subgraph decision-level listof-edges new-subgraph
                              newer-frontier))
         (backjump-subgraph decision-level listof-edges subgraph new-frontier)))
    ('()
     subgraph)))

(define (backjump-decision-level decision stack)
  (match stack
    (`(,literal . ,new-stack)
     (if (set-member? decision literal)
         `(,literal)
         `(,literal . ,(backjump-decision-level decision new-stack))))
    ('()
     (error "backjump-decision-level: impossible"))))

(define (backjump-uip decision stack)
  (match stack
    (`(,literal . ,new-stack)
     (if (set-member? decision literal)
         literal
         (backjump-uip decision new-stack)))
    ('()
     (error "backjump-uip: impossible"))))

(define (backjump-clause conflict-clause state)
  (match-let* (((State stack decision edges model formula) state)
               (frontier (map negate conflict-clause))
               (uip (backjump-uip decision stack))
               (decision-level (backjump-decision-level decision stack))
               (listof-edges (hash->list edges))
               (subgraph (backjump-subgraph 
                          decision-level listof-edges
                          (foldl 
                           (lambda (literal subgraph)
                             (hash-set subgraph literal (set)))
                           (hash) frontier)
                          frontier))
               (clause-w/o-uip (map
                                negate
                                (foldl
                                 (match-lambda**
                                  ((`(,_ . ,successors) literals)
                                   (filter (compose not (curry set-member? 
                                                               successors))
                                           literals)))
                                 (list-remove (hash-keys subgraph) uip)
                                 (hash->list subgraph)))))
    (list clause-w/o-uip (negate uip))))

(define (sanity-check-16)
  (println
   (backjump-clause
    '(1 -2 3)
    (State
     '(-3 2 -1 4 -5 -8 9 -7 6 11 10)
     (set 9 10 11)
     (hash -1 (set) 2 (set) -3 (set) 4 (set -1 2) -5 (set 2 -3) 6 (set 4 -8)
          -7 (set -3 -5 -8) -8 (set 4 -5) 9 (set -8) 10 (set 6) 11 (set -7))
     (set -1 2 -3 4 -5 6 -7 -8 9 10 11)
     #f))))

(define (sanity-check-17)
  (println
   (backjump-clause
    '(6 -5 -2)
    (State
     '(-6 5 4 3 2 1)
     (set 1 3 5)
     (hash 1 (set 2) 2 (set) 3 (set 4) 4 (set) 5 (set -6) -6 (set))
     (set 1 2 3 4 5 -6)
     #f))))

(define (backjump-model prime-C prime-l state)
  ;;(printf "prime-C: ~v~nprime-l: ~v~nstate: ~v~n~n" prime-C prime-l state)
  (match-let (((State stack decision edges model formula) state)
              (not-prime-C (negate prime-C)))
    (match stack
      (`(,literal . ,new-stack)
       (if (and (not (defined model prime-l))
                (entails-formula model not-prime-C)
                (not (entails-formula (set-remove model literal)
                                      not-prime-C)))
           (let* ((new-stack (cons prime-l stack))
                  (new-edges (foldl
                              (lambda (model-literal edges)
                                (hash-update edges model-literal
                                             (curryr set-add prime-l)))
                              (hash-set edges prime-l (set))
                              (map negate prime-C)))
                  (new-model (set-add model prime-l))
                  (new-formula (snoc formula (snoc prime-C prime-l)))
                  (new-state (State new-stack decision new-edges new-model
                                    new-formula)))
             new-state)
           (let* ((new-decision (set-remove decision literal))
                  (new-edges (foldl
                              (lambda (vertex edges)
                                (hash-update edges vertex
                                             (curryr set-remove literal)))
                              (hash-remove edges literal)
                              (list-remove (hash-keys edges) literal)))
                  (new-model (set-remove model literal))
                  (new-state (State new-stack new-decision new-edges 
                                    new-model formula)))
             (backjump-model prime-C prime-l new-state))))
      ('()
       (if (entails-formula model not-prime-C)
           (let* ((new-stack `(,prime-l))
                  (new-decision (set))
                  (new-edges (hash prime-l (set)))
                  (new-model (set prime-l))
                  (new-formula (snoc formula (snoc prime-C prime-l)))
                  (new-state (State new-stack new-decision new-edges new-model
                                    new-formula)))
             new-state)
           (error "backjump-model: impossible"))))))

;; backjump-formula : State → Formula → Option State
(define (backjump-formula state clauses)
  (match-let (((State stack decision edges model formula) state))
    (match clauses
      (`(,clause . ,new-clauses)
       (if (entails-formula model (negate clause))
           (match-let
               ((`(,backjump-clause-w/o-uip ,uip) (backjump-clause clause
                                                                   state)))
             (backjump-model backjump-clause-w/o-uip uip state))
           (backjump-formula state new-clauses)))
      ('()
       (error "backjump-formula: impossible")))))

;; backjump : State → Option State
(define (backjump state)
  (and (conflict state) (not (set-empty? (State-decision state)))
       (backjump-formula state (State-formula state))))

;; sanity-check-18 : → Void
(define (sanity-check-18)
  (println
   (backjump
    (State
     '(-6 5 4 3 2 1)
     (set 1 3 5)
     (hash 1 (set 2) 2 (set) 3 (set 4) 4 (set) 5 (set -6) -6 (set))
     (set 1 2 3 4 5 -6)
     '((-1 2) (-3 4) (-5 -6) (6 -5 -2))))))

;; get-model-check : State → Option Model
(define (get-model-check state backjump?)
  (let ((maybe-new-state ((if backjump? backjump backtrack) state)))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "~a      ~a" 
                       (if backjump? "__backjump__ " "__backtrack__")
                       (pretty-state new-state)))
          (get-model-check new-state backjump?))
        (if (fail state)
            #f
            (get-model-guess state backjump?)))))

;; get-model-guess : State → Option Model
(define (get-model-guess state backjump?)
  (let ((maybe-new-state (unit-propagate state)))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "__unit-propagate__ ~a" (pretty-state new-state)))
          (get-model-check new-state backjump?))
        (let ((maybe-new-state (decide state)))
          (if maybe-new-state
              (let ((new-state maybe-new-state))
                (log (format "__decide__         ~a" (pretty-state new-state)))
                (get-model-check new-state backjump?))
              (State-model state))))))

;;                       output #f
;; get-model                 ^
;;    |                      | Y
;;    V                 N    |
;; pure-literal     -------fail
;;    |            /         ^
;;    V           V          | N
;; get-model-guess           |
;;    |                  back(track/jump)
;;    |                      ^  |
;;    |                      |  | Y
;;    V            Y         |  V
;; unit-propagate ---> get-model-check
;;    |                ^
;;    | N           Y /
;;    V              / 
;; decide ----------/
;;    |
;;    | N
;;    V
;; output model
;;
;; get-model : Formula → Option Model
(define (get-model formula (backjump? #f))
  (let* ((state (State '() (set) (hash) (set) formula))
         (maybe-new-state (pure-literal state)))
    (log (format "__initial__        ~a" '()))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "__pure-literal__   ~a" (pretty-state new-state)))
          (get-model-guess new-state backjump?))
        (get-model-guess state backjump?))))

;; sanity-check-11 : → Void
(define (sanity-check-11 (backjump? #f))
  (println (get-model '((-1 2) (-3 4) (-3 2 -1) (2 -2) (4)) backjump?)))

;; sanity-check-12 : → Void
(define (sanity-check-12 (backjump? #f))
  (println (get-model '((-1 -2) (3 4) (-3 -2 1) (2) (-4)) backjump?)))

;; sanity-check-13 : → Void
(define (sanity-check-13 (backjump? #f))
  (println (get-model '((-1 -2) (2 3) (-1 -3 4) (2 -3 -4) (1 4)) backjump?)))

;; sanity-check-14 : → Void
(define (sanity-check-14 (backjump? #f))
  (println (get-model '((-1 2) (-3 4) (-5 -6) (6 -5 -2)) backjump?)))

;; sanity-check-15 : → Void
(define (sanity-check-15 (backjump? #f))
  (println (get-model '((1 2) (-1 3) (-1 -2) (-3 2) (-1 -3)) backjump?)))

;; https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
(define (sanity-check-19 (backjump? #f))
  (println
   (get-model
    '((4 -18 19)
      (3 18 -5)
      (-5 -8 -15)
      (-20 7 -16)
      (10 -13 -7)
      (-12 -9 17)
      (17 19 5)
      (-16 9 15)
      (11 -5 -14)
      (18 -10 13)
      (-3 11 12)
      (-6 -17 -8)
      (-18 14 1)
      (-19 -15 10)
      (12 18 -19)
      (-8 4 7)
      (-8 -9 4)
      (7 17 -15)
      (12 -7 -14)
      (-10 -11 8)
      (2 -15 -11)
      (9 6 1)
      (-11 20 -17)
      (9 -15 13)
      (12 -7 -17)
      (-18 -2 20)
      (20 12 4)
      (19 11 14)
      (-16 18 -4)
      (-1 -17 -19)
      (-13 15 10)
      (-12 -14 -13)
      (12 -14 -7)
      (-7 16 10)
      (6 10 7)
      (20 14 -16)
      (-19 17 11)
      (-7 1 -20)
      (-5 12 15)
      (-4 -9 -13)
      (12 -11 -7)
      (-5 19 -8)
      (1 16 17)
      (20 -14 -15)
      (13 -4 10)
      (14 7 10)
      (-5 9 20)
      (10 1 -19)
      (-16 -15 -1)
      (16 3 -11)
      (-15 -10 4)
      (4 -15 -3)
      (-10 -16 11)
      (-8 12 -5)
      (14 -6 12)
      (1 6 11)
      (-13 -5 -1)
      (-7 -2 12)
      (1 -20 19)
      (-2 -13 -8)
      (15 18 4)
      (-11 14 9)
      (-6 -15 -2)
      (5 -12 -15)
      (-6 17 5)
      (-13 5 -19)
      (20 -1 14)
      (9 -17 15)
      (-5 19 -18)
      (-12 8 -10)
      (-18 14 -4)
      (15 -9 13)
      (9 -5 -1)
      (10 -19 -14)
      (20 9 4)
      (-9 -2 19)
      (-5 13 -17)
      (2 -10 -18)
      (-18 3 11)
      (7 -9 17)
      (-15 -6 -3)
      (-2 3 -13)
      (12 3 -2)
      (-2 -3 17)
      (20 -15 -16)
      (-5 -17 -19)
      (-20 -18 11)
      (-9 1 -5)
      (-19 9 17)
      (12 -2 17)
      (4 -16 -5))
    backjump?)))
