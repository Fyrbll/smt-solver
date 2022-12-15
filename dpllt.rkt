#lang racket/base

(require racket/match racket/set
         (rename-in racket/function (negate function-negate)) racket/list
         racket/string racket/port "./cnf.rkt" "./dpll.rkt" "./euf.rkt")

(define (make-term->literal terms (term->literal (hash)) (next-literal 1))
  (match terms
    ((cons term terms)
     (let-values
         (((term->literal next-literal)
           (if (hash-has-key? term->literal term)
               (values term->literal next-literal)
               (values (hash-set term->literal term next-literal)
                       (+ next-literal 1)))))
       (make-term->literal terms term->literal next-literal)))
    ((list)
     term->literal)))

(define (collect-terms formula (terms null))
  (match formula
    ((list 'and)
     terms)
    ((list 'and formula formulas ...)
     (collect-terms formula 
                    (collect-terms (cons 'and formulas) terms)))
    ((list 'or)
     terms)
    ((list 'or formula formulas ...)
     (collect-terms formula 
                    (collect-terms (cons 'or formulas) terms)))
    ((list '=>)
     terms)
    ((list '=> formula formulas ...)
     (collect-terms formula
                    (collect-terms (cons '=> formulas) terms)))
    ((list 'not formula)
     (collect-terms formula terms))
    ((and (list '= _ _) term)
     (cons term terms))))

(define (hash-invert hsh)
  (foldl (match-lambda**
          (((cons key value) hsh)
           (hash-set hsh value key))) (hash) (hash->list hsh)))

(define (replace term->literal formula)
  (match formula
    ((cons 'and formulas)
     (cons 'and (map (lambda (formula)
                       (replace term->literal formula)) formulas)))
    ((cons 'or formulas)
     (cons 'or (map (lambda (formula)
                      (replace term->literal formula)) formulas)))
    ((cons '=> formulas)
     (cons '=> (map (lambda (formula)
                      (replace term->literal formula)) formulas)))
    ((list 'not formula)
     (list 'not (replace term->literal formula)))
    ((and (list '= _ _) term)
     (hash-ref term->literal term))))

(define (main path)
  (let* ((in-port (open-input-file path))
         (assertions (port->list read in-port))
         (_ (close-input-port in-port))
         (formulas (map (match-lambda
                          ((list 'assert formula)
                           formula)) assertions))
         (terms (append-map (lambda (formula)
                              (collect-terms formula)) formulas))
         (term->literal (make-term->literal terms))
         (literal->term (hash-invert term->literal))
         (formulas (map (lambda (formula)
                          (replace term->literal formula)) formulas))
         (formula (if (> (length formulas) 1)
                      (cons 'and formulas)
                      (first formulas)))
         (formula (cnf formula)))
    (log (hash-map literal->term (lambda (literal term)
                                   (list literal '<=> term))))
    (get-model^ term->literal literal->term formula #t)))

(define (tlearn t->l l->t state backjump?)
  (let*-values
      (((model) (State-model state))
       ((literals) (set->list model))
       ((positive-literals negative-literals) 
        (partition (lambda (literal)
                     (> literal 0)) literals))
       ((equalities) (map (lambda (literal)
                            (hash-ref l->t literal)) positive-literals))
       ((inequalities) (map (lambda (literal)
                              (hash-ref l->t (- literal))) negative-literals))
       ((consistency) (problem-initialize (list equalities inequalities))))
    (match consistency
      ((list 'sat interpretation)
       interpretation)
      ((list 'unsat equalities inequality)
       (let* ((positive-literals (map (lambda (literal)
                                        (hash-ref t->l literal)) equalities))
              (negative-literal (- (hash-ref t->l inequality)))
              (learned-lemma (map (lambda (literal)
                                    (- literal))
                                  (cons negative-literal positive-literals)))
              (formula (cons learned-lemma (State-formula state))))
         (log (format "__tlearn__         ~a" learned-lemma))
         (log (format "__restart__"))
         (get-model^ t->l l->t formula backjump?))))))

(define (get-model-check^ t->l l->t state backjump?)
  (let ((maybe-new-state ((if backjump? backjump backtrack) state)))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "~a      ~a" 
                       (if backjump? "__backjump__ " "__backtrack__")
                       (pretty-state new-state)))
          (get-model-check^ t->l l->t new-state backjump?))
        (if (fail state)
            #f
            (get-model-guess^ t->l l->t state backjump?)))))

(define (get-model-guess^ t->l l->t state backjump?)
  (let ((maybe-new-state (unit-propagate state)))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "__unit-propagate__ ~a" (pretty-state new-state)))
          (get-model-check^ t->l l->t new-state backjump?))
        (let ((maybe-new-state (decide state)))
          (if maybe-new-state
              (let ((new-state maybe-new-state))
                (log (format "__decide__         ~a" (pretty-state new-state)))
                (get-model-check^ t->l l->t new-state backjump?))
              (tlearn t->l l->t state backjump?))))))

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
(define (get-model^ t->l l->t formula (backjump? #f))
  (let* ((state (State '() (set) (hash) (set) formula))
         (maybe-new-state (pure-literal state)))
    (log (format "__initial__        ~a" '()))
    (if maybe-new-state
        (let ((new-state maybe-new-state))
          (log (format "__pure-literal__   ~a" (pretty-state new-state)))
          (get-model-guess^ t->l l->t new-state backjump?))
        (get-model-guess^ t->l l->t state backjump?))))
