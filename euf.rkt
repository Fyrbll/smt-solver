#lang racket/base

(require
 (only-in racket/list append-map index-where range first second list-set)
 (only-in racket/match match match-let match-lambda match-lambda**)
 (only-in racket/set set mutable-set set-union set->list set-member? set-add! set-clear! for/set set-count set-add)
 (only-in racket/syntax format-symbol)
 (only-in racket/function curryr curry identity))
(provide problem-initialize)

(define idx (box 0))

(define (fresh)
  (let ((idx-old (unbox idx)))
    (set-box! idx (+ idx-old 1))
    idx-old))

(define terms (mutable-set))

(define vtxs (mutable-set))

(define tau (make-hash))

(define tau-inverse (make-hash))

(define adj (make-hash))

(define R '())

(define (cleanup)
  (set-box! idx 0)
  (set-clear! terms)
  (set-clear! vtxs)
  (hash-clear! tau)
  (hash-clear! tau-inverse)
  (hash-clear! adj)
  (set! R '()))

(define example-1
  '(((= (f a b) a) 
     (= (f (f a b) b) (f (f a b) b)))
    ()))

(define example-2
  '(((= (f a b) a))
    ((= (f (f a b) b) a))))

(define example-3
  '(((= (f (f (f a))) a)
     (= (f (f (f (f (f a))))) a))
    ((= (f a) a))))

(define (term-terms term)
  (unless (set-member? terms term)
    (when (pair? term)
      (for ((argument (cdr term)))
        (term-terms argument)))
    (set-add! terms term)
    (let ((vtx (fresh)))
      (set-add! vtxs vtx)
      (hash-set! tau term vtx))))

(define (problem-terms problem)
  (match-let ((`(,equalities ,inequalities) problem))
    (foldl
     (match-lambda**
      ((`(= ,term-l ,term-r) _)
       (term-terms term-l)
       (term-terms term-r)))
     (void) `(,@equalities ,@inequalities))))

(define (insert lst elt)
  (match lst
    (`(,lst-first . ,lst-rest)
     (cond
       ((< elt lst-first)
        `(,elt . ,lst))
       ((= elt lst-first)
        lst)
       (else
        `(,lst-first . ,(insert lst-rest elt)))))
    ('()
     `(,elt))))

(define (term-adj term)
  (when (pair? term)
    (for ((arg (reverse (cdr term))))
      (let* ((term-vtx (hash-ref tau term))
             (arg-vtx (hash-ref tau arg))
             (term-adj (hash-ref adj term-vtx '())))
        (hash-set! adj term-vtx `(,arg-vtx . ,term-adj))))))

(define (terms-adj)
  (for ((term terms))
    (term-adj term)))

(define (list-remove lst idx)
  (match lst
    ('() '())
    (`(,lst-first . ,lst-rest)
     (match idx
       (0 lst-rest)
       (_ `(,lst-first . ,(list-remove lst-rest (- idx 1))))))))

(define (R-union vtx0 vtx1)
  (let ((vtx0-idx (index-where R (curryr set-member? vtx0)))
        (vtx1-idx (index-where R (curryr set-member? vtx1))))
    #;(printf "~a union ~a (at ~a) and ~a (at ~a)~n" 
            R vtx0 vtx0-idx vtx1 vtx1-idx)
    (unless (equal? vtx0-idx vtx1-idx)
      (let* ((vtx0-set (list-ref R vtx0-idx))
             (vtx1-set (list-ref R vtx1-idx))
             (R^ R)
             (R^ (list-set R^ vtx0-idx #f))
             (R^ (list-set R^ vtx1-idx #f))
             (R^ (filter identity R^))
             (R^ (cons (set-union vtx0-set vtx1-set) R^)))
        (set! R R^)))))

(define (R-find vtx)
  (apply min (set->list (findf (curryr set-member? vtx) R))))

(define (vtxs-R)
  (set! R (map (lambda (vtx) (set vtx)) (set->list vtxs)))
  #;(printf "initial R: ~a~n" R))

(define (problem-R problem)
  (match-let ((`(,equalities ,_) problem))
    (for ((equality equalities))
      (match equality
        (`(= ,term0 ,term1)
         (let ((term0-vtx (hash-ref tau term0))
               (term1-vtx (hash-ref tau term1)))
           (R-union term0-vtx term1-vtx)))))))

(define (vtx-predecessors vtx)
  (foldl
   (lambda (vtx^ acc)
     (if (member vtx (hash-ref adj vtx^ '()))
         (set-add acc vtx^)
         acc))
   (set) (range (set-count vtxs))))

(define (vtx-all-predecessors vtx)
  (let ((vtx-equiv (findf (curryr set-member? vtx) R)))
    (apply set-union (set) (map vtx-predecessors (set->list vtx-equiv)))))

(define (congruent vtx0 vtx1)
  (let ((vtx0-adj (hash-ref adj vtx0 '()))
        (vtx1-adj (hash-ref adj vtx1 '())))
    (let ((vtx0-deg (length vtx0-adj)))
      (and (equal? vtx0-deg (length vtx1-adj))
           (andmap 
            (lambda (idx)
              (equal? (R-find (list-ref vtx0-adj idx))
                      (R-find (list-ref vtx1-adj idx))))
            (range vtx0-deg))))))

(define (merge vtx0 vtx1)
  (unless (equal? (R-find vtx0) (R-find vtx1))
    (R-union vtx0 vtx1)
    (let ((vtx0-pre (vtx-all-predecessors vtx0))
          (vtx1-pre (vtx-all-predecessors vtx1)))
      (for ((vtx vtx0-pre))
        (for ((vtx^ vtx1-pre))
          (unless (equal? (R-find vtx) (R-find vtx^))
            (when (congruent vtx vtx^)
              (merge vtx vtx^))))))))

(define (equalities-R equalities)
  (for ((equality equalities))
    (match equality
      (`(= ,lhs ,rhs)
       (let ((lhs-vtx (hash-ref tau lhs))
             (rhs-vtx (hash-ref tau rhs)))
         (merge lhs-vtx rhs-vtx))))))

#;(define (inequalities-sat inequalities)
  (andmap
   (match-lambda
     (`(= ,lhs ,rhs)
      (not
       (equal?
        (R-find (hash-ref tau lhs))
        (R-find (hash-ref tau rhs))))))
   inequalities))

(define (inequalities-sat inequalities)
  (match inequalities
    ((cons (and inequality `(= ,lhs ,rhs)) inequalities)
     (if (equal? (R-find (hash-ref tau lhs)) (R-find (hash-ref tau rhs)))
         inequality
         (inequalities-sat inequalities)))
    ((list)
     #f)))

(define (tau-invert)
  (hash-for-each tau (lambda (k v)
                       (hash-set! tau-inverse v k))))

(define (search function argument-interpretations)
  (foldl
   (lambda (vtx acc)
     (if acc
         acc
         (let ((vtx-term (hash-ref tau-inverse vtx)))
           (match vtx-term
             (`(,function^ . ,_)
              (if (equal? function function^)
                  (let ((vtx-adj (hash-ref adj vtx '())))
                    (if (equal? (length argument-interpretations)
                                (length vtx-adj))
                        (if (andmap
                             (lambda (vtx^ interpretation)
                               (set-member? interpretation vtx^))
                             vtx-adj argument-interpretations)
                            (findf (curryr set-member? vtx) R)
                            acc)
                        adj))
                  acc))
             (_ acc))))) #f (set->list vtxs)))

(define (term-interpretation term)
  (match term
    (`(,function . ,arguments)
     (let ((argument-interpretations
            (map term-interpretation arguments)))
       (search function argument-interpretations)))
    (_
     (findf (curryr set-member? (hash-ref tau term)) R))))

(define (model)
  (map (lambda (term)
         (cons term (term-interpretation term))) (set->list terms)))

(define (problem-initialize problem)
  (cleanup)
  (problem-terms problem)
  (tau-invert)
  (terms-adj)
  (vtxs-R)
  (equalities-R (first problem))
  (let ((maybe-conflict (inequalities-sat (second problem))))
    (if maybe-conflict
        (let ((conflict maybe-conflict))
          (list 'unsat (first problem) conflict))
        (list 'sat (model)))))
