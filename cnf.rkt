#lang racket/base

(require racket/match)
(provide cnf)

(define (eliminate-=> t)
  (match t
    ((? integer?)
     t)
    ((list 'not t1)
     (list 'not (eliminate-=> t1)))
    ((list 'and ts ...)
     (cons 'and (map eliminate-=> ts)))
    ((list 'or ts ...)
     (cons 'or (map eliminate-=> ts)))
    ((list '=> ts ... tn)
     (cons 'or (append (map (lambda (ti)
                              (list 'not (eliminate-=> ti))) ts)
                       (list (eliminate-=> tn)))))))

(define (homogenize t)
  (match t
    ((? integer?)
     t)
    ((list 'not t1)
     (list 'not (homogenize t1)))
    ((list 'and t1 t2 ts ...)
     (foldl (lambda (ti t)
              (list 'and t ti))
            (list 'and (homogenize t1) (homogenize t2))
            (map homogenize ts)))
    ((list 'or t1 t2 ts ...)
     (foldl (lambda (ti t)
              (list 'or t ti))
            (list 'or (homogenize t1) (homogenize t2))
            (map homogenize ts)))))

(define (eliminate-not t)
  (match t
    ((? integer?)
     t)
    ((list 'not t)
     (match t
       ((? integer?)
        (- t))
       ((list 'not t)
        t)
       ((list 'and t1 t2)
        (list 'or (eliminate-not (list 'not t1)) 
              (eliminate-not (list 'not t2))))
       ((list 'or t1 t2)
        (list 'and (eliminate-not (list 'not t1))
              (eliminate-not (list 'not t2))))))
    ((list 'and t1 t2)
     (list 'and (eliminate-not t1) (eliminate-not t2)))
    ((list 'or t1 t2)
     (list 'or (eliminate-not t1) (eliminate-not t2)))))

(define (pull-and t)
  (match t
    ((? integer?)
     t)
    ((list 'and t1 t2)
     (list 'and (pull-and t1) (pull-and t2)))
    ((list 'or t1 t2)
     (let ((t1 (pull-and t1))
           (t2 (pull-and t2)))
       (match* (t1 t2)
         (((list 'and t11 t12) t2)
          (list 'and 
                (pull-and (list 'or t11 t2))
                (pull-and (list 'or t12 t2))))
         ((t1 (list 'and t21 t22))
          (list 'and
                (pull-and (list 'or t1 t21))
                (pull-and (list 'or t1 t22))))
         ((_ _)
          (list 'or t1 t2)))))))

(define (clause t)
  (match t
    ((? integer?)
     (list t))
    ((list 'or t1 t2)
     (append (clause t1) (clause t2)))))

(define (formula t)
  (match t
    ((? integer?)
     (list (clause t)))
    ((list 'or t1 t2)
     (list (append (clause t1) (clause t2))))
    ((list 'and t1 t2)
     (append (formula t1) (formula t2)))))

(define (cnf t)
  (formula
   (pull-and
    (eliminate-not
     (homogenize
      (eliminate-=> t))))))
