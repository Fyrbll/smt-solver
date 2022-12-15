;; From https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UF/-/raw/master/eq_diamond/eq_diamond10.smt2
;; NOTE. This takes about **8.1 MINUTES** but produces UNSAT as expected by the original benchmark
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1)))
             (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2)))
             (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3)))
             (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4)))
             (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5)))
             (or (and (= x5 y5) (= y5 x6)) (and (= x5 z5) (= z5 x6)))
             (or (and (= x6 y6) (= y6 x7)) (and (= x6 z6) (= z6 x7)))
             (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8)))
             (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9)))
             (not (= x0 x9))))