;; From https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UF/-/raw/master/eq_diamond/eq_diamond11.smt2
;; I deleted some part of the input formula to force SAT instead of UNSAT
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1)))
             (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2)))
             (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8)))
             (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9)))
             (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10)))
             (not (= x0 x10))))