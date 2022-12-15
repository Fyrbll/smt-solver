;; from "Fast Decision Procedures Based on Congruence Closure" by Nelson and Oppen
(assert (= (f a b) a))
(assert (not (= (f (f a b) b) a)))