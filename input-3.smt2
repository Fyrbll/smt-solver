;; From https://www21.in.tum.de/teaching/sar/SS20/6.pdf
(assert (= a b))
(assert (= b c))
(assert (= (g (f a) b) (g (f c) a)))
(assert (not (= (f a) b)))