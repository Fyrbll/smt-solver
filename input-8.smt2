;; I didn't take this from anywhere, I wrote it specifically for the README
(assert (not
  (=> (and (= (f x) y)
           (= (f y) z)
           (= (f z) x))
      (= (f (f (f x))) y))))