;; Getting Started with Z3: A Guide
;; https://rise4fun.com/z3/tutorial

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (forall ((x Int))
                (! (= (f (g x)) x)
                   :pattern ((f (g x))))))
(assert (= (g a) c))
(assert (= (g b) c))
(assert (not (= a b)))
(check-sat)
