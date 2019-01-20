;; Figure 3.5
;;
;; Barrett, Clark, Aaron Stump, and Cesare Tinelli. "The smt-lib standard: Version 2.0."
;; Proceedings of the 8th International Workshop on Satisfiability Modulo Theories (Edinburgh, England).
;; Vol. 13. 2010.

(set-option :print-success false)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int) Int)

(assert (= (f x) (f y)))
(assert (not (= x y)))

(check-sat)
; sat

(get-value (x y))
; ((x 0)
;  (y 1)
; )

(declare-fun a () (Array Int (List Int)))

(check-sat)
; sat

(get-value (a))
; ((a @_0_1)
; )

(get-value (select 2 @_0_1))
; (((select 2 @_0_1) @_2_0)
; )

(get-value ((first @_2_0) (rest @_2_0)))
; (((first @_2_0) 1)
;  ((rest @_2_0) nil)
; )
