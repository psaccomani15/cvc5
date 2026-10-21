; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=subst --check-proofs --proof-check=eager
; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=ite --check-proofs --proof-check=eager
; EXPECT: unsat
; Pigeonhole: symmetry breaking emits a unit and a binary clause, whose
; justifications are chains of length 2 and 1.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x1 () U)
(declare-fun x2 () U)
(declare-fun x3 () U)
(declare-fun x4 () U)
(assert (or (= x1 a) (= x1 b) (= x1 c)))
(assert (or (= x2 a) (= x2 b) (= x2 c)))
(assert (or (= x3 a) (= x3 b) (= x3 c)))
(assert (or (= x4 a) (= x4 b) (= x4 c)))
(assert (distinct x1 x2 x3 x4))
(check-sat)
