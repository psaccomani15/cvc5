; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=subst --check-proofs --proof-check=eager
; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=ite --check-proofs --proof-check=eager
; EXPECT: unsat
; Two interchangeable constants: symmetry breaking emits a single unit clause.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(assert (or (= x a) (= x b)))
(assert (or (= y a) (= y b)))
(assert (or (= z a) (= z b)))
(assert (distinct x y z))
(check-sat)
