; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=subst --check-proofs --proof-check=eager
; COMMAND-LINE: --symmetry-breaker --symmetry-breaker-proof-mode=ite --check-proofs --proof-check=eager
; EXPECT: unsat
; Terms that contain constants of the partition, and preconditions that are
; already contained in the emitted clause. No fixpoint-free involution exists
; on three elements.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(assert (or (= (f a) a) (= (f a) b) (= (f a) c)))
(assert (or (= (f b) a) (= (f b) b) (= (f b) c)))
(assert (or (= (f c) a) (= (f c) b) (= (f c) c)))
(assert (not (= (f a) a)))
(assert (not (= (f b) b)))
(assert (not (= (f c) c)))
(assert (distinct (f a) (f b) (f c)))
(assert (= (f (f a)) a))
(assert (= (f (f b)) b))
(assert (= (f (f c)) c))
(check-sat)
