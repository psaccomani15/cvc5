; EXPECT: sat
; The invariance check of the symmetry breaker for {a, b} normalizes the
; image of the second assertion under the swap of a and b, which is not
; asserted. The values of (f b) must not be recorded from it: otherwise the
; breaker takes (f b) to be one of c and d, and adds (= (f b) c) for the
; invariant set {c, d}, which contradicts the last assertions.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const y U)
(assert (or (P (f b)) (P (f a))))
(assert (or (= (f a) c) (= (f a) d)))
(assert (or (= y a) (= y b)))
(assert (not (= (f b) c)))
(assert (not (= (f b) d)))
(check-sat)
