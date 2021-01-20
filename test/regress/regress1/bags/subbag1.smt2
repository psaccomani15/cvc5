(set-logic ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun x () Int)
(assert (= x 1))
(assert (subbag A B))
(assert (subbag B A))
(assert (= (bag.count x A) 5))
(assert (= (bag.count x B) 10))
(check-sat)