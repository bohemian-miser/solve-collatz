import Collatz

/-!
Verify that every exported Track A / Track B core theorem depends ONLY on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool` (`native_decide`).
-/

#print axioms SolveCollatz.collatzDisproof_of_hasNontrivialCycle
#print axioms SolveCollatz.collatzDisproof_of_hasDivergentOrbit
#print axioms SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz
#print axioms SolveCollatz.Barriers.three_n_minus_one_cycle_5
#print axioms SolveCollatz.Barriers.five_n_plus_one_cycle_13
#print axioms SolveCollatz.Barriers.neg_int_cycle_neg5
