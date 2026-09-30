# RealNumbers.lean

## module header

This file used to hold the whole ℝ layer (3,615 lines); a one-character edit cost a 37.5 s
rebuild. It is now split into `Metatheorems/RealNumbers/*.lean`, in dependency order:

The import graph is deliberately flat below `Field`: `Negation → Mul` is a real dependency
(`mul_comm_R_core` needs `cauchyfy_congr`), but `Order` and `Metric` import only `Field`, so an
edit to `Negation` (the 14 s module) does not cascade into them.

Importing `Metatheorems.RealNumbers` still brings the whole layer into scope, so no other file
in the project changed. Everything is in the `Metatheorems` namespace, as before.

### the `LeOrder` row of the module table

`≤_ℝ` had only the `Field.lean` conversions before this module existed, so two
`Derivable.dist_tri`s could not be chained

## the `#print axioms` block (comments between the `#print axioms` lines)

Two genuinely different lemmas that once shared a name: `_r` subtracts the right summand,
`_l` the left. Both are true and they are not interchangeable, so neither could be dropped.
(before `le_Q_sub_of_le_add_r` / `_l`)

The NON-STRICT order package (`RealNumbers/LeOrder.lean`). Before it the ℝ
layer had reflexivity/transitivity/monotonicity for `<_ℝ` and *nothing* for `≤_ℝ` beyond
the `le_R`/`le_R_pu`/bound conversions in `Field.lean`, so two `Derivable.dist_tri`s could
not be chained. `BaseEquality.dist_tri_chain` is the first consumer. (before `leR_pair_step`)

Subtraction: the ℝ content of the reverse triangle inequality
(`BaseEquality.dist_rev_tri`). Tight as a direct estimate, but *no new estimate* — right
monotonicity, then the cancellation `(g +ℝ h) +ℝ (−ℝ h) ≤ℝ g`, chained by `le_R_trans_core`;
the two `=ℝ` facts hold on the nose at every index. (before `sub_R_eq_add_neg_R_core`)

The ℝ-MCT assembly (`RealNumbers/MCTLemmas.lean`): constants, cancellation,
absolute value, the sample lower bound, the window drop, transport along ℕ-equalities and
the antitone chain over ℝ — everything `ProofMode/RealMCT.lean` consumes. All algebra over
`LeOrder.lean`; no new estimate. (before `sub_Q_nonpos_of_le`)
