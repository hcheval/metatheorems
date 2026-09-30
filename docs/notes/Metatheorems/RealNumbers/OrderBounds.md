# RealNumbers/OrderBounds.lean

## module header

The kit `Order.lean`'s four order proofs (`lt_add_R`, `lt_mul_pos_R`, `archimedean_R`,
`lt_trans_R_core`) need and nothing else has: implication-form `≤_ℚ` transitivity,
cancellation and subtraction monotonicity, the dyadic product `2^{-a} ·_ℚ 2^{-b} =_ℚ
2^{-(a+b)}`, the persistence of a positive lower bound under `cauchyfy` drift, and the
`Formula.weakenBy`/`substF` normal-form theorems that let the two nested `∃`-eliminations
those proofs need be done **at the Lean level with `Derivable.exist_rule`** rather than with
nested `pobtain`s (which the note at `lt_trans_R_core` records as a measured heartbeat
timeout — exit 3 of that note is implemented here).

This file imports `Mul` (for `cauchyfy_mul_R` and, transitively, `Bounds`/`QBounds`), which
makes `Order.lean` sit above the multiplicative layer — the price of `lt_mul_pos_R` needing
`mul_R_check`. `Order.lean` remains a leaf, so its edit cost does not cascade.

## Object-level multiplication monotonicity (section comment)

`le_Q_zero_mul` / `le_Q_mul_mono_l` (QBounds) take their order facts as *Lean-level*
premises, so they cannot consume a proof-mode hypothesis. `lt_mul_pos_R`'s lower bounds
come out of `pintro`, so it needs the same content as an object implication.
