# RealNumbers/LeOrder.lean

## module header

Before this file the ℝ layer had a complete **strict**-order package (`Order.lean`:
`lt_add_R`, `lt_trans_R`, `lt_mul_pos_R`, `lt_irrefl_R`, `zero_lt_one_R`, `archimedean_R`)
and, for `≤_ℝ`, only *conversions* — `le_R_of_le_R_pu`, `le_R_pu_of_le_R`, `le_R_all`,
`le_R_of_all`, `le_R_of_bound` (`Field.lean`), plus the `clamp01` bounds and `approx_le_R`.
There was no reflexivity, no transitivity and no additive monotonicity.

That was a real blocker rather than a gap in taste: `Derivable.dist_tri` and every space
axiom in the tower (`WHyperbolic`, `CAT0`, `Normed`) are stated with `≤_ℝ` through
`le_R_pu`, so **two triangle inequalities could not be chained**. `BaseEquality.dist_tri_chain`
is the first consumer.

### What `≤_ℝ` is, and which estimates are tight

`le_R f g` is `¬(g <_ℝ f)`, and `le_R_all`/`le_R_of_all` pin that down completely:

    f ≤_ℝ g   ⟺   ∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}.

Everything here is stated against that characterisation, and — following the layer's rule,
*triage by tightness, not by shape* — the results split cleanly in two:

* **Slack-free, no engine.** `le_R_refl_core`, `le_R_of_eq_R_core`, `le_R_antisymm_core`,
  `lt_imp_le_R_core` and both additive-monotonicity lemmas close directly. Monotonicity is
  the interesting case: `add_R`'s `+1` index shift means the goal at index `n` is a statement
  about `f̂(n+2)`, where the hypothesis is available with bound `2^{-(n+1)}` — *half* the
  budget, so the common summand cancels exactly (`sub_Q_add_cancel`) and a single
  `pow2neg_Q_le_succ` finishes. No telescope, no squeeze.
* **Tight — the engine is unavoidable.** Transitivity is not: at a common index the two
  hypotheses give `2^{-n} +ℚ 2^{-n} = 2^{-(n-1)}`, and moving to a farther index costs
  `2·2^{-(n+1)} = 2^{-n}` by `cauchyfy_shift_le`, which is the *whole* budget. Every finite
  choice overshoots, exactly as for `eq_R_trans` (see `Estimates.lean`'s header).

So `le_R_trans_core` is proved by the **one-sided mirror of the `eqR_tail`/`eqR_le`/
`eqR_strict` telescope**: `leR_pair_step`, `leR_tail`, `leR_le`, `leR_strict`, on the signed
difference `sDiff` where the `eq_R` engine uses the absolute value `cDiff`. The mirror is
exact — the only new ingredient is that a signed one-step estimate must bound the two
`cauchyfy` drifts *directionally*, which `le_Q_self_abs` supplies, exactly as `lt_shift1`
already does for `<_ℝ`.

## `le_R_trans_core`

See this file's header for why no direct estimate closes.

## Additive monotonicity (section comment)

`add_R f g n = add_Q (f̂(n+1), ĝ(n+1))` — the `+1` shift.  So the goal at index `n` is a
statement about index `n+2`, where the hypothesis carries the bound `2^{-(n+1)}`.  Half the
budget is left over; `pow2neg_Q_le_succ` spends it and nothing else is needed.

## `le_R_add_mono_l_core`

Proved directly rather than through `add_comm_R` and `le_R_congr`: the estimate is the same
one, and going round by commutativity would spend two `=_ℝ` congruences for nothing.

## Subtraction: `f ≤ g +ℝ h → f −ℝ h ≤ g` (section comment)

The ℝ content of the reverse triangle inequality (`BaseEquality.dist_rev_tri`).

The accounting, done directly: the goal at index `n` is about `(f −ℝ h)^(n+1) −ℚ ĝ(n+1)`,
i.e. `f̂(n+2) −ℚ ĥ(n+2) −ℚ ĝ(n+1)` by `cauchyfy_sub_R`, while the hypothesis at index `m`
is `f̂(m+1) −ℚ (ĝ(m+2) +ℚ ĥ(m+2)) <ℚ 2^{-m}`. Bringing `ĝ` from `m+2` to `n+1`, `ĥ` from
`m+2` to `n+2` and `f̂` from `m+1` to `n+2` costs at least `2^{-(n+1)} + 2^{-(n+2)}` for
every `m ≥ n+1`, so the total is `2^{-m} + 2^{-(n+1)} + 2^{-(n+2)} + …`, which reaches
`2^{-n}` only as `m → ∞`: **tight**, every finite `m` overshoots (at `m = n+1` by exactly
`2^{-(n+3)}`; at `m = n` by `2^{-(n+1)}`). So a direct proof must go through the
`leR_strict` telescope.

But that telescope is already packaged in `le_R_trans_core`, and the statement is
*algebraically* `f +ℝ (−ℝ h) ≤ (g +ℝ h) +ℝ (−ℝ h) =ℝ g` — right monotonicity (slack-free,
above) followed by the cancellation `(g +ℝ h) +ℝ (−ℝ h) ≤ℝ g`, which is associativity,
`add_neg_R_core` and `add_zero_R_core` chained by transitivity. No new estimate is written
at all; the one new `cauchyfy` fact is `f −ℝ h =ℝ f +ℝ (−ℝ h)`, which holds *on the nose*
at every index (`cauchyfy_sub_R` against `cauchyfy_add_R` + `cauchyfy_neg`), so it is
`eq_R_of_cauchyfy_eqQ` with no estimate either.
