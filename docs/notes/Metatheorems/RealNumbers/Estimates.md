# RealNumbers/Estimates.lean

## The tightness estimate behind `eq_R_trans` (section comment before `cauchyState_subst`)

`eq_R`'s bound is exactly tight — `2^{-n} = 2·2^{-(n+1)}` — so no route through
"|f̂−ĝ| + |ĝ−ĥ| at a common index" closes: every such estimate overshoots by exactly one
dyadic step, at *every* choice of index. (REALS_PLAN.md §0.5 records this, and its
proposed five-term split does not in fact close either: it collects `2·2^{-(m-1)}` from
the two hypotheses where the telescope only returns `2·2^{-m}`.)

What does work is a *limit* argument made finite:

  1. `cauchy_pair_step`  — one step, strict: `X_q <ℚ 2^{-q} +ℚ X_{q+1}`, where
     `X_q := |f̂(q) −ℚ ĥ(q)|`. Two strict `cauchyfy` steps at `2^{-(q+1)}` each.
  2. `eqR_tail`  — iterate it: `∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}`. Induction on `k`.
  3. `eqR_le`  — squeeze: holding for *every* `k`, that gives `X_{p+1} ≤ℚ 2^{-p}`.
     `pow2neg_rat_den_le` supplies the index at which the dyadic scale falls below the
     hypothetical excess. This is where the strict `<` is traded for a non-strict `≤`.
  4. `eqR_strict`  — spend one *more* step: `X_{n+1} <ℚ 2^{-(n+1)} +ℚ X_{n+2}` with
     `X_{n+2} ≤ℚ 2^{-(n+1)}` gives `X_{n+1} <ℚ 2^{-n}` — strictly, because step 1 is.

Steps 3 and 4 together are the finite surrogate for "`|f̂(p) − F| < 2^{-p}` strictly".

## `add_eq_zero_R_core`

The sum is fed in through `add_eq_zero_R_gen`'s abstract `u` rather than rewritten inside the
goal: `prw` would have to push a substitution through `Term.add_R`, which is the
delta-expansion blow-up CLAUDE.md's build-cost section warns about (measured here: a
heartbeat timeout). As a Lean-level parameter it costs nothing.

## `eq_R_sym_core`

Instantiating the `∀`-quantified `eq_R_sym` at two terms means pushing two `subst0`s through
`eq_R`; taking the terms as parameters skips that entirely, and the proof is `eq_R_sym`'s own
body with `f`/`g` in place of the two bound variables. Used by
`MetricSpace.admissibleEqX.eqx_sym`.

## ℚ helpers: `|·|_ℚ` against a two-sided bound (section comment before `sub_Q_zero_l`)

Everything in this block is a ℚ fact; it lives here rather than in
`RationalNumbers.lean` only because that file is another workstream's. The two
load-bearing ones are `le_Q_self_abs` (`z ≤_ℚ |z|_ℚ`, which is how a *directed*
estimate is recovered from a `cauchyfy` bound) and `abs_Q_lt_of_two_sided`
(`z <_ℚ c` and `−z <_ℚ c` give `|z| <_ℚ c`, which is how an `eq_R` goal is discharged
from a pair of one-sided bounds). Neither existed; REALS_PLAN §0.8 item 1 lists the
family as missing.

The route is `le_Q_of_cross` throughout: it turns a `≤_ℚ` goal into ℕ arithmetic on
signed cross products, with no `sub_Q` anywhere.

## The symbolic-shift telescope (section comment before `tele_base_eq`)

`cauchyfy_two_step` is a *fixed* two-step estimate.  What `mul_one_R` (and, with
`mul_R_check`, `distrib_R` / `mul_assoc_R`) needs is the same estimate over *symbolically
many* steps: `mul_R`'s index shift `b = f(0) +ℕ g(0) +ℕ 2` depends on the arguments, so
comparing `(f ·ℝ 1ℝ)^(n+1) = f̂(n+1+b)` with `f̂(n+1)` is a telescope of `b` steps.

The statement has to **carry the remaining slack**, or the induction step has none:

    ∀k ∀p.  |f̂(p) −ℚ f̂(p+k)|  +ℚ  2^{-(p+k)}  ≤ℚ  2^{-p}

Base `k = 0`: `0 +ℚ 2^{-p} ≤ℚ 2^{-p}`.  Step: split off `|f̂(p+k) −ℚ f̂(p+k+1)| <ℚ
`2^{-(p+k+1)}` by `cauchyfy_cauchy`, and pay for it with the carried `2^{-(p+k)}` — which is
exactly `2^{-(p+k+1)} +ℚ 2^{-(p+k+1)}` (`pow2neg_Q_halve`), so one half funds the new step
and the other becomes the new carried slack.  Nothing is spent, which is why the conclusion
stays `≤ℚ 2^{-p}` at every `k`.

The `+ℚ`-form is used rather than REALS_PLAN §0.5 item 3's `≤ℚ 2^{-p} −ℚ 2^{-(p+k)}`: the
two say the same thing, but the difference form needs `sub_Q` cancellation lemmas at every
step, while the `+ℚ` form is pure `le_Q_add_both` / `add_Q_assoc_inst` bookkeeping.
