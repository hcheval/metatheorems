# RealNumbers/Interval.lean

## module header

**No shift is needed anywhere.** Clamping is 1-Lipschitz, so `clamp01 f` inherits `f̂`'s own
Cauchy rate index for index, and `cauchyfy` fixes it; and result 4 closes at `eq_R`'s own
index with **no `cauchyfy` step spent at all** — `0ℝ ≤ℝ f` read at `n` says `−f̂(n+1) <ℚ 2^{-n}`,
which is exactly the drift `|clamp01_Q (f̂(n+1)) −ℚ f̂(n+1)|` when the clamp bites from below,
and symmetrically from above. So the tightness triage of CLAUDE.md lands on the cheap side:
neither `cauchyfy_cauchy` nor the `eqR_tail` engine is touched by result 4.

## `clamp01_Q_lip_core`

`clamp01_Q` is monotone and non-expansive, so with `z := clamp01_Q a −ℚ clamp01_Q b` one has
`0 ≤ℚ z ≤ℚ a −ℚ b`, hence `|z| = z ≤ a −ℚ b ≤ |a −ℚ b|`. The two facts are established by a
case split on where `a` and then `b` fall — `≤ 0`, `≥ 1`, or strictly between — which is
**seven cases** (nine minus the two `b > a` shapes that `b ≤ℚ a` excludes; one of the seven
is itself absurd). Every case is `lip_case` fed two order facts, and the only content is
`sub_Q_mono`. The sign-magnitude encoding never surfaces: `le_Q_or_lt_Q` supplies the
splits and `clamp01_Q_of_*` the values.

## `clamp01_eq` at an abstract `u` (docstring of the `∀`-peeled lemma)

**No estimate is spent.** At the goal's index `n`, write `a := f̂(n+1)`. The two hypotheses,
read at `n` through `le_R_all`, are exactly `0ℚ −ℚ a <ℚ 2^{-n}` and `a −ℚ 1ℚ <ℚ 2^{-n}`, and
the goal is `|clamp01_Q a −ℚ a| <ℚ 2^{-n}`. If `a ≤ℚ 0` the clamp is `0` and the drift is
`0 −ℚ a`, non-negative, so its magnitude is the first hypothesis; if `1 ≤ℚ a` it is `1 −ℚ a`,
whose magnitude `a −ℚ 1` is the second; otherwise the clamp is `a` itself and the drift is
`|a −ℚ a|`. No `cauchyfy` step, no tightness engine — the clamp's drift is *exactly* what
`≤ℝ` measures.
