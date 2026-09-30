# RealNumbers/Negation.lean

## `cauchyfy` commutes with negation, and `add_neg_R` (section comment)

`add_zero_R` and `add_assoc_R` above needed no new `cauchyfy` theory, because `add_R`'s
own `cauchyfy_add_R` already says everything about the composite. **`add_neg_R` does**,
and this is the one place in the additive package where that bites:
`neg_R f = λn. neg_Q (f n)` applies to the *raw* `f`, not to `f̂`, so nothing yet relates
`(neg_R f)^` to `f̂` — and `f` is an arbitrary `ℕ → ℕ`, so `neg_R f` is not Cauchy and
`cauchyfy_id` does not apply either.

What makes it work is that the two recursions run in *lockstep*, on the nose:

    state(neg_R f, n)  =₀  pair( neg_Q (fst_pair (state(f, n))), snd_pair (state(f, n)) )

— same flag, negated value, at *every* index. The value half is immediate; the flag half
is the content, because the Cauchy check is taken on the raw sequences and
`|neg_Q a −ℚ neg_Q b|` is only `eq_Q`-equal to `|a −ℚ b|`, not `=₀`-equal. So the flags
agree only because `lt_Q_dec`'s *decision* is `eq_Q`-invariant, which is what
`sg_bar_congr_iff` below is for: it turns the two-way implication `lt_Q_congr` supplies
into the `=₀` equality of `sg_bar` values that `cauchyState_advance` / `cauchyState_trip`
demand.

(This is the same machinery `add_comm_R` / `mul_comm_R` are blocked on — see REALS_PLAN
§0.2 — but only in the special case where the two sequences are related by a *fixed*
ℚ-operation, so the induction needs no object-level hypothesis beyond its own IH.)

## `cauchyfy` respects pointwise `=_ℚ` (section comment)

This is REALS_PLAN §0.2's second option, the one it called out of reach: "an `eq_Q`-level
congruence for `cauchyfy`: pointwise `f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n`… an induction carrying an
object-level hypothesis, so it needs `seq_induction` and the weakened-hypothesis plumbing".

It needs neither. The pointwise hypothesis is taken as a **Lean-level schema** — a function
from index terms to derivations — so it is available at whatever index each case of the
induction asks for, and nothing has to be carried through the induction except the
invariant itself. Plain `pinduction` suffices, exactly as for `cauchyState_neg`; that lemma
is this one specialised to `v := neg_R u`, where the value halves happen to agree on the
nose so the first conjunct could be stated with `=₀`.

The invariant is a conjunction because the two halves of the state behave differently: the
**values** agree only up to `=_ℚ`, but the **flags** must agree on the nose, since
`cauchyState_advance`/`_trip` branch on them. `check_sg_congr` is what keeps the flags in
step, and it is the only step that is not bookkeeping.
