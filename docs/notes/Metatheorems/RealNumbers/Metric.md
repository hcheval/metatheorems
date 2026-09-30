# RealNumbers/Metric.lean

## `le_zero_eq_zero_R_core`

**The old statement of `le_zero_eq_zero_R` — without the first conjunct — was FALSE**, and the
counterexample is worth keeping. Take `f := λn.⟨−1⟩_ℚ` and `g := 0_ℝ`. Then

* `le_R f g` unfolds to `¬ lt_R g f`, i.e. `¬∃n (f̂(n+1) −_ℚ ĝ(n+1) ≥_ℚ 2^{-n})`. Here that
  difference is `−1`, which is below every `2^{-n}`, so the `∃` is empty and `f ≤_ℝ g` holds;
* `g =_ℝ 0_ℝ` holds (`cauchyfy_zero_R`);
* `f =_ℝ 0_ℝ` fails already at `n = 0`: it asks `|−1|_ℚ <_ℚ ⟨2^{-0}⟩_ℚ`, i.e. `1 <_ℚ 1`.

So that formula was false in the standard model and hence not derivable: `f ≤_ℝ 0` says
nothing about how far *below* `0` the real `f` is. Adding `0_ℝ ≤_ℝ f` repairs it, and the
repaired form is what is proved here.

The estimate, at the goal's index `n`. Write `a_k := f̂(k)`, `b_k := ĝ(k)`.

* **lower bound** `−a_{n+1} <ℚ 2^{-n}` — `0_ℝ ≤_ℝ f` read at `n`, directly;
* **upper bound** `a_{n+1} <ℚ 2^{-n}` — three steps, at index `n+2` rather than `n`, because
  reading the two hypotheses at `n` gives only `2^{-n} + 2^{-n}` and overshoots:
  `f ≤_ℝ g` at `n+2` gives `a_{n+3} −ℚ b_{n+3} <ℚ 2^{-(n+2)}`, `g =_ℝ 0` at `n+2` gives
  `b_{n+3} <ℚ 2^{-(n+2)}` (through `le_Q_self_abs`), so `a_{n+3} <ℚ 2^{-(n+1)}`; and
  `cauchyfy_two_step` moves back from `n+3` to `n+1` for another `2^{-(n+1)}`.

Both bounds are then folded into `|a_{n+1}| <ℚ 2^{-n}` by `abs_Q_lt_of_two_sided`. Unlike
`eq_R_trans` this needs no telescoping induction — the shift is a fixed two steps.

`eqAtType_trans_base` (`BaseEquality.lean`) still has to supply `0_ℝ ≤_ℝ d(x,z)` from the
pseudometric axioms; `nonneg_of_add_self_nonneg` below is the ℝ-side half of that, and
`dist_nonneg` is the assembly.

## `le_zero_eq_zero_R`

The repaired form of the old (false) `le_zero_eq_zero_R`; see `le_zero_eq_zero_R_core` for
the counterexample to the version without `0_ℝ ≤_ℝ f`, and for the estimate.

## `nonneg_of_add_self_gen`

The sum is fed in through an abstract `u` rather than rewritten inside the goal, for the same
reason `add_eq_zero_R_gen` does it: `prw` at a goal containing `Term.add_R` has to push a
substitution through that constant, and that is the delta-expansion blow-up CLAUDE.md's
build-cost section warns about.

The argument, contrapositively — `le_R` on both sides is a negated `∃`, so a witness `n`
against `0_ℝ ≤_ℝ f` has to be turned into a witness against `0_ℝ ≤_ℝ u`, and the *same* index
works. Writing `c := −ℚ f̂(n+1)`, `b := −ℚ f̂(n+2)`:

    2^{-n} ≤ℚ c                              -- the given witness at n
    c <ℚ 2^{-(n+2)} +ℚ b                      -- one `cauchyfy` step, |c −ℚ b| = |f̂(n+1) −ℚ f̂(n+2)|
    2^{-n} <ℚ 2^{-(n+1)} +ℚ b                 -- and 2^{-(n+2)} ≤ℚ 2^{-(n+1)}
    2^{-(n+1)} <ℚ b                           -- cancel, since 2^{-n} =ℚ 2^{-(n+1)} +ℚ 2^{-(n+1)}
    2^{-n} <ℚ b +ℚ b                          -- double

and `b +ℚ b` is `−ℚ û(n+1)`. Note the margin: the Cauchy step costs `2^{-(n+2)}` where a whole
`2^{-(n+1)}` is available, so this is not a tight estimate and needs no telescoping.

## `nonneg_of_add_self_nonneg_core`

This is the ℝ-side half of the non-negativity of a pseudo-metric: with `ax_refl`, `ax_sym` and
`ax_triangle` one gets `0 =_ℝ d(x,x) ≤_ℝ d(x,y) +_ℝ d(y,x) =_ℝ d(x,y) +_ℝ d(x,y)`, and this
lemma converts that into `0_ℝ ≤_ℝ d(x,y)` — the hypothesis `le_zero_eq_zero_R` needs and whose
absence made the old statement of that lemma false.

## `nonneg_R_of_double_bound`

This packages `le_R_of_bound`, the two `Term.weaken` computations, the
`cauchyfy_zero_R` / `cauchyfy_add_R` rewrites and `nonneg_of_add_self_nonneg_core`, so that a
caller never has to see `f +_ℝ f` at all — which matters, because pushing a substitution
through `Term.add_R` is the delta-expansion blow-up the build-cost notes warn about.

`dist_nonneg` (`BaseEquality.lean`) is the one consumer, and the doubling is not an artefact:
the triangle inequality at `(x, y, x)` bounds `0` by `d(x,y) + d(y,x)`, which symmetry turns
into `2·d(x,y)` and nothing smaller.

## From Kohlenbach, *Applied Proof Theory*, §4.1 (section comment)

Note the book's own calibration of effort: it calls the ℚ ordered-field
package "easily verified" (p. 79) — that is the ~4,600 lines of
`RationalNumbers.lean` — and asserts the ℝ package in one parenthesis
(p. 80) with no proof at all.

## `approx_R_core`

This is the workhorse for the tightness estimates that block Class C — it is what
lets a proof move between a real and a rational approximation of it at a chosen
index, which is exactly what the five-term split needs.

**The shape of the proof, and the two things about it that are easy to get wrong.** The
goal reduces
to `∃n. 2^{-k} −ℚ |f̂(n+2) −ℚ f̂(k)| ≥ℚ 2^{-n}`, and the crude telescoping bound falls
short by a factor of 4 *at every `n`*. The witness must depend on `f` through the
Cauchy slack at index `k` — `d := 2^{-(k+1)} −ℚ |f̂(k) −ℚ f̂(k+1)|`, positive for every
`f` because `cauchyState_cauchy` is strict — and `pow2neg_rat_den_le` is the
Archimedean step. Two points the obvious plan gets wrong:

* the witness is **`n := k +ℕ rat_den d`**, not `max(k, rat_den d)` — the sum
  dominates both (`pow2neg_Q_le_add_r`), so no object-level `max` lemmas and no case
  split are needed;
* the "refined telescope keeping the `k`-th step's slack out of the sum" needs nothing
  new — it is exactly `cauchyfy_tele_at` at `p = k+1`: the carried
  slack `2^{-((k+1)+(D+1))}` lands, after the index identity
  `(k+1)+(D+1) =₀ n+2`, on precisely the `2^{-(n+2)}` piece of the split
  `2^{-n} = 2^{-(n+2)} + (2^{-(n+1)} + 2^{-(n+2)})`, and the remaining
  `2^{-(n+1)} + 2^{-(n+2)} ≤ 2^{-n} ≤ 2^{-D} ≤ d` is what the witness buys.

## `abs_R_bound` (docstring)

This is the majorization fact `mul_R`'s operand bound silently relies on — a code
dominates the magnitude it encodes. It is Kohlenbach's lemma, not an invention of
this development, and `mul_R` should not be "fixed" to avoid it.
