# BaseEquality.lean

## module header

That is the one genuine stratification the `Term.dist` design forces, and this file is where
it is discharged:

* `Arithmetic.lean` proves `eqAtType_sym`/`eqAtType_trans` for **eq-base-free** types (an
  `autoParam` on `Ty.eqBaseFree`, so the ~164 ℚ/ℝ call sites are unchanged);
* this file proves the **base** cases, which is everything the earlier ones exclude;
* nothing in between needs them.

See ARCHITECTURE.md §1 and §8.

## `eqAtType_sym_base`

Nothing beyond the two already-proved `=ℝ` facts is needed — in particular none of the open
ordered-field axioms.

## `dist_nonneg`

What costs work is that `≤ℝ` and `=ℝ` are *tight*
Π₁⁰ statements about `cauchyfy` codes, so the three ingredients must be read at indices far
enough out that the estimate still fits inside `2^{-n}` after the doubling.

The budget, with `Pₖ := 2^{-(n+k)}`, `D̂ₖ := ĉ(d(s,u))(n+k)`, `Êₖ`, `Ŝₖ` likewise for
`d(u,s)` and `d(s,s)`:

* `dist_tri` at `n+3` gives `Ŝ₄ −ℚ (D̂₅ +ℚ Ê₅) <ℚ P₃`, and `dist_self` at `n+3` gives
  `−ℚ Ŝ₄ <ℚ P₃`; together `−ℚ(D̂₅ +ℚ Ê₅) <ℚ P₂`;
* `dist_comm` at `n+4` gives `Ê₅ −ℚ D̂₅ <ℚ P₄`; adding, `−D̂₅ −ℚ D̂₅ <ℚ P₂ +ℚ P₄`;
* moving back from index `n+5` to `n+2` costs `P₂` (`cauchyfy_two_step`) plus `P₅ ≤ P₄`
  (`cauchyfy_cauchy`), i.e. the *same* bound `B := P₂ +ℚ P₄`, twice after doubling.

Total `3B`, and `pow2neg_triple_bound` is exactly the fact that `3B ≤ℚ 2^{-n}` — with
`2^{-(n+4)}` to spare. It is the sole reason index `n+3` is where the triangle inequality is
read: at `n+2` the same accounting overshoots by `2^{-(n+3)}`.

`MetricModel` will want this too, so it is factored out rather than inlined into
`eqAtType_trans_base`.

## `eqAtType_trans_base`

* `le_zero_eq_zero_R_core` closes it — and its first conjunct, non-negativity, is the
  hypothesis whose absence once made that lemma false. `dist_nonneg` supplies it.

With `eqAtType_refl_base` and `eqAtType_sym_base` this completes the proof that base-type
equality is an equivalence relation — the three fields the deleted `AdmissibleEqX` used to
assume.

## `dist_tri_chain`

The project's first *derived* object-level theorem about a space — everything else said about
metric, W-hyperbolic, CAT(0) or normed spaces so far is either an axiom, a model fact, or a
statement about the encoding itself.

Chaining two triangle inequalities was **impossible before that package existed**: `dist_tri`
delivers its conclusion as `le_R_pu`, and the `≤_ℝ` API was conversions only — no `le_R_trans`,
no monotonicity. That is why this file, and the four space files above it, previously derived
nothing at all.

## `dist_rev_tri`

`Derivable.dist_tri` at `(x,y,z)` gives `d(x,z) ≤ℝ d(x,y) +ℝ d(y,z)`; moving `d(y,z)` to
the left is `le_sub_R_of_le_add_core` (`RealNumbers/LeOrder.lean`), whose section comment
records the accounting: as a *direct* estimate the statement is tight — every finite reading
index overshoots `2^{-n}` — but it is derived instead from right monotonicity and the
cancellation `(g +ℝ h) +ℝ (−ℝ h) ≤ℝ g`, so the only telescope it spends is the one inside
`le_R_trans_core`.
