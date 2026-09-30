# RealNumbers/Field.lean

## Additive group (section comment)

`add_comm_R` is PROVED, further down the file, next to `add_zero_R`: it uses `canorm`,
which is defined below (it folds in the `cauchyfy`-state simp lemmas).

`add_assoc_R` and `add_zero_R` are PROVED, but further down the file: both rest on
`cauchyfy_cauchy` / `cauchyfy_two_step`, which are stated after the order axioms. See
"The additive axioms `cauchyfy_cauchy` alone settles" below.

`add_neg_R` is PROVED, further down: it needs `cauchyfy_neg`, which is an induction on
the `cauchyfy` recursion and so sits with the rest of that theory.

## The additive axioms `cauchyfy_cauchy` alone settles (section comment)

`add_zero_R` and `add_assoc_R` are **not tight**, and that is the whole story: the two
sides of each are the *same* sum read at indices that differ by a fixed number of
`cauchyfy` steps, each step costing `2^{-(index+1)}`, against a budget of `2^{-n}` at the
goal's own index `n`. Both close with room to spare, so neither needs the `eqR_le`
telescoping engine that `eq_R_trans` needed. (`add_neg_R` is a different matter — see the
note at its `sorry`.)

Each goes through a `_gen` companion taking the composed real as an **abstract Lean
parameter**, for the reason `add_eq_zero_R_gen` does: `prw` at a goal containing
`Term.add_R` has to push a substitution through that constant, which is the
delta-expansion blow-up the build-cost notes warn about. As a parameter it costs nothing,
and the `cauchyfy_add_R` chain that computes it is assembled outside the proof mode.

## `add_comm_R_gen`

**There is no estimate here at all, and no `cauchyfy` congruence either.** REALS_PLAN §0.2
declared `add_comm_R` blocked on an `eq_Q`-level congruence for `cauchyfy` — pointwise
`f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n` — on the ground that `add_Q` does not commute on the nose. That
diagnosis is right about ℚ and wrong about where the outer `cauchyfy` sits: `add_R f g` is
*provably Cauchy* (`add_R_check`), so `cauchyfy_add_R` evaluates that cauchyfication on
**both** sides before the two are ever compared. What is left is
`|(A +ℚ B) −ℚ (B +ℚ A)| <ℚ 2^{-n}`, and `add_Q_comm_inst` makes the difference `eq_Q`-zero.

The general congruence is still needed — by `mul_comm_R`, where no `mul_R_check` exists — but
not by this.

## `le_R_all`

The conclusion is stated as a `∀`-formula rather than at a caller-supplied index so that it
can be `pinst`-antiated *after* a `pforall`; instantiating is what lets `closed_subst` clear
the proof mode's weakening of `Term.zero_R`, which a direct `papplym` at the weakened
hypothesis cannot do.

Note the argument order: this is `le_R f g`, i.e. `f ≤ g`, and `le_R_pu f g` means the same
thing. (It once meant `g ≤_ℝ f`; `le_R_of_le_R_pu` / `le_R_pu_of_le_R` above convert between
the two spellings in either direction.)

## ℚ rearrangements the ℝ estimates need (section comment)

Four abelian-group identities and one `pow2neg` bound. They are ℚ facts, but they live
here rather than in `RationalNumbers.lean` for the reason stated above: that file is
another workstream's, and these exist only to serve `dist_nonneg`.
