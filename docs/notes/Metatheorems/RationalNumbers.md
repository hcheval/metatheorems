# RationalNumbers.lean

## the `realTy` comment (before the first `variable`)

`realTy` moved to `TypeSystem.lean` — `Term.dist` mentions it, and `Term` is below here.

## Sections 1-8: term definitions — MOVED to Metatheorems/Terms/Rational.lean

The `Term`-level ℚ encoding now lives below `eqAtType` and `Derivable` in the import
order, because `eqAtType` at a base type is `eq_R (dist i s t) 0ℝ` and so depends on it.
Only the definitions moved; every proof about them, including the `closed_subst`
lemmas below, stays here. See ARCHITECTURE.md.

## Closed term substitution lemmas — MOVED

The whole `ClosedSubst` section now lives in `Metatheorems/Terms/ClosedSubst.lean`, below
`eqAtType` in the import order. It had to move because `eqAtType` at a base type is
`eq_R (dist i s t) 0ℝ`, so `eqAtType_substF`'s base case is `eq_R_substF` — and that is
proved in `Arithmetic.lean`, which sits below this file. Nothing was restated: the same
declarations, verbatim, at a lower point. They reach here through the import chain, so
every use below is unchanged. See ARCHITECTURE.md §7.

## Section 9: Rational Ordered Field Axioms (as Derivable terms)

These are number-theoretic facts provable in WE-HA^ω from the primitive
arithmetic operations (rec, succ, etc.) and the rational encoding.

## Congruence helpers (outside section to avoid Γ capture)

`mul_congr_l` / `mul_congr_r` now live in `Arithmetic.lean` (non-private); the local
duplicates that used to sit here were removed to avoid the name clash.

## after `sg_bar_zero_implies_ne`-style helpers (comment before `sg_bar_eq_S0_implies_zero`)

Distributivity of ∧ over ∨ (`and_or_dist`) now lives in `PropositionalLemmas`.

## comment before `dw_subst0`

`add_cancel_r` (right additive cancellation) is a ℕ fact and now lives in `Arithmetic.lean`,
next to the `monus_cancel` it is proved from.

## Implication-form congruences (section comment)

The kernel has no deduction theorem, so a congruence that has to be applied *under* a
hypothesis cannot be got from the closed version. These say `s =₀ t →ᶠ r[s] =₀ r[t]` for
each context `r` the `add_Q` congruence proof needs, so that a hypothesis-carrying equation
composes with them by plain `.syllogism`.

## forward references (comments before `add_Q_zero`, `mul_Q_one`, the `eq_Q` elimination block, `neg_Q_zero_Q`)

`add_Q_assoc` needs the signed-numerator machinery, so it is proved further down, in the
"Associativity" block after `addQ_signed`.

`mul_Q_assoc` needs the signed-numerator machinery, so it is proved further down, in the
"Signed parts of a product" block.

`distrib_Q` needs the signed-numerator machinery and `eq_Q_of_signed_cross`, so it is
proved at the end of the file, in the "Distributivity" block.

`lt_Q_trans`, `lt_Q_trichotomy`, `lt_Q_add` and `lt_Q_mul_pos` all need the additive-group
laws and the signed-numerator machinery, so they are proved further down, in the "Order"
block after `neg_Q_add_Q`.

## `eq_Q` elimination (section comment)

`eq_Q_from_components` builds an `eq_Q` out of its two halves. These go the other way:
they take one apart. The two consequences that matter downstream are that "the numerator
vanishes" is an `eq_Q`-invariant, and that once the numerators are nonzero the sign bits
have to agree — the argument the sign half of `mul_Q_right_congr` makes inline.

## `add_Q` component lemmas (section comment)

The `body`/`body_eq`/`nf`/`lam2_correct_nf` unfolding is rebuilt inline sixteen times in
this file, once per proof that needs it. These name it once for `add_Q`, the way
`mul_Q_body`/`mul_Q_unfold`/`rat_*_mul_Q` below do for `mul_Q`.

`add_Q` is the harder of the two: both its numerator and its sign are `ite_nat`s over the
"do the two arguments have the same sign bit" test, so the components are *conditional*.
The unconditional lemmas below state them with the `ite_nat` still in place; the four
`addQ_num_*`/`addQ_sign_*` lemmas discharge it once the test's value is known.

## Signed numerators (section comment)

The encoding stores a magnitude and a sign bit, which makes addition a three-way case
analysis and associativity a nightmare of nested comparisons. Splitting the numerator into
a *positive part* and a *negative part* removes the cases: a rational's value is
`(posN − negN) / den`, addition adds the parts componentwise, and componentwise addition of
pairs of naturals is associative for free.

Nothing below ever subtracts. `u` and `v` have the same value exactly when
`posN u · den v + negN v · den u =₀ posN v · den u + negN u · den v`, and that is an
identity in `+` and `·` alone.

## `add_Q` under `eq_Q` in the second argument (section comment)

The pieces of `add_Q_right_congr`. Everything is stated at the level of the components, so
that the final assembly is just `eq_Q_from_components`.

Write `P = na·dc`, `Q = nc·da` for the two cross products of `add_Q a c`, and `P' = na·dd`,
`Q' = nd·da` for those of `add_Q a d`. The two identities `P·dd =₀ P'·dc` and
`Q·dd =₀ Q'·dc` are what `eq_Q c d` buys, and everything below is those two pushed through
whichever branch of `add_Q` is live.

## `abs_Q`, and `eq_Q`-congruence for the order relations (section comment)

Everything above this line is what the ℚ layer needed for its own sake. What follows is
what the *real* layer needs and ℚ did not: `abs_Q` had no lemmas at all (`eq_R` is stated
through `|·|_ℚ`), and neither `<_ℚ` nor `≤_ℚ` had a congruence rule under `eq_Q` — the
order proofs above all went through `lt_Q_of_eq_Q_diff` on the *difference*, which is not
the shape a real-number proof arrives in.

## The `≤_ℚ` toolkit (section comment)

`le_Q` had only `le_Q_refl`, `le_Q_cases`, `le_Q_of_sign`/`le_Q_of_num_zero` and the
`eq_Q`-congruence. Everything below mirrors the `<_ℚ` development one lemma at a time:
positivity in terms of the signed parts, the additive facts, transitivity. The one place
the mirror is *not* mechanical is `addQ_negN_zero` — for `<_ℚ` the corresponding step is
buried inside `lt_Q_zero_add`, and it is factored out here because the mixed `<`/`≤`
addition lemma needs exactly that half of it and none of the rest.

## ℕ order in `monus` form (section comment)

`a ≤ b` at ℕ is `a ∸ b =₀ 0`. `Arithmetic.lean` has the `monus` calculus but no order
*relation* facts — no transitivity, no monotonicity. By subject these four belong there;
they are here because `Arithmetic.lean` sits below `ProofMode` in the import graph and
these are a few lines in proof mode against a page each in Hilbert style.

Note the shape of the two `_aux` lemmas: the reasoning is done over *fresh* variables and
instantiated afterwards. A rewrite hits every occurrence of its pattern, so rewriting `b`
by `(b ∸ a) + a` in a goal that also mentions `c ∸ b` corrupts the other occurrence. Stating
the step generically, where the five terms are opaque, is what makes the rewrites safe.

## Additions for the real-number layer (Class C) (section comment)

Everything below was forced by `eq_R_trans`. The two that are not bookkeeping are
`eq_Q_imp_le_Q` — the middle case of `lt_Q_trichotomy`, without which the trichotomy
cannot be used to *prove* a `≤_ℚ` — and `pow2neg_Q_le_add`, the dyadic monotonicity
that turns `pow2neg_rat_den_le`'s index into a usable one.
