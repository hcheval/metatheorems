# RealNumbers/Defs.lean

## Sections 1-2: term definitions and the ℝ formulas — MOVED

`Term.cauchy_check_at`, `cauchyfy`, `zero_R`, `one_R`, `embed_nat_R`, `neg_R`, `add_R`,
`sub_R`, `mul_R`, `abs_R`, `round_nat`, and the formulas `eq_R`, `lt_R`, `le_R`,
`le_R_pu` now live in `Metatheorems/Terms/Real.lean`.

This is the file the layering exists for: `eqAtType` at a base type is
`eq_R (dist i s t) 0ℝ`, so `eqAtType` must see `eq_R`. Only definitions moved; every
proof — the `closed_subst` lemmas, the `cauchyfy` theory, the ordered-field axioms —
stays here. See ARCHITECTURE.md.

## Closed term substitution lemmas (real-level)

`cauchyfy_closed_subst`, `zero_R_closed_subst` and `one_R_closed_subst` MOVED to
`Metatheorems/Terms/ClosedSubst.lean` (below `eqAtType`), together with the ℚ block they
rest on and with `eq_R_substF` / `le_R_pu_substF`. See that file and ARCHITECTURE.md §7.

## Key Properties

`eq_R_isPurelyUniversal`, `eq_R_substF`, `le_R_pu_isPurelyUniversal` and
`le_R_pu_substF` MOVED to `Metatheorems/Terms/ClosedSubst.lean`: `eqAtType`'s base case is
`eq_R`, so `eqAtType_substF` (in `Arithmetic.lean`) needs `eq_R_substF` below it.

`le_R` is Π₁⁰ (purely universal after unfolding ¬∃ to ∀¬).
Note: le_R unfolds to (∃n. body) → ⊥, which is NOT syntactically purely
universal in our formula representation. For metric space axioms that need
purely universal premises, we would need to reformulate le_R as
∀n. ¬(body) = ∀n. (body → ⊥). This is logically equivalent but
syntactically different. See le_R_unfolded below.

## Ordered Ring Axioms (Derivable in WE-HA^ω)

This header said "ordered field" until 2026-09-08, and that was false: there is no
multiplicative inverse anywhere in the ℚ or ℝ towers. No `inv_Q`/`div_Q`/`inv_R`/`div_R`,
no reciprocal term, and no derived `x ≠ 0 → ∃y (x ·ℝ y =ℝ 1ℝ)`.

The gap is in what is FORMALIZED, not in what is REPRESENTABLE, and the difference matters
because this layer is full of fractions. `rat_encode` is sign/numerator/denominator, so
every rational has a code, reciprocals included; `pow2neg_Q n = pair(2, exp2 n - 1)` is
literally the code of 1/2^n. The dyadic constants below — the Cauchy moduli `2^{-n}`, and
MCT's rungs `q_j = j ·ℚ 2^{-(k+1)}` — are constants and products of constants, never
quotients. What is missing is the operation and the axiom, not the power to state them.

Nothing downstream needs either: the space axioms use only +, ·, |·|, ≤ℝ and =ℝ.
