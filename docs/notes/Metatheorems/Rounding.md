# Rounding.lean

## module header

He flags the domain himself — *"[0,∞) refers to the 'real' space of all positive reals, i.e.
not to the sets of representatives"*. Leuştean (§4, eq. 4.4) says it in so many words: *"we
need a semantic operator which for any real number `x ∈ [0,∞)` selects out of all the
representatives `f : ℕ → ℕ` of `x` a unique representative `(x)◦`"*.

So this file lives on the Lean side of the interpretation and uses Mathlib's `ℝ`. There is
deliberately **no** `Term F Γ (realTy ι →ₜ Ty.nat)`; that would be the wrong type and the
wrong side. Contrast `Term.round_nat` in `RealNumbers.lean`, which is `(·)◦` *restricted to
ℕ* (Kohlenbach p. 430: `(x⁰)◦(n) = j(x·2^{n+2}, 2^{n+1} − 1)`) and is therefore an
object-level term, correctly.

Why this matters for scoping: because the domain is Mathlib's `ℝ`, the parts of Lemma 17.8
that the majorants consume are provable **without** any of `RealNumbers.lean`'s open
ordered-field goals. See `METRIC_PLAN.md` §2 and §2.5.

Part (i) is **not** here, on purpose; see the note at the bottom of the file
(`## What is deliberately not here (closing section)`, below).

## `roundR_natCast`

This is what lets the metric majorant `λn₁⁰n₂⁰.(n₁+n₂)∘` be evaluated to a literal
at a given precision index (`MetricModel.constMajorants` in `MetricSpaces.lean`), even though
`roundR` itself is `noncomputable` on account of taking a Mathlib real.

## What is deliberately not here (closing section)

**Part (1)** — "`(x)◦` is a representative of `x`", i.e. `(x)◦` satisfies the Cauchy condition
(4.2) and `((x)◦)^b =₁ (x)◦`. The **first half is now proved, in `QVal.lean`**: that file
defines `qval : ℕ → ℚ`, the missing Lean-level "meaning of a rational code", and proves
`roundR_cauchy` (`|(x)◦(n) − (x)◦(n+1)| < 2^{-(n+1)}`) together with
`qval_roundR_dist_le` and `roundR_tendsto`. It is stated at the level of actual rationals;
relating it to the *object-level* decision term `Term.lt_Q_dec` under `Term.interpret` is
still open, as is the `((x)◦)^b =₁ (x)◦` half, which needs `cauchyfy`.

**Part (4)** used to be excluded too, blocked on the one-clause `bezemMaj`, which lacked the
self-majorization conjunct — at type `1 = ℕ → ℕ` that conjunct is exactly what distinguishes
`s-maj₁` from `≤₁`. Widening `bezemMaj` to two clauses removed the blocker; part (4) is
`roundR_maj_pair` above.
