# RealNumbers/MCTLemmas.lean

## module header

### Why there is no `import Metatheorems.ProofMode.Arith` (first `/-! … -/` block)

That module declares the *global*
notations `S`, `+ᵗ`, `∸ᵗ`, `*ᵗ`, `pdᵗ`; importing it from a module below the `RealNumbers`
umbrella leaks them into every importer of the umbrella, and `MetricSpaces.lean` uses `S` as
an identifier — the build then fails there with "unexpected token 'S'", a long way from the
cause.

### Design rules, and where the plan (`docs/REAL_MCT.md` §5) was revised

* **Everything with a rational side condition is an object implication.** There is no
  derivation-weakening combinator (`Derivable … A` in `Γ` does not give one in `ρ :: Γ`), so a
  lemma whose ℚ hypothesis arises *inside* a sequent — under the `∀n` of `le_R_of_all`, or in
  the bad branch of the dichotomy — cannot take it as a Lean-level argument. `const_R_mono`,
  `const_R_le_add`, `const_R_le_sub`, `zero_lt_const_R` and `const_le_R_of_sample` are all
  `… →ᶠ …`, and Lean-level uses go through `Derivable.mp`.
* **`≤` where the plan said `=`.** `const_R_add`/`const_R_sub`/`const_R_congr` were listed as
  `=ℝ` facts; the descent only ever needs one direction, and the `≤` versions are slack-free
  index-wise (`cauchyfy_const`, `cauchyfy_add_R`/`cauchyfy_sub_R`, then `p −ℚ q ≤ℚ 0 <ℚ 2^{-n}`).
  No `=ℝ` engine is touched.
* **`≤` where the plan said `<`.** `le_add_of_abs_sub_lt` became `le_add_of_abs_sub_le`,
  because `approx_le_R_core` already delivers `|f −ℝ ⟨f̂(n)⟩| ≤ℝ ⟨2^{-n}⟩` and the `≤` form is
  what chains; `approx_R`'s strict form is never used.
* **Algebra, not estimates.** `add_sub_cancel_le_R_core`, `le_add_sub_R`,
  `le_add_neg_cancel_R`, `le_R_add_cancel_r_core`, `sub_R_nonneg_of_le` are Lean-level chains
  of `le_R_of_eq_R_core` over the ring identities and the two monotonicity lemmas, exactly as
  `add_neg_cancel_le_R_core` is written. As the reverse-triangle note in CLAUDE.md predicts,
  each is tight as a direct estimate and free as algebra.
* **Transport along ℕ-equalities.** The antitone chain rewrites `a (m + S i)` to
  `a (S (m + i))` *inside* a `le_R`, which `prw` cannot do (the goal is not an equation).
  `le_R_app_congr_l` does it once: unpack the `¬∃`, and `prwby` the equation inside the
  quantifier-free witness. This lemma is the one genuinely new shape here.

## `Formula.weakenBy` through the formula shapes a script `pexact`s (section comment)

`pm_allI` wraps every hypothesis in `Formula.weakenBy`. For a `∀`-hypothesis that wrapper
is what `pspecialize`/`pinst` match on, so it is left alone; for a quantifier-free
hypothesis, or a `le_R`, it must become the *syntactic* weakening of the leaves, or the
final `pexact` unfolds a closed constant under a rename (the trap that killed the first
version of `const_R_mono`).
