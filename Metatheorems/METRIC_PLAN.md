# Scoping the metric-space layer

Written 2026-09-01, from `Metateorema-New3/particular-cases-metric-spaces.tex` (130 lines),
Kohlenbach §4.2 and Lemma 17.80, and an audit of `MetricSpaces.lean` (153 lines, 3 sorries,
not in the build).

## 1. The headline: the metric-space chapter is about *majorizability*, not the ordered field

The chapter's entire content is:

1. **Definition** of metric majorizability `≽ᵃ`, relative to a reference point `a : X`:
   - `x ≽ᵃ₀ y :≡ x ≥₀ y`
   - `x ≽ᵃ_X y :≡ (x)ℝ ≥ℝ d_X(a, y)`
   - `x ≽ᵃ_{ρ→τ} y :≡ ∀z',z (z' ≽ᵃ_ρ z → x z' ≽ᵃ_τ y z) ∧ ∀z',z (z' ≽ᵃ_ρ̂ z → x z' ≽ᵃ_τ̂ x z)`
2. **Lemma 17.80** — the characterisation at `ρ₁→…→ρₖ→τ`. Note the document's `\solution{}` for
   it is **empty**: unproved even on paper.
3. **Proposition** — `≽ᵃ` is an abstract majorizability. This is the bulk: the two structural
   conditions, then every constant majorizable — `0`, `S`, `Π`, `Σ` (self-majorising, via
   Lemma 17.80), `R` (by induction on `n`), `0_X`, and `d_X`.
4. **Theorem** — the metric metatheorem, by applying the general metatheorem to the above.

**Consequence: most of `RealNumbers.lean` is not on the critical path.** The ordered-field
package is what makes ℝ *an ordered field*; the metric-space metatheorem does not consume it.

## 2. What the metric layer actually needs from ℝ

**Needed (5 items):**

| what | for | status |
|---|---|---|
| `eq_R_trans` | `admissibleEqX.eqx_sym`/`eqx_trans` | ✗ Class C |
| `add_eq_zero_R` | `eqx_trans` (with `ax_triangle`) | ✗ Class C |
| `le_zero_eq_zero_R` | `eqx_trans` | ✗ Class C |
| rounding theory for `(·)∘` — `(n)ℝ ≥ℝ (x)∘ ↔ n ≤ x`, `x ≤ y → (x)∘ ≼₁ (y)∘` (Kohlenbach Lem. 17.8) | the `d_X` and `0_X` majorants, and the `X`-clause of `≽ᵃ` | ✗ `round_nat` is defined, **zero lemmas** |
| `abs_R_bound` (p. 430) | bounding a majorant | ✗ stated, sorried |

`eq_R_refl` and `eq_R_sym` are proved; `substF_nat` and `eqx_pu` in `MetricSpaces.lean` are
proved. Note `eqx_refl` needs the *premise* `ax_refl`, not `eq_R_refl` — the names mislead.

**NOT needed (14 of the 18 `RealNumbers.lean` sorries):** `add_comm_R`, `add_assoc_R`,
`add_zero_R`, `add_neg_R`, `mul_comm_R`, `mul_assoc_R`, `mul_one_R`, `distrib_R`,
`lt_trans_R`, `lt_add_R`, `lt_mul_pos_R`, `archimedean_R`, `approx_R`, `cauchy_complete_R`.

They are worth having — they are Kohlenbach's p. 80 assertion, and any *mined proof* that
does real arithmetic will want them — but they do not gate the metatheorem.

## 3. The bulk of the work: the majorizability instance, and it is untouched

`general_metatheorem` takes `Majorizability si` = `MajorizabilityRel` (`maj`, `maj_le`,
`maj_app`) **+ `majorizer` + `majorizer_maj`**, i.e. a *total* majorising function on all
semantic values.

Good news: **`bezemRel si base` already builds a `MajorizabilityRel` from a base-type relation**
(`StrongMajorizability.lean`). So for the metric case, setting

```
base () n x  :≡  (n : ℝ) ≥ℝ d(a, x)
```

gives `maj`, `maj_le`, `maj_app` **for free**. That is three of the five fields.

What remains is `majorizer` / `majorizer_maj`:
- at `nat`: identity;
- at `base ()`: `x ↦ ⌈d(a,x)⌉` — this is where the rounding theory of §2 is consumed;
- at `ρ →ₜ τ`: the Bezem construction, and this is the hard one — a *total* majoriser for an
  arbitrary set-theoretic function is a genuinely stronger demand than majorising the
  interpretation of a closed term.

## 4. A possible mismatch to resolve before building

The document proves **abstract majorizability** — the two structural conditions plus
*each constant* majorizable — which in Lean is `AbstractMajorizability` in
`Majorizability.lean`, feeding `all_closed_terms_majorizable`.

But `general_metatheorem` does **not** take `AbstractMajorizability`. It takes
`Majorizability`, with a total `majorizer`. Grep confirms `AbstractMajorizability` appears
nowhere on the metatheorem path except in one comment.

So the document's route (per-constant majorizability → all closed terms majorizable) and the
formalization's route on `main` (a total majoriser) are **not the same route**.

### This is already solved on `syntactic-witnesses` — and it is *why that branch exists*

Recorded here because the scoping above rediscovered it the long way round. CLAUDE.md's
Branches section says it plainly: the branch makes Dialectica witness/counter *types*
object-level `Ty ι`, "so realizers are `Term`s and can be majorized by
`all_closed_terms_majorizable`". That is exactly the per-constant route the document takes.

The branch carries `Metatheorems/SyntacticMetatheorem.lean` with

```lean
theorem syntactic_general_metatheorem (eqxi) (spremise) (am : AbstractMajorizability si) …
```

whose own docstring reads: *"the `U_star`/`V_star` that `metatheorem_core_of_majorants` asks
for are produced by `all_closed_terms_majorizable`, because the extracted functionals are
closed terms. Compare `general_metatheorem`, which had to assume a total majorizer on every
semantic value."*

**Verified 2026-09-01:** `SyntacticMetatheorem.lean` and `Dialectica/Syntactic.lean` have
**zero sorries**; the branch merges into current `main` with one conflict (the import list)
and builds green at 8063 jobs with `mct_p1`/`mct_p2`/ℚ unregressed.

So the metric-space work should target `syntactic_general_metatheorem` +
`AbstractMajorizability`, not `general_metatheorem` + `Majorizability`. §3's hard part — a
total majoriser for arbitrary set-theoretic functions at arrow types — **disappears**; what
replaces it is the document's own per-constant obligations (`0`, `S`, `Π`, `Σ`, `R`, `0_X`,
`d_X`), which is what §1's Proposition actually proves.

## 5. Suggested order

1. **Merge `syntactic-witnesses`** (§4). It is the prerequisite, it is proved, and the merge is
   measured. It also brings products to `Ty`, which independently allows deleting ℚ's Cantor
   pairing layer (`triag` 289 uses, `inv_triag` 207, `pair` 176, `fst_pair` 134, `snd_pair`
   108) — a second payoff, and a separate optional job.
2. **Rounding theory for `(·)∘`** — `round_nat` exists with no lemmas; it is needed by the
   `X`-clause of `≽ᵃ`, by `0_X`, and by `d_X`, and nothing else is blocked on ℝ's field
   structure.
3. **The metric `base` relation + `bezemRel`**, giving `MajorizabilityRel` immediately.
4. **The per-constant obligations** — `0`, `S`, `Π`, `Σ` self-majorising via Lemma 17.80, `R`
   by induction, `0_X`, `d_X`. This is §1's Proposition, transcribed. Note Lemma 17.80 is
   `\solution{}`-empty in the document, so it must be proved, not transcribed.
5. **The three `admissibleEqX` sorries**, needing the three Class C real facts — the only place
   the ℝ obstruction actually bites, and it can proceed in parallel with 2–4.

## 6. What this says about the last two days

The ℝ work (18 sorries, two agent runs) was aimed at the ordered-field package. Per §2 that is
**not** what the metric-space metatheorem consumes. The genuinely needed ℝ facts are three
Class C statements plus a rounding theory that nobody has started. The ℚ layer and the
`cauchyfy` layer were prerequisites for those too, so none of it is wasted — but the target
should move.
