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
| Lemma 17.8 for `(·)◦` — see the note below | the `d_X` and `0_X` majorants, and the `X`-clause of `≽ᵃ` | 🔶 **parts (2),(3),(5),(6) proved** in `Rounding.lean` 2026-09-02, zero sorry. (1) is the ℝ↔code bridge, still open; (4) blocked on §2.5 |
| `abs_R_bound` (p. 430) | bounding a majorant | ✗ stated, sorried |

`eq_R_refl` and `eq_R_sym` are proved; `substF_nat` and `eqx_pu` in `MetricSpaces.lean` are
proved. Note `eqx_refl` needs the *premise* `ax_refl`, not `eq_R_refl` — the names mislead.

### `(·)◦` is SEMANTIC. Checked against the book 2026-09-02; get this right.

Kohlenbach **Definition 17.7**: for `x ∈ [0,∞)`, `(x)◦(n) := j(2k₀, 2^{n+1} − 1)` with
`k₀ := max{k : k/2^{n+1} ≤ x}`. He states the domain caveat himself — *"[0,∞) refers to the
'real' space of all positive reals, i.e. not to the sets of representatives"*. So `(·)◦` maps
an **actual real** to its canonical `ℕ^ℕ` representative. It is a Lean-level function, used to
*interpret* the constants in the model: `[dX]_M := λ x,y ∈ X.(d(x,y))◦` (p. 430). There is no
object-level `Term` for it and there should not be one — a `Term F Γ (realTy ι →ₜ Ty.nat)` is
the wrong type and the wrong side of the interpretation.

**But `Term.round_nat` is `(·)◦` restricted to ℕ, and is correct as written.** At p. 430
Kohlenbach writes `(·)◦ : ℕ → ℕ^ℕ` "here denotes the restriction", with
`(x⁰)◦(n) = j(x·2^{n+2}, 2^{n+1} − 1)` — exactly `round_nat`'s body. (For `x ∈ ℕ`,
`k₀ = x·2^{n+1}`, so `2k₀ = x·2^{n+2}`.) The restriction *is* the embedding `ℕ → ℝ`; calling it
either name is right, and the section header in `RealNumbers.lean` is not a mislabelling.

A second source (Leuştean, *Logical metatheorems*, §4, eq. 4.4 and Lemma 4.0.6) states the
point in so many words: *"we need a **semantic operator** which for any real number
`x ∈ [0,∞)` selects out of all the representatives `f : ℕ → ℕ` of `x` a unique representative
`(x)◦`"*. Same definition, same numbering, cited as [95, Lemma 17.8].

An earlier version of this file claimed `(·)◦` was "undefined, not merely unproved" because
`round_nat` had the wrong type. That was wrong on both counts, and wrong in the direction of
making the work look bigger. What is actually missing is **Lemma 17.8** (six parts:
representative, `≤`-monotone in both `≤R` and `≤₁`, pointwise monotone, `x ≤ y → (y)◦ s-maj₁ (x)◦`,
`x ∈ [0,b] → (x)◦ ≤₁ M(b)`, `M(b)` monotone) plus `M(b) := λn. j(b·2^{n+2}, 2^{n+1} − 1)`. Parts
2–6 are the ones the majorants consume; part 1 is where the ℝ layer is touched.

**Consequence for scoping, and it is favourable.** Because `(·)◦` takes a genuine
`x ∈ [0,∞)`, its domain is Lean's `ℝ` (mathlib), not the object-level encoded reals. So
Lemma 17.8 parts 2–6 — the parts the majorants actually consume — are statements about
mathlib reals and `ℕ → ℕ` functions, provable **without any of `RealNumbers.lean`'s 18
ordered-field sorries**. Only part 1 ("`(x)◦` is a representative of `x`") crosses between
mathlib `ℝ` and the object-level representation, and even that is a Lean lemma about
`Ty.interpret`-level data, not a `Derivable`. Treat this as a reading of the sources rather
than a measured claim until part 1 is actually attempted.

**`cauchyfy` is `f^b`** (Leuştean eq. 4.3): `f^b(n) := f(n)` if `∀k<n |f(k+1) −Q f(k)|Q <Q 2^{-k-1}`,
else `f(k)` for the least bad `k`. That is precisely the flag/value invariant `cauchy_inv`
proves, and `cauchyState_cauchy` is "`f^b` always satisfies (4.2)". Both are already done, so
the hat-construction side of the semantic bridge is not new work.

Also worth having when `[0,1]`-valued data appears (W-hyperbolic spaces): Kohlenbach Lemma
4.25 / Leuştean 4.0.7, the truncation `λ̃ := λn.j(2k₀, 2^{n+2} − 1)` onto `[0,1]`, with
`λ̃ ≤₁ M := λn.j(2^{n+3}, 2^{n+2} − 1)`. Not needed for plain metric spaces.

**NOT needed (14 of the 18 `RealNumbers.lean` sorries):** `add_comm_R`, `add_assoc_R`,
`add_zero_R`, `add_neg_R`, `mul_comm_R`, `mul_assoc_R`, `mul_one_R`, `distrib_R`,
`lt_trans_R`, `lt_add_R`, `lt_mul_pos_R`, `archimedean_R`, `approx_R`, `cauchy_complete_R`.

They are worth having — they are Kohlenbach's p. 80 assertion, and any *mined proof* that
does real arithmetic will want them — but they do not gate the metatheorem.

## 2.5 The blocker: `bezemMaj` is missing the self-majorization conjunct

Found 2026-09-02 while doing §5 step 3, which is exactly what that step was for.

> **Measured and fixed on branch `bezem-twoclause` (2026-09-02).** The widening works and
> `prec_maj` goes through. The cost, precisely:
>
> * `hatMaj` — the relation at hat types, indexed by `ρ` rather than by `ρ̂`. That indexing is
>   what makes the whole thing cast-free: `ρ̂.hat = ρ̂` is propositional, not definitional, so
>   writing the second conjunct literally as `bezemMaj base ρ.hat` would put a transport at
>   every use. `hatMaj` does not mention `base` at all.
> * Four structural lemmas (`hatMaj_self`, `hatMaj_trans`, `hatMaj_of_bezemMaj`,
>   `bezemMaj_of_hatMaj`) and a `maxT` (pointwise max at hat types) with four congruence
>   lemmas. All by plain induction on `ρ`; no proof is longer than eight lines.
> * `bezemMaj_of_hatMaj` — the bridge from equal-`n` to `n* ≥ n` — needs the base relation to
>   be **monotone in its numeric argument** (`BaseMono`). That is a new hypothesis, and it is
>   satisfied by the metric relation `base i n x :≡ n ≥ d(a, x)`. It is unavoidable: the
>   composition `a ≽ᵃ_ρ̂ b`, `b ≽ᵃ_ρ c ⊢ a ≽ᵃ_ρ c` at type `X` *is* the statement that the
>   base relation is upward closed.
> * `AbstractMajorizability` gains a `selfMaj` field plus seven laws, and `arrow_intro` gains
>   a second hypothesis. `all_terms_majorizable` correspondingly proves a **conjunction** —
>   the majorant majorizes, *and* it is `selfMaj`-monotone in its environment — carried by a
>   new `SelfMajEnv`. This is the only genuinely non-mechanical part, and the reason is
>   structural: `arrow_intro`'s self obligation is a statement about the majorant alone, so
>   the induction has to know how the majorant varies with the environment, which the old
>   statement never tracked.
> * `bezem_succ_maj` needs its clause duplicated; `bezem_zero_maj` is unchanged;
>   `bezemRel` is unchanged except that `maj_app` now projects `.1`.
> * `general_metatheorem` and everything under it are untouched — both `MajorizabilityRel`
>   fields still come from the first conjunct.
>
> New: `bezem_prec_maj`, majorant `R*(y*, z*, n) = max(z*(R*(n−1))(n−1), R*(n−1))`. See
> `recMaj_hatMaj` / `recMaj_bezemMaj` in `Majorizability.lean`.

The document's `≽ᵃ` at arrow type (`particular-cases-metric-spaces.tex:19`) is a
**conjunction**; `bezemMaj` (`StrongMajorizability.lean`) has only the first half:

| | document `≽ᵃ_{ρ→τ}` | `bezemMaj .arr` |
|---|---|---|
| majorization | `∀z',z (z' ≽ᵃ_ρ z → x z' ≽ᵃ_τ y z)` | ✅ present |
| self-majorization | `∀z',z (z' ≽ᵃ_ρ̂ z → x z' ≽ᵃ_τ̂ x z)` | ❌ **absent** |

So `bezemMaj` is Howard majorizability, not Bezem's, despite the file name and the old
docstring (now corrected in place).

**Why nothing has noticed.** `MajorizabilityRel` asks only for `maj_le` and `maj_app`, and
both follow from the first conjunct alone. `bezemRel` is therefore genuinely correct as a
`MajorizabilityRel`, and `general_metatheorem` is unaffected. The gap is invisible until the
per-constant route is attempted.

**Where it bites**, both read off the document's own proofs:

* **`prec_maj`.** The document's induction (`.tex:82–96`) establishes
  `R n y* z* ≽ᵃ R n y z` at *equal* `n`. But `maj` at `nat →ₜ ρ` unfolds to
  `∀n*,n (n* ≥ n → R y* z* n* ≽ᵃ R y z n)`. Bridging equal-`n` to `n* ≥ n` needs monotonicity
  in `n`, which is precisely what the second conjunct gives. This is *the* reason Bezem
  introduced the clause; a one-clause relation cannot majorize the recursor.
* **`func_maj` for `d_X`.** The document says it outright: *"We also need to check that
  `λx⁰,y⁰.(x+y)∘` majorizes itself."*

**Fix**: widen `bezemMaj`'s `.arr` case to the conjunction, then re-derive `bezemRel` (the
first projection) and re-check `bezemAbstract`'s structural fields — `arrow_intro` will stop
being `fun _ _ h => h` and will need the self-majorization witness threaded through, which is
the one place this is more than mechanical. Deferred by decision 2026-09-02, not overlooked.

**Free from the same passage**, and worth having written down before the fix:
* `0_X` majorant: any `n ≥ d(a, 0_X)`.
* `d_X` majorant: `λx⁰,y⁰.(x+y)∘`, justified by the triangle inequality
  `d(x,y) ≤ d(a,x) + d(a,y) ≤ x* + y*` and then `≤ → s-maj₁` (Lemma 17.8(2,4)).
* `Π`, `Σ` are self-majorising using only property 2 — no induction, no second conjunct
  needed for the *first* clause (`.tex:70–79`).

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
2. ~~**Rounding theory for `(·)∘`**~~ — **mostly done 2026-09-02**, in `Rounding.lean`.
   `(·)◦` is defined semantically on Mathlib `ℝ` (`roundR`), with `Mmaj` and the pointwise
   order `≤₁`, and Lemma 17.8 (2),(3),(5),(6) are proved with zero sorry. The prediction that
   this needs none of `RealNumbers.lean`'s open goals held: the file imports only
   `Metatheorems.Semantics`. Remaining: part (1), the ℝ↔code bridge — it needs a Lean-level
   "meaning of a `ℚ` code" function, which does not exist yet — and part (4), blocked on §2.5.
3. ~~**The metric `base` relation + `bezemRel`**~~ — **partly done 2026-09-02, then blocked.**
   `bezemAbstract` (`Majorizability.lean`) now builds the structural half of
   `AbstractMajorizability` from any base relation: all seven structural fields hold by
   definitional unfolding (`arrow_intro` is `fun _ _ h => h`), plus `bezem_zero_maj` /
   `bezem_succ_maj` for the two ℕ constants, which are `base`-independent. **Blocked on §2.5**
   before the metric `base` itself is worth writing.
4. **The per-constant obligations** — `0` ✅, `S` ✅, `Π`, `Σ` self-majorising via Lemma 17.80,
   `R` by induction (needs §2.5), `0_X`, `d_X` (needs §2.5). This is §1's Proposition,
   transcribed. Note Lemma 17.80 is `\solution{}`-empty in the document, so it must be proved,
   not transcribed.
5. **The three `admissibleEqX` sorries**, needing the three Class C real facts — the only place
   the ℝ obstruction actually bites, and it can proceed in parallel with 2–4.

## 6. What this says about the last two days

The ℝ work (18 sorries, two agent runs) was aimed at the ordered-field package. Per §2 that is
**not** what the metric-space metatheorem consumes. The genuinely needed ℝ facts are three
Class C statements plus a rounding theory that nobody has started. The ℚ layer and the
`cauchyfy` layer were prerequisites for those too, so none of it is wasted — but the target
should move.
