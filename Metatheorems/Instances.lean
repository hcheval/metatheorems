/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.CAT0
import Metatheorems.Normed

namespace Metatheorems

/-!
# Mathlib structures ARE models of our theories

Everything above this file is quantified over `MetricModel`, `WHyperbolicModel`, `CAT0Model`
or `NormedModel` **as variables**. Until this file, the project constructed **no inhabitant of
any of them** — so every space metatheorem was a statement about a class not known to be
non-empty. That is not a hypothetical worry here: the total-majorizer `Majorizability` had
provably no instances and was deleted for it (`MajorizabilityRel.lean`), and
`AdmissibleEqX.eqx_refl` was outright *refutable* while looking like ordinary unfinished
work. Both were found by trying to build the thing.

This file does that, from **arbitrary** Mathlib structures — no concrete carrier, no extra
hypotheses:

| our structure | built from | how |
|---|---|---|
| `MetricModel` | any `[MetricSpace X]` + a point | `d := dist`; six Mathlib lemmas |
| `NormedModel` | any **nontrivial** normed space over `ℝ` | `{ E := E }` — no axiom fields |
| `WHyperbolicModel` | any Mathlib normed space | `W x y λ := (1−λ)•x + λ•y`, the segment map |
| `CAT0Model` | any Mathlib real inner-product space | CN **with equality** — the median law |

Combined with `NormedModel.axiomsHold`, `WHyperbolicModel.axiomsHold` and
`CAT0Model.axiomsHold`, this closes the loop: **the normed metatheorem applies to every
*nontrivial* Mathlib real normed space, and the W-hyperbolic and CAT(0) metatheorems to every
Mathlib real normed / real inner-product space, end to end, with no hypothesis beyond the
Mathlib typeclasses.**

The nontriviality side condition is confined to `NormedModel`, and it is not bookkeeping:
`Normed.ax_norm_one` (Kohlenbach's (9), `‖1_X‖ =ℝ 1ℝ`) is *false* in the zero space.
`WHyperbolicModel` and `CAT0Model` are over `WHyperbolic.F`, a different signature with no
`1_X`, so `WHyperbolicModel.ofNormed` and `CAT0Model.ofInner` are untouched by it and still
take only the two/three Mathlib instances.

`NormedModel` is not an imitation of Mathlib's notion — it is a bundling of it (`E : Type`
plus the three instance fields, no axioms of its own), so `ofNormed` is essentially the
identity and the instances come straight back out.

## Two mechanical hazards, both paid for here

* **`WHyperbolicModel.ofNormed` must be an `abbrev`.** As a `def`, `(ofNormed E).carrier` does
  not reduce to `E` at elaboration time and every subsequent `•`/`−` fails instance synthesis
  with `failed to synthesize HSMul ℝ (ofNormed E).carrier`. Same reason
  `NormedModel.toMetricModel` is an `abbrev`.
* **Every Mathlib `‖·‖` in this file is parenthesised.** The project's `‖t‖ si env` notation
  takes *three* arguments, so an unparenthesised `‖a‖ * ‖a‖` tries to consume the `*` as `si`.
  This is a live hazard in any file mixing the object notation with Mathlib norms.

The four W-axiom identities are all discharged by Mathlib's `module` tactic; hand-rolled
`abel` versions of them do **not** go through.

## Scope

`carrier : Type` and `E : Type` are universe-monomorphic, so this covers `Type 0` spaces —
`ℝ`, `EuclideanSpace ℝ (Fin n)`, and essentially every concrete example. A space in `Type u`
would need the structures generalised first.

All three space theories are covered. Normed spaces were the last to join: until
`NormedModel.axiomsHold` was proved, `ofNormed` gave a model but the normed metatheorem still
carried an `AxiomsHold` binder, so it was inhabited-but-not-applicable. No such gap remains,
and no `AxiomsHold` binder survives anywhere in the tower.

`ℝ` witnesses all of it — and `Nontrivial ℝ` is an instance, so the added binder costs the
examples below nothing.
-/

-- ============================================================================
-- Metric spaces
-- ============================================================================

/-- **Any Mathlib metric space, with a chosen point, is a `MetricModel`.** The point serves as
both `0_X` and the majorization reference `a`. -/
def MetricModel.ofMetricSpace (X : Type) [MetricSpace X] (pt : X) : MetricModel where
  carrier := X
  d := dist
  d_nonneg := fun _ _ => _root_.dist_nonneg
  d_self := _root_.dist_self
  d_comm := _root_.dist_comm
  d_triangle := _root_.dist_triangle
  d_eq_zero := fun _ _ h => _root_.dist_eq_zero.mp h
  zeroX := pt
  ref := pt

-- ============================================================================
-- Normed spaces
-- ============================================================================

/-- **Any *nontrivial* Mathlib normed space over `ℝ` is a `NormedModel`** — definitionally,
since `NormedModel` bundles exactly `E` with its three instances and asserts nothing further.

`[Nontrivial E]` is what interprets `1_X` and validates Kohlenbach's axiom (9),
`‖1_X‖ =ℝ 1ℝ` — false in the zero space, so the hypothesis is not removable. Carrying it as a
*typeclass* rather than as an explicit unit vector is what keeps this the identity: the
normalisation `‖v‖⁻¹ • v` happens once, inside `NormedModel.unitVec`, not at every
instantiation site. -/
abbrev NormedModel.ofNormed (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] : NormedModel :=
  { E := E }

/-- The Mathlib instance comes back out, so the bundling loses nothing. -/
example (M : NormedModel) : NormedAddCommGroup M.E := M.normedGroup

-- ============================================================================
-- W-hyperbolic spaces
-- ============================================================================

/-- **Any Mathlib normed space is a W-hyperbolic model**, with `W` the segment map
`W(x,y,λ) = (1−λ)x + λy` and `d(x,y) = ‖x − y‖`.

(W2) holds exactly — `W(x,y,λ) − W(x,y,μ) = (λ−μ)(y−x)` — while (W1) and (W4) are the triangle
inequality plus `norm_smul`, and (W3) is an identity. An `abbrev`; see the header. -/
noncomputable abbrev WHyperbolicModel.ofNormed (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : WHyperbolicModel where
  carrier := E
  d := fun x y => (‖x - y‖)
  d_nonneg := fun _ _ => norm_nonneg _
  d_self := fun x => by simp
  d_comm := fun x y => by rw [← norm_neg]; congr 1; abel
  d_triangle := fun x y z => by
    have h : x - z = (x - y) + (y - z) := by abel
    rw [h]; exact norm_add_le _ _
  d_eq_zero := fun _ _ h => sub_eq_zero.mp (norm_eq_zero.mp h)
  zeroX := 0
  ref := 0
  W := fun x y l => (1 - l) • x + l • y
  W1 := fun z x y l h0 h1 => by
    have hz : z - ((1 - l) • x + l • y) = (1 - l) • (z - x) + l • (z - y) := by module
    rw [hz]
    calc (‖(1 - l) • (z - x) + l • (z - y)‖)
        ≤ (‖(1 - l) • (z - x)‖) + (‖l • (z - y)‖) := norm_add_le _ _
      _ = (1 - l) * (‖z - x‖) + l * (‖z - y‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l), abs_of_nonneg h0]
  W2 := fun x y l m _ _ _ _ => by
    have h : ((1 - l) • x + l • y) - ((1 - m) • x + m • y) = (l - m) • (y - x) := by module
    rw [h, norm_smul, Real.norm_eq_abs]
    congr 1
    rw [← norm_neg]; congr 1; abel
  W3 := fun x y l _ _ => by
    show (1 - l) • x + l • y = (1 - (1 - l)) • y + (1 - l) • x
    rw [sub_sub_cancel]; abel
  W4 := fun x y z w l h0 h1 => by
    have h : ((1 - l) • x + l • z) - ((1 - l) • y + l • w)
        = (1 - l) • (x - y) + l • (z - w) := by module
    rw [h]
    calc (‖(1 - l) • (x - y) + l • (z - w)‖)
        ≤ (‖(1 - l) • (x - y)‖) + (‖l • (z - w)‖) := norm_add_le _ _
      _ = (1 - l) * (‖x - y‖) + l * (‖z - w‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l), abs_of_nonneg h0]

-- ============================================================================
-- CAT(0) spaces
-- ============================================================================

/-- **Any Mathlib real inner-product space is a CAT(0) model.** CN holds with *equality* there
— it is the median law, one step from `parallelogram_law_with_norm`:
`‖z − (x+y)/2‖² = ½‖z−x‖² + ½‖z−y‖² − ¼‖x−y‖²`. -/
noncomputable abbrev CAT0Model.ofInner (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] : CAT0Model where
  toWHyperbolicModel := WHyperbolicModel.ofNormed E
  CN := fun z x y => by
    change (‖z - ((1 - (1/2:ℝ)) • x + (1/2:ℝ) • y)‖) * (‖z - ((1 - (1/2:ℝ)) • x + (1/2:ℝ) • y)‖)
        ≤ (1/2) * ((‖z - x‖) * (‖z - x‖)) + (1/2) * ((‖z - y‖) * (‖z - y‖))
          - (1/4) * ((‖x - y‖) * (‖x - y‖))
    have hpar := parallelogram_law_with_norm ℝ (z - x) (z - y)
    have hd : (z - x) - (z - y) = y - x := by module
    have h3 : (‖(z - x) - (z - y)‖) = (‖x - y‖) := by rw [hd, norm_sub_rev]
    rw [h3] at hpar
    have h1 : z - ((1 - (1/2:ℝ)) • x + (1/2:ℝ) • y) = (2:ℝ)⁻¹ • ((z - x) + (z - y)) := by
      module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    nlinarith [hpar, norm_nonneg ((z - x) + (z - y)), norm_nonneg (x - y)]

-- ============================================================================
-- The payoff: the axioms hold in these models, with no hypotheses
-- ============================================================================

/-- **Every Mathlib normed space satisfies the object-level normed-space axioms.**
`NormedModel.axiomsHold` at `ofNormed`; no hypothesis beyond the typeclasses. -/
theorem NormedModel.ofNormed_axiomsHold (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ∀ {Γ : Ctx MetricSpace.ι} (A : Formula Normed.F Γ), Normed.Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => (NormedModel.ofNormed E).E) Γ,
        Formula.interpret (NormedModel.ofNormed E).si A env :=
  (NormedModel.ofNormed E).axiomsHold

/-- **Every Mathlib normed space satisfies the object-level W-hyperbolic axioms.**
`WHyperbolicModel.axiomsHold` at `ofNormed`; no hypothesis beyond the typeclasses. -/
theorem WHyperbolicModel.ofNormed_axiomsHold (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ {Γ : Ctx MetricSpace.ι} (A : Formula WHyperbolic.F Γ), WHyperbolic.Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => (WHyperbolicModel.ofNormed E).carrier) Γ,
        Formula.interpret (WHyperbolicModel.ofNormed E).si A env :=
  (WHyperbolicModel.ofNormed E).axiomsHold

/-- **Every Mathlib real inner-product space satisfies the object-level CAT(0) axioms.** -/
theorem CAT0Model.ofInner_axiomsHold (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ {Γ : Ctx MetricSpace.ι} (A : Formula WHyperbolic.F Γ), CAT0.Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => (CAT0Model.ofInner E).carrier) Γ,
        Formula.interpret (CAT0Model.ofInner E).si A env :=
  (CAT0Model.ofInner E).axiomsHold

-- `ℝ` is a concrete witness for all of the above, so none of it is vacuous.
noncomputable example : CAT0Model := CAT0Model.ofInner ℝ
noncomputable example : NormedModel := NormedModel.ofNormed ℝ
noncomputable example : MetricModel := MetricModel.ofMetricSpace ℝ 0

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms MetricModel.ofMetricSpace
#print axioms NormedModel.ofNormed
#print axioms WHyperbolicModel.ofNormed
#print axioms CAT0Model.ofInner
#print axioms NormedModel.ofNormed_axiomsHold
#print axioms WHyperbolicModel.ofNormed_axiomsHold
#print axioms CAT0Model.ofInner_axiomsHold

end Metatheorems
