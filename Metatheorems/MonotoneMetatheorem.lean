/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Dialectica.Monotone

/-!
# The metatheorem through the monotone functional interpretation

`monotone_general_metatheorem_at` has **the same statement** as
`syntactic_general_metatheorem_at` (`SyntacticMetatheorem.lean`) and produces a bound of the
same shape, `Φ = coreBound U* V*`; what changes is where `U*`/`V*` come from:

| route | `U*`, `V*` | majorization fact |
|---|---|---|
| term (`syntactic_general_metatheorem_at`) | `closedMajorizer cm (extractedUTerm …)` — the majorant of an extracted realizer **term** | `closedMajorizer_maj` |
| monotone (this file) | `mfiU cm r`, `mfiV cm r` — read off the **monotone realizer** `r := monotone_soundness … prf`, a semantic value at the hat type | the `Prop` half of `MRealizer`: an existential realizer, majorized at `n = am.N`, self-majorizing |

`metatheorem_core_of_majorants_at` is consumed unchanged. The extraction half is
`mfi_extract_core`, stated over an abstract `MRealizer`; `mfi_bound_property` is the bound
property over such a realizer, and the entry points instantiate it.
-/

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type}

section Monotone

variable {si : SpaceInterp X F} {Premises : PremiseSet F} {am : AbstractMajorizability si}

/-- **The extraction half, monotone.** From a monotone realizer of `∀x (∀u B₀ → ∃v C₀)`:
two functionals `U`, `V` — the projections of the existential realizer, exactly as
`extractUTerm`/`extractVTerm` project the realizing term — with

* `mfiU cm r` majorizes `U` and `mfiV cm r` majorizes `V` (at `ρ →ₜ nat`, via `arrow_intro`
  from the `MRealizer` majorization and self-majorization clauses), and
* the matrix-level content: if `B₀`'s matrix holds at `U x` for every witness and counter,
  `C₀`'s matrix holds at `V x` for some witness and counter.

The matrix-level form serves both the QF and the general-matrix metatheorem: the QF one
converts both sides with `dialecticaMatrix_iff_interpFormula`, the general one with
`dialecticaMatrix_of_interp_pu` / `interp_of_dialecticaMatrix_pe`. -/
theorem mfi_extract_core (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    ∃ U V : Ty.interpret X ρ → Nat,
      am.maj (ρ →ₜ Ty.nat) (mfiU cm r) U ∧
      am.maj (ρ →ₜ Ty.nat) (mfiV cm r) V ∧
      ∀ x : Ty.interpret X ρ,
        (∀ (w : 𝕎 X B₀) (c : ℂ X B₀), dialecticaMatrix si B₀ (U x, (x, ())) w c) →
        ∃ (w : 𝕎 X C₀) (c : ℂ X C₀), dialecticaMatrix si C₀ (V x, (x, ())) w c := by
  obtain ⟨⟨xr, hx, hm⟩, hs⟩ := r.property am.N (Nat.le_refl _)
  -- the default witness of `∀u B₀` and default counter of `∃v C₀`, as `Term.interpret` of the
  -- default terms (the shape `termMajorizer_maj` relates to `mfiU`/`mfiV`'s majorants)
  let dW : Ty.interpret X ρ → 𝕎 X (Formula.all Ty.nat B₀) :=
    fun x => Term.interpret si (defaultWTerm (Formula.all Ty.nat B₀)) (x, ())
  let dC : Ty.interpret X ρ → ℂ X (Formula.ex Ty.nat C₀) :=
    fun x => Term.interpret si (defaultCTerm (Formula.ex Ty.nat C₀)) (x, ())
  refine ⟨fun x => ((xr () x).2 (dW x) (dC x)).1, fun x => ((xr () x).1 (dW x)).1, ?_, ?_, ?_⟩
  · -- `mfiU` majorizes `U`
    have hall := hx () () trivial
    have hsall := hs () () trivial
    refine am.arrow_intro _ _ ?_ ?_
    · intro xs x hxs
      have hW := (termMajorizer_maj cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N
        (Nat.le_refl _)).1 (xs, ()) (x, ()) ⟨hxs, trivial⟩
      have hC := (termMajorizer_maj cm (defaultCTerm (Formula.ex Ty.nat C₀)) am.N
        (Nat.le_refl _)).1 (xs, ()) (x, ()) ⟨hxs, trivial⟩
      exact am.prod_fst _ _ (am.app_compat _ _ _ _ (am.app_compat _ _ _ _
        (am.prod_snd _ _ (am.app_compat _ _ _ _ hall hxs)) hW) hC)
    · intro xs₁ xs₂ hxs
      have hW := (termMajorizer_maj cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N
        (Nat.le_refl _)).2 (xs₁, ()) (xs₂, ()) ⟨hxs, trivial⟩
      have hC := (termMajorizer_maj cm (defaultCTerm (Formula.ex Ty.nat C₀)) am.N
        (Nat.le_refl _)).2 (xs₁, ()) (xs₂, ()) ⟨hxs, trivial⟩
      exact am.selfMaj_prod_fst _ _ (am.selfMaj_app (am.selfMaj_app
        (am.selfMaj_prod_snd _ _ (am.selfMaj_app hsall hxs)) hW) hC)
  · -- `mfiV` majorizes `V`
    have hall := hx () () trivial
    have hsall := hs () () trivial
    refine am.arrow_intro _ _ ?_ ?_
    · intro xs x hxs
      have hW := (termMajorizer_maj cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N
        (Nat.le_refl _)).1 (xs, ()) (x, ()) ⟨hxs, trivial⟩
      exact am.prod_fst _ _ (am.app_compat _ _ _ _
        (am.prod_fst _ _ (am.app_compat _ _ _ _ hall hxs)) hW)
    · intro xs₁ xs₂ hxs
      have hW := (termMajorizer_maj cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N
        (Nat.le_refl _)).2 (xs₁, ()) (xs₂, ()) ⟨hxs, trivial⟩
      exact am.selfMaj_prod_fst _ _ (am.selfMaj_app
        (am.selfMaj_prod_fst _ _ (am.selfMaj_app hsall hxs)) hW)
  · -- the content
    intro x hB
    have h_spec := hm () (x, (dW x, dC x))
    simp only [dialecticaMatrix] at h_spec
    exact ⟨_, _, h_spec (hB _ _)⟩

/-- **The bound property, over an abstract monotone realizer** (QF matrices). This is the
statement `syntactic_general_metatheorem_at` makes about its `Φ`, made about
`coreBound (mfiU cm r) (mfiV cm r)`. -/
theorem mfi_bound_property (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      am.toRel.maj ρ x_star x →
      (∀ u : Nat, u ≤ coreBound (mfiU cm r) (mfiV cm r) x_star →
        Formula.interpret si B₀ (u, (x, ()))) →
      ∃ v : Nat, v ≤ coreBound (mfiU cm r) (mfiV cm r) x_star ∧
        Formula.interpret si C₀ (v, (x, ())) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := mfi_extract_core cm r
  refine metatheorem_core_of_majorants_at am.toRel
    (fun x u => Formula.interpret si B₀ (u, (x, ())))
    (fun x v => Formula.interpret si C₀ (v, (x, ())))
    U V _ _ hU hV ?_
  intro x hBx
  obtain ⟨w, c, hwc⟩ := hUV x (fun w c =>
    (dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf _ w c).mpr hBx)
  exact (dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf _ w c).mp hwc

/-- **The bound property, general matrices** (`B` purely universal, `C` purely existential,
both ∨-free — Kohlenbach 17.52's `B∀`/`C∃`). -/
theorem mfi_bound_property_gen (cm : ConstMajorants am)
    {ρ : Ty ι} {B C : Formula F [Ty.nat, ρ]}
    (hB_pu : B.isPurelyUniversal = true) (hB_vf : B.isVFree = true)
    (hC_pe : C.isPurelyExistential = true) (hC_vf : C.isVFree = true)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B)
      (Formula.ex Ty.nat C)))) :
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      am.toRel.maj ρ x_star x →
      (∀ u : Nat, u ≤ coreBound (mfiU cm r) (mfiV cm r) x_star →
        Formula.interpret si B (u, (x, ()))) →
      ∃ v : Nat, v ≤ coreBound (mfiU cm r) (mfiV cm r) x_star ∧
        Formula.interpret si C (v, (x, ())) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := mfi_extract_core cm r
  refine metatheorem_core_of_majorants_at am.toRel
    (fun x u => Formula.interpret si B (u, (x, ())))
    (fun x v => Formula.interpret si C (v, (x, ())))
    U V _ _ hU hV ?_
  intro x hBx
  obtain ⟨w, c, hwc⟩ := hUV x (fun w c =>
    dialecticaMatrix_of_interp_pu si B hB_pu hB_vf _ hBx w c)
  exact interp_of_dialecticaMatrix_pe si C hC_pe hC_vf _ w c hwc

/-- **The metatheorem, with the bound computed by the monotone functional interpretation.**

Same statement as `syntactic_general_metatheorem_at`; `Φ := coreBound (mfiU cm r) (mfiV cm r)`
with `r := monotone_soundness eqxi spremise cm prf`. -/
def monotone_general_metatheorem_at
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } :=
  ⟨coreBound (mfiU cm (monotone_soundness eqxi spremise cm prf))
             (mfiV cm (monotone_soundness eqxi spremise cm prf)),
   mfi_bound_property cm hB_qf hB_vf hC_qf hC_vf (monotone_soundness eqxi spremise cm prf)⟩

/-- **The general-matrix form** (Kohlenbach 17.52), monotone: `syntactic_general_metatheorem_at_gen`
with the bound computed by `monotone_soundness`. -/
def monotone_general_metatheorem_at_gen
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {ρ : Ty ι} {B C : Formula F [Ty.nat, ρ]}
    (hB_pu : B.isPurelyUniversal = true) (hB_vf : B.isVFree = true)
    (hC_pe : C.isPurelyExistential = true) (hC_vf : C.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B) (Formula.ex .nat C)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C (v, (x, ())) } :=
  ⟨coreBound (mfiU cm (monotone_soundness eqxi spremise cm prf))
             (mfiV cm (monotone_soundness eqxi spremise cm prf)),
   mfi_bound_property_gen cm hB_pu hB_vf hC_pe hC_vf
     (monotone_soundness eqxi spremise cm prf)⟩

/-- The bound is, definitionally, the `max` of the two monotone majorants — so a client that
has evaluated `mfiU` and `mfiV` has evaluated `Φ`. -/
theorem monotone_general_metatheorem_at_val
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀))))
    (x_star : Ty.interpret X ρ.hat) :
    (monotone_general_metatheorem_at eqxi spremise cm hB_qf hB_vf hC_qf hC_vf prf).val x_star
      = Nat.max (mfiU cm (monotone_soundness eqxi spremise cm prf) x_star)
                (mfiV cm (monotone_soundness eqxi spremise cm prf) x_star) := rfl

end Monotone

#print axioms mfi_extract_core
#print axioms mfi_bound_property
#print axioms mfi_bound_property_gen
#print axioms monotone_general_metatheorem_at
#print axioms monotone_general_metatheorem_at_gen

end Metatheorems
