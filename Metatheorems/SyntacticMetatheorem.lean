/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Metatheorem
import Metatheorems.Dialectica.Syntactic

namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι} {X : ι → Type}

-- ============================================================================
-- The metatheorem, with majorants supplied by the syntax
-- ============================================================================

section Metatheorem

variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) →
    Formula F Γ} {si : SpaceInterp X F} {Premises : PremiseSet F}

/-- **The point of the whole branch.**

From a derivation of `∀x (∀u B₀ → ∃v C₀)` we obtain a bound `Φ` depending only on a
majorant of `x` — with *no* majorizability hypotheses beyond `AbstractMajorizability`
itself. The `U_star` / `V_star` that `metatheorem_core_of_majorants` asks for are produced
by `all_closed_terms_majorizable`, because the extracted functionals are closed terms.

Compare `general_metatheorem`, which had to assume a total majorizer on every semantic
value. -/
theorem syntactic_general_metatheorem
    (eqxi : EqXInterp X F si EqX)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) := by
  -- the witness, as a closed term
  let r := syntactic_soundness eqxi spremise prf
  let Ut := extractUTerm (ρ := ρ) (B₀ := B₀) (C₀ := C₀) r.val
  let Vt := extractVTerm (ρ := ρ) (B₀ := B₀) (C₀ := C₀) r.val
  -- majorants, free
  obtain ⟨U_star, hU⟩ := majorant_of_closed_term am Ut
  obtain ⟨V_star, hV⟩ := majorant_of_closed_term am Vt
  -- the extracted content
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (Term.interpret si Ut () x, (x, ())) →
      Formula.interpret si C₀ (Term.interpret si Vt () x, (x, ())) := by
    intro x hBx
    have h_spec := r.property ()
      (x, (Ty.interpret_default si (wTy (Formula.all Ty.nat B₀)),
           Ty.interpret_default si (cTy (Formula.ex Ty.nat C₀))))
    simp only [dialecticaMatrix] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf] at h_spec
    simp only [Ut, Vt, extractUTerm, extractVTerm, defaultWTerm, defaultCTerm,
      Term.interpret, Term.interpret_weaken, interpret_defaultOf, Ctx.lookup] at hBx ⊢
    exact h_spec hBx
  exact metatheorem_core_of_majorants am.toRel
    (fun x u => Formula.interpret si B₀ (u, (x, ())))
    (fun x v => Formula.interpret si C₀ (v, (x, ())))
    (Term.interpret si Ut ()) (Term.interpret si Vt ()) U_star V_star hU hV hUV

end Metatheorem

end Metatheorems
