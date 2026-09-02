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

/-- **The classical syntactic metatheorem.**

Same conclusion as `syntactic_general_metatheorem`, but the input derivation may use LEM and
QF-AC (`Allowed.classical`), and — as there — the only majorizability hypothesis is
`AbstractMajorizability`. Compare `general_metatheorem_classical`, which needs a
`Majorizability`, i.e. a *total* majorizer on every semantic value; that field is not
satisfiable over the full set-theoretic type structure, which is why the metric model could
not use it.

The route:

1. `classical_to_prenex_extended` — prenexify, negatively translate, push the outer `¬¬`
   inside the `∀`, cast to `Allowed.extended`. Shared with `general_metatheorem_classical`.
2. `syntactic_soundness` — a closed **`Term`** realizing `∀x ¬¬∃u∃v(B₀' → C₀')`.
3. `extractUTermP` / `extractVTermP` — go *through* the surviving `¬¬` at the term level
   (the semantic version strips it with `Classical.not_not` instead), challenging it with the
   default `¬E`-witness.
4. `majorant_of_closed_term` twice — majorants, free, because the extractors are closed.
5. `metatheorem_core_of_majorants`.

The default challenge in step 3 is legitimate for the same reason the semantic version's is:
`B₀' →ᶠ C₀'` is quantifier-free and ∨-free, so `dialecticaMatrix_iff_interpFormula` reduces
its matrix to the formula's interpretation **for every** counter. That is precisely the
property the unprenexified route lacks. -/
theorem syntactic_general_metatheorem_classical
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    (nts : NTStableD EqX Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) := by
  classical
  let B₀' : Formula F [Ty.nat, Ty.nat, ρ] := B₀.weakenBy Ty.nat
  let C₀' : Formula F [Ty.nat, Ty.nat, ρ] :=
    C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
  have hB'_qf : B₀'.isQF = true := by rw [show B₀'.isQF = B₀.isQF from isQF_weakenBy B₀, hB_qf]
  have hB'_vf : B₀'.isVFree = true := by
    rw [show B₀'.isVFree = B₀.isVFree from isVFree_weakenBy B₀, hB_vf]
  have hC'_qf : C₀'.isQF = true := by
    rw [show C₀'.isQF = C₀.isQF from isQF_renameF _ C₀, hC_qf]
  have hC'_vf : C₀'.isVFree = true := by
    rw [show C₀'.isVFree = C₀.isVFree from isVFree_renameF _ C₀, hC_vf]
  -- Steps 1–2: the closed realizing term for the prenexified, doubly-negated statement.
  -- `obtain`, not `let`: as a let-value this term is enormous and every later defeq check
  -- would try to `whnf` it.
  obtain ⟨w, hw⟩ :=
    syntactic_soundness eqxi spremise
      (classical_to_prenex_extended adm nts hB_qf hB_vf hC_qf hC_vf prf)
  -- Step 3: the two extractors, as closed terms
  let Ut := extractUTermP (P := B₀' →ᶠ C₀') w
  let Vt := extractVTermP (P := B₀' →ᶠ C₀') w
  -- Step 4: majorants, free
  obtain ⟨U_star, hU⟩ := majorant_of_closed_term am Ut
  obtain ⟨V_star, hV⟩ := majorant_of_closed_term am Vt
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (Term.interpret si Ut () x, (x, ())) →
      Formula.interpret si C₀ (Term.interpret si Vt () x, (x, ())) := by
    intro x hBx
    -- move to the raw projections, which is the shape the matrix produces
    rw [show Term.interpret si Ut () x = _ from interpret_extractUTermP w x] at hBx
    rw [show Term.interpret si Vt () x = _ from interpret_extractVTermP w x]
    -- the ¬¬-challenge: any `¬E`-witness will do (see the docstring)
    have key := hw ()
      (x, (Ty.interpret_default si
             (wTy (¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))))), ()))
    simp only [Formula.neg, dialecticaMatrix] at key
    rw [dialecticaMatrix_iff_interpFormula si B₀' hB'_qf hB'_vf,
        dialecticaMatrix_iff_interpFormula si C₀' hC'_qf hC'_vf] at key
    -- back from B₀'/C₀' to B₀/C₀
    have hb : ∀ u v : Nat, Formula.interpret si B₀' (v, (u, (x, ()))) =
        Formula.interpret si B₀ (u, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si (Term.Renaming.shift (σ := Ty.nat)) B₀
        (v, (u, (x, ()))) (u, (x, ())) (fun {_} _ => rfl)
    have hc : ∀ u v : Nat, Formula.interpret si C₀' (v, (u, (x, ()))) =
        Formula.interpret si C₀ (v, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si
        (Term.Renaming.ext (σ := Ty.nat) (Term.Renaming.shift (σ := Ty.nat))) C₀
        (v, (u, (x, ()))) (v, (x, ()))
        (fun {_} vv => match vv with | .vz => rfl | .vs _ => rfl)
    by_contra hCn
    exact key (fun himp => hCn (Eq.mp (hc _ _) (himp (Eq.mpr (hb _ _) hBx))))
  exact metatheorem_core_of_majorants am.toRel
    (fun x u => Formula.interpret si B₀ (u, (x, ())))
    (fun x v => Formula.interpret si C₀ (v, (x, ())))
    (Term.interpret si Ut ()) (Term.interpret si Vt ()) U_star V_star hU hV hUV

end Metatheorem

end Metatheorems
