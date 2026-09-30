/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetatheoremPrereqs
import Metatheorems.Dialectica.Syntactic

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type}

-- The metatheorem, with majorants supplied by the syntax

section Metatheorem

variable {si : SpaceInterp X F} {Premises : PremiseSet F}

/-- The `U` functional a derivation extracts — where the premise must be tested — as a
**closed term**. Named so that both the `∃`-valued and the `Subtype`-valued metatheorem can
speak about the same object. -/
def extractedUTerm
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  extractUTerm (ρ := ρ) (B₀ := B₀) (C₀ := C₀) (syntactic_soundness eqxi spremise prf).val

/-- The `V` functional — the witness — as a closed term. -/
def extractedVTerm
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  extractVTerm (ρ := ρ) (B₀ := B₀) (C₀ := C₀) (syntactic_soundness eqxi spremise prf).val

/-- **The extracted content**: challenged at `U`, the premise yields the conclusion at `V`.
This is the Dialectica half of the metatheorem, with no majorizability in sight; both the
`∃`-valued and the `Subtype`-valued metatheorem consume it unchanged. -/
theorem syntactic_extraction
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀
        (Term.interpret si (extractedUTerm eqxi spremise prf) () x, (x, ())) →
      Formula.interpret si C₀
        (Term.interpret si (extractedVTerm eqxi spremise prf) () x, (x, ())) := by
  intro x hBx
  have h_spec := (syntactic_soundness eqxi spremise prf).property ()
    (x, (Ty.interpret_default si (wTy (Formula.all Ty.nat B₀)),
         Ty.interpret_default si (cTy (Formula.ex Ty.nat C₀))))
  simp only [dialecticaMatrix] at h_spec
  rw [dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf] at h_spec
  rw [dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf] at h_spec
  simp only [extractedUTerm, extractedVTerm, extractUTerm, extractVTerm, defaultWTerm,
    defaultCTerm, Term.interpret, Term.interpret_weaken, interpret_defaultOf,
    Ctx.lookup] at hBx ⊢
  exact h_spec hBx

/-- **The metatheorem with the bound as DATA.**

Identical in content to `syntactic_general_metatheorem` below, but the conclusion is a
`Subtype` rather than an `∃`, so `Φ` is *available* — `(… ).val` is a function that computes.
Takes a `ConstMajorants am` where the `∃` version needs only `AbstractMajorizability`. -/
def syntactic_general_metatheorem_at
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
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
  ⟨coreBound (closedMajorizer cm (extractedUTerm eqxi spremise prf))
             (closedMajorizer cm (extractedVTerm eqxi spremise prf)),
   metatheorem_core_of_majorants_at am.toRel
     (fun x u => Formula.interpret si B₀ (u, (x, ())))
     (fun x v => Formula.interpret si C₀ (v, (x, ())))
     _ _ _ _
     (closedMajorizer_maj cm (extractedUTerm eqxi spremise prf))
     (closedMajorizer_maj cm (extractedVTerm eqxi spremise prf))
     (syntactic_extraction eqxi spremise hB_qf hB_vf hC_qf hC_vf prf)⟩

/-- From a derivation of `∀x (∀u B₀ → ∃v C₀)` we obtain a bound `Φ` depending only on a
majorant of `x` — with *no* majorizability hypotheses beyond `AbstractMajorizability`
itself. The `U_star` / `V_star` that `metatheorem_core_of_majorants` asks for are produced
by `all_closed_terms_majorizable`, because the extracted functionals are closed terms. -/
theorem syntactic_general_metatheorem
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) := by
  obtain ⟨U_star, hU⟩ := majorant_of_closed_term am (extractedUTerm eqxi spremise prf)
  obtain ⟨V_star, hV⟩ := majorant_of_closed_term am (extractedVTerm eqxi spremise prf)
  exact metatheorem_core_of_majorants am.toRel
    (fun x u => Formula.interpret si B₀ (u, (x, ())))
    (fun x v => Formula.interpret si C₀ (v, (x, ())))
    _ _ U_star V_star hU hV
    (syntactic_extraction eqxi spremise hB_qf hB_vf hC_qf hC_vf prf)

/-- **The classical syntactic metatheorem.**

Same conclusion as `syntactic_general_metatheorem`, but the input derivation may use LEM and
QF-AC (`Allowed.classical`), and — as there — the only majorizability hypothesis is
`AbstractMajorizability`.

The route:

1. `classical_to_prenex_extended` — prenexify, negatively translate, push the outer `¬¬`
   inside the `∀`, cast to `Allowed.extended`. Shared with the MFI classical entry point.
2. `syntactic_soundness` — a closed **`Term`** realizing `∀x ¬¬∃u∃v(B₀' → C₀')`.
3. `extractUTermP` / `extractVTermP` — go *through* the surviving `¬¬` at the term level
   (the semantic version strips it with `Classical.not_not` instead), challenging it with the
   default `¬E`-witness.
4. `majorant_of_closed_term` twice — majorants, free, because the extractors are closed.
5. `metatheorem_core_of_majorants`. -/
theorem syntactic_general_metatheorem_classical
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
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
      (classical_to_prenex_extended nts hB_qf hB_vf hC_qf hC_vf prf)
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

-- The classical metatheorem with the bound as data

/-- The realizing term for the prenexified, negatively translated statement — the classical
route's analogue of `syntactic_soundness … prf`. -/
def prenexRealizer
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    SRealizer si (Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
      (B₀.weakenBy Ty.nat →ᶠ C₀.renameF (Term.Renaming.ext Term.Renaming.shift)))))) :=
  syntactic_soundness eqxi spremise
    (classical_to_prenex_extended nts hB_qf hB_vf hC_qf hC_vf prf)

/-- The classical route's `U` functional, as a closed term. Unlike `extractedUTerm` this goes
*through* the surviving `¬¬` at the term level, challenging it with the default `¬E`-witness
(`extractUTermP`). -/
def extractedUTermP
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  extractUTermP
    (P := B₀.weakenBy Ty.nat →ᶠ C₀.renameF (Term.Renaming.ext Term.Renaming.shift))
    (prenexRealizer eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf).val

/-- The classical route's `V` functional — the witness — as a closed term. -/
def extractedVTermP
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  extractVTermP
    (P := B₀.weakenBy Ty.nat →ᶠ C₀.renameF (Term.Renaming.ext Term.Renaming.shift))
    (prenexRealizer eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf).val

/-- **The extraction half of the classical metatheorem**, over an *abstract* realizer of the
prenexified, negatively translated statement: challenged at `U`, the premise yields the
conclusion at `V`. No majorizability in sight. `w` is a variable, not the applied
`prenexRealizer`. -/
theorem extraction_of_prenex_realizer
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (w : SRealizer si (Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
      (B₀.weakenBy Ty.nat →ᶠ C₀.renameF (Term.Renaming.ext Term.Renaming.shift))))))) :
    ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀
        (Term.interpret si (extractUTermP
          (P := B₀.weakenBy Ty.nat →ᶠ
            C₀.renameF (Term.Renaming.ext Term.Renaming.shift)) w.val) () x, (x, ())) →
      Formula.interpret si C₀
        (Term.interpret si (extractVTermP
          (P := B₀.weakenBy Ty.nat →ᶠ
            C₀.renameF (Term.Renaming.ext Term.Renaming.shift)) w.val) () x, (x, ())) := by
  classical
  intro x hBx
  have hB'_qf : (B₀.weakenBy Ty.nat).isQF = true := by
    rw [show (B₀.weakenBy Ty.nat).isQF = B₀.isQF from isQF_weakenBy B₀, hB_qf]
  have hB'_vf : (B₀.weakenBy Ty.nat).isVFree = true := by
    rw [show (B₀.weakenBy Ty.nat).isVFree = B₀.isVFree from isVFree_weakenBy B₀, hB_vf]
  have hC'_qf :
      (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
        (Term.Renaming.shift (σ := Ty.nat)))).isQF = true := by
    rw [show (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
        (Term.Renaming.shift (σ := Ty.nat)))).isQF = C₀.isQF from
      isQF_renameF _ C₀, hC_qf]
  have hC'_vf :
      (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
        (Term.Renaming.shift (σ := Ty.nat)))).isVFree = true := by
    rw [show (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
        (Term.Renaming.shift (σ := Ty.nat)))).isVFree = C₀.isVFree from
      isVFree_renameF _ C₀, hC_vf]
  -- move to the raw projections, which is the shape the matrix produces
  rw [interpret_extractUTermP w.val x] at hBx
  rw [interpret_extractVTermP w.val x]
  -- the ¬¬-challenge: any `¬E`-witness will do (see `syntactic_general_metatheorem_classical`)
  have key := w.property ()
    (x, (Ty.interpret_default si
           (wTy (¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
             (B₀.weakenBy Ty.nat →ᶠ
               C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
                 (Term.Renaming.shift (σ := Ty.nat)))))))), ()))
  simp only [Formula.neg, dialecticaMatrix] at key
  rw [dialecticaMatrix_iff_interpFormula si (B₀.weakenBy Ty.nat) hB'_qf hB'_vf,
      dialecticaMatrix_iff_interpFormula si
        (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
          (Term.Renaming.shift (σ := Ty.nat)))) hC'_qf hC'_vf] at key
  -- back from B₀'/C₀' to B₀/C₀
  have hb : ∀ u v : Nat, Formula.interpret si (B₀.weakenBy Ty.nat) (v, (u, (x, ()))) =
      Formula.interpret si B₀ (u, (x, ())) := fun u v =>
    Formula.interpret_renameF_gen si (Term.Renaming.shift (σ := Ty.nat)) B₀
      (v, (u, (x, ()))) (u, (x, ())) (fun {_} _ => rfl)
  have hc : ∀ u v : Nat,
      Formula.interpret si (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
          (Term.Renaming.shift (σ := Ty.nat))))
        (v, (u, (x, ()))) = Formula.interpret si C₀ (v, (x, ())) := fun u v =>
    Formula.interpret_renameF_gen si
      (Term.Renaming.ext (σ := Ty.nat) (Term.Renaming.shift (σ := Ty.nat))) C₀
      (v, (u, (x, ()))) (v, (x, ()))
      (fun {_} vv => match vv with | .vz => rfl | .vs _ => rfl)
  by_contra hCn
  exact key (fun himp => hCn (Eq.mp (hc _ _) (himp (Eq.mpr (hb _ _) hBx))))

/-- `extraction_of_prenex_realizer` at the realizer a classical derivation actually produces.
The two statements match by delta on `extractedUTermP`/`extractedVTermP` — a cheap unfolding
that never enters the realizer. -/
theorem syntactic_extraction_classical
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀
        (Term.interpret si (extractedUTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf) () x,
          (x, ())) →
      Formula.interpret si C₀
        (Term.interpret si (extractedVTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf) () x,
          (x, ())) :=
  extraction_of_prenex_realizer hB_qf hB_vf hC_qf hC_vf
    (prenexRealizer eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf)

/-- **The classical metatheorem with the bound as DATA.**

`syntactic_general_metatheorem_classical` with a `Subtype` in place of the `∃`, so `Φ` is
*available* rather than merely known to exist. Stands to it exactly as
`syntactic_general_metatheorem_at` stands to `syntactic_general_metatheorem`, and takes a
`ConstMajorants` for the same reason. This is the entry point a *classical* derivation needs
in order to produce a numeral. -/
def syntactic_general_metatheorem_classical_at
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } :=
  ⟨coreBound
      (closedMajorizer cm (extractedUTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf))
      (closedMajorizer cm (extractedVTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf)),
   metatheorem_core_of_majorants_at am.toRel
     (fun x u => Formula.interpret si B₀ (u, (x, ())))
     (fun x v => Formula.interpret si C₀ (v, (x, ())))
     _ _ _ _
     (closedMajorizer_maj cm
       (extractedUTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf))
     (closedMajorizer_maj cm
       (extractedVTermP eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf))
     (syntactic_extraction_classical eqxi nts spremise hB_qf hB_vf hC_qf hC_vf prf)⟩

end Metatheorem

/-!
## The metatheorem with general matrices — Kohlenbach, Theorem 17.52

The theorems in this section relax the quantifier-free restriction of
`syntactic_general_metatheorem`: the premise matrix may be any **purely universal**
formula (`isPurelyUniversal`) and the conclusion matrix any **purely existential** one
(`isPurelyExistential`), both ∨-free. The QF versions are the instances
`Formula.isPurelyUniversal_of_qf` / `Formula.isPurelyExistential_of_qf`. A single quantifier
block `∀b^σ` plays the role of the book's tuple `∀b̲`, since `Ty` has products.
-/

section GeneralMatrices

variable {si : SpaceInterp X F} {Premises : PremiseSet F}

/-- **The extracted content, with general matrices**: `B` purely universal, `C` purely
existential, both ∨-free. Challenged at `U`, the premise yields the conclusion at `V`. The
extractors are the *same* `extractedUTerm` / `extractedVTerm` — they never depended on the
matrices being quantifier-free. -/
theorem syntactic_extraction_gen
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {ρ : Ty ι} {B C : Formula F [Ty.nat, ρ]}
    (hB_pu : B.isPurelyUniversal = true) (hB_vf : B.isVFree = true)
    (hC_pe : C.isPurelyExistential = true) (hC_vf : C.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B) (Formula.ex .nat C)))) :
    ∀ x : Ty.interpret X ρ,
      Formula.interpret si B
        (Term.interpret si (extractedUTerm eqxi spremise prf) () x, (x, ())) →
      Formula.interpret si C
        (Term.interpret si (extractedVTerm eqxi spremise prf) () x, (x, ())) := by
  intro x hBx
  have h_spec := (syntactic_soundness eqxi spremise prf).property ()
    (x, (Ty.interpret_default si (wTy (Formula.all Ty.nat B)),
         Ty.interpret_default si (cTy (Formula.ex Ty.nat C))))
  simp only [dialecticaMatrix] at h_spec
  simp only [extractedUTerm, extractedVTerm, extractUTerm, extractVTerm, defaultWTerm,
    defaultCTerm, Term.interpret, Term.interpret_weaken, interpret_defaultOf,
    Ctx.lookup] at hBx ⊢
  exact interp_of_dialecticaMatrix_pe si C hC_pe hC_vf _ _ _
    (h_spec (dialecticaMatrix_of_interp_pu si B hB_pu hB_vf _ hBx _ _))

/-- **The metatheorem with general matrices, bound as data.** `syntactic_general_metatheorem_at`
with `B∀` purely universal and `C∃` purely existential (Kohlenbach 17.52). -/
def syntactic_general_metatheorem_at_gen
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
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
  ⟨coreBound (closedMajorizer cm (extractedUTerm eqxi spremise prf))
             (closedMajorizer cm (extractedVTerm eqxi spremise prf)),
   metatheorem_core_of_majorants_at am.toRel
     (fun x u => Formula.interpret si B (u, (x, ())))
     (fun x v => Formula.interpret si C (v, (x, ())))
     _ _ _ _
     (closedMajorizer_maj cm (extractedUTerm eqxi spremise prf))
     (closedMajorizer_maj cm (extractedVTerm eqxi spremise prf))
     (syntactic_extraction_gen eqxi spremise hB_pu hB_vf hC_pe hC_vf prf)⟩

/-- **The metatheorem with general matrices** — Kohlenbach 17.52's shape: from a derivation
of `∀x (∀u B∀ → ∃v C∃)` with `B∀` a ∀-formula and `C∃` an ∃-formula (both ∨-free), a bound
`Φ` on `u` and `v` depending only on a majorant of `x`. Extended input; the same statement
as `syntactic_general_metatheorem`, which is the instance where both matrices are QF. -/
theorem syntactic_general_metatheorem_gen
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B C : Formula F [Ty.nat, ρ]}
    (hB_pu : B.isPurelyUniversal = true) (hB_vf : B.isVFree = true)
    (hC_pe : C.isPurelyExistential = true) (hC_vf : C.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B) (Formula.ex .nat C)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C (v, (x, ())) := by
  obtain ⟨U_star, hU⟩ := majorant_of_closed_term am (extractedUTerm eqxi spremise prf)
  obtain ⟨V_star, hV⟩ := majorant_of_closed_term am (extractedVTerm eqxi spremise prf)
  exact metatheorem_core_of_majorants am.toRel
    (fun x u => Formula.interpret si B (u, (x, ())))
    (fun x v => Formula.interpret si C (v, (x, ())))
    _ _ U_star V_star hU hV
    (syntactic_extraction_gen eqxi spremise hB_pu hB_vf hC_pe hC_vf prf)

/-- **The single-block form**, spelled out: `∀x (∀u ∀b^σ B₀ → ∃v ∃c^τ C₀)` with `B₀`, `C₀`
quantifier-free and ∨-free, `σ τ : Ty ι` arbitrary. Because `Ty` has products this *is* the
book's `∀b̲` / `∃c̲` (see the section header), and the conclusion reads exactly as 17.52's:
`∀u ≤ Φ(x*) ∀b B₀(x,u,b) → ∃v ≤ Φ(x*) ∃c C₀(x,v,c)`. An instance of
`syntactic_general_metatheorem_gen`. -/
theorem syntactic_general_metatheorem_block
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ σ τ : Ty ι} {B₀ : Formula F [σ, Ty.nat, ρ]} {C₀ : Formula F [τ, Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat (Formula.all σ B₀))
                                  (Formula.ex .nat (Formula.ex τ C₀))))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star →
          ∀ b : Ty.interpret X σ, Formula.interpret si B₀ (b, (u, (x, ())))) →
        ∃ v : Nat, v ≤ Φ x_star ∧
          ∃ c : Ty.interpret X τ, Formula.interpret si C₀ (c, (v, (x, ()))) :=
  syntactic_general_metatheorem_gen eqxi spremise am
    (B := Formula.all σ B₀) (C := Formula.ex τ C₀)
    (Formula.isPurelyUniversal_of_qf B₀ hB_qf) hB_vf
    (Formula.isPurelyExistential_of_qf C₀ hC_qf) hC_vf prf

/-- **The classical metatheorem with general matrices.** `syntactic_general_metatheorem_classical`
with `B∀` purely universal and `C∃` purely existential — Kohlenbach 17.52 for classical
input, which is how the book states it. The route is the same five steps; step 1 is
`classical_to_prenex_extended_gen`, and in step 5 `dialecticaMatrix_iff_interpFormula` is
replaced by `dialecticaMatrix_of_interp_pu` / `interp_of_dialecticaMatrix_pe`. -/
theorem syntactic_general_metatheorem_classical_gen
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    {ρ : Ty ι} {B C : Formula F [Ty.nat, ρ]}
    (hB_pu : B.isPurelyUniversal = true) (hB_vf : B.isVFree = true)
    (hC_pe : C.isPurelyExistential = true) (hC_vf : C.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B) (Formula.ex .nat C)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C (v, (x, ())) := by
  classical
  let B' : Formula F [Ty.nat, Ty.nat, ρ] := B.weakenBy Ty.nat
  let C' : Formula F [Ty.nat, Ty.nat, ρ] :=
    C.renameF (Term.Renaming.ext Term.Renaming.shift)
  have hB'_pu : B'.isPurelyUniversal = true := by
    rw [show B'.isPurelyUniversal = B.isPurelyUniversal from isPurelyUniversal_renameF _ B, hB_pu]
  have hB'_vf : B'.isVFree = true := by
    rw [show B'.isVFree = B.isVFree from isVFree_weakenBy B, hB_vf]
  have hC'_pe : C'.isPurelyExistential = true := by
    rw [show C'.isPurelyExistential = C.isPurelyExistential from
      isPurelyExistential_renameF _ C, hC_pe]
  have hC'_vf : C'.isVFree = true := by
    rw [show C'.isVFree = C.isVFree from isVFree_renameF _ C, hC_vf]
  -- Steps 1–2: the closed realizing term for the prenexified, doubly-negated statement.
  -- `obtain`, not `let` (hard rule 4).
  obtain ⟨w, hw⟩ :=
    syntactic_soundness eqxi spremise
      (classical_to_prenex_extended_gen nts hB_pu hC_pe prf)
  -- Step 3: the two extractors, as closed terms
  let Ut := extractUTermP (P := B' →ᶠ C') w
  let Vt := extractVTermP (P := B' →ᶠ C') w
  -- Step 4: majorants, free
  obtain ⟨U_star, hU⟩ := majorant_of_closed_term am Ut
  obtain ⟨V_star, hV⟩ := majorant_of_closed_term am Vt
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B (Term.interpret si Ut () x, (x, ())) →
      Formula.interpret si C (Term.interpret si Vt () x, (x, ())) := by
    intro x hBx
    rw [show Term.interpret si Ut () x = _ from interpret_extractUTermP w x] at hBx
    rw [show Term.interpret si Vt () x = _ from interpret_extractVTermP w x]
    -- the ¬¬-challenge: any `¬E`-witness will do, for the same reason as in the QF case —
    -- the matrix of `B' →ᶠ C'` is discharged for EVERY witness/counter by the two lemmas
    have key := hw ()
      (x, (Ty.interpret_default si
             (wTy (¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B' →ᶠ C'))))), ()))
    simp only [Formula.neg, dialecticaMatrix] at key
    -- back from B'/C' to B/C
    have hb : ∀ u v : Nat, Formula.interpret si B' (v, (u, (x, ()))) =
        Formula.interpret si B (u, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si (Term.Renaming.shift (σ := Ty.nat)) B
        (v, (u, (x, ()))) (u, (x, ())) (fun {_} _ => rfl)
    have hc : ∀ u v : Nat, Formula.interpret si C' (v, (u, (x, ()))) =
        Formula.interpret si C (v, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si
        (Term.Renaming.ext (σ := Ty.nat) (Term.Renaming.shift (σ := Ty.nat))) C
        (v, (u, (x, ()))) (v, (x, ()))
        (fun {_} vv => match vv with | .vz => rfl | .vs _ => rfl)
    by_contra hCn
    exact key (fun himp => hCn (Eq.mp (hc _ _)
      (interp_of_dialecticaMatrix_pe si C' hC'_pe hC'_vf _ _ _
        (himp (dialecticaMatrix_of_interp_pu si B' hB'_pu hB'_vf _
          (Eq.mpr (hb _ _) hBx) _ _)))))
  exact metatheorem_core_of_majorants am.toRel
    (fun x u => Formula.interpret si B (u, (x, ())))
    (fun x v => Formula.interpret si C (v, (x, ())))
    (Term.interpret si Ut ()) (Term.interpret si Vt ()) U_star V_star hU hV hUV

end GeneralMatrices

#print axioms syntactic_general_metatheorem_gen
#print axioms syntactic_general_metatheorem_at_gen
#print axioms syntactic_general_metatheorem_block
#print axioms syntactic_general_metatheorem_classical_gen

end Metatheorems
