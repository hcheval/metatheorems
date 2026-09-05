/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneND
import Metatheorems.MonotoneMetatheorem
import Metatheorems.SyntacticMetatheorem

/-!
# The classical metatheorem through the monotone functional interpretation

`monotone_general_metatheorem_classical_at` has the **same statement** as
`syntactic_general_metatheorem_classical_at` (`SyntacticMetatheorem.lean`) but computes the
bound through the monotone functional interpretation of the *classical* derivation, avoiding
`negTrans_sound`'s ×230 blow-up (`ARCHITECTURE.md` §14.5, `Probes/ClassicalMfiProbe.lean`
part C0):

1. `prenexify` under `∀x` — a closed classical derivation applied **once** (it uses LEM), so
   `monotone_nd_soundness` interprets it as an ordinary sub-derivation, not per-node;
2. `monotone_nd_soundness` (`Dialectica/MonotoneND.lean`) — the fused negative-translation +
   MFI recursion, giving a monotone realizer of `(∀ρ E)ᴺᵀ = ¬¬(∀ρ ¬¬E)`, `E := ∃u∃v(B₀'→C₀')`;
3. `nn_all_nn` at the `MRealizer` level (a leaf composition), giving a realizer of `∀ρ ¬¬E`;
4. the `¬¬∃u∃v` projection — the MFI analogue of `extractUTermP`/`extractVTermP`
   (`interpret_extractUTermP`): challenge the surviving `¬¬` with the default `¬E`-witness,
   read the `∃u`/`∃v` index off the resulting witness. Legitimate because `B₀'→C₀'` is QF and
   ∨-free, so `dialecticaMatrix_iff_interpFormula` reduces its matrix for **every** counter —
   the argument written for the term route (`extraction_of_prenex_realizer`), followed here on
   the semantic realizer;
5. `metatheorem_core_of_majorants_at`, unchanged.

`mfiU_cl`/`mfiV_cl` read the two majorants off the monotone realizer's `tstar`; the semantic
`U`/`V` are the same projection off its existential realizer, and the two are related by the
`MRealizer` majorization clause.
-/

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type}

section ClassicalMonotone

variable {si : SpaceInterp X F} {Premises : PremiseSet F} {am : AbstractMajorizability si}

/-- `E := ∃u∃v (B₀' →ᶠ C₀')`, the prenexified matrix body (`B₀'`, `C₀'` the weakenings that
`prenexify`/`classical_to_prenex_extended` produce). -/
private abbrev clE (B₀ C₀ : Formula F [Ty.nat, ρ]) : Formula F [ρ] :=
  Formula.ex Ty.nat (Formula.ex Ty.nat
    (B₀.weakenBy Ty.nat →ᶠ C₀.renameF (Term.Renaming.ext Term.Renaming.shift)))

/-- `¬E`, the formula the surviving `¬¬` is challenged with. -/
private abbrev clNegE (B₀ C₀ : Formula F [Ty.nat, ρ]) : Formula F [ρ] :=
  ¬ᶠ(clE B₀ C₀)

/-- **The classical monotone realizer**: `∀ρ ¬¬E`, from `prenexify` + `monotone_nd_soundness`
+ `nn_all_nn`. No realizer term is built on the way. -/
def clMRealizer (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    (spremise_nd : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → MRealizer cm (Bᴺᵀ))
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    MRealizer cm (Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀))) :=
  -- step 1: prenexify under ∀ρ (classical), giving `∀ρ E`
  let prf' : @Derivable ι κ F Allowed.classical Premises []
      (Formula.all ρ (clE B₀ C₀)) :=
    Derivable.mp prf (forall_map (prenexify hB_qf hB_vf hC_qf hC_vf))
  -- step 2: the fused NT + MFI, giving `(∀ρ E)ᴺᵀ = ¬¬(∀ρ ¬¬E.ki)`; `E.ki = E` (QF matrix)
  let r0 : MRealizer cm ((Formula.all ρ (clE B₀ C₀))ᴺᵀ) :=
    monotone_nd_soundness eqxi spremise cm spremise_nd prf'
  have hEki : (clE B₀ C₀).kurodaInner = clE B₀ C₀ := by
    have hpe : (clE B₀ C₀).isPurelyExistential = true := by
      simp only [clE, Formula.isPurelyExistential, Formula.isQF, isQF_weakenBy, isQF_renameF,
        hB_qf, hC_qf, Bool.and_self]
    exact kurodaInner_pe _ hpe
  let r1 : MRealizer cm (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀)))) :=
    MRealizer.transport
      (congrArg (fun G : Formula F [ρ] => ¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠ G))) hEki) r0
  -- step 3: `nn_all_nn`, giving `∀ρ ¬¬E`
  MRealizer.mp cm r1 (leafM eqxi spremise cm nn_all_nn)

/-- The `U`-majorant, read off the monotone realizer's `tstar`: challenge the surviving `¬¬`
with the default `¬E`-witness majorant, read the `∃u` index. Mirror of `interpret_extractUTermP`
on the majorant side. -/
def mfiU_cl (cm : ConstMajorants am) {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (r : MRealizer cm (Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).2
    (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs, ())) ()).1.1

/-- The `V`-majorant (the `∃v` index). -/
def mfiV_cl (cm : ConstMajorants am) {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (r : MRealizer cm (Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).2
    (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs, ())) ()).1.2.1

/-- **The extraction half, classical + monotone.** From a monotone realizer of `∀ρ ¬¬E`
(`E := ∃u∃v(B₀'→C₀')`, `B₀`,`C₀` QF ∨-free), two functionals `U`, `V` majorized by
`mfiU_cl`/`mfiV_cl`, with the interpret-level content — the classical counterpart of
`mfi_extract_core`, peeling the surviving `¬¬` as `extraction_of_prenex_realizer` does. -/
theorem mfi_extract_classical (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (r : MRealizer cm (Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀)))) :
    ∃ U V : Ty.interpret X ρ → Nat,
      am.maj (ρ →ₜ Ty.nat) (mfiU_cl cm r) U ∧
      am.maj (ρ →ₜ Ty.nat) (mfiV_cl cm r) V ∧
      ∀ x : Ty.interpret X ρ,
        Formula.interpret si B₀ (U x, (x, ())) →
        Formula.interpret si C₀ (V x, (x, ())) := by
  classical
  obtain ⟨⟨xr, hx, hm⟩, hs⟩ := r.property am.N (Nat.le_refl _)
  -- QF/VFree of the weakened matrices
  have hB'_qf : (B₀.weakenBy Ty.nat).isQF = true := by
    rw [show (B₀.weakenBy Ty.nat).isQF = B₀.isQF from isQF_weakenBy B₀, hB_qf]
  have hB'_vf : (B₀.weakenBy Ty.nat).isVFree = true := by
    rw [show (B₀.weakenBy Ty.nat).isVFree = B₀.isVFree from isVFree_weakenBy B₀, hB_vf]
  have hC'_qf : (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
      (Term.Renaming.shift (σ := Ty.nat)))).isQF = true := by
    rw [show (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
      (Term.Renaming.shift (σ := Ty.nat)))).isQF = C₀.isQF from isQF_renameF _ C₀, hC_qf]
  have hC'_vf : (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
      (Term.Renaming.shift (σ := Ty.nat)))).isVFree = true := by
    rw [show (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
      (Term.Renaming.shift (σ := Ty.nat)))).isVFree = C₀.isVFree from isVFree_renameF _ C₀, hC_vf]
  -- the default `¬E`-challenge and its majorant
  let dwit : Ty.interpret X (wTy (clNegE B₀ C₀)) := Ty.interpret_default si (wTy (clNegE B₀ C₀))
  -- the semantic U, V: the projections off the existential realizer
  refine ⟨fun x => ((xr () x).2 dwit ()).1.1, fun x => ((xr () x).2 dwit ()).1.2.1, ?_, ?_, ?_⟩
  · -- `mfiU_cl` majorizes U
    refine am.arrow_intro _ _ ?_ ?_
    · intro xs x hxs
      have happ : am.maj (wTy (¬ᶠ¬ᶠ(clE B₀ C₀))) (r.val am.N () xs) (xr () x) :=
        am.app_compat _ _ _ _ (hx () () trivial) hxs
      have hd : am.maj (wTy (clNegE B₀ C₀))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs, ())) dwit := by
        have := (termMajorizer_maj cm (defaultWTerm (clNegE B₀ C₀)) am.N (Nat.le_refl _)).1
          (xs, ()) (x, ()) ⟨hxs, trivial⟩
        rwa [show Term.interpret si (defaultWTerm (clNegE B₀ C₀)) (x, ()) = dwit from by
          simp only [dwit, defaultWTerm, interpret_defaultOf]] at this
      exact am.prod_fst _ _ (am.prod_fst _ _ (am.app_compat _ _ _ _
        (am.app_compat _ _ _ _ (am.prod_snd _ _ happ) hd) am.unit_maj))
    · intro xs₁ xs₂ hxs
      have happ : am.selfMaj (wTy (¬ᶠ¬ᶠ(clE B₀ C₀))) (r.val am.N () xs₁) (r.val am.N () xs₂) :=
        am.selfMaj_app (hs () () trivial) hxs
      have hd : am.selfMaj (wTy (clNegE B₀ C₀))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs₁, ()))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs₂, ())) :=
        (termMajorizer_maj cm (defaultWTerm (clNegE B₀ C₀)) am.N (Nat.le_refl _)).2
          (xs₁, ()) (xs₂, ()) ⟨hxs, trivial⟩
      exact am.selfMaj_prod_fst _ _ (am.selfMaj_prod_fst _ _ (am.selfMaj_app
        (am.selfMaj_app (am.selfMaj_prod_snd _ _ happ) hd)
        (am.maj_selfMaj am.unit_maj)))
  · -- `mfiV_cl` majorizes V
    refine am.arrow_intro _ _ ?_ ?_
    · intro xs x hxs
      have happ : am.maj (wTy (¬ᶠ¬ᶠ(clE B₀ C₀))) (r.val am.N () xs) (xr () x) :=
        am.app_compat _ _ _ _ (hx () () trivial) hxs
      have hd : am.maj (wTy (clNegE B₀ C₀))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs, ())) dwit := by
        have := (termMajorizer_maj cm (defaultWTerm (clNegE B₀ C₀)) am.N (Nat.le_refl _)).1
          (xs, ()) (x, ()) ⟨hxs, trivial⟩
        rwa [show Term.interpret si (defaultWTerm (clNegE B₀ C₀)) (x, ()) = dwit from by
          simp only [dwit, defaultWTerm, interpret_defaultOf]] at this
      exact am.prod_fst _ _ (am.prod_snd _ _ (am.prod_fst _ _ (am.app_compat _ _ _ _
        (am.app_compat _ _ _ _ (am.prod_snd _ _ happ) hd) am.unit_maj)))
    · intro xs₁ xs₂ hxs
      have happ : am.selfMaj (wTy (¬ᶠ¬ᶠ(clE B₀ C₀))) (r.val am.N () xs₁) (r.val am.N () xs₂) :=
        am.selfMaj_app (hs () () trivial) hxs
      have hd : am.selfMaj (wTy (clNegE B₀ C₀))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs₁, ()))
          (termMajorizer cm (defaultWTerm (clNegE B₀ C₀)) am.N (xs₂, ())) :=
        (termMajorizer_maj cm (defaultWTerm (clNegE B₀ C₀)) am.N (Nat.le_refl _)).2
          (xs₁, ()) (xs₂, ()) ⟨hxs, trivial⟩
      exact am.selfMaj_prod_fst _ _ (am.selfMaj_prod_snd _ _ (am.selfMaj_prod_fst _ _
        (am.selfMaj_app (am.selfMaj_app (am.selfMaj_prod_snd _ _ happ) hd)
          (am.maj_selfMaj am.unit_maj))))
  · -- the content: peel the `¬¬`, exactly as `extraction_of_prenex_realizer`
    intro x hBx
    have key := hm () (x, (dwit, ()))
    simp only [clE, clNegE, Formula.neg, dialecticaMatrix] at key
    rw [dialecticaMatrix_iff_interpFormula si (B₀.weakenBy Ty.nat) hB'_qf hB'_vf,
        dialecticaMatrix_iff_interpFormula si
          (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
            (Term.Renaming.shift (σ := Ty.nat)))) hC'_qf hC'_vf] at key
    have hb : ∀ u v : Nat, Formula.interpret si (B₀.weakenBy Ty.nat) (v, (u, (x, ()))) =
        Formula.interpret si B₀ (u, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si (Term.Renaming.shift (σ := Ty.nat)) B₀
        (v, (u, (x, ()))) (u, (x, ())) (fun {_} _ => rfl)
    have hc : ∀ u v : Nat,
        Formula.interpret si (C₀.renameF (Term.Renaming.ext (σ := Ty.nat)
            (Term.Renaming.shift (σ := Ty.nat)))) (v, (u, (x, ()))) =
          Formula.interpret si C₀ (v, (x, ())) := fun u v =>
      Formula.interpret_renameF_gen si
        (Term.Renaming.ext (σ := Ty.nat) (Term.Renaming.shift (σ := Ty.nat))) C₀
        (v, (u, (x, ()))) (v, (x, ()))
        (fun {_} vv => match vv with | .vz => rfl | .vs _ => rfl)
    by_contra hCn
    exact key (fun himp => hCn (Eq.mp (hc _ _) (himp (Eq.mpr (hb _ _) hBx))))

/-- **The bound property, classical + monotone.** -/
theorem mfi_bound_property_classical (cm : ConstMajorants am)
    {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (r : MRealizer cm (Formula.all ρ (¬ᶠ¬ᶠ(clE B₀ C₀)))) :
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      am.toRel.maj ρ x_star x →
      (∀ u : Nat, u ≤ coreBound (mfiU_cl cm r) (mfiV_cl cm r) x_star →
        Formula.interpret si B₀ (u, (x, ()))) →
      ∃ v : Nat, v ≤ coreBound (mfiU_cl cm r) (mfiV_cl cm r) x_star ∧
        Formula.interpret si C₀ (v, (x, ())) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := mfi_extract_classical cm hB_qf hB_vf hC_qf hC_vf r
  exact metatheorem_core_of_majorants_at am.toRel
    (fun x u => Formula.interpret si B₀ (u, (x, ())))
    (fun x v => Formula.interpret si C₀ (v, (x, ())))
    U V _ _ hU hV hUV

/-- **The classical metatheorem, with the bound computed by the monotone functional
interpretation.** Same statement as `syntactic_general_metatheorem_classical_at`; `Φ` is data,
`Φ := coreBound (mfiU_cl cm r) (mfiV_cl cm r)` with `r` the classical monotone realizer.
No `negTrans_sound`, no realizer term — the ×230 classical blow-up is not incurred at
elaboration (`ARCHITECTURE.md` §14.5). -/
def monotone_general_metatheorem_classical_at
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    (spremise_nd : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → MRealizer cm (Bᴺᵀ))
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
  let r := clMRealizer eqxi spremise cm spremise_nd hB_qf hB_vf hC_qf hC_vf prf
  ⟨coreBound (mfiU_cl cm r) (mfiV_cl cm r),
   mfi_bound_property_classical cm hB_qf hB_vf hC_qf hC_vf r⟩

end ClassicalMonotone

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms clMRealizer
#print axioms mfi_extract_classical
#print axioms mfi_bound_property_classical
#print axioms monotone_general_metatheorem_classical_at

end Metatheorems
