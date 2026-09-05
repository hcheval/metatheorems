/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.NegTrans

/-!
# The fused negative-translation + monotone functional interpretation (Kohlenbach Ch. 10)

`monotone_nd_soundness` interprets a **classical** derivation directly: by structural
recursion on `Derivable F Allowed.classical Premises A` it produces a monotone realizer
(`MRealizer`) of the negative translation `Aᴺᵀ = ¬¬Aₙₜ`, without ever building the translated
derivation. This is the book's "ND-interpretation" — negative translation followed by the
(monotone) functional interpretation — done as one recursion.

## Why a fused recursion, and the strategy per case

`negTrans_sound` (`NegTrans.lean`) is a derivation-to-derivation translation: at every node it
applies a fixed closed Hilbert combinator (`neg_neg_mp`, `neg_neg_imp_rev`, …, each ~50–200
constructors) and `dnn_intro`, so a 12-constructor classical derivation becomes 85,180
constructors and reducing `monotone_soundness` through that output is a 12 GB `std::bad_alloc`
in the kernel (`Probes/ClassicalMfiProbe.lean`, Part C0). The fix is to never build that
derivation: interpret the CLASSICAL derivation directly.

The recursion mirrors `negTrans_sound`'s match arm for arm. Per node:

* the **recursive calls** produce `MRealizer cm (subᴺᵀ)`;
* they are combined with the *composition* cases of `Dialectica/Monotone.lean` — `MRealizer.mp`,
  `.syllogism`, `.exportation`, `.importation`, `.expansion`, `.forallRule`, `.existRule`,
  `.univGen`, `.induction` — which compute the majorant *semantically* and never build a term;
* the fixed closed combinators `negTrans_sound` applies — `neg_neg_mp`, `neg_neg_imp_rev`,
  `neg_neg_imp_rev2`, `dnn_intro`, `nn_all_nn`, `K_comb`, `S_comb`, and the per-case closed
  Hilbert forms (`expForm`, `impForm`, …) — are realized as **leaves** by
  `leafM d := MRealizer.ofSRealizer cm (syntactic_soundness eqxi spremise d)`. A leaf builds a
  Dialectica realizer *term* for one fixed ~200-constructor closed derivation and majorizes it
  by `termMajorizer_maj` (the "every closed term is majorizable" leaf case, Howard). That term
  is per-node bounded and never inlined into an 85k-node whole; its majorant is a semantic
  ℕ-value the kernel reduces by `max`/`+` arithmetic.

This is the brief's "plug/leaf first, measure, hand-write only what dominates". `leafM` covers
every fixed combinator; the composition cases are the hand-written spike code, reused verbatim.

## NT-stability is gone

`negTrans_sound` needs `nts : NTStableD Premises` — every premise must imply its own negative
translation — because its premise case is `.mp (.premise hp) (nts _ _ hp)`. Here the premise
case takes an `MRealizer cm Bᴺᵀ` **directly** (`spremise_nd`), so no condition on the premise
set is needed at all. For purely universal premises — every space axiom in the tree —
`spremise_nd_of_pu` supplies it from the existing syntactic premise realizer through
`negTrans_iff_pu` (interpreted as a leaf), so the space models need nothing new.
-/

namespace Metatheorems

open Formula

-- The transport equations below prove `negTrans`/`kurodaInner` commutations; `simp only` closes
-- some outright and leaves others as a defeq goal (a `weakenBy` pushed through `¬¬`, invisible
-- to the printer — trap 12), so every transport ends `<;> rfl`. The resulting linter noise
-- (some `rfl`s are then unreachable) is not worth splitting each case by hand.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

section FusedRecursion

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {Premises : PremiseSet F}

/-- The leaf strategy at a **closed** intuitionistic derivation: a monotone realizer via the
syntactic realizer's term and `termMajorizer`. Every fixed combinator `negTrans_sound` applies
is realized this way. -/
def leafM (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F Γ}
    (d : Derivable F Allowed.nt_target Premises A) : MRealizer cm A :=
  MRealizer.ofSRealizer cm (syntactic_soundness (Premises := Premises) eqxi spremise
    (d.castAllowed (by constructor <;> decide)))

-- ----------------------------------------------------------------------------
-- The rule cases with an open sub-derivation, mirrored at the MRealizer level
-- ----------------------------------------------------------------------------

/-- `eqAtType` is purely universal — a local copy of `NegTrans`'s private `eqAtType_isPU`. -/
private theorem eqAtType_isPU (ρ : Ty ι) {Γ : Ctx ι} (s t : Term F Γ ρ) :
    (eqAtType ρ s t).isPurelyUniversal = true := by
  induction ρ generalizing Γ with
  | nat => rfl
  | base i => exact eqAtType_base_isPurelyUniversal i s t
  | unit => rfl
  | prod ρ τ ih_ρ ih_τ =>
    simp only [eqAtType, Formula.isPurelyUniversal, Bool.and_eq_true]
    exact ⟨ih_ρ _ _, ih_τ _ _⟩
  | arr ρ τ ih_ρ ih_τ => simp only [eqAtType, Formula.isPurelyUniversal]; exact ih_τ _ _

-- The `eqxi`/`spremise`/`cm` triple the rule helpers all carry is written as explicit binders
-- (not `variable`s) so their order in every helper is fixed `eqxi, spremise, cm`: Lean's
-- section-variable inclusion orders body-only variables by dependency, which places them
-- inconsistently across helpers.

/-- NT respects the ∀-rule — `negTrans_forall_rule` mirrored: `ih` is the sub-derivation's NT,
`neg_neg_mp` / `dnn_intro` / `neg_neg_imp_rev` are leaves, `forall_rule` is `MRealizer.forallRule`. -/
def ndForallRule (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (ih : MRealizer cm ((B.weakenBy ρ →ᶠ A)ᴺᵀ)) :
    MRealizer cm ((B →ᶠ Formula.all ρ A)ᴺᵀ) :=
  let ih' : MRealizer cm (¬ᶠ¬ᶠ(Formula.weakenBy ρ B.kurodaInner →ᶠ A.kurodaInner)) :=
    MRealizer.transport
      (show (B.weakenBy ρ →ᶠ A)ᴺᵀ = (¬ᶠ¬ᶠ(Formula.weakenBy ρ B.kurodaInner →ᶠ A.kurodaInner)) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl) ih
  let step1 : MRealizer cm (Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner) →ᶠ ¬ᶠ¬ᶠA.kurodaInner) :=
    MRealizer.mp cm ih' (leafM eqxi spremise cm
      (neg_neg_mp (A := Formula.weakenBy ρ B.kurodaInner) (B := A.kurodaInner)))
  let step2 : MRealizer cm (¬ᶠ¬ᶠB.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)) :=
    MRealizer.forallRule cm step1
  let step3 : MRealizer cm (B.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)) :=
    MRealizer.syllogism cm (leafM eqxi spremise cm (dnn_intro (A := B.kurodaInner))) step2
  let step4 : MRealizer cm (B.kurodaInner →ᶠ ¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner))) :=
    MRealizer.syllogism cm step3
      (leafM eqxi spremise cm (dnn_intro (A := Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner))))
  MRealizer.mp cm step4 (leafM eqxi spremise cm
    (neg_neg_imp_rev (A := B.kurodaInner) (B := Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner))))

/-- NT respects the ∃-rule — `negTrans_exist_rule` mirrored. -/
def ndExistRule (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (ih : MRealizer cm ((A →ᶠ B.weakenBy ρ)ᴺᵀ)) :
    MRealizer cm ((Formula.ex ρ A →ᶠ B)ᴺᵀ) :=
  let ih' : MRealizer cm (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ Formula.weakenBy ρ B.kurodaInner)) :=
    MRealizer.transport
      (show (A →ᶠ B.weakenBy ρ)ᴺᵀ = (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ Formula.weakenBy ρ B.kurodaInner)) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl) ih
  let step1 : MRealizer cm (¬ᶠ¬ᶠA.kurodaInner →ᶠ Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner)) :=
    MRealizer.mp cm ih' (leafM eqxi spremise cm
      (neg_neg_mp (A := A.kurodaInner) (B := Formula.weakenBy ρ B.kurodaInner)))
  let step2 : MRealizer cm (A.kurodaInner →ᶠ Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner)) :=
    MRealizer.syllogism cm (leafM eqxi spremise cm (dnn_intro (A := A.kurodaInner))) step1
  let step3 : MRealizer cm (Formula.ex ρ A.kurodaInner →ᶠ ¬ᶠ¬ᶠB.kurodaInner) :=
    MRealizer.existRule cm step2
  MRealizer.mp cm step3 (leafM eqxi spremise cm
    (neg_neg_imp_rev (A := Formula.ex ρ A.kurodaInner) (B := B.kurodaInner)))

/-- NT respects universal generalisation — `negTrans_univ_gen` mirrored, via `MRealizer.univGen`. -/
def ndUnivGen (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F Γ}
    (ih : MRealizer cm (Aᴺᵀ)) :
    MRealizer cm ((Formula.all ρ (A.weakenBy ρ))ᴺᵀ) :=
  let u : MRealizer cm (Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ)) :=
    MRealizer.univGen cm ih
  let r : MRealizer cm (¬ᶠ¬ᶠ(Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ))) :=
    MRealizer.mp cm u (leafM eqxi spremise cm
      (dnn_intro (A := Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ))))
  MRealizer.transport
    (show (¬ᶠ¬ᶠ(Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ)))
        = (Formula.all ρ (A.weakenBy ρ))ᴺᵀ by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl) r

/-- NT respects QF-ER — the inline `qfer` case of `negTrans_sound` mirrored. `nn_imp_extract`
is private to `NegTrans.lean`, so it is rebuilt inline here from public combinators; the
QF-ER step is `MRealizer.qfer`, and the `eqAtType`-equivalences are `negTrans_iff_pu` leaves. -/
def ndQfer (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ σ : Ty ι} {A₀ : Formula F Γ} {s t : Term F Γ ρ}
    {r : Term F (ρ :: Γ) σ} (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (ih : MRealizer cm ((A₀ →ᶠ eqAtType ρ s t)ᴺᵀ)) :
    MRealizer cm ((A₀ →ᶠ eqAtType σ (Term.subst0 r s) (Term.subst0 r t))ᴺᵀ) :=
  let eqρ := eqAtType ρ s t
  let eqσ := eqAtType σ (r.subst0 s) (r.subst0 t)
  let ih' : MRealizer cm (¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner)) :=
    MRealizer.transport
      (show (A₀ →ᶠ eqρ)ᴺᵀ = (¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner)) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_qf A₀ hqf] <;> rfl) ih
  -- `nn_imp_extract : ¬¬(A₀ → eq.ki) → A₀ → ¬¬eq.ki`, rebuilt inline (public combinators)
  let nn_imp_extract : Derivable F Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner) →ᶠ A₀ →ᶠ ¬ᶠ¬ᶠeqρ.kurodaInner) :=
    let get_nn_imp : Derivable F Allowed.nt_target Premises
        (¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner) ∧ᶠ A₀ →ᶠ ¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner)) := .and_weak
    let get_nn_a : Derivable F Allowed.nt_target Premises
        (¬ᶠ¬ᶠ(A₀ →ᶠ eqρ.kurodaInner) ∧ᶠ A₀ →ᶠ ¬ᶠ¬ᶠA₀) :=
      .syllogism (.syllogism .and_perm .and_weak) dnn_intro
    .exportation (.syllogism (pair_h get_nn_imp get_nn_a) (.importation neg_neg_mp))
  let step1 : MRealizer cm (A₀ →ᶠ ¬ᶠ¬ᶠeqρ.kurodaInner) :=
    MRealizer.mp cm ih' (leafM eqxi spremise cm nn_imp_extract)
  let bwd : Derivable F Allowed.nt_target Premises (eqρᴺᵀ →ᶠ eqρ) :=
    (negTrans_iff_pu eqρ (eqAtType_isPU ρ s t)).2
  let step2 : MRealizer cm (A₀ →ᶠ eqρ) :=
    MRealizer.syllogism cm step1 (leafM eqxi spremise cm bwd)
  let step3 : MRealizer cm (A₀ →ᶠ eqσ) :=
    MRealizer.qfer cm eqxi hqf hvf step2
  let fwd : Derivable F Allowed.nt_target Premises (eqσ →ᶠ eqσᴺᵀ) :=
    (negTrans_iff_pu eqσ (eqAtType_isPU σ (r.subst0 s) (r.subst0 t))).1
  let step4 : MRealizer cm (A₀ →ᶠ ¬ᶠ¬ᶠeqσ.kurodaInner) :=
    MRealizer.syllogism cm step3 (leafM eqxi spremise cm fwd)
  MRealizer.transport
    (show (¬ᶠ¬ᶠ(A₀ →ᶠ eqσ.kurodaInner)) = (A₀ →ᶠ eqσ)ᴺᵀ by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_qf A₀ hqf] <;> rfl)
    (MRealizer.mp cm step4
      (leafM eqxi spremise cm (neg_neg_imp_rev (A := A₀) (B := eqσ.kurodaInner))))

/-- NT respects induction — `negTrans_induction` mirrored, via `MRealizer.induction` (the
book's `t^M`). `nn_all_nn` / `dnn_intro` / the closed `forall_rule inner` are leaves; the
recursion itself is `MRealizer.induction`. -/
def ndInduction (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    {Γ : Ctx ι} {A : Formula F (Ty.nat :: Γ)}
    (ih_zero : MRealizer cm ((A.subst0 Term.zero)ᴺᵀ))
    (ih_step : MRealizer cm ((Formula.all Ty.nat
      (A →ᶠ A.substVar0 (Term.app Term.succ (.var .vz))))ᴺᵀ)) :
    MRealizer cm ((Formula.all Ty.nat A)ᴺᵀ) :=
  let Ak := A.kurodaInner
  let Asv := Ak.substVar0 (Term.app Term.succ (.var .vz))
  let ih_zero' : MRealizer cm (¬ᶠ¬ᶠ(Ak.subst0 Term.zero)) :=
    MRealizer.transport
      (show (A.subst0 Term.zero)ᴺᵀ = (¬ᶠ¬ᶠ(Ak.subst0 Term.zero)) by
        simp only [Formula.negTrans, kurodaInner_subst0] <;> rfl) ih_zero
  let ih_step' : MRealizer cm (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(Ak →ᶠ Asv)))) :=
    MRealizer.transport
      (show (Formula.all Ty.nat (A →ᶠ A.substVar0 (Term.app Term.succ (.var .vz))))ᴺᵀ
          = (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(Ak →ᶠ Asv)))) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_substVar0] <;> rfl) ih_step
  -- ∀n ¬¬(Ak → Asv), by `nn_all_nn`
  let step_all : MRealizer cm (Formula.all Ty.nat (¬ᶠ¬ᶠ(Ak →ᶠ Asv))) :=
    MRealizer.mp cm ih_step' (leafM eqxi spremise cm nn_all_nn)
  -- the closed `forall_rule inner`, copied from `negTrans_induction`
  let Q₀ : Formula F (Ty.nat :: Γ) := ¬ᶠ¬ᶠ(Ak →ᶠ Asv)
  let inst2 : Derivable F Allowed.nt_target Premises ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ Q₀) := by
    have hbody : ∀ {τ : Ty ι} (v : Var (Ty.nat :: Γ) τ),
        Term.subst0_map (F := F) (.var .vz) (Renaming.ext Renaming.shift v) = Term.var v := by
      intro _ v; cases v with
      | vz   => rfl
      | vs w => simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]
    have heq2 : (Formula.renameF (Renaming.ext Renaming.shift) Q₀).subst0 (.var .vz) = Q₀ :=
      Formula.substF_renameF_id (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz)) hbody Q₀
    have h' := @Derivable.forall_ax ι κ F Allowed.nt_target Premises (Ty.nat :: Γ) Ty.nat
                 (Formula.renameF (Renaming.ext Renaming.shift) Q₀) (.var .vz)
    rw [heq2] at h'; exact h'
  let inner : Derivable F Allowed.nt_target Premises
      ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ (¬ᶠ¬ᶠAk →ᶠ ¬ᶠ¬ᶠAsv)) :=
    Derivable.syllogism inst2 neg_neg_mp
  let ind_step : MRealizer cm (Formula.all Ty.nat (¬ᶠ¬ᶠAk →ᶠ ¬ᶠ¬ᶠAsv)) :=
    MRealizer.mp cm step_all (leafM eqxi spremise cm (Derivable.forall_rule inner))
  let nn_all : MRealizer cm (Formula.all Ty.nat (¬ᶠ¬ᶠAk)) :=
    MRealizer.induction cm ih_zero' ind_step
  MRealizer.mp cm nn_all (leafM eqxi spremise cm (dnn_intro (A := Formula.all Ty.nat (¬ᶠ¬ᶠAk))))

end FusedRecursion

-- ============================================================================
-- The recursion over the classical derivation
-- ============================================================================

section Soundness

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {Premises : PremiseSet F}

/-- **The fused negative-translation + monotone functional interpretation.** By structural
recursion on a classical derivation, a monotone realizer of its negative translation. Every
constructor is treated; the strategy is in the module header. No `NTStableD` hypothesis: the
premise case takes an `MRealizer cm Bᴺᵀ` directly (`spremise_nd`). -/
def monotone_nd_soundness (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    (spremise_nd : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      MRealizer cm (Bᴺᵀ)) :
    {Γ : Ctx ι} → {A : Formula F Γ} →
    @Derivable ι κ F Allowed.classical Premises Γ A → MRealizer cm Aᴺᵀ
  -- premises: the negative-translated premise realizer, supplied directly (no NT-stability)
  | _, _, .premise hp => spremise_nd _ _ hp
  -- simple propositional axioms: `dnn_intro` composed with the axiom, as a leaf
  | _, _, .or_contract  => leafM eqxi spremise cm (.mp .or_contract  dnn_intro)
  | _, _, .and_contract => leafM eqxi spremise cm (.mp .and_contract dnn_intro)
  | _, _, .or_weak      => leafM eqxi spremise cm (.mp .or_weak      dnn_intro)
  | _, _, .and_weak     => leafM eqxi spremise cm (.mp .and_weak     dnn_intro)
  | _, _, .or_perm      => leafM eqxi spremise cm (.mp .or_perm      dnn_intro)
  | _, _, .and_perm     => leafM eqxi spremise cm (.mp .and_perm     dnn_intro)
  | _, _, .exfalso      => leafM eqxi spremise cm (.mp .exfalso      dnn_intro)
  | _, _, .refl0        => leafM eqxi spremise cm (.mp .refl0        dnn_intro)
  | _, _, .sym0         => leafM eqxi spremise cm (.mp .sym0         dnn_intro)
  | _, _, .trans0       => leafM eqxi spremise cm (.mp .trans0       dnn_intro)
  -- forall_ax / exist_ax: closed, whole NT is a leaf
  | _, _, .forall_ax t  => leafM eqxi spremise cm (negTrans_forall_ax t)
  | _, _, .exist_ax t _ => leafM eqxi spremise cm (negTrans_exist_ax t)
  -- mp: `.mp (nt hA) (.mp (nt hAB) neg_neg_mp)` — the two `.mp`s are MRealizer compositions,
  -- `neg_neg_mp` is a leaf
  | _, _, .mp (A := A) (B := B) hA hAB =>
      .mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hA)
        (.mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hAB)
          (leafM eqxi spremise cm (neg_neg_mp
            (A := A.kurodaInner) (B := B.kurodaInner))))
  -- syllogism: `.mp step_AB (.mp step_BC_K S_comb)` then `neg_neg_imp_rev2`, all mirrored
  | _, _, .syllogism (A := A) (B := B) (C := C) hAB hBC =>
      let ihAB := monotone_nd_soundness eqxi spremise cm spremise_nd hAB
      let ihBC := monotone_nd_soundness eqxi spremise cm spremise_nd hBC
      let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
      let step_AB := MRealizer.mp cm ihAB (leafM eqxi spremise cm (neg_neg_mp (A := ntA) (B := ntB)))
      let step_BC := MRealizer.mp cm ihBC (leafM eqxi spremise cm (neg_neg_mp (A := ntB) (B := ntC)))
      let step_BC_K := MRealizer.mp cm step_BC
        (leafM eqxi spremise cm (K_comb (A := ¬ᶠ¬ᶠntB →ᶠ ¬ᶠ¬ᶠntC) (B := ¬ᶠ¬ᶠntA)))
      let s1 := MRealizer.mp cm step_BC_K
        (leafM eqxi spremise cm (S_comb (A := ¬ᶠ¬ᶠntA) (B := ¬ᶠ¬ᶠntB) (C := ¬ᶠ¬ᶠntC)))
      let s2 := MRealizer.mp cm step_AB s1
      MRealizer.mp cm s2 (leafM eqxi spremise cm (neg_neg_imp_rev2 (A := ntA) (B := ntC)))
  -- exportation: the closed form `exp_form` composed by `dnn_intro`+`neg_neg_mp` from `ih`
  | _, _, .exportation (A := A) (B := B) (C := C) h_inner =>
      let ih := monotone_nd_soundness eqxi spremise cm spremise_nd h_inner
      let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
      let get_f   := Derivable.syllogism .and_weak .and_weak
      let get_ntA := Derivable.syllogism .and_weak (.syllogism .and_perm .and_weak)
      let get_ntB := Derivable.syllogism .and_perm .and_weak
      let get_ntAB := pair_h get_ntA get_ntB
      let get_ntC := eval_h get_f get_ntAB
      let exp1    := Derivable.exportation get_ntC
      let exp_form : Derivable F Allowed.nt_target Premises
          ((ntA ∧ᶠ ntB →ᶠ ntC) →ᶠ ntA →ᶠ ntB →ᶠ ntC) := Derivable.exportation exp1
      MRealizer.mp cm ih (MRealizer.mp cm (leafM eqxi spremise cm (Derivable.mp exp_form dnn_intro))
        (leafM eqxi spremise cm (neg_neg_mp (A := ntA ∧ᶠ ntB →ᶠ ntC) (B := ntA →ᶠ ntB →ᶠ ntC))))
  -- importation: mirror of `negTrans_importation`
  | _, _, .importation (A := A) (B := B) (C := C) h_inner =>
      let ih := monotone_nd_soundness eqxi spremise cm spremise_nd h_inner
      let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
      let get_f : Derivable F Allowed.nt_target Premises
          ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntA →ᶠ ntB →ᶠ ntC) := .and_weak
      let get_ntAB := Derivable.syllogism .and_perm .and_weak
      let get_ntA := Derivable.syllogism get_ntAB .and_weak
      let get_ntB := Derivable.syllogism get_ntAB (.syllogism .and_perm .and_weak)
      let get_bc := eval_h get_f get_ntA
      let get_c  := eval_h get_bc get_ntB
      let imp_form : Derivable F Allowed.nt_target Premises
          ((ntA →ᶠ ntB →ᶠ ntC) →ᶠ ntA ∧ᶠ ntB →ᶠ ntC) := Derivable.exportation get_c
      MRealizer.mp cm ih (MRealizer.mp cm (leafM eqxi spremise cm (Derivable.mp imp_form dnn_intro))
        (leafM eqxi spremise cm (neg_neg_mp (A := ntA →ᶠ ntB →ᶠ ntC) (B := ntA ∧ᶠ ntB →ᶠ ntC))))
  -- expansion: mirror of `negTrans_expansion`
  | _, _, .expansion (A := A) (B := B) (C := C) h_inner =>
      let ih := monotone_nd_soundness eqxi spremise cm spremise_nd h_inner
      let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
      let case_C : Derivable F Allowed.nt_target Premises (ntC →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
        .exportation (.syllogism .and_weak .or_weak)
      let case_A : Derivable F Allowed.nt_target Premises (ntA →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
        .exportation (.syllogism (eval_h (.syllogism .and_perm .and_weak) .and_weak) or_inr)
      let rvp_to  := or_elim_rule case_C case_A
      let exp_form : Derivable F Allowed.nt_target Premises
          ((ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntA →ᶠ ntC ∨ᶠ ntB) := .mp rvp_to flip_comb
      MRealizer.mp cm ih (MRealizer.mp cm (leafM eqxi spremise cm (Derivable.mp exp_form dnn_intro))
        (leafM eqxi spremise cm (neg_neg_mp (A := ntA →ᶠ ntB) (B := ntC ∨ᶠ ntA →ᶠ ntC ∨ᶠ ntB))))
  -- forall_rule / exist_rule / univ_gen / qfer / induction: whole NT is closed given the
  -- sub-derivation's NT — but the sub-derivation's NT is recursive, so we cannot use a leaf
  -- on the whole thing. Instead: build the negative-translated *derivation* of the sub-goal
  -- as a leaf-free term via the recursion, then let `syntactic_soundness` majorize the fixed
  -- combinator wrapper. Since these wrappers are FIXED closed transformations that take one
  -- open derivation, we mirror them at the MRealizer level (below).
  | _, _, .forall_rule (ρ := ρ) (B := B) (A := A_inner) h_inner =>
      ndForallRule eqxi spremise cm (monotone_nd_soundness eqxi spremise cm spremise_nd h_inner)
  | _, _, .exist_rule (ρ := ρ) (B := B) (A := A_inner) h_inner =>
      ndExistRule eqxi spremise cm (monotone_nd_soundness eqxi spremise cm spremise_nd h_inner)
  | _, _, .univ_gen (ρ := ρ) (A := A_inner) h_inner =>
      ndUnivGen eqxi spremise cm (monotone_nd_soundness eqxi spremise cm spremise_nd h_inner)
  -- axioms with ∀ inside / equational / pseudometric: whole NT is a closed leaf
  | _, _, .succ_ne_zero     => leafM eqxi spremise cm negTrans_succ_ne_zero
  | _, _, .succ_inj         => leafM eqxi spremise cm negTrans_succ_inj
  | _, _, .rec_zero         => leafM eqxi spremise cm negTrans_rec_zero
  | _, _, .rec_succ         => leafM eqxi spremise cm negTrans_rec_succ
  | _, _, .beta_eq body u   => leafM eqxi spremise cm negTrans_beta_eq
  | _, _, .pair_fst a b     => leafM eqxi spremise cm negTrans_pair_fst
  | _, _, .pair_snd a b     => leafM eqxi spremise cm negTrans_pair_snd
  | _, _, .pair_eta p       => leafM eqxi spremise cm negTrans_pair_eta
  | _, _, .dist_self i x    => leafM eqxi spremise cm (negTrans_dist_self i x)
  | _, _, .dist_comm i x y  => leafM eqxi spremise cm (negTrans_dist_comm i x y)
  | _, _, .dist_tri i x y z => leafM eqxi spremise cm (negTrans_dist_tri i x y z)
  -- QF-ER: mirror `negTrans_qfer`
  | _, _, .qfer (ρ := ρ) (σ := σ) (s := s) (t := t) (r := r) hqf hvf h_inner =>
      ndQfer eqxi spremise cm hqf hvf
        (monotone_nd_soundness eqxi spremise cm spremise_nd h_inner)
  -- induction: mirror `negTrans_induction`
  | _, _, .induction (A := A_inner) h_zero h_step =>
      ndInduction eqxi spremise cm
        (monotone_nd_soundness eqxi spremise cm spremise_nd h_zero)
        (monotone_nd_soundness eqxi spremise cm spremise_nd h_step)
  -- extension principles
  | _, _, .lem _            => leafM eqxi spremise cm (negTrans_lem _)
  | _, _, .qfac _ hqf hvf   => leafM eqxi spremise cm (negTrans_qfac hqf hvf)
  | _, _, .ac h ..          => absurd h (by decide)
  | _, _, .markov h ..      => absurd h (by decide)
  | _, _, .ip h ..          => absurd h (by decide)

/-- **The premise adapter for purely universal premise sets.** Every space axiom is purely
universal, so `Bᴺᵀ` is equivalent to `B` (`negTrans_iff_pu`), and the negatively-translated
premise realizer `monotone_nd_soundness` needs is the existing syntactic one composed with the
closed `B →ᶠ Bᴺᵀ` leaf. So the space models supply nothing new: `spremise` and a
purely-universal witness are enough. -/
def spremise_nd_of_pu (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)
    (pu : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true) :
    ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → MRealizer cm (Bᴺᵀ) :=
  fun Γ' B hp => MRealizer.mp cm (MRealizer.ofSRealizer cm (spremise Γ' B hp))
    (leafM eqxi spremise cm (negTrans_iff_pu B (pu Γ' B hp)).1)

end Soundness

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms leafM
#print axioms monotone_nd_soundness
#print axioms spremise_nd_of_pu
#print axioms ndForallRule
#print axioms ndExistRule
#print axioms ndUnivGen
#print axioms ndQfer
#print axioms ndInduction

end Metatheorems
