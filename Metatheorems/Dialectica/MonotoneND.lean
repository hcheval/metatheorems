/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.Dialectica.MonotoneNDLeaves
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
  `.syllogism`, `.forallRule`, `.existRule`, `.univGen`, `.induction`, `.qfer` — which compute
  the majorant *semantically* and never build a term;
* the fixed `¬¬`-combinators `negTrans_sound` applies at every node — `dnn_intro`,
  `neg_neg_mp`, `neg_neg_imp_rev`, `neg_neg_imp_rev2`, `nn_all_nn`, the exportation /
  importation / expansion forms and `dnn_lem` — are **hand-written monotone realizers**
  (`Dialectica/MonotoneNDLeaves.lean`: `dnnIntroF`, `nnMpF`, `nnImpRevF`, `expF`, `impF`,
  `expansionF`, `dnnLemF`; `neg_neg_imp_rev2` and `K`/`S` are eliminated — `syllogism`
  composes `MRealizer.syllogism` with `dnnIntroF` and `nnImpRevF` — and `nn_all_nn` is
  assembled from them as `nnAllNnF`). Their majorants are hat-level λ-terms, so per node the
  kernel β-reduces a few small closures instead of running `termMajorizer` over a
  `syntactic_soundness` term of a 100–200-node Hilbert derivation several times per node —
  which is what the first version of this file did (`leafM` on every combinator) and what made
  the classical bound's kernel reduction a 12 GB `std::bad_alloc`: `prenexify`'s 347 nodes are
  134 `syllogism`s (5 leaves each), 34 exportations, 30 importations, 11 `forall_rule`s.
* **`leafM` (`ofSRealizer ∘ syntactic_soundness`, the term route on one closed derivation)
  survives only for**: the propositional axioms' own terms (`sAndWeak`, … — fixed tiny
  combinators, the same as `monotone_soundness` uses; wrapped in `dnnIntroF`), the
  `forall_ax`/`exist_ax` terms (`sForallAx t`/`sExistAx t` — one `lam` around `t`), and the
  cases NOT on the classical gate route: `succ_ne_zero`, `succ_inj`, the equational axioms
  (`rec_*`, `beta_eq`, `pair_*`), the pseudometric axioms, `qfac`, and the two
  `negTrans_iff_pu` legs of `qfer`. Those are left as leaves deliberately and are listed here
  so nobody mistakes them for hand-written ones.

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

/-- The leaf strategy at a **closed** derivation: a monotone realizer via the syntactic
realizer's term and `termMajorizer` — the term route on that one derivation. Used only where
the module header says. -/
def leafM (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F Γ}
    (d : Derivable F Allowed.nt_target Premises A) : MRealizer cm A :=
  MRealizer.ofSRealizer cm (syntactic_soundness (Premises := Premises) eqxi spremise
    (d.castAllowed (by constructor <;> decide)))

-- ----------------------------------------------------------------------------
-- The `¬¬`-combinators as transformations (one `MRealizer.mp` each)
-- ----------------------------------------------------------------------------

/-- `A ⊢ ¬¬A`. -/
def MRealizer.dnn (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F Γ}
    (h : MRealizer cm A) : MRealizer cm (¬ᶠ¬ᶠA) :=
  MRealizer.mp cm h (MRealizer.dnnIntroF cm A)

/-- `¬¬(A → B) ⊢ ¬¬A → ¬¬B`. -/
def MRealizer.nnMp (cm : ConstMajorants am) {Γ : Ctx ι} {A B : Formula F Γ}
    (h : MRealizer cm (¬ᶠ¬ᶠ(A →ᶠ B))) : MRealizer cm (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) :=
  MRealizer.mp cm h (MRealizer.nnMpF cm A B)

/-- `A → ¬¬B ⊢ ¬¬(A → B)`. -/
def MRealizer.nnImpRev (cm : ConstMajorants am) {Γ : Ctx ι} {A B : Formula F Γ}
    (h : MRealizer cm (A →ᶠ ¬ᶠ¬ᶠB)) : MRealizer cm (¬ᶠ¬ᶠ(A →ᶠ B)) :=
  MRealizer.mp cm h (MRealizer.nnImpRevF cm A B)

/-- `¬¬A → ¬¬B ⊢ ¬¬(A → B)` — `neg_neg_imp_rev2`, as `nnImpRev` after precomposing `dnn_intro`. -/
def MRealizer.nnImpRev2 (cm : ConstMajorants am) {Γ : Ctx ι} {A B : Formula F Γ}
    (h : MRealizer cm (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB)) : MRealizer cm (¬ᶠ¬ᶠ(A →ᶠ B)) :=
  MRealizer.nnImpRev cm (MRealizer.syllogism cm (MRealizer.dnnIntroF cm A) h)

/-- `(Q.renameF (ext shift)).subst0 vz = Q` — the identity behind `forall_ax` at the variable. -/
theorem renameF_ext_shift_subst0_vz {Γ : Ctx ι} {ρ : Ty ι} (Q : Formula F (ρ :: Γ)) :
    (Q.renameF (Renaming.ext Renaming.shift)).subst0 (.var .vz) = Q :=
  Formula.substF_renameF_id (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
    (fun {_} v => match v with
      | .vz => rfl
      | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]) Q

/-- **`nn_all_nn` as a formula**: `¬¬(∀x ¬¬Q) → ∀x ¬¬Q`, assembled from `nnImpRev`, `nnMp` and
`MRealizer.forallRule` around one `sForallAx` leaf — the object-level `nn_all_nn` is 274
constructors, almost all of them `neg_neg_imp_rev` and `neg_neg_mp`. -/
def MRealizer.nnAllNnF (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι}
    (Q : Formula F (ρ :: Γ)) :
    MRealizer cm (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠQ)) →ᶠ Formula.all ρ (¬ᶠ¬ᶠQ)) :=
  let inst : MRealizer cm ((Formula.all ρ (¬ᶠ¬ᶠQ)).weakenBy ρ →ᶠ ¬ᶠ¬ᶠQ) :=
    MRealizer.transport
      (show (Formula.all ρ ((¬ᶠ¬ᶠQ).renameF (Renaming.ext Renaming.shift)) →ᶠ
            ((¬ᶠ¬ᶠQ).renameF (Renaming.ext Renaming.shift)).subst0 (.var .vz))
          = ((Formula.all ρ (¬ᶠ¬ᶠQ)).weakenBy ρ →ᶠ ¬ᶠ¬ᶠQ) by
        rw [renameF_ext_shift_subst0_vz]; rfl)
      (MRealizer.ofSRealizer cm (sForallAx (A := (¬ᶠ¬ᶠQ).renameF (Renaming.ext Renaming.shift))
        (.var .vz)))
  let step : MRealizer cm (Formula.weakenBy ρ (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠQ))) →ᶠ ¬ᶠ¬ᶠQ) :=
    MRealizer.nnMp cm (MRealizer.nnImpRev cm inst)
  MRealizer.forallRule cm step

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

-- The `eqxi`/`spremise`/`cm` triple the rule helpers carry is written as explicit binders (not
-- `variable`s) so their order in every helper is fixed `eqxi, spremise, cm`: Lean's
-- section-variable inclusion orders body-only variables by dependency, which places them
-- inconsistently across helpers.

/-- NT respects the ∀-rule — `negTrans_forall_rule` mirrored with the hand-written combinators:
`neg_neg_mp` ↦ `nnMp`, `dnn_intro` ↦ `dnnIntroF`, `neg_neg_imp_rev` ↦ `nnImpRev`, `forall_rule`
↦ `MRealizer.forallRule`. -/
def ndForallRule (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (ih : MRealizer cm ((B.weakenBy ρ →ᶠ A)ᴺᵀ)) :
    MRealizer cm ((B →ᶠ Formula.all ρ A)ᴺᵀ) :=
  let ih' : MRealizer cm (¬ᶠ¬ᶠ(Formula.weakenBy ρ B.kurodaInner →ᶠ A.kurodaInner)) :=
    MRealizer.transport
      (show (B.weakenBy ρ →ᶠ A)ᴺᵀ = (¬ᶠ¬ᶠ(Formula.weakenBy ρ B.kurodaInner →ᶠ A.kurodaInner)) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl) ih
  let step1 : MRealizer cm (Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner) →ᶠ ¬ᶠ¬ᶠA.kurodaInner) :=
    MRealizer.nnMp cm ih'
  let step2 : MRealizer cm (¬ᶠ¬ᶠB.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)) :=
    MRealizer.forallRule cm step1
  let step3 : MRealizer cm (B.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)) :=
    MRealizer.syllogism cm (MRealizer.dnnIntroF cm B.kurodaInner) step2
  let step4 : MRealizer cm (B.kurodaInner →ᶠ ¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner))) :=
    MRealizer.syllogism cm step3 (MRealizer.dnnIntroF cm (Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)))
  MRealizer.nnImpRev cm step4

/-- NT respects the ∃-rule — `negTrans_exist_rule` mirrored. -/
def ndExistRule (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (ih : MRealizer cm ((A →ᶠ B.weakenBy ρ)ᴺᵀ)) :
    MRealizer cm ((Formula.ex ρ A →ᶠ B)ᴺᵀ) :=
  let ih' : MRealizer cm (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ Formula.weakenBy ρ B.kurodaInner)) :=
    MRealizer.transport
      (show (A →ᶠ B.weakenBy ρ)ᴺᵀ = (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ Formula.weakenBy ρ B.kurodaInner)) by
        simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl) ih
  let step1 : MRealizer cm (¬ᶠ¬ᶠA.kurodaInner →ᶠ Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner)) :=
    MRealizer.nnMp cm ih'
  let step2 : MRealizer cm (A.kurodaInner →ᶠ Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner)) :=
    MRealizer.syllogism cm (MRealizer.dnnIntroF cm A.kurodaInner) step1
  let step3 : MRealizer cm (Formula.ex ρ A.kurodaInner →ᶠ ¬ᶠ¬ᶠB.kurodaInner) :=
    MRealizer.existRule cm step2
  MRealizer.nnImpRev cm step3

/-- NT respects universal generalisation — `negTrans_univ_gen` mirrored, via `MRealizer.univGen`. -/
def ndUnivGen (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F Γ}
    (ih : MRealizer cm (Aᴺᵀ)) :
    MRealizer cm ((Formula.all ρ (A.weakenBy ρ))ᴺᵀ) :=
  let u : MRealizer cm (Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ)) :=
    MRealizer.univGen cm ih
  MRealizer.transport
    (show (¬ᶠ¬ᶠ(Formula.all ρ ((¬ᶠ¬ᶠA.kurodaInner).weakenBy ρ)))
        = (Formula.all ρ (A.weakenBy ρ))ᴺᵀ by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] <;> rfl)
    (MRealizer.dnn cm u)

/-- NT respects QF-ER — the inline `qfer` case of `negTrans_sound` mirrored. `nn_imp_extract`
(`¬¬(A₀ → E) → A₀ → ¬¬E`) is `dnnIntroF` composed with `nnMp`; the QF-ER step is
`MRealizer.qfer`; the two `eqAtType`-equivalences (`negTrans_iff_pu`) stay leaves — `qfer` is
not on the classical gate route. -/
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
  let step1 : MRealizer cm (A₀ →ᶠ ¬ᶠ¬ᶠeqρ.kurodaInner) :=
    MRealizer.syllogism cm (MRealizer.dnnIntroF cm A₀) (MRealizer.nnMp cm ih')
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
    (MRealizer.nnImpRev cm step4)

/-- NT respects induction — `negTrans_induction` mirrored, via `MRealizer.induction` (the
book's `t^M`): `nn_all_nn` ↦ `nnAllNnF`, the closed `inner` ↦ `sForallAx` composed with the
formula-level `nnMpF`, `dnn_intro` ↦ `dnn`. -/
def ndInduction (cm : ConstMajorants am)
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
  let Q₀ : Formula F (Ty.nat :: Γ) := ¬ᶠ¬ᶠ(Ak →ᶠ Asv)
  let step_all : MRealizer cm (Formula.all Ty.nat Q₀) :=
    MRealizer.mp cm ih_step' (MRealizer.nnAllNnF cm (Ak →ᶠ Asv))
  let inst2 : MRealizer cm ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ Q₀) :=
    MRealizer.transport
      (show (Formula.all Ty.nat (Q₀.renameF (Renaming.ext Renaming.shift)) →ᶠ
            (Q₀.renameF (Renaming.ext Renaming.shift)).subst0 (.var .vz))
          = ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ Q₀) by
        rw [renameF_ext_shift_subst0_vz]; rfl)
      (MRealizer.ofSRealizer cm (sForallAx (A := Q₀.renameF (Renaming.ext Renaming.shift))
        (.var .vz)))
  let inner : MRealizer cm (Formula.weakenBy Ty.nat (Formula.all Ty.nat Q₀) →ᶠ
      (¬ᶠ¬ᶠAk →ᶠ ¬ᶠ¬ᶠAsv)) :=
    MRealizer.syllogism cm inst2 (MRealizer.nnMpF cm Ak Asv)
  let ind_step : MRealizer cm (Formula.all Ty.nat (¬ᶠ¬ᶠAk →ᶠ ¬ᶠ¬ᶠAsv)) :=
    MRealizer.mp cm step_all (MRealizer.forallRule cm inner)
  let nn_all : MRealizer cm (Formula.all Ty.nat (¬ᶠ¬ᶠAk)) :=
    MRealizer.induction cm ih_zero' ind_step
  MRealizer.dnn cm nn_all

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
  -- propositional axioms: the axiom's own realizer (`max`/leaf as in `monotone_soundness`),
  -- wrapped in `dnnIntroF`
  | _, _, .or_contract  => .dnn cm (.orContract cm _)
  | _, _, .and_contract => .dnn cm (.andContract cm _)
  | _, _, .or_weak      => .dnn cm (.ofSRealizer cm sOrWeak)
  | _, _, .and_weak     => .dnn cm (.ofSRealizer cm sAndWeak)
  | _, _, .or_perm      => .dnn cm (.orPerm cm _ _)
  | _, _, .and_perm     => .dnn cm (.ofSRealizer cm sAndPerm)
  | _, _, .exfalso      => .dnn cm (.ofSRealizer cm sExfalso)
  | _, _, .refl0        => .dnn cm (.ofSRealizer cm sRefl0)
  | _, _, .sym0         => .dnn cm (.ofSRealizer cm sSym0)
  | _, _, .trans0       => .dnn cm (.ofSRealizer cm sTrans0)
  -- forall_ax: `neg_neg_imp_rev` on the axiom at `¬¬Aₙₜ`; exist_ax: `dnn_intro` on the axiom
  | _, _, .forall_ax (A := A_body) t =>
      MRealizer.transport
        (show (¬ᶠ¬ᶠ(Formula.all _ (¬ᶠ¬ᶠA_body.kurodaInner) →ᶠ A_body.kurodaInner.subst0 t))
            = (Formula.all _ A_body →ᶠ A_body.subst0 t)ᴺᵀ by
          simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_subst0] <;> rfl)
        (.nnImpRev cm (.ofSRealizer cm (sForallAx (A := ¬ᶠ¬ᶠA_body.kurodaInner) t)))
  | _, _, .exist_ax t A_body =>
      MRealizer.transport
        (show (¬ᶠ¬ᶠ(A_body.kurodaInner.subst0 t →ᶠ Formula.ex _ A_body.kurodaInner))
            = (A_body.subst0 t →ᶠ Formula.ex _ A_body)ᴺᵀ by
          simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_subst0] <;> rfl)
        (.dnn cm (.ofSRealizer cm (sExistAx (A := A_body.kurodaInner) t)))
  -- mp: `¬¬(A→B)` ⊢ `¬¬A → ¬¬B`, then modus ponens
  | _, _, .mp hA hAB =>
      .mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hA)
        (.nnMp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hAB))
  -- syllogism: compose `¬¬A → ¬¬B` and `¬¬B → ¬¬C`, then `neg_neg_imp_rev2`
  | _, _, .syllogism hAB hBC =>
      .nnImpRev2 cm (.syllogism cm
        (.nnMp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hAB))
        (.nnMp cm (monotone_nd_soundness eqxi spremise cm spremise_nd hBC)))
  -- exportation / importation / expansion: `¬¬P ⊢ ¬¬Q` through the closed form `P → Q`
  | _, _, .exportation (A := A) (B := B) (C := C) h' =>
      .mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
        (.nnMp cm (.dnn cm (.expF cm A.kurodaInner B.kurodaInner C.kurodaInner)))
  | _, _, .importation (A := A) (B := B) (C := C) h' =>
      .mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
        (.nnMp cm (.dnn cm (.impF cm A.kurodaInner B.kurodaInner C.kurodaInner)))
  | _, _, .expansion (A := A) (B := B) (C := C) h' =>
      .mp cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
        (.nnMp cm (.dnn cm (.expansionF cm A.kurodaInner B.kurodaInner C.kurodaInner)))
  -- the eigenvariable rules
  | _, _, .forall_rule h' =>
      ndForallRule cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
  | _, _, .exist_rule h' =>
      ndExistRule cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
  | _, _, .univ_gen h' =>
      ndUnivGen cm (monotone_nd_soundness eqxi spremise cm spremise_nd h')
  -- axioms with ∀ inside / equational / pseudometric: whole NT is a closed leaf (NOT on the
  -- classical gate route; kept as `leafM` deliberately)
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
  -- QF-ER and induction
  | _, _, .qfer hqf hvf h' =>
      ndQfer eqxi spremise cm hqf hvf (monotone_nd_soundness eqxi spremise cm spremise_nd h')
  | _, _, .induction h_zero h_step =>
      ndInduction cm (monotone_nd_soundness eqxi spremise cm spremise_nd h_zero)
        (monotone_nd_soundness eqxi spremise cm spremise_nd h_step)
  -- excluded middle: `dnn_lem`, hand-written
  | _, _, .lem (A := A) _   => .dnnLemF cm A.kurodaInner
  -- QF-AC: closed leaf (not on the classical gate route)
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
#print axioms MRealizer.nnAllNnF
#print axioms monotone_nd_soundness
#print axioms spremise_nd_of_pu
#print axioms ndForallRule
#print axioms ndExistRule
#print axioms ndUnivGen
#print axioms ndQfer
#print axioms ndInduction

end Metatheorems
