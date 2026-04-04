/-
  PureFOLLemmas.lean — Pure first-order logic combinators for Derivable.
  These factor out the expensive `forall_rule`/`weakenBy` computation
  from specific arithmetic proofs.
-/
import Metatheorems.Derivable
import Metatheorems.PropositionalLemmas


namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F}

-- Re-export helpers that are private in Arithmetic.lean
private def self_imp_h {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX a Premises (A →ᶠ A) :=
  .syllogism .and_contract .and_weak

private def weaken_intro_h {Γ : Ctx ι} {A B : Formula F Γ}
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises (B →ᶠ A) :=
  .mp h (.exportation .and_weak)

-- The key identity: (A.renameF (ext shift)).subst0 (var vz) = A
private theorem weaken_subst0_id {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) :
    (A.renameF (Renaming.ext Renaming.shift)).subst0 (.var .vz : Term F (ρ :: Γ) ρ) = A :=
  substF_renameF_id (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
    (fun {_} v => match v with
      | .vz => rfl
      | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift])
    A

-- Helper: instantiate a weakened ∀ at var vz, getting back the body
private def forall_ax_vz {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises ((Formula.all ρ A).weakenBy ρ →ᶠ A) := by
  have h := @Derivable.forall_ax ι F EqX a Premises (ρ :: Γ) ρ
    (A.renameF (Renaming.ext Renaming.shift)) (.var .vz)
  -- h : (all ρ (A.renameF (ext shift))).weakenBy ρ → (A.renameF (ext shift)).subst0 (var vz)
  -- Rewrite conclusion using weaken_subst0_id
  exact Eq.mp (congrArg (Derivable F EqX a Premises ·)
    (congrArg ((Formula.all ρ A).weakenBy ρ →ᶠ ·) (weaken_subst0_id A))) h

/-- Lift an implication through ∀:
    from ⊢ ∀x. P(x) → Q(x), derive ⊢ (∀x. P(x)) → (∀x. Q(x)).
    Combines forall_ax + syllogism + forall_rule in one reusable combinator. -/
def forall_lift {Γ : Ctx ι} {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}
    (h : Derivable F EqX a Premises (Formula.all ρ (P →ᶠ Q))) :
    Derivable F EqX a Premises (Formula.all ρ P →ᶠ Formula.all ρ Q) :=
  -- In context ρ :: Γ:
  -- forall_ax_vz : (∀x.P→Q).w → P→Q
  -- forall_ax_vz : (∀x.P).w → P
  -- Combined: (∀x.P→Q) ∧ (∀x.P) → via weakenBy both → P→Q ∧ P → Q
  let get_PQ : Derivable F EqX a Premises
      ((Formula.all ρ (P →ᶠ Q)).weakenBy ρ ∧ᶠ (Formula.all ρ P).weakenBy ρ →ᶠ P →ᶠ Q) :=
    .syllogism .and_weak forall_ax_vz
  let get_P : Derivable F EqX a Premises
      ((Formula.all ρ (P →ᶠ Q)).weakenBy ρ ∧ᶠ (Formula.all ρ P).weakenBy ρ →ᶠ P) :=
    .syllogism (.syllogism .and_perm .and_weak) forall_ax_vz
  let body : Derivable F EqX a Premises
      ((Formula.all ρ (P →ᶠ Q)).weakenBy ρ ∧ᶠ (Formula.all ρ P).weakenBy ρ →ᶠ Q) :=
    .syllogism (pair_h get_PQ get_P) (.importation I_comb)
  -- forall_rule on body: (∀x.P→Q) ∧ (∀x.P) → ∀x.Q
  let fr : Derivable F EqX a Premises (Formula.all ρ (P →ᶠ Q) ∧ᶠ Formula.all ρ P →ᶠ Formula.all ρ Q) :=
    .forall_rule body
  -- From h : ∀x.P→Q, pair with (∀x.P) to get the conjunction:
  .syllogism (pair_h (weaken_intro_h h) I_comb) fr

/-- Term-level: (t.rename r).subst σ = t.subst (σ ∘ r). -/
private theorem term_subst_rename {Γ Γ' Δ : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Γ') (σ : Term.Subst F Γ' Δ)
    (t : Term F Γ τ) :
    (t.rename r).subst σ = t.subst (fun {τ} v => σ (r v)) :=
  Term.rename_subst r σ t

/-- Term-level: (t.rename (ext shift)).subst (subst0_map s) = t.subst (substVar0_map s). -/
private theorem term_rename_ext_shift_subst0 {Γ : Ctx ι} {ρ τ : Ty ι}
    (t : Term F (ρ :: Γ) τ) (s : Term F (ρ :: Γ) ρ) :
    (t.rename (Renaming.ext Renaming.shift)).subst (Term.subst0_map s) =
    t.subst (Term.substVar0_map s) := by
  rw [Term.rename_subst]; congr 1; funext τ v; cases v with
  | vz => rfl
  | vs w => rfl

/-- General: (A.renameF r).substF σ = A.substF (fun v => σ (r v)) when the compositions
    of ext match. Proved by induction on A generalizing over contexts. -/
private theorem substF_renameF {Γ Γ' Δ : Ctx ι}
    (r : Renaming Γ Γ') (σ : Term.Subst F Γ' Δ)
    (A : Formula F Γ) :
    (A.renameF r).substF σ = A.substF (fun {τ} v => σ (r v)) := by
  induction A generalizing Γ' Δ with
  | bot => rfl
  | eq0 s t =>
    simp only [Formula.renameF, Formula.substF]
    exact congr (congrArg _ (term_subst_rename r σ s)) (term_subst_rename r σ t)
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp only [Formula.renameF, Formula.substF]
    exact congr (congrArg _ (ihA r σ)) (ihB r σ)
  | all ρ _ ih | ex ρ _ ih =>
    simp only [Formula.renameF, Formula.substF]; congr 1
    rw [ih (Renaming.ext r) (Term.Subst.ext σ)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => simp [Term.Renaming.ext, Term.Subst.ext]

/-- Key identity: rename(ext shift) then subst0 = substVar0. -/
theorem renameF_ext_shift_subst0 {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ) :
    (A.renameF (Renaming.ext Renaming.shift)).subst0 t = A.substVar0 t := by
  simp only [Formula.subst0, Formula.substVar0]
  rw [substF_renameF]
  congr 1; funext τ v; cases v with
  | vz => rfl
  | vs _ => simp [Term.Renaming.ext, Term.Renaming.shift, Term.subst0_map, Term.substVar0_map]

/-- Re-index a ∀ by successor: from ⊢ ∀k. P(k), derive ⊢ ∀k. P(Sk). -/
def forall_inst_succ {Γ : Ctx ι} {P : Formula F (Ty.nat :: Γ)} :
    Derivable F EqX a Premises (Formula.all Ty.nat P →ᶠ
      Formula.all Ty.nat (P.substVar0 (.app .succ (.var .vz)))) :=
  .forall_rule (Eq.mp (congrArg (Derivable F EqX a Premises ·)
    (congrArg ((Formula.all Ty.nat P).weakenBy Ty.nat →ᶠ ·)
      (renameF_ext_shift_subst0 P (.app .succ (.var .vz)))))
    (.forall_ax (.app .succ (.var .vz))))

/-- Map a derivation through ∀:
    from ⊢ P(x) → Q(x) (in extended context), derive ⊢ (∀x. P(x)) → (∀x. Q(x)).
    Often more convenient than `forall_lift`. -/
def forall_map {Γ : Ctx ι} {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}
    (h : Derivable F EqX a Premises (P →ᶠ Q)) :
    Derivable F EqX a Premises (Formula.all ρ P →ᶠ Formula.all ρ Q) :=
  -- Use forall_rule directly: (∀x.P).w → P [forall_ax_vz] → Q [h]
  .forall_rule (.syllogism forall_ax_vz h)

/-- Introduce ∃ from variable 0: Q → (∃x.Q).weakenBy ρ in context ρ :: Γ. -/
private def exist_ax_vz {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises (A →ᶠ (Formula.ex ρ A).weakenBy ρ) :=
  Eq.mp (congrArg (Derivable F EqX a Premises ·)
    (congrArg (· →ᶠ (Formula.ex ρ A).weakenBy ρ) (weaken_subst0_id A)))
    (.exist_ax (.var .vz) (A.renameF (Renaming.ext Renaming.shift)))

/-- Map a derivation through ∃:
    from ⊢ P(x) → Q(x), derive ⊢ (∃x. P(x)) → (∃x. Q(x)). -/
def exist_map {Γ : Ctx ι} {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}
    (h : Derivable F EqX a Premises (P →ᶠ Q)) :
    Derivable F EqX a Premises (Formula.ex ρ P →ᶠ Formula.ex ρ Q) :=
  .exist_rule (.syllogism h exist_ax_vz)

end Metatheorems
