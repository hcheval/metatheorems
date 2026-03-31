/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Derivable
import Metatheorems.PropositionalLemmas
import Metatheorems.PureFOLLemmas
import Metatheorems.Arithmetic


namespace Metatheorems

/-!
# Kuroda's Negative Translation

Kuroda's negative translation maps a formula `A` to `NT(A) = ¬¬nt(A)`,
where `nt` is defined inductively (Definition nd.tex §1):

  - `nt(A) = A`           for prime formulas (⊥, s =₀ t)
  - `nt(A ★ B) = nt(A) ★ nt(B)` for ★ ∈ {∨, ∧, →}   (structural)
  - `nt(∃x.A) = ∃x.nt(A)`                              (structural)
  - `nt(∀x.A) = ∀x.¬¬nt(A)`                            (only ∀ changes)

  `NT(A) = ¬¬nt(A)`

Key property (Lemma lem:negative-eliminates-lem in nd.tex):
  if `T^ω_c[X,F] + QF-AC ⊢ A`  then  `T^ω[X,F] + QF-AC + M^ω ⊢ NT(A)`

Combined with Dialectica soundness, this yields the ND interpretation (Thm 10.7).
-/

open Formula

-- ============================================================================
-- Kuroda Inner Translation (nt)
-- ============================================================================

/-- The inner Kuroda translation `nt(A)`. Only `∀` is modified:
    `∀x.A ↦ ∀x.¬¬nt(A)`.  All other connectives are structural. -/
def Formula.kurodaInner {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} :
    Formula F Γ → Formula F Γ
  | .bot     => .bot
  | .eq0 s t => .eq0 s t
  | .and A B => .and A.kurodaInner B.kurodaInner
  | .or  A B => .or  A.kurodaInner B.kurodaInner
  | .imp A B => .imp A.kurodaInner B.kurodaInner
  | .ex  ρ A => .ex  ρ A.kurodaInner
  | .all ρ A => .all ρ (¬ᶠ¬ᶠA.kurodaInner)

/-- The full Kuroda negative translation `NT(A) = ¬¬nt(A)`. -/
def Formula.negTrans {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) : Formula F Γ :=
  ¬ᶠ¬ᶠA.kurodaInner

postfix:max "ᴺᵀ" => Formula.negTrans
postfix:max "ₙₜ" => Formula.kurodaInner

-- ============================================================================
-- kurodaInner commutes with renaming and substitution
-- ============================================================================

/-- `nt` commutes with formula renaming. -/
theorem kurodaInner_renameF {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) {Δ : Ctx ι} (r : Renaming Γ Δ) :
    (A.renameF r).kurodaInner = A.kurodaInner.renameF r := by
  induction A generalizing Δ with
  | bot | eq0 => rfl
  | and _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.renameF, ih₁ r, ih₂ r]
  | or _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.renameF, ih₁ r, ih₂ r]
  | imp _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.renameF, ih₁ r, ih₂ r]
  | ex _ _ ih =>
    simp [Formula.kurodaInner, Formula.renameF, ih (Renaming.ext r)]
  | all _ _ ih =>
    simp [Formula.kurodaInner, Formula.renameF, Formula.neg, ih (Renaming.ext r)]

/-- `nt` commutes with formula substitution. -/
theorem kurodaInner_substF {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) {Δ : Ctx ι} (s : Term.Subst F Γ Δ) :
    (A.substF s).kurodaInner = A.kurodaInner.substF s := by
  induction A generalizing Δ with
  | bot | eq0 => rfl
  | and _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.substF, ih₁ s, ih₂ s]
  | or _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.substF, ih₁ s, ih₂ s]
  | imp _ _ ih₁ ih₂ =>
    simp [Formula.kurodaInner, Formula.substF, ih₁ s, ih₂ s]
  | ex _ _ ih =>
    simp [Formula.kurodaInner, Formula.substF, ih (Term.Subst.ext s)]
  | all _ _ ih =>
    simp [Formula.kurodaInner, Formula.substF, Formula.neg, ih (Term.Subst.ext s)]

/-- `nt` commutes with `subst0`. -/
theorem kurodaInner_subst0 {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    (A.subst0 t).kurodaInner = A.kurodaInner.subst0 t :=
  kurodaInner_substF A _

/-- `nt` commutes with `substVar0`. -/
theorem kurodaInner_substVar0 {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ) :
    (A.substVar0 t).kurodaInner = A.kurodaInner.substVar0 t :=
  kurodaInner_substF A _

/-- `nt` commutes with weakening. -/
theorem kurodaInner_weaken {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F Γ) :
    (A.weakenBy ρ).kurodaInner = A.kurodaInner.weakenBy ρ :=
  kurodaInner_renameF A _

/-- `NT` commutes with `subst0`. -/
theorem negTrans_subst0 {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    (A.subst0 t).negTrans = A.negTrans.subst0 t := by
  show (¬ᶠ¬ᶠ(A.subst0 t).kurodaInner) = (¬ᶠ¬ᶠ(A.kurodaInner.subst0 t))
  rw [kurodaInner_subst0]

/-- `NT` commutes with `substVar0`. -/
theorem negTrans_substVar0 {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ) :
    (A.substVar0 t).negTrans = A.negTrans.substVar0 t := by
  show (¬ᶠ¬ᶠ(A.substVar0 t).kurodaInner) = (¬ᶠ¬ᶠ(A.kurodaInner.substVar0 t))
  rw [kurodaInner_substVar0]

/-- `NT` commutes with weakening. -/
theorem negTrans_weaken {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F Γ) :
    (A.weakenBy ρ).negTrans = A.negTrans.weakenBy ρ := by
  show (¬ᶠ¬ᶠ(A.weakenBy ρ).kurodaInner) = (¬ᶠ¬ᶠ(A.kurodaInner.weakenBy ρ))
  rw [kurodaInner_weaken]


-- ============================================================================
-- kurodaInner is identity on QF formulas; purely universal ↔ negTrans
-- ============================================================================

/-- `kurodaInner` is the identity on quantifier-free formulas. -/
theorem kurodaInner_qf {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) : A.kurodaInner = A := by
  induction A with
  | bot | eq0 => rfl
  | and _ _ ihA ihB =>
    simp only [Formula.isQF, Bool.and_eq_true] at hqf
    simp [Formula.kurodaInner, ihA hqf.1, ihB hqf.2]
  | or _ _ ihA ihB =>
    simp only [Formula.isQF, Bool.and_eq_true] at hqf
    simp [Formula.kurodaInner, ihA hqf.1, ihB hqf.2]
  | imp _ _ ihA ihB =>
    simp only [Formula.isQF, Bool.and_eq_true] at hqf
    simp [Formula.kurodaInner, ihA hqf.1, ihB hqf.2]
  | all => simp [Formula.isQF] at hqf
  | ex => simp [Formula.isQF] at hqf

-- ============================================================================
-- Hilbert-system building blocks (in Derivable)
-- ============================================================================

section HilbertExtras

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F}

/-- A → A. -/
private def self_imp {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX a Premises (A →ᶠ A) :=
  .syllogism .and_contract .and_weak

/-- If ⊢ A then ⊢ B → A (weakening). -/
private def weaken_intro {Γ : Ctx ι} {A B : Formula F Γ}
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises (B →ᶠ A) :=
  .mp h (.exportation .and_weak)


/-- ¬¬(A → B) → ¬¬A → ¬¬B  (app:not-not-A-ra-B-2 forward direction). -/
private def not_not_mp2 {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) :=
  neg_neg_mp

/-- (¬¬A → ¬¬B) → ¬¬(A → B)  (app:not-not-A-ra-B-2 reverse direction). -/
private def not_not_mp2_rev {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
  neg_neg_imp_rev2

/-- A → ¬¬B → ¬¬(A → B)  (app:not-not-A-ra-B reverse direction). -/
private def not_not_imp_rev {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises ((A →ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
  neg_neg_imp_rev

/-- ¬¬(A ∧ B) → ¬¬A  (left projection under ¬¬). -/
private def not_not_and_left {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠ(A ∧ᶠ B) →ᶠ ¬ᶠ¬ᶠA) :=
  -- contrapositive twice: and_weak : A∧B → A ↦ ¬A → ¬(A∧B) ↦ ¬¬(A∧B) → ¬¬A
  -- (contrapositive is defined later; inline it here)
  let cp := fun {X Y : Formula F Γ} (h : Derivable F EqX a Premises (X →ᶠ Y)) =>
    Derivable.exportation (.syllogism .and_perm (.importation (.syllogism h dnn_intro)))
  cp (cp .and_weak)

/-- ¬¬(A ∧ B) → ¬¬B  (right projection under ¬¬). -/
private def not_not_and_right {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠ(A ∧ᶠ B) →ᶠ ¬ᶠ¬ᶠB) :=
  let cp := fun {X Y : Formula F Γ} (h : Derivable F EqX a Premises (X →ᶠ Y)) =>
    Derivable.exportation (.syllogism .and_perm (.importation (.syllogism h dnn_intro)))
  cp (cp (.syllogism .and_perm .and_weak))

/-- ¬¬A → ¬¬B → ¬¬(A ∧ B). -/
private def not_not_and_intro {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB →ᶠ ¬ᶠ¬ᶠ(A ∧ᶠ B)) :=
  neg_neg_and_intro

/-- ¬¬A ∨ ¬¬B → ¬¬(A ∨ B)  (easy direction). -/
private def not_not_or_intro {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises ((¬ᶠ¬ᶠA ∨ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A ∨ᶠ B)) :=
  neg_neg_or_intro

/-- ¬¬(∀x^ρ.¬¬Q) → ∀x^ρ.¬¬Q  — provable intuitionistically.

Proof: apply `forall_rule` with the derivation (in context ρ :: Γ):
  `(¬¬(∀x.¬¬Q)).weaken → ¬¬Q`
obtained via `forall_ax (.var .vz)` (using `substF_renameF_id` to simplify the
substituted formula to `¬¬Q`) composed with `neg_neg_imp_rev + neg_neg_mp`. -/
private def nn_all_nn {Γ : Ctx ι} {ρ : Ty ι} {Q : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠQ)) →ᶠ Formula.all ρ (¬ᶠ¬ᶠQ)) :=
  -- Use forall_rule: suffices to derive (¬¬(∀x.¬¬Q)).weaken →ᶠ ¬¬Q in context ρ :: Γ.
  -- Key: forall_ax (.var .vz) gives (∀x.¬¬Q).weaken →ᶠ ¬¬Q after substF_renameF_id.
  -- Then ¬¬(∀x.¬¬Q).weaken →ᶠ ¬¬Q via neg_neg_imp_rev + neg_neg_mp.
  let hbody : ∀ {τ : Ty ι} (v : Var (ρ :: Γ) τ),
      Term.subst0_map (.var .vz) (Renaming.ext Renaming.shift v) = Term.var v :=
    fun {_} v => match v with
    | .vz => rfl
    | .vs w => by simp [Renaming.ext, Term.subst0_map, Renaming.shift]
  let heq : (Formula.renameF (Renaming.ext Renaming.shift) (¬ᶠ¬ᶠQ)).subst0 (.var .vz) =
            (¬ᶠ¬ᶠQ : Formula F (ρ :: Γ)) :=
    Formula.substF_renameF_id (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
      hbody (¬ᶠ¬ᶠQ)
  -- inst : (∀x.¬¬Q).weakenBy ρ →ᶠ ¬¬Q, proved via forall_ax + heq rewrite
  let inst : Derivable F EqX a Premises ((Formula.all ρ (¬ᶠ¬ᶠQ)).weakenBy ρ →ᶠ ¬ᶠ¬ᶠQ) := by
    have h := @Derivable.forall_ax ι F EqX a Premises (ρ :: Γ) ρ
                (Formula.renameF (Renaming.ext Renaming.shift) (¬ᶠ¬ᶠQ)) (.var .vz)
    rw [heq] at h
    exact h
  Derivable.forall_rule (Derivable.mp (Derivable.mp inst neg_neg_imp_rev) neg_neg_mp)


/-- ¬¬(A → B) → A → ¬¬B  (intuitionistically valid). -/
private def nn_imp_extract {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX a Premises (¬ᶠ¬ᶠ(A →ᶠ B) →ᶠ A →ᶠ ¬ᶠ¬ᶠB) :=
  let get_nn_imp : Derivable F EqX a Premises (¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ A →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) := .and_weak
  let get_nn_a : Derivable F EqX a Premises (¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ A →ᶠ ¬ᶠ¬ᶠA) :=
    .syllogism (.syllogism .and_perm .and_weak) dnn_intro
  .exportation (.syllogism (pair_h get_nn_imp get_nn_a) (.importation neg_neg_mp))

end HilbertExtras

-- ============================================================================
-- Lift Derivable lemmas to DerivableExt
-- ============================================================================

/-- Wrap a derivation in ¬¬. -/
private def wrap_dnn {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises (¬ᶠ¬ᶠA) :=
  .mp h dnn_intro

/-- Alias for backward compat — identity in the unified system. -/
private abbrev lift {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises A := h

-- ============================================================================
-- lem:negative-forall-equiv: purely universal A ↔ NT(A)
-- ============================================================================

/-- For purely universal A, ⊢ A → NT(A) and ⊢ NT(A) → A.
    Base (QF): kurodaInner_qf gives A.kurodaInner = A, so NT(A) = ¬¬A, and
    ⊢ A → ¬¬A by dnn_intro, ⊢ ¬¬A → A by qf_double_neg_elim.
    Step (∀x.B): NT(∀x.B) = ¬¬∀x.¬¬B.kurodaInner.
    Forward: ∀x.B → ∀x.NT(B) (IH + forall_map) → ¬¬∀x.NT(B) (dnn_intro) = NT(∀x.B).
    Backward: NT(∀x.B) → ∀x.¬¬B.kurodaInner (nn_all_nn) → ∀x.B (IH backward + forall_map). -/
def negTrans_iff_pu {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (adm : AdmissibleEqX EqX)
    {a : Allowed} {Premises : PremiseSet F}
    {Γ : Ctx ι} (A : Formula F Γ) (hpu : A.isPurelyUniversal = true) :
    Derivable F EqX a Premises (A →ᶠ Aᴺᵀ) ×
    Derivable F EqX a Premises (Aᴺᵀ →ᶠ A) :=
  match A, hpu with
  | .bot, _ =>
    ⟨dnn_intro, .syllogism (pair_h self_imp (weaken_intro self_imp)) (.importation mp_form)⟩
  | .eq0 .., _ =>
    ⟨dnn_intro, qf_double_neg_elim adm (by rfl)⟩
  | .and A B, hpu => by
    have hqf : (A.and B).isQF = true := hpu
    have hki := kurodaInner_qf (A.and B) hqf
    simp only [Formula.negTrans, hki]
    exact ⟨dnn_intro, qf_double_neg_elim adm hqf⟩
  | .or A B, hpu => by
    have hqf : (A.or B).isQF = true := hpu
    have hki := kurodaInner_qf (A.or B) hqf
    simp only [Formula.negTrans, hki]
    exact ⟨dnn_intro, qf_double_neg_elim adm hqf⟩
  | .imp A B, hpu => by
    have hqf : (A.imp B).isQF = true := hpu
    have hki := kurodaInner_qf (A.imp B) hqf
    simp only [Formula.negTrans, hki]
    exact ⟨dnn_intro, qf_double_neg_elim adm hqf⟩
  | .ex .., hpu => absurd hpu (by simp [Formula.isPurelyUniversal, Formula.isQF])
  | .all ρ B, hpu =>
    let ⟨ih_fwd, ih_bwd⟩ := negTrans_iff_pu adm B hpu
    ⟨Derivable.syllogism (forall_map ih_fwd) dnn_intro,
     Derivable.syllogism nn_all_nn (forall_map ih_bwd)⟩

-- ============================================================================
-- Per-axiom/rule soundness definitions
-- ============================================================================

section NegTransCases

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}

-- ── LEM ──────────────────────────────────────────────────────────────────────

/-- NT(A ∨ ¬A) is provable intuitionistically.
    NT(A ∨ ¬A) = ¬¬(nt(A) ∨ ¬nt(A)), which holds by ¬¬-LEM. -/
def negTrans_lem {Γ : Ctx ι} (A : Formula F Γ) :
    Derivable F EqX Allowed.nt_target Premises (A ∨ᶠ ¬ᶠA).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(A.kurodaInner ∨ᶠ ¬ᶠA.kurodaInner))
  exact dnn_lem

-- ── Modus Ponens ─────────────────────────────────────────────────────────────

/-- NT respects modus ponens. -/
def negTrans_mp {Γ : Ctx ι} {A B : Formula F Γ}
    (hA  : Derivable F EqX Allowed.nt_target Premises A.negTrans)
    (hAB : Derivable F EqX Allowed.nt_target Premises (A →ᶠ B).negTrans) :
    Derivable F EqX Allowed.nt_target Premises B.negTrans :=
  .mp hA (.mp hAB (not_not_mp2))

-- ── Syllogism ────────────────────────────────────────────────────────────────

/-- NT respects syllogism. -/
def negTrans_syllogism {Γ : Ctx ι} {A B C : Formula F Γ}
    (hAB : Derivable F EqX Allowed.nt_target Premises (A →ᶠ B).negTrans)
    (hBC : Derivable F EqX Allowed.nt_target Premises (B →ᶠ C).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (A →ᶠ C).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ C.kurodaInner))
  -- step_AB : ¬¬ntA → ¬¬ntB  (from hAB via neg_neg_mp)
  let step_AB := Derivable.mp hAB (neg_neg_mp)
  -- step_BC : ¬¬ntB → ¬¬ntC  (from hBC via neg_neg_mp)
  let step_BC := Derivable.mp hBC (neg_neg_mp)
  -- Weaken step_BC to ignore the extra ¬¬ntA argument:
  --   K_comb : (¬¬ntB→¬¬ntC) → ¬¬ntA → (¬¬ntB→¬¬ntC)
  let step_BC_K : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠB.kurodaInner →ᶠ ¬ᶠ¬ᶠC.kurodaInner) :=
    Derivable.mp step_BC (K_comb)
  -- S_comb applied to step_BC_K and step_AB gives ¬¬ntA → ¬¬ntC
  let s1 : Derivable F EqX Allowed.nt_target Premises
      ((¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠB.kurodaInner) →ᶠ ¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠC.kurodaInner) :=
    Derivable.mp step_BC_K (S_comb)
  let s2 : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠC.kurodaInner) :=
    Derivable.mp step_AB s1
  -- Lift ¬¬ntA→¬¬ntC to ¬¬(ntA→ntC) via neg_neg_imp_rev2
  exact Derivable.mp s2 (neg_neg_imp_rev2)

-- ── Exportation ──────────────────────────────────────────────────────────────

/-- NT respects exportation. -/
def negTrans_exportation {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : Derivable F EqX Allowed.nt_target Premises (A ∧ᶠ B →ᶠ C).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (A →ᶠ B →ᶠ C).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ B.kurodaInner →ᶠ C.kurodaInner))
  -- (ntA∧ntB→ntC) → (ntA→ntB→ntC) as a Derivable formula:
  -- From H = ((ntA∧ntB→ntC)∧ntA)∧ntB: get f, a, b; pair a+b; apply f; export twice
  let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
  -- Prove: (ntA∧ntB→ntC) → ntA → ntB → ntC  as a Derivable formula.
  -- Work in context H = ((ntA∧ntB→ntC) ∧ ntA) ∧ ntB (left-assoc).
  let get_f : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA ∧ᶠ ntB →ᶠ (ntA ∧ᶠ ntB →ᶠ ntC)) :=
    .syllogism .and_weak .and_weak
  let get_ntA : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA ∧ᶠ ntB →ᶠ ntA) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let get_ntB : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA ∧ᶠ ntB →ᶠ ntB) :=
    .syllogism .and_perm .and_weak
  let get_ntAntB : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA ∧ᶠ ntB →ᶠ ntA ∧ᶠ ntB) :=
    pair_h get_ntA get_ntB
  let get_ntC : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA ∧ᶠ ntB →ᶠ ntC) :=
    eval_h get_f get_ntAntB
  -- exportation twice: H = ((f ∧ ntA) ∧ ntB) where f = ntA∧ntB→ntC
  let exp1 : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) ∧ᶠ ntA →ᶠ ntB →ᶠ ntC) :=
    .exportation get_ntC
  let exp_form : Derivable F EqX Allowed.nt_target Premises ((ntA ∧ᶠ ntB →ᶠ ntC) →ᶠ ntA →ᶠ ntB →ᶠ ntC) :=
    .exportation exp1
  -- Lift: ¬¬(ntA∧ntB→ntC) → ¬¬(ntA→ntB→ntC) via neg_neg_mp + wrap_dnn
  let nn_exp := wrap_dnn exp_form
  exact Derivable.mp h (Derivable.mp nn_exp (neg_neg_mp))

-- ── Importation ──────────────────────────────────────────────────────────────

/-- NT respects importation. -/
def negTrans_importation {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : Derivable F EqX Allowed.nt_target Premises (A →ᶠ B →ᶠ C).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (A ∧ᶠ B →ᶠ C).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(A.kurodaInner ∧ᶠ B.kurodaInner →ᶠ C.kurodaInner))
  -- (ntA→ntB→ntC) → (ntA∧ntB→ntC) as a Derivable formula:
  -- From H = (ntA→ntB→ntC)∧(ntA∧ntB): get f, pair ntA∧ntB; eval twice; export
  let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
  -- Work in H = (ntA→ntB→ntC) ∧ (ntA∧ntB) with explicit inner parens.
  -- H → (ntA→ntB→ntC) = and_weak, H → ntA∧ntB = and_proj2
  let get_f : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntA →ᶠ ntB →ᶠ ntC) :=
    .and_weak
  let get_ntAB : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntA ∧ᶠ ntB) :=
    .syllogism .and_perm .and_weak
  let get_ntA : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntA) :=
    .syllogism get_ntAB .and_weak
  let get_ntB : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntB) :=
    .syllogism get_ntAB (.syllogism .and_perm .and_weak)
  let get_bc := eval_h get_f get_ntA
  let get_c := eval_h get_bc get_ntB
  -- exportation: (ntA→ntB→ntC) ∧ (ntA∧ntB) → ntC splits as A=(ntA→ntB→ntC), B=(ntA∧ntB)
  let imp_form : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) →ᶠ ntA ∧ᶠ ntB →ᶠ ntC) :=
    .exportation get_c
  let nn_imp := wrap_dnn imp_form
  exact Derivable.mp h (Derivable.mp nn_imp (neg_neg_mp))

-- ── Expansion ────────────────────────────────────────────────────────────────

/-- NT respects expansion. -/
def negTrans_expansion {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : Derivable F EqX Allowed.nt_target Premises (A →ᶠ B).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (C ∨ᶠ A →ᶠ C ∨ᶠ B).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(C.kurodaInner ∨ᶠ A.kurodaInner →ᶠ C.kurodaInner ∨ᶠ B.kurodaInner))
  -- From h : ¬¬(ntA→ntB), derive ¬¬(ntC∨ntA→ntC∨ntB).
  -- Strategy: build closed Derivable formula (ntA→ntB) → (ntC∨ntA → ntC∨ntB)
  -- using or_elim_rule with two closed cases, then push through ¬¬ via neg_neg_mp.
  let ntA := A.kurodaInner; let ntB := B.kurodaInner; let ntC := C.kurodaInner
  -- Case C: ntC → (ntA→ntB) → ntC∨ntB  via  exportation(and_weak;or_weak)
  let case_C : Derivable F EqX Allowed.nt_target Premises (ntC →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
    .exportation (.syllogism .and_weak .or_weak)
  -- Case A: ntA → (ntA→ntB) → ntC∨ntB  via  eval_h(and_perm;and_weak, and_weak) then or_inr
  let case_A : Derivable F EqX Allowed.nt_target Premises (ntA →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
    .exportation (.syllogism (eval_h (.syllogism .and_perm .and_weak) .and_weak) or_inr)
  -- or_elim on ntC∨ntA gives: ntC∨ntA → (ntA→ntB) → ntC∨ntB
  let rvp_to : Derivable F EqX Allowed.nt_target Premises (ntC ∨ᶠ ntA →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
    or_elim_rule case_C case_A
  -- flip: (ntA→ntB) → ntC∨ntA → ntC∨ntB   (closed Derivable formula)
  let exp_form : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntA →ᶠ ntC ∨ᶠ ntB) :=
    .mp rvp_to flip_comb
  -- wrap in ¬¬ and apply neg_neg_mp to h
  exact Derivable.mp h (Derivable.mp (wrap_dnn exp_form) (neg_neg_mp))

-- ── ∀-rule ───────────────────────────────────────────────────────────────────

/-- NT respects the ∀-rule. -/
def negTrans_forall_rule {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : Derivable F EqX Allowed.nt_target Premises (B.weakenBy ρ →ᶠ A).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (B →ᶠ Formula.all ρ A).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(B.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner)))
  simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] at h
  -- h : Derivable (¬¬(B.ki.weaken → A.ki)) in context ρ :: Γ
  -- step1 : ¬¬B.ki.weaken → ¬¬A.ki  (= Formula.weakenBy ρ (¬¬B.ki) → ¬¬A.ki)
  let step1 := Derivable.mp h neg_neg_mp
  -- cast to the syntactic form forall_rule expects
  let step1' : Derivable F EqX Allowed.nt_target Premises (Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner) →ᶠ ¬ᶠ¬ᶠA.kurodaInner) :=
    step1
  -- step2 : ¬¬B.ki → ∀ρ. ¬¬A.ki  (forall_rule changes context ρ::Γ → Γ)
  let step2 := Derivable.forall_rule step1'
  -- step3 : B.ki → ∀ρ. ¬¬A.ki  (via dnn_intro : B.ki → ¬¬B.ki)
  let step3 := Derivable.syllogism dnn_intro step2
  -- step4 : B.ki → ¬¬(∀ρ. ¬¬A.ki)  (via dnn_intro on the right)
  let step4 := Derivable.syllogism step3 dnn_intro
  -- conclude ¬¬(B.ki → ∀ρ. ¬¬A.ki) via neg_neg_imp_rev : (A → ¬¬B) → ¬¬(A→B)
  exact Derivable.mp step4 neg_neg_imp_rev

-- ── ∃-rule ───────────────────────────────────────────────────────────────────

/-- NT respects the ∃-rule (Derivable level, mirrors negTrans_forall_rule). -/
def negTrans_exist_rule {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : Derivable F EqX Allowed.nt_target Premises (A →ᶠ B.weakenBy ρ).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (Formula.ex ρ A →ᶠ B).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(Formula.ex ρ A.kurodaInner →ᶠ B.kurodaInner))
  simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken] at h
  -- step1 : ¬¬A.ki → ¬¬B.ki.weaken
  let step1 := Derivable.mp h neg_neg_mp
  -- step2 : A.ki → ¬¬B.ki.weaken  (via dnn_intro : A → ¬¬A)
  let step2 : Derivable F EqX Allowed.nt_target Premises (A.kurodaInner →ᶠ Formula.weakenBy ρ (¬ᶠ¬ᶠB.kurodaInner)) :=
    Derivable.syllogism dnn_intro step1
  -- step3 : (∃ρ. A.ki) → ¬¬B.ki
  let step3 := Derivable.exist_rule step2
  -- conclude ¬¬((∃ρ. A.ki) → B.ki)
  exact Derivable.mp step3 neg_neg_imp_rev

-- ── Universal generalization ──────────────────────────────────────────────────

/-- NT respects universal generalization. -/
def negTrans_univ_gen {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F Γ}
    (h : Derivable F EqX Allowed.nt_target Premises A.negTrans) :
    Derivable F EqX Allowed.nt_target Premises (Formula.all ρ (A.weakenBy ρ)).negTrans := by
  simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken]
  -- h : DerivableExt (¬¬A.ki)
  -- goal : DerivableExt (¬¬(∀ρ. ¬¬A.ki.weaken))
  -- forall_rule I_comb : ¬¬A.ki → ∀ρ. ¬¬A.ki.weaken
  -- (B.weaken = ¬¬A.ki.weaken means B = ¬¬A.ki; I_comb : B.weaken → B.weaken = B.weaken → A')
  let to_all : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠA.kurodaInner →ᶠ Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner.weakenBy ρ)) :=
    .forall_rule (@I_comb ι F EqX Allowed.nt_target Premises (ρ :: Γ) (¬ᶠ¬ᶠA.kurodaInner.weakenBy ρ))
  exact Derivable.mp (Derivable.mp h (to_all)) (dnn_intro)

-- ── Induction ────────────────────────────────────────────────────────────────

/-- NT respects induction (Derivable level, mirrors negTrans_forall_rule). -/
def negTrans_induction {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {A : Formula F (Ty.nat :: Γ)}
    (h_zero : Derivable F EqX Allowed.nt_target Premises (A.subst0 Term.zero).negTrans)
    (h_step : Derivable F EqX Allowed.nt_target Premises (Formula.all Ty.nat (A →ᶠ A.substVar0 (Term.app Term.succ (.var .vz)))).negTrans) :
    Derivable F EqX Allowed.nt_target Premises (Formula.all Ty.nat A).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠA.kurodaInner)))
  -- IH for the base case: ¬¬(A.ki.subst0 zero)
  have ih_zero : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠA.kurodaInner.subst0 Term.zero) := by
    simp only [Formula.negTrans, kurodaInner_subst0] at h_zero; exact h_zero
  -- IH for the step case: ¬¬(∀n.¬¬(A.ki → A.ki.substVar0 Sn))
  have ih_step : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ
        A.kurodaInner.substVar0 (Term.app Term.succ (.var .vz)))))) := by
    simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_substVar0] at h_step
    exact h_step
  -- Strip outer ¬¬ from ih_step to get ∀n.¬¬(A.ki → A.ki.substVar0 Sn)
  have step_all : Derivable F EqX Allowed.nt_target Premises
      (Formula.all Ty.nat (¬ᶠ¬ᶠ(A.kurodaInner →ᶠ
        A.kurodaInner.substVar0 (Term.app Term.succ (.var .vz))))) :=
    Derivable.mp ih_step nn_all_nn
  -- Build ∀n.(¬¬A.ki → ¬¬(A.ki.substVar0 Sn)) via forall_rule + neg_neg_mp
  have ind_step : Derivable F EqX Allowed.nt_target Premises (Formula.all Ty.nat
      (¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠA.kurodaInner.substVar0
        (Term.app Term.succ (.var .vz)))) := by
    let Q₀ : Formula F (Ty.nat :: Γ) :=
      ¬ᶠ¬ᶠ(A.kurodaInner →ᶠ A.kurodaInner.substVar0 (Term.app Term.succ (.var .vz)))
    have hbody : ∀ {τ : Ty ι} (v : Var (Ty.nat :: Γ) τ),
        Term.subst0_map (F := F) (.var .vz) (Renaming.ext Renaming.shift v) = Term.var v := by
      intro _ v; cases v with
      | vz   => rfl
      | vs w => simp [Renaming.ext, Term.subst0_map, Renaming.shift]
    have heq2 : (Formula.renameF (Renaming.ext Renaming.shift) Q₀).subst0 (.var .vz) = Q₀ :=
      Formula.substF_renameF_id (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
        hbody Q₀
    have inst2 : Derivable F EqX Allowed.nt_target Premises ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ Q₀) := by
      have h' := @Derivable.forall_ax ι F EqX Allowed.nt_target Premises (Ty.nat :: Γ) Ty.nat
                   (Formula.renameF (Renaming.ext Renaming.shift) Q₀) (.var .vz)
      rw [heq2] at h'; exact h'
    let inner : Derivable F EqX Allowed.nt_target Premises ((Formula.all Ty.nat Q₀).weakenBy Ty.nat →ᶠ
        ¬ᶠ¬ᶠA.kurodaInner →ᶠ ¬ᶠ¬ᶠA.kurodaInner.substVar0 (Term.app Term.succ (.var .vz))) :=
      Derivable.syllogism inst2 neg_neg_mp
    exact Derivable.mp step_all (Derivable.forall_rule inner)
  -- Apply induction to ¬¬A.ki, getting ∀n.¬¬A.ki, then wrap in ¬¬
  -- Explicit type annotation lets Lean infer A = ¬¬A.ki for Derivable.induction
  have nn_all : Derivable F EqX Allowed.nt_target Premises (Formula.all Ty.nat (¬ᶠ¬ᶠA.kurodaInner)) :=
    Derivable.induction ih_zero ind_step
  exact Derivable.mp nn_all dnn_intro

-- ── Axioms without ∀ inside ────────────────────────────────────────────────

def negTrans_or_contract {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A ∨ᶠ A →ᶠ A).negTrans :=
  wrap_dnn (.or_contract (A := A.kurodaInner))

def negTrans_and_contract {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A →ᶠ A ∧ᶠ A).negTrans :=
  wrap_dnn (.and_contract (A := A.kurodaInner))

def negTrans_or_weak {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A →ᶠ A ∨ᶠ B).negTrans :=
  wrap_dnn (.or_weak (A := A.kurodaInner) (B := B.kurodaInner))

def negTrans_and_weak {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A ∧ᶠ B →ᶠ A).negTrans :=
  wrap_dnn (.and_weak (A := A.kurodaInner) (B := B.kurodaInner))

def negTrans_or_perm {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A ∨ᶠ B →ᶠ B ∨ᶠ A).negTrans :=
  wrap_dnn (.or_perm (A := A.kurodaInner) (B := B.kurodaInner))

def negTrans_and_perm {Γ : Ctx ι} {A B : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (A ∧ᶠ B →ᶠ B ∧ᶠ A).negTrans :=
  wrap_dnn (.and_perm (A := A.kurodaInner) (B := B.kurodaInner))

def negTrans_exfalso {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX Allowed.nt_target Premises (⊥ᶠ →ᶠ A).negTrans :=
  wrap_dnn (.exfalso (A := A.kurodaInner))

def negTrans_refl0 {Γ : Ctx ι} {s : Term F Γ Ty.nat} :
    Derivable F EqX Allowed.nt_target Premises (Formula.eq0 s s).negTrans :=
  wrap_dnn .refl0

def negTrans_sym0 {Γ : Ctx ι} {s t : Term F Γ Ty.nat} :
    Derivable F EqX Allowed.nt_target Premises (Formula.eq0 s t →ᶠ Formula.eq0 t s).negTrans :=
  wrap_dnn .sym0

def negTrans_trans0 {Γ : Ctx ι} {s t u : Term F Γ Ty.nat} :
    Derivable F EqX Allowed.nt_target Premises (Formula.eq0 s t ∧ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u).negTrans :=
  wrap_dnn .trans0

-- ── Axioms with ∀ inside (NT ≠ wrap_dnn, need sorry) ─────────────────────

def negTrans_succ_ne_zero {Γ : Ctx ι} :
    Derivable F EqX Allowed.nt_target Premises
      (@Formula.all ι F Γ Ty.nat
        (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ)).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises
    (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ))))
  -- In context Ty.nat :: Γ, prove ¬¬(succ(.vz)=0→⊥):
  -- Use succ_ne_zero in context Ty.nat::Γ, instantiate with .var .vz
  let inst : Derivable F EqX Allowed.nt_target Premises
      (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ) :=
    .mp (@Derivable.succ_ne_zero ι F EqX Allowed.nt_target Premises (Ty.nat :: Γ)) (.forall_ax (.var .vz))
  let inner : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ)) :=
    .mp inst dnn_intro
  -- forall_rule with B = ¬⊥ (= ⊥→⊥ provable by I_comb):
  -- h_inner must have syntactic type (B.weakenBy Ty.nat) → A to match forall_rule
  let h_inner : Derivable F EqX Allowed.nt_target Premises
      (Formula.weakenBy Ty.nat (¬ᶠ⊥ᶠ) →ᶠ
       ¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ)) :=
    weaken_intro inner
  -- forall_rule h_inner : ¬ᶠ⊥ᶠ → ∀n. ¬¬(succ(n)=0→⊥)
  let all_h : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ⊥ᶠ →ᶠ Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ))) :=
    .forall_rule h_inner
  -- ¬⊥ is provable: I_comb at ⊥
  let neg_bot : Derivable F EqX Allowed.nt_target Premises (¬ᶠ⊥ᶠ) := @I_comb ι F EqX Allowed.nt_target Premises Γ ⊥ᶠ
  -- Derive ∀n. ¬¬(succ(n)=0→⊥) and wrap in ¬¬
  exact .mp (.mp neg_bot all_h) dnn_intro

def negTrans_succ_inj {Γ : Ctx ι} :
    Derivable F EqX Allowed.nt_target Premises
      (@Formula.all ι F Γ Ty.nat (@Formula.all ι F (Ty.nat :: Γ) Ty.nat
        (Formula.eq0
          (Term.app Term.succ (.var (.vs .vz)))
          (Term.app Term.succ (.var .vz))
        →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))).negTrans := by
  -- NT of the body: ¬¬(succ m = succ n → m = n), no ∀ inside eq0/imp
  -- The outer two ∀s add ¬¬ layers. Use forall_rule twice.
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(
    Formula.eq0 (Term.app Term.succ (.var (.vs .vz))) (Term.app Term.succ (.var .vz))
    →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))))))
  -- In context Ty.nat :: Ty.nat :: Γ, prove the innermost ¬¬(succ m = succ n → m = n)
  -- Use explicit annotations to avoid subst0 elaboration issues.
  -- step_m: after instantiating the outer ∀m with m = .var(.vs .vz), inside ∀n the context
  --         is Ty.nat::{n}::{m}::Γ so m appears as de Bruijn 2 = .vs(.vs .vz).
  let step_m : Derivable F EqX Allowed.nt_target Premises
      (Formula.all Ty.nat
        (Formula.eq0 (Term.app Term.succ (.var (.vs (.vs .vz)))) (Term.app Term.succ (.var .vz))
         →ᶠ Formula.eq0 (.var (.vs (.vs .vz))) (.var .vz))) :=
    .mp (@Derivable.succ_inj ι F EqX Allowed.nt_target Premises (Ty.nat :: Ty.nat :: Γ)) (.forall_ax (.var (.vs .vz)))
  -- step_mn: instantiate inner ∀n with n = .var .vz, getting succ m = succ n → m = n
  let step_mn : Derivable F EqX Allowed.nt_target Premises
      (Formula.eq0 (Term.app Term.succ (.var (.vs .vz))) (Term.app Term.succ (.var .vz))
       →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)) :=
    .mp step_m (.forall_ax (.var .vz))
  let innermost : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var (.vs .vz))) (Term.app Term.succ (.var .vz))
       →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))) :=
    .mp step_mn dnn_intro
  -- Step up to ∀n. ¬¬(inner) in context Ty.nat :: Γ:
  let h1 : Derivable F EqX Allowed.nt_target Premises
      (Formula.weakenBy Ty.nat (¬ᶠ⊥ᶠ) →ᶠ
       ¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var (.vs .vz))) (Term.app Term.succ (.var .vz))
            →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))) :=
    weaken_intro innermost
  let all_inner : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ⊥ᶠ →ᶠ Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var (.vs .vz)))
           (Term.app Term.succ (.var .vz)) →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))) :=
    .forall_rule h1
  let neg_bot1 : Derivable F EqX Allowed.nt_target Premises (¬ᶠ⊥ᶠ) := @I_comb ι F EqX Allowed.nt_target Premises (Ty.nat :: Γ) ⊥ᶠ
  let step1 : Derivable F EqX Allowed.nt_target Premises
      (Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var (.vs .vz)))
           (Term.app Term.succ (.var .vz)) →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))) :=
    .mp neg_bot1 all_inner
  -- Now get ¬¬(∀n. ¬¬(inner)) in context Ty.nat :: Γ:
  let step2 := Derivable.mp step1 dnn_intro
  -- Step up again to ∀m. ¬¬(∀n. ¬¬(inner)) in context Γ:
  let h2 : Derivable F EqX Allowed.nt_target Premises
      (Formula.weakenBy Ty.nat (¬ᶠ⊥ᶠ) →ᶠ
       ¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.eq0 (Term.app Term.succ (.var (.vs .vz)))
            (Term.app Term.succ (.var .vz)) →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))))) :=
    weaken_intro step2
  let all_step2 : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ⊥ᶠ →ᶠ Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.all Ty.nat (¬ᶠ¬ᶠ(
       Formula.eq0 (Term.app Term.succ (.var (.vs .vz))) (Term.app Term.succ (.var .vz))
       →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))))) :=
    .forall_rule h2
  let neg_bot2 : Derivable F EqX Allowed.nt_target Premises (¬ᶠ⊥ᶠ) := @I_comb ι F EqX Allowed.nt_target Premises Γ ⊥ᶠ
  let step3 := Derivable.mp neg_bot2 all_step2
  exact .mp step3 dnn_intro


def negTrans_forall_ax {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (t : Term F Γ ρ) :
    Derivable F EqX Allowed.nt_target Premises (Formula.all ρ A →ᶠ A.subst0 t).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠA.kurodaInner) →ᶠ (A.subst0 t).kurodaInner))
  rw [kurodaInner_subst0]
  exact (Derivable.mp (@Derivable.forall_ax ι F EqX Allowed.nt_target Premises _ _ (¬ᶠ¬ᶠA.kurodaInner) t) neg_neg_imp_rev)

def negTrans_exist_ax {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (t : Term F Γ ρ) :
    Derivable F EqX Allowed.nt_target Premises (A.subst0 t →ᶠ Formula.ex ρ A).negTrans := by
  show Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ((A.subst0 t).kurodaInner →ᶠ Formula.ex ρ A.kurodaInner))
  rw [kurodaInner_subst0]
  exact wrap_dnn (.exist_ax t _)

/-- NT of a purely universal axiom: from ⊢ A (axiom), derive ⊢ NT(A)
    using negTrans_iff_pu. -/
private def negTrans_pu_axiom {a : Allowed} {Premises : PremiseSet F} (adm : AdmissibleEqX EqX) {Γ : Ctx ι}
    {A : Formula F Γ} (hpu : A.isPurelyUniversal = true)
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises A.negTrans :=
  .mp h (negTrans_iff_pu adm A hpu).1

/-- eqAtType is purely universal (from adm.eqx_pu + induction on ρ). -/
private theorem eqAtType_isPU (adm : AdmissibleEqX EqX) (ρ : Ty ι)
    {Γ : Ctx ι} (s t : Term F Γ ρ) :
    (eqAtType EqX ρ s t).isPurelyUniversal = true := by
  induction ρ generalizing Γ with
  | nat => rfl
  | base i => exact adm.eqx_pu i s t
  | arr ρ τ ih_ρ ih_τ => simp only [eqAtType, Formula.isPurelyUniversal]; exact ih_τ _ _

def negTrans_proj_ax (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {ρ τ : Ty ι} {s : Term F Γ ρ} {t : Term F Γ τ} :
    Derivable F EqX Allowed.nt_target Premises (eqAtType EqX ρ (Term.app2 (Term.proj ρ τ) s t) s).negTrans :=
  negTrans_pu_axiom adm (eqAtType_isPU adm ρ _ _) .proj_ax

def negTrans_comb_ax (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {δ ρ τ : Ty ι}
    {f : Term F Γ (δ →ₜ ρ →ₜ τ)} {g : Term F Γ (δ →ₜ ρ)} {x : Term F Γ δ} :
    Derivable F EqX Allowed.nt_target Premises (eqAtType EqX τ
      (Term.app3 (Term.comb δ ρ τ) f g x)
      (Term.app (Term.app f x) (Term.app g x))).negTrans :=
  negTrans_pu_axiom adm (eqAtType_isPU adm τ _ _) .comb_ax

def negTrans_rec_zero (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {ρ : Ty ι}
    {y : Term F Γ ρ} {z : Term F Γ (ρ →ₜ Ty.nat →ₜ ρ)} :
    Derivable F EqX Allowed.nt_target Premises (eqAtType EqX ρ (Term.app3 (Term.prec ρ) y z Term.zero) y).negTrans :=
  negTrans_pu_axiom adm (eqAtType_isPU adm ρ _ _) .rec_zero

def negTrans_rec_succ (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {ρ : Ty ι}
    {y : Term F Γ ρ} {z : Term F Γ (ρ →ₜ Ty.nat →ₜ ρ)} {x : Term F Γ Ty.nat} :
    Derivable F EqX Allowed.nt_target Premises (eqAtType EqX ρ
      (Term.app3 (Term.prec ρ) y z (Term.app Term.succ x))
      (Term.app2 z (Term.app3 (Term.prec ρ) y z x) x)).negTrans :=
  negTrans_pu_axiom adm (eqAtType_isPU adm ρ _ _) .rec_succ

-- ── QF-ER ────────────────────────────────────────────────────────────────────

/-- NT respects QF-ER.
    From ⊢ A₀ → s =_ρ t (Derivable), derive ⊢ NT(A₀ → r[s] =_σ r[t]).
    Proof: extract A₀ → s=t (by negTrans backward on PU equality),
    apply QF-ER, then lift back via negTrans forward. -/
def negTrans_qfer {a : Allowed} {Premises : PremiseSet F} (adm : AdmissibleEqX EqX) {Γ : Ctx ι} {ρ σ : Ty ι}
    {A₀ : Formula F Γ} {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h_inner : Derivable F EqX a Premises (A₀ →ᶠ eqAtType EqX ρ s t)) :
    Derivable F EqX a Premises (A₀ →ᶠ eqAtType EqX σ (Term.subst0 r s) (Term.subst0 r t)).negTrans :=
  -- Step 1: QF-ER gives A₀ → r[s] =_σ r[t]
  let step1 : Derivable F EqX a Premises (A₀ →ᶠ eqAtType EqX σ (r.subst0 s) (r.subst0 t)) :=
    .qfer hqf hvf h_inner
  -- Step 2: compose with forward direction of negTrans_iff_pu on the conclusion
  let fwd := (negTrans_iff_pu adm (eqAtType EqX σ (r.subst0 s) (r.subst0 t))
    (eqAtType_isPU adm σ _ _)).1
  -- step1 gives A₀ → result. fwd gives result → NT(result) = ¬¬result.kurodaInner.
  -- So: A₀ → ¬¬result.kurodaInner. Then dnn_intro: ¬¬(A₀ → result.kurodaInner).
  -- But we need A₀ → result.kurodaInner first, then wrap in ¬¬.
  -- Actually: A₀ → result → result.kurodaInner (via negTrans_iff_pu backward... no, forward gives result → ¬¬result.ki)
  -- Hmm. fwd : result → ¬¬result.ki. So A₀ → ¬¬result.ki. Then neg_neg_imp_rev2: ¬¬(A₀ → result.ki).
  -- NT(A₀ → result) = ¬¬(A₀.ki → result.ki) = ¬¬(A₀ → result.ki) (since A₀ is QF).
  -- NT(A₀ → result) = ¬¬(A₀.ki → result.ki) = ¬¬(A₀ → result.ki) since A₀ is QF
  -- fwd : result → NT(result) = ¬¬result.ki
  -- So: A₀ → result → ¬¬result.ki. By neg_neg_imp_rev2: ¬¬(A₀ → result.ki).
  have ki_imp : (A₀ →ᶠ eqAtType EqX σ (r.subst0 s) (r.subst0 t)).kurodaInner =
      (A₀ →ᶠ (eqAtType EqX σ (r.subst0 s) (r.subst0 t)).kurodaInner) := by
    simp [Formula.kurodaInner, kurodaInner_qf A₀ hqf]
  Eq.mp (congrArg (fun x => Derivable F EqX a Premises (Formula.neg (Formula.neg x))) ki_imp.symm)
    (.mp (.syllogism step1 fwd) neg_neg_imp_rev)

-- ── QF-AC ──────────────────────────────────────────────────────────────────

/-- NT(QF-AC): from Markov + QF-AC, derive the negative translation of QF-AC.

    NT((∀ρ ∃τ A₀) → ∃(ρ→τ) (∀ρ acSubst A₀))
    = ¬¬(∀ρ ¬¬(∃τ A₀) → ∃(ρ→τ) (∀ρ ¬¬(acSubst A₀)))

    Proof: Markov eliminates ¬¬∃ under ∀, QF-AC gives the choice function,
    then dnn_intro strengthens the conclusion. -/
def negTrans_qfac (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {ρ τ : Ty ι} {A₀ : Formula F (τ :: ρ :: Γ)}
    (hqf : A₀.isQF = true) (hvf : Formula.isVFree A₀ = true) :
    Derivable F EqX Allowed.nt_target Premises
      ((Formula.all ρ (Formula.ex τ A₀)) →ᶠ
       Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀))).negTrans := by
  -- The NT unfolds to ¬¬(∀ρ ¬¬(∃τ A₀) → ∃(ρ→τ) (∀ρ ¬¬(acSubst A₀)))
  -- kurodaInner is identity on QF formulas; substF preserves QF
  have hqf_subst : (Formula.substF Formula.acSubst A₀).isQF = true := by
    suffices h : ∀ {Γ' Δ : Ctx ι} (B : Formula F Γ') (σ : Term.Subst F Γ' Δ),
        B.isQF = true → (B.substF σ).isQF = true from h A₀ _ hqf
    intro Γ' Δ B σ hB
    induction B generalizing Δ with
    | bot | eq0 => simp [Formula.substF, Formula.isQF]
    | and A B ihA ihB => simp [Formula.substF, Formula.isQF] at hB ⊢; exact ⟨ihA _ hB.1, ihB _ hB.2⟩
    | or A B ihA ihB => simp [Formula.substF, Formula.isQF] at hB ⊢; exact ⟨ihA _ hB.1, ihB _ hB.2⟩
    | imp A B ihA ihB => simp [Formula.substF, Formula.isQF] at hB ⊢; exact ⟨ihA _ hB.1, ihB _ hB.2⟩
    | all | ex => simp [Formula.isQF] at hB
  simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_qf _ hqf,
    kurodaInner_qf _ hqf_subst]
  -- Step 1: Markov at context ρ :: Γ: ¬¬(∃τ A₀) → ∃τ A₀
  have markov_step : Derivable F EqX Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(Formula.ex τ A₀) →ᶠ Formula.ex τ A₀) :=
    .markov rfl hqf hvf
  -- Step 2: ∀ρ (¬¬∃τ A₀) → ∀ρ (∃τ A₀)  via forall_map
  have step2 : Derivable F EqX Allowed.nt_target Premises
      (Formula.all ρ (¬ᶠ¬ᶠFormula.ex τ A₀) →ᶠ Formula.all ρ (Formula.ex τ A₀)) :=
    forall_map markov_step
  -- Step 3: QF-AC: ∀ρ (∃τ A₀) → ∃(ρ→τ) (∀ρ (acSubst A₀))
  have step3 : Derivable F EqX Allowed.nt_target Premises
      (Formula.all ρ (Formula.ex τ A₀) →ᶠ
       Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀))) :=
    .qfac rfl hqf hvf
  -- Step 4: Strengthen conclusion: acSubst A₀ → ¬¬(acSubst A₀) via dnn_intro
  -- Lift B → ¬¬B through ∀ρ then ∃(ρ→τ):
  -- ∃(ρ→τ)(∀ρ B) → ∃(ρ→τ)(∀ρ ¬¬B) by exist_rule + forall_map dnn_intro + exist_ax
  have step4 : Derivable F EqX Allowed.nt_target Premises
      (Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀)) →ᶠ
       Formula.ex (ρ →ₜ τ) (Formula.all ρ (¬ᶠ¬ᶠFormula.substF Formula.acSubst A₀))) :=
    exist_map (forall_map dnn_intro)
  -- Compose steps 2, 3, 4 and wrap in ¬¬
  exact Derivable.mp (.syllogism (.syllogism step2 step3) step4) dnn_intro

end NegTransCases

-- ============================================================================
-- Soundness of Kuroda's negative translation
-- ============================================================================

section NegTransSound

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    (adm : AdmissibleEqX EqX)

/-- **NT Soundness Theorem** (Lemma lem:negative-eliminates-lem in nd.tex).

    If `A` is classically derivable (in WE-HA^{ω,X} + LEM + QF-AC),
    then `NT(A) = ¬¬nt(A)` is provable in `WE-HA^{ω,X} + QF-AC + M^ω`
    (which is exactly `Derivable F EqX Allowed.nt_target`).

    Composed with `dialectica_soundness`, this gives the ND interpretation:
    from a classical proof, extract Lean-computable witnesses. -/
def negTrans_sound {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F EqX Allowed.classical Premises A) : Derivable F EqX Allowed.nt_target Premises A.negTrans :=
  match h with
  -- Premises: the NT of a premise is proved using negTrans_iff_pu if PU,
  -- or left as sorry for general premises.
  | .premise hp   => sorry -- TODO: NT of premises (requires PU assumption on premises)
  -- Simple propositional axioms: wrap in ¬¬ via dnn_intro
  | .or_contract  => .mp .or_contract  dnn_intro
  | .and_contract => .mp .and_contract dnn_intro
  | .or_weak      => .mp .or_weak      dnn_intro
  | .and_weak     => .mp .and_weak     dnn_intro
  | .or_perm      => .mp .or_perm      dnn_intro
  | .and_perm     => .mp .and_perm     dnn_intro
  | .exfalso      => .mp .exfalso      dnn_intro
  | .refl0        => .mp .refl0        dnn_intro
  | .sym0         => .mp .sym0         dnn_intro
  | .trans0       => .mp .trans0       dnn_intro
  -- forall_ax
  | .forall_ax (A := A_body) t => by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_subst0]
      exact Derivable.mp (@Derivable.forall_ax ι F EqX Allowed.nt_target Premises _ _ (¬ᶠ¬ᶠA_body.kurodaInner) t) neg_neg_imp_rev
  -- exist_ax
  | .exist_ax (A := A_body) t => by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_subst0]
      exact Derivable.mp (@Derivable.exist_ax ι F EqX Allowed.nt_target Premises _ _ t (A_body.kurodaInner)) dnn_intro
  -- mp
  | .mp hA hAB =>
      .mp (negTrans_sound hA) (.mp (negTrans_sound hAB) neg_neg_mp)
  -- syllogism
  | .syllogism hAB hBC =>
      let ihAB := negTrans_sound hAB
      let ihBC := negTrans_sound hBC
      let step_AB := .mp ihAB neg_neg_mp
      let step_BC := .mp ihBC neg_neg_mp
      let step_BC_K := .mp step_BC K_comb
      let s1 := .mp step_BC_K S_comb
      let s2 := .mp step_AB s1
      .mp s2 neg_neg_imp_rev2
  -- exportation
  | .exportation (A := A_u) (B := B_u) (C := C_u) h_inner =>
      let ntA := A_u.kurodaInner; let ntB := B_u.kurodaInner; let ntC := C_u.kurodaInner
      let ih : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(ntA ∧ᶠ ntB →ᶠ ntC)) := negTrans_sound h_inner
      let get_f   := Derivable.syllogism .and_weak .and_weak
      let get_ntA := Derivable.syllogism .and_weak (.syllogism .and_perm .and_weak)
      let get_ntB := Derivable.syllogism .and_perm .and_weak
      let get_ntAB := pair_h get_ntA get_ntB
      let get_ntC := eval_h get_f get_ntAB
      let exp1    := Derivable.exportation get_ntC
      let exp_form := Derivable.exportation exp1
      .mp ih (.mp (.mp exp_form dnn_intro) neg_neg_mp)
  -- importation
  | .importation (A := A_u) (B := B_u) (C := C_u) h_inner =>
      let ntA := A_u.kurodaInner; let ntB := B_u.kurodaInner; let ntC := C_u.kurodaInner
      let ih : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(ntA →ᶠ ntB →ᶠ ntC)) := negTrans_sound h_inner
      let get_f   : Derivable F EqX Allowed.nt_target Premises ((ntA →ᶠ ntB →ᶠ ntC) ∧ᶠ (ntA ∧ᶠ ntB) →ᶠ ntA →ᶠ ntB →ᶠ ntC) :=
        .and_weak
      let get_ntAB := Derivable.syllogism .and_perm .and_weak
      let get_ntA := Derivable.syllogism get_ntAB .and_weak
      let get_ntB := Derivable.syllogism get_ntAB (.syllogism .and_perm .and_weak)
      let get_bc := eval_h get_f get_ntA
      let get_c  := eval_h get_bc get_ntB
      let imp_form := Derivable.exportation get_c
      .mp ih (.mp (.mp imp_form dnn_intro) neg_neg_mp)
  -- expansion
  | .expansion (A := A_u) (B := B_u) (C := C_u) h_inner =>
      let ntA := A_u.kurodaInner; let ntB := B_u.kurodaInner; let ntC := C_u.kurodaInner
      let ih : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠ(ntA →ᶠ ntB)) := negTrans_sound h_inner
      let case_C : Derivable F EqX Allowed.nt_target Premises (ntC →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
        .exportation (.syllogism .and_weak .or_weak)
      let case_A : Derivable F EqX Allowed.nt_target Premises (ntA →ᶠ (ntA →ᶠ ntB) →ᶠ ntC ∨ᶠ ntB) :=
        .exportation (.syllogism (eval_h (.syllogism .and_perm .and_weak) .and_weak) or_inr)
      let rvp_to  := or_elim_rule case_C case_A
      let exp_form := .mp rvp_to flip_comb
      .mp ih (.mp (.mp exp_form dnn_intro) neg_neg_mp)
  -- forall_rule
  | .forall_rule h_inner =>
      negTrans_forall_rule (negTrans_sound h_inner)
  -- exist_rule
  | .exist_rule h_inner =>
      negTrans_exist_rule (negTrans_sound h_inner)
  -- univ_gen
  | .univ_gen (ρ := ρ_v) (A := A_inner) h_inner => by
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_weaken]
      have ih : Derivable F EqX Allowed.nt_target Premises (¬ᶠ¬ᶠA_inner.kurodaInner) := negTrans_sound h_inner
      let to_all : Derivable F EqX Allowed.nt_target Premises
          (¬ᶠ¬ᶠA_inner.kurodaInner →ᶠ Formula.all ρ_v (¬ᶠ¬ᶠA_inner.kurodaInner.weakenBy ρ_v)) :=
        Derivable.forall_rule (@I_comb ι F EqX Allowed.nt_target Premises _ (¬ᶠ¬ᶠA_inner.kurodaInner.weakenBy ρ_v))
      exact Derivable.mp (Derivable.mp ih to_all) dnn_intro
  -- Axioms with ∀ inside
  | .succ_ne_zero          => negTrans_succ_ne_zero
  | .succ_inj              => negTrans_succ_inj
  -- Equational axioms: eqAtType is purely universal, use negTrans_pu_axiom
  | .proj_ax               => negTrans_proj_ax adm
  | .comb_ax               => negTrans_comb_ax adm
  | .rec_zero              => negTrans_rec_zero adm
  | .rec_succ              => negTrans_rec_succ adm
  -- QF-ER
  | .qfer (ρ := ρ_v) (σ := σ_v) (s := s_v) (t := t_v) (r := r_v) hqf hvf h_inner => by
      -- ih : NT(A₀ → eq_ρ s t) = ¬¬(A₀ → eq_ρ.ki)
      let ih := negTrans_sound h_inner
      simp only [Formula.negTrans, Formula.kurodaInner, kurodaInner_qf _ hqf] at ih ⊢
      -- step1: A₀ → ¬¬eq_ρ.ki  (from ¬¬(A₀ → eq_ρ.ki) using nn_imp_extract)
      let step1 := Derivable.mp ih nn_imp_extract
      -- step2: A₀ → eq_ρ  (syllogism with backward of negTrans_iff_pu)
      let bwd := (negTrans_iff_pu (a := Allowed.nt_target) (Premises := Premises) adm (eqAtType EqX ρ_v s_v t_v)
        (eqAtType_isPU adm ρ_v s_v t_v)).2
      let step2 := Derivable.syllogism step1 bwd
      -- step3: A₀ → eq_σ r[s] r[t]  (QF-ER)
      let step3 := Derivable.qfer (σ := σ_v) (r := r_v) hqf hvf step2
      -- step4: A₀ → ¬¬eq_σ.ki  (syllogism with forward of negTrans_iff_pu)
      let fwd := (negTrans_iff_pu (a := Allowed.nt_target) (Premises := Premises) adm
        (eqAtType EqX σ_v (r_v.subst0 s_v) (r_v.subst0 t_v))
        (eqAtType_isPU adm σ_v _ _)).1
      let step4 := Derivable.syllogism step3 fwd
      -- step5: ¬¬(A₀ → eq_σ.ki) = NT(A₀ → eq_σ)
      exact Derivable.mp step4 neg_neg_imp_rev
  -- induction
  | .induction h_zero h_step =>
      negTrans_induction (negTrans_sound h_zero) (negTrans_sound h_step)
  -- Extension principles
  | .lem _                 => negTrans_lem _
  | .qfac _ hqf hvf        => negTrans_qfac adm hqf hvf
  | .ac h ..               => absurd h (by decide)
  | .markov h ..           => absurd h (by decide)
  | .ip h ..               => absurd h (by decide)

end NegTransSound

end Metatheorems
