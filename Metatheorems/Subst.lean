/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Term


namespace Metatheorems

/-!
# Substitution and Renaming for Terms

We define substitution, renaming, and related operations on well-typed terms.

## Main Definitions

* `Term.rename` — Apply a variable renaming to a term.
* `Term.subst0` — Substitute a term for the outermost bound variable (index 0).
-/

namespace Term

/-- The identity renaming. -/
def Renaming.id : Renaming Γ Γ := fun v => v

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Substitutions (variable-to-term maps)
-- ============================================================================

/-- A substitution from context Γ to context Δ: maps each variable in Γ to
    a term of the same type in Δ. -/
def Subst (F : ι → Ty ι) (Γ Δ : Ctx ι) : Type :=
  ∀ {τ : Ty ι}, Var Γ τ → Term F Δ τ

/-- The identity substitution. -/
def Subst.id : Subst F Γ Γ := fun v => .var v

/-- Extend a substitution under a binder. -/
def Subst.ext (s : Subst F Γ Δ) : Subst F (σ :: Γ) (σ :: Δ) :=
  fun v => match v with
  | .vz   => .var .vz
  | .vs w => (s w).weaken

/-- Apply a substitution to a term. -/
def subst (s : Subst F Γ Δ) : Term F Γ τ → Term F Δ τ
  | .var v         => s v
  | .app f a       => .app (subst s f) (subst s a)
  | .lam body      => .lam (subst (Subst.ext s) body)
  | .zero          => .zero
  | .succ          => .succ
  | .prec ρ'       => .prec ρ'
  | .func ff       => .func ff
  | .zeroX i       => .zeroX i

-- ============================================================================
-- Substitution for variable 0
-- ============================================================================

/-- The single-variable substitution: replace variable 0 with `s`,
    and shift all other variables down by one. -/
def subst0_map (s : Term F Γ ρ) : Subst F (ρ :: Γ) Γ :=
  fun v => match v with
  | .vz   => s
  | .vs w => .var w

/-- Substitute a term for the outermost bound variable (de Bruijn index 0). -/
def subst0 (t : Term F (ρ :: Γ) τ) (s : Term F Γ ρ) : Term F Γ τ :=
  subst (subst0_map s) t

-- ============================================================================
-- Foundational substitution/renaming commutation lemmas
-- ============================================================================

/-- Composing two renamings. -/
theorem rename_rename {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r₁ : Renaming Γ Δ) (r₂ : Renaming Δ Δ') (t : Term F Γ τ) :
    (t.rename r₁).rename r₂ = t.rename (fun v => r₂ (r₁ v)) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename]; exact congr (congrArg app (ihf r₁ r₂)) (iha r₁ r₂)
  | lam body ih =>
    simp only [rename]; congr 1
    rw [ih (Renaming.ext r₁) (Renaming.ext r₂)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX => rfl

/-- Renaming then substituting = substituting with composed map. -/
theorem rename_subst {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Δ) (s : Subst F Δ Δ') (t : Term F Γ τ) :
    (t.rename r).subst s = t.subst (fun v => s (r v)) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename, subst]; exact congr (congrArg app (ihf r s)) (iha r s)
  | lam body ih =>
    simp only [rename, subst]; congr 1
    rw [ih (Renaming.ext r) (Subst.ext s)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX => rfl

/-- Substituting then renaming = substituting with renamed map. -/
theorem subst_rename {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (s : Subst F Γ Δ) (r : Renaming Δ Δ') (t : Term F Γ τ) :
    (t.subst s).rename r = t.subst (fun v => (s v).rename r) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [subst, rename]; exact congr (congrArg app (ihf s r)) (iha s r)
  | lam body ih =>
    simp only [subst, rename]; congr 1
    rw [ih (Subst.ext s) (Renaming.ext r)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w =>
      show rename (Renaming.ext r) ((s w).weaken) = ((s w).rename r).weaken
      simp only [weaken]; rw [rename_rename, rename_rename]; rfl
  | zero | succ | prec | func | zeroX => rfl

/-- `Subst.ext` of the identity substitution is the identity. -/
theorem Subst.ext_id {Γ : Ctx ι} {σ : Ty ι} :
    @Subst.ext ι F Γ Γ σ Subst.id = @Subst.id ι F (σ :: Γ) := by
  funext τ v; cases v with
  | vz => rfl
  | vs w => rfl

/-- Identity substitution leaves terms unchanged. -/
theorem subst_id (t : Term F Γ τ) : t.subst Subst.id = t := by
  induction t with
  | var v => rfl
  | app _ _ ihf iha => simp only [subst]; exact congr (congrArg app ihf) iha
  | lam body ih => simp only [subst]; congr 1; rw [Subst.ext_id]; exact ih
  | zero | succ | prec | func | zeroX => rfl

/-- Renaming equals substitution with variable injection. -/
theorem rename_eq_subst (r : Renaming Γ Δ) (t : Term F Γ τ) :
    t.rename r = t.subst (fun v => .var (r v)) := by
  induction t generalizing Δ with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename, subst]; exact congr (congrArg app (ihf r)) (iha r)
  | lam body ih =>
    simp only [rename, subst]; congr 1
    rw [ih (Renaming.ext r)]; congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX => rfl

/-- Applying a substitution after a renaming with an identity composition leaves terms
    unchanged.  Corollary of `rename_subst`. -/
theorem subst_rename_id {Γ Γ' : Ctx ι}
    (r : Renaming Γ Γ') (s : Subst F Γ' Γ)
    (h : ∀ {τ} (v : Var Γ τ), s (r v) = Term.var v)
    {τ : Ty ι} (t : Term F Γ τ) :
    (t.rename r).subst s = t := by
  rw [rename_subst]
  have : (fun {τ} (v : Var Γ τ) => s (r v)) = @Subst.id ι F Γ :=
    funext fun τ => funext fun v => h v
  rw [this]; exact subst_id t

/-- Weakening commutes with extended substitution:
    `t.weaken.subst (Subst.ext σ) = (t.subst σ).weaken`.
    Standard de Bruijn naturality lemma. -/
theorem weaken_subst_ext {Γ Δ : Ctx ι} {σ_ty : Ty ι}
    (t : Term F Γ τ) (σ : Subst F Γ Δ) :
    (t.weaken (σ := σ_ty)).subst (Subst.ext σ) = (t.subst σ).weaken := by
  simp only [weaken]
  rw [rename_subst, subst_rename]; rfl

/-- Weakening then substituting for variable 0 cancels out:
    `t.weaken.subst0 s = t`. -/
theorem weaken_subst0 (t : Term F Γ τ) (s : Term F Γ ρ) :
    t.weaken.subst0 s = t := by
  simp only [subst0, weaken]
  rw [rename_subst]
  exact subst_id t

end Term

-- Re-export Renaming at Metatheorems level for backwards compatibility
abbrev Renaming {ι : Type} (Γ Δ : Ctx ι) := Term.Renaming Γ Δ

namespace Renaming
abbrev ext {ι : Type} {Γ Δ : Ctx ι} {σ : Ty ι} (r : Renaming Γ Δ) :
    Renaming (σ :: Γ) (σ :: Δ) := Term.Renaming.ext r
abbrev shift {ι : Type} {Γ : Ctx ι} {σ : Ty ι} : Renaming Γ (σ :: Γ) :=
    Term.Renaming.shift
abbrev id {ι : Type} {Γ : Ctx ι} : Renaming Γ Γ := Term.Renaming.id
end Renaming

end Metatheorems
