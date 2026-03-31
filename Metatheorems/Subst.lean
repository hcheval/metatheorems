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

-- ============================================================================
-- Renamings (variable-to-variable maps)
-- ============================================================================

/-- A renaming from context Γ to context Δ: maps each variable in Γ to
    a variable of the same type in Δ. -/
def Renaming {ι : Type} (Γ Δ : Ctx ι) : Type :=
  ∀ {τ : Ty ι}, Var Γ τ → Var Δ τ

namespace Renaming

variable {ι : Type}

/-- The identity renaming. -/
def id : Renaming Γ Γ := fun v => v

/-- Extend a renaming under a binder: if r : Γ → Δ, then
    ext r : (σ :: Γ) → (σ :: Δ) maps vz to vz and (vs v) to vs (r v). -/
def ext (r : Renaming Γ Δ) : Renaming (σ :: Γ) (σ :: Δ) :=
  fun v => match v with
  | .vz   => .vz
  | .vs w => .vs (r w)

/-- Shift renaming: weakens all variables by one. -/
def shift : Renaming Γ (σ :: Γ) := Var.vs

end Renaming

-- ============================================================================
-- Renaming on terms
-- ============================================================================

namespace Term

variable {ι : Type} {F : ι → Ty ι}

/-- Apply a renaming to a term. -/
def rename (r : Renaming Γ Δ) : Term F Γ τ → Term F Δ τ
  | .var v         => .var (r v)
  | .app f a       => .app (rename r f) (rename r a)
  | .zero          => .zero
  | .succ          => .succ
  | .proj ρ' τ'    => .proj ρ' τ'
  | .comb δ' ρ' τ' => .comb δ' ρ' τ'
  | .prec ρ'       => .prec ρ'
  | .func f        => .func f
  | .zeroX i       => .zeroX i

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
  | .zero          => .zero
  | .succ          => .succ
  | .proj ρ' τ'    => .proj ρ' τ'
  | .comb δ' ρ' τ' => .comb δ' ρ' τ'
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

/-- Applying a substitution after a renaming with an identity composition leaves terms
    unchanged.  Specifically: if `s ∘ r = Var.var` on all variables in Γ, then
    `(t.rename r).subst s = t`. -/
theorem subst_rename_id {Γ Γ' : Ctx ι}
    (r : Renaming Γ Γ') (s : Subst F Γ' Γ)
    (h : ∀ {τ} (v : Var Γ τ), s (r v) = Term.var v)
    {τ : Ty ι} (t : Term F Γ τ) :
    (t.rename r).subst s = t := by
  induction t with
  | var v => exact h v
  | app f a ihf iha => simp [Term.rename, Term.subst, ihf, iha]
  | zero | succ | proj | comb | prec | func | zeroX => rfl

/-- Weakening commutes with extended substitution:
    `t.weaken.subst (Subst.ext σ) = (t.subst σ).weaken`.
    Standard de Bruijn naturality lemma. -/
theorem weaken_subst_ext {Γ Δ : Ctx ι} {σ_ty : Ty ι}
    (t : Term F Γ τ) (σ : Subst F Γ Δ) :
    (t.weaken (σ := σ_ty)).subst (Subst.ext σ) = (t.subst σ).weaken := by
  induction t with
  | var v => rfl
  | app f a ihf iha => simp [weaken, subst, ihf, iha]
  | zero | succ | proj | comb | prec | func | zeroX => rfl

/-- Weakening then substituting for variable 0 cancels out:
    `t.weaken.subst0 s = t`. -/
theorem weaken_subst0 (t : Term F Γ τ) (s : Term F Γ ρ) :
    t.weaken.subst0 s = t := by
  induction t with
  | var v => rfl
  | app f a ihf iha =>
    change app (f.weaken.subst0 s) (a.weaken.subst0 s) = app f a
    rw [ihf, iha]
  | zero | succ | proj | comb | prec | func | zeroX => rfl

end Term

end Metatheorems
