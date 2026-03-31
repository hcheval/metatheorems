/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Mathlib
import Metatheorems.Language


namespace Metatheorems

/-!
# Semantics: The Full Type Structure S^{ω,X}

Following §1.1 and Proposition 2.3.52, we define the set-theoretic model
S^{ω,X} that interprets WE-HA^{ω,X}.

Given an abstract space family `X : ι → Type` providing a Lean type for each
base type, we interpret:
- Type 0 as ℕ
- Type X_i as X i
- Type ρ → τ as (Ty.interpret ρ) → (Ty.interpret τ)

## Main Definitions

* `Ty.interpret` — Interpretation of types as Lean types (Def. 1.1.1).
* `Ctx.interpret` — Interpretation of contexts as nested products.
* `Term.interpret` — Evaluation of terms in the model.
* `Formula.interpret` — Interpretation of formulas as Lean propositions.
-/

-- ============================================================================
-- Type interpretation
-- ============================================================================

/-- Interpretation of types in S^{ω,X} (Definition 1.1.1).

  S_0       := ℕ
  S_{X_i}   := X i
  S_{ρ → τ} := S_τ ^ S_ρ  (function space) -/
def Ty.interpret {ι : Type} (X : ι → Type) : Ty ι → Type
  | .nat      => Nat
  | .base i   => X i
  | .arr ρ τ  => Ty.interpret X ρ → Ty.interpret X τ

/-- Interpretation of a typing context as a nested product. -/
def Ctx.interpret {ι : Type} (X : ι → Type) : Ctx ι → Type
  | []      => Unit
  | ρ :: Γ  => Ty.interpret X ρ × Ctx.interpret X Γ

-- ============================================================================
-- Environment lookup
-- ============================================================================

/-- Look up a variable in an interpreted context. -/
def Ctx.lookup {ι : Type} {X : ι → Type} :
    {Γ : Ctx ι} → {τ : Ty ι} → Var Γ τ → Ctx.interpret X Γ → Ty.interpret X τ
  | _ :: _, _, .vz,   (v, _)   => v
  | _ :: _, _, .vs x, (_, env) => Ctx.lookup x env

-- ============================================================================
-- Term evaluation
-- ============================================================================

/-- Data needed to interpret abstract space constants:
    - An element of `Ty.interpret X (F f)` for each function constant f
    - A zero element of `X i` for each base type X_i -/
structure SpaceInterp {ι : Type} (X : ι → Type) (F : ι → Ty ι) where
  /-- Interpretation of function constants f_χ ∈ F. -/
  funcInterp : (f : ι) → Ty.interpret X (F f)
  /-- Interpretation of zero elements 0_{X_i}. -/
  zeroInterp : (i : ι) → X i

/-- Evaluate a term in the model S^{ω,X}.

The interpretation of constants follows Proposition 2.3.52:
  [0]     := 0
  [S]     := Nat.succ
  [Π]     := fun x y => x
  [Σ]     := fun x y z => x z (y z)
  [R]     := primitive recursion
  [f_χ]   := spaceInterp.funcInterp f
  [0_{X_i}] := spaceInterp.zeroInterp i -/
def Term.interpret {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → Ctx.interpret X Γ → Ty.interpret X τ
  | _, _, .var v,       env => Ctx.lookup v env
  | _, _, .app f a,     env => (Term.interpret si f env) (Term.interpret si a env)
  | _, _, .zero,        _   => (0 : Nat)
  | _, _, .succ,        _   => (Nat.succ : Nat → Nat)
  | _, _, .proj _ _,    _   => fun x _ => x
  | _, _, .comb _ _ _,  _   => fun x y z => x z (y z)
  | _, _, .prec _,      _   => fun y z n => Nat.rec y (fun n ih => z ih n) n
  | _, _, .func f,      _   => si.funcInterp f
  | _, _, .zeroX i,     _   => si.zeroInterp i

-- ============================================================================
-- Formula interpretation
-- ============================================================================

/-- Interpret a formula as a Lean proposition. -/
def Formula.interpret {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → Formula F Γ → Ctx.interpret X Γ → Prop
  | _, .bot,      _   => False
  | _, .eq0 s t,  env => Term.interpret si s env = Term.interpret si t env
  | _, .and A B,  env => Formula.interpret si A env ∧ Formula.interpret si B env
  | _, .or  A B,  env => Formula.interpret si A env ∨ Formula.interpret si B env
  | _, .imp A B,  env => Formula.interpret si A env → Formula.interpret si B env
  | _, .all ρ A,  env => ∀ x : Ty.interpret X ρ, Formula.interpret si A (x, env)
  | _, .ex  ρ A,  env => ∃ x : Ty.interpret X ρ, Formula.interpret si A (x, env)

notation "‖" t "‖" si env => Term.interpret si t env
notation "‖" A "‖ₚ" si env => Formula.interpret si A env

-- ============================================================================
-- Substitution environment
-- ============================================================================

/-- Apply a substitution to an environment: evaluate each variable of Γ
    in the target environment via the substitution. -/
def Ctx.interpretSubst {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) : {Γ Δ : Ctx ι} → Term.Subst F Γ Δ → Ctx.interpret X Δ → Ctx.interpret X Γ
  | [],     _, _, _   => ()
  | _ :: _, _, s, env => (Term.interpret si (s .vz) env, Ctx.interpretSubst si (fun v => s (.vs v)) env)

-- ============================================================================
-- Term evaluation commutes with weakening and substitution
-- ============================================================================

/-- Evaluating a weakened term in an extended environment equals the original. -/
lemma Term.interpret_weaken {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {τ σ : Ty ι}
    (t : Term F Γ τ) (v : Ty.interpret X σ) (env : Ctx.interpret X Γ) :
    Term.interpret si t.weaken (v, env) = Term.interpret si t env := by
  induction t with
  | var w => simp only [Term.weaken, Var.weaken, Term.interpret, Ctx.lookup]
  | app _ _ ihf iha => simp only [Term.weaken, Term.interpret, ihf, iha]
  | zero => simp [Term.weaken, Term.interpret]
  | succ => simp [Term.weaken, Term.interpret]
  | proj _ _ => simp [Term.weaken, Term.interpret]
  | comb _ _ _ => simp [Term.weaken, Term.interpret]
  | prec _ => simp [Term.weaken, Term.interpret]
  | func _ => simp [Term.weaken, Term.interpret]
  | zeroX _ => simp [Term.weaken, Term.interpret]

private lemma lookupVar_interpCtxSubst {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (s : Term.Subst F Γ Δ) (v : Var Γ τ) (env : Ctx.interpret X Δ) :
    Ctx.lookup v (Ctx.interpretSubst si s env) = Term.interpret si (s v) env := by
  induction v with
  | vz => simp [Ctx.interpretSubst, Ctx.lookup]
  | vs w ih => simp [Ctx.interpretSubst, Ctx.lookup, ih]

lemma Term.interpret_substF {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (s : Term.Subst F Γ Δ) (t : Term F Γ τ) (env : Ctx.interpret X Δ) :
    Term.interpret si (t.subst s) env = Term.interpret si t (Ctx.interpretSubst si s env) := by
  induction t with
  | var v => simp [Term.subst, Term.interpret, lookupVar_interpCtxSubst]
  | app _ _ ihf iha => simp [Term.subst, Term.interpret, ihf, iha]
  | zero => simp [Term.subst, Term.interpret]
  | succ => simp [Term.subst, Term.interpret]
  | proj _ _ => simp [Term.subst, Term.interpret]
  | comb _ _ _ => simp [Term.subst, Term.interpret]
  | prec _ => simp [Term.subst, Term.interpret]
  | func _ => simp [Term.subst, Term.interpret]
  | zeroX _ => simp [Term.subst, Term.interpret]

lemma Ctx.interpretSubst_weaken_eq {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {σ : Ty ι}
    (s : Term.Subst F Γ Δ) (env : Ctx.interpret X Δ) (v : Ty.interpret X σ) :
    Ctx.interpretSubst si (fun w => (s w).weaken) (v, env) = Ctx.interpretSubst si s env := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih =>
    simp only [Ctx.interpretSubst]
    exact Prod.ext (Term.interpret_weaken si (s .vz) v env) (ih (fun w => s (.vs w)))

lemma Ctx.interpretSubst_id {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (env : Ctx.interpret X Γ) :
    Ctx.interpretSubst si (fun v => .var v) env = env := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih =>
    obtain ⟨a, env'⟩ := env
    simp only [Ctx.interpretSubst, Term.interpret, Ctx.lookup]
    refine Prod.ext rfl ?_
    have : Ctx.interpretSubst si (fun w => ((.var w : Term F _ _)).weaken) (a, env') =
           Ctx.interpretSubst si (fun v => .var v) env' := Ctx.interpretSubst_weaken_eq si _ env' a
    simp only [Term.weaken, Var.weaken] at this
    rw [this, ih env']

lemma Ctx.interpretSubst_ext {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {σ : Ty ι} (s : Term.Subst F Γ Δ)
    (env : Ctx.interpret X Δ) (v : Ty.interpret X σ) :
    Ctx.interpretSubst si (Term.Subst.ext s) (v, env) = (v, Ctx.interpretSubst si s env) := by
  simp only [Ctx.interpretSubst, Term.Subst.ext, Term.interpret, Ctx.lookup]
  exact Prod.ext rfl (Ctx.interpretSubst_weaken_eq si s env v)

/-- Renaming is a special case of substitution (each variable maps to .var). -/
private lemma Term.rename_eq_subst {ι : Type} {F : ι → Ty ι} {Γ Δ : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Δ) (t : Term F Γ τ) :
    t.rename r = t.subst (fun v => .var (r v)) := by
  induction t with
  | var v => rfl
  | app _ _ ihf iha => simp only [Term.rename, Term.subst, ihf, iha]
  | zero => rfl
  | succ => rfl
  | proj _ _ => rfl
  | comb _ _ _ => rfl
  | prec _ => rfl
  | func _ => rfl
  | zeroX _ => rfl

/-- Term evaluation commutes with renaming. -/
theorem Term.interpret_rename {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Δ) (t : Term F Γ τ) (env : Ctx.interpret X Δ) :
    Term.interpret si (t.rename r) env =
    Term.interpret si t (Ctx.interpretSubst si (fun v => .var (r v)) env) := by
  rw [Term.rename_eq_subst, Term.interpret_substF]

lemma Ctx.interpretSubst_subst0_map {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (t : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    Ctx.interpretSubst si (Term.subst0_map t) env = (Term.interpret si t env, env) := by
  simp only [Ctx.interpretSubst, Term.subst0_map, Term.interpret]
  exact Prod.ext rfl (Ctx.interpretSubst_id si env)

lemma Ctx.interpretSubst_substVar0_map {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (t : Term F (ρ :: Γ) ρ) (v : Ty.interpret X ρ) (env : Ctx.interpret X Γ) :
    Ctx.interpretSubst si (Formula.Term.substVar0_map t) (v, env) = (Term.interpret si t (v, env), env) := by
  simp only [Ctx.interpretSubst, Formula.Term.substVar0_map, Term.interpret, Ctx.lookup]
  refine Prod.ext rfl ?_
  have h : (fun {τ : Ty ι} (w : Var Γ τ) =>
              (Term.var (Var.vs w) : Term F (ρ :: Γ) τ)) =
           (fun {τ : Ty ι} (w : Var Γ τ) =>
              (Term.var w : Term F Γ τ).weaken) := by funext; rfl
  rw [h, Ctx.interpretSubst_weaken_eq, Ctx.interpretSubst_id]

lemma Term.interpret_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ τ : Ty ι}
    (t : Term F (ρ :: Γ) τ) (u : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    Term.interpret si (t.subst0 u) env = Term.interpret si t (Term.interpret si u env, env) := by
  induction t with
  | var v => cases v with
    | vz => simp [Term.subst0, Term.subst, Term.subst0_map, Term.interpret, Ctx.lookup]
    | vs w => simp [Term.subst0, Term.subst, Term.subst0_map, Term.interpret, Ctx.lookup]
  | app f a ihf iha =>
      change Term.interpret si (Term.app (f.subst0 u) (a.subst0 u)) env = _
      simp only [Term.interpret, ihf, iha]
  | zero => simp [Term.subst0, Term.subst, Term.interpret]
  | succ => simp [Term.subst0, Term.subst, Term.interpret]
  | proj _ _ => simp [Term.subst0, Term.subst, Term.interpret]
  | comb _ _ _ => simp [Term.subst0, Term.subst, Term.interpret]
  | prec _ => simp [Term.subst0, Term.subst, Term.interpret]
  | func _ => simp [Term.subst0, Term.subst, Term.interpret]
  | zeroX _ => simp [Term.subst0, Term.subst, Term.interpret]

end Metatheorems
