/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Mathlib
import Metatheorems.Language

/-!
# Semantics: The Full Type Structure S^{ω,X}

Following §1.1 and Proposition 2.3.52, we define the set-theoretic model
S^{ω,X} that interprets WE-HA^{ω,X}.

Given an abstract space family `X : ι → Type` providing a Lean type for each
base type, we interpret:
- Type 0 as ℕ
- Type X_i as X i
- Type ρ → τ as (interpTy ρ) → (interpTy τ)

## Main Definitions

* `interpTy` — Interpretation of types as Lean types (Def. 1.1.1).
* `interpCtx` — Interpretation of contexts as nested products.
* `interpTerm` — Evaluation of terms in the model.
* `interpFormula` — Interpretation of formulas as Lean propositions.
-/

-- ============================================================================
-- Type interpretation
-- ============================================================================

/-- Interpretation of types in S^{ω,X} (Definition 1.1.1).

  S_0       := ℕ
  S_{X_i}   := X i
  S_{ρ → τ} := S_τ ^ S_ρ  (function space) -/
def interpTy {ι : Type} (X : ι → Type) : Ty ι → Type
  | .nat      => Nat
  | .base i   => X i
  | .arr ρ τ  => interpTy X ρ → interpTy X τ

/-- Interpretation of a typing context as a nested product. -/
def interpCtx {ι : Type} (X : ι → Type) : Ctx ι → Type
  | []      => Unit
  | ρ :: Γ  => interpTy X ρ × interpCtx X Γ

-- ============================================================================
-- Environment lookup
-- ============================================================================

/-- Look up a variable in an interpreted context. -/
def lookupVar {ι : Type} {X : ι → Type} :
    {Γ : Ctx ι} → {τ : Ty ι} → Var Γ τ → interpCtx X Γ → interpTy X τ
  | _ :: _, _, .vz,   (v, _)   => v
  | _ :: _, _, .vs x, (_, env) => lookupVar x env

-- ============================================================================
-- Term evaluation
-- ============================================================================

/-- Data needed to interpret abstract space constants:
    - An element of `interpTy X (F f)` for each function constant f
    - A zero element of `X i` for each base type X_i -/
structure SpaceInterp {ι : Type} (X : ι → Type) (F : ι → Ty ι) where
  /-- Interpretation of function constants f_χ ∈ F. -/
  funcInterp : (f : ι) → interpTy X (F f)
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
def interpTerm {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → interpCtx X Γ → interpTy X τ
  | _, _, .var v,       env => lookupVar v env
  | _, _, .app f a,     env => (interpTerm si f env) (interpTerm si a env)
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
def interpFormula {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → Formula F Γ → interpCtx X Γ → Prop
  | _, .bot,      _   => False
  | _, .eq0 s t,  env => interpTerm si s env = interpTerm si t env
  | _, .and A B,  env => interpFormula si A env ∧ interpFormula si B env
  | _, .or  A B,  env => interpFormula si A env ∨ interpFormula si B env
  | _, .imp A B,  env => interpFormula si A env → interpFormula si B env
  | _, .all ρ A,  env => ∀ x : interpTy X ρ, interpFormula si A (x, env)
  | _, .ex  ρ A,  env => ∃ x : interpTy X ρ, interpFormula si A (x, env)

-- ============================================================================
-- Substitution environment
-- ============================================================================

/-- Apply a substitution to an environment: evaluate each variable of Γ
    in the target environment via the substitution. -/
def interpCtxSubst {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) : {Γ Δ : Ctx ι} → Term.Subst F Γ Δ → interpCtx X Δ → interpCtx X Γ
  | [],     _, _, _   => ()
  | _ :: _, _, s, env => (interpTerm si (s .vz) env, interpCtxSubst si (fun v => s (.vs v)) env)

-- ============================================================================
-- Term evaluation commutes with weakening and substitution
-- ============================================================================

/-- Evaluating a weakened term in an extended environment equals the original. -/
lemma interpTerm_weaken {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {τ σ : Ty ι}
    (t : Term F Γ τ) (v : interpTy X σ) (env : interpCtx X Γ) :
    interpTerm si t.weaken (v, env) = interpTerm si t env := by
  induction t with
  | var w => simp only [Term.weaken, Var.weaken, interpTerm, lookupVar]
  | app _ _ ihf iha => simp only [Term.weaken, interpTerm, ihf, iha]
  | zero => simp [Term.weaken, interpTerm]
  | succ => simp [Term.weaken, interpTerm]
  | proj _ _ => simp [Term.weaken, interpTerm]
  | comb _ _ _ => simp [Term.weaken, interpTerm]
  | prec _ => simp [Term.weaken, interpTerm]
  | func _ => simp [Term.weaken, interpTerm]
  | zeroX _ => simp [Term.weaken, interpTerm]

private lemma lookupVar_interpCtxSubst {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (s : Term.Subst F Γ Δ) (v : Var Γ τ) (env : interpCtx X Δ) :
    lookupVar v (interpCtxSubst si s env) = interpTerm si (s v) env := by
  induction v with
  | vz => simp [interpCtxSubst, lookupVar]
  | vs w ih => simp [interpCtxSubst, lookupVar, ih]

lemma interpTerm_substF {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (s : Term.Subst F Γ Δ) (t : Term F Γ τ) (env : interpCtx X Δ) :
    interpTerm si (t.subst s) env = interpTerm si t (interpCtxSubst si s env) := by
  induction t with
  | var v => simp [Term.subst, interpTerm, lookupVar_interpCtxSubst]
  | app _ _ ihf iha => simp [Term.subst, interpTerm, ihf, iha]
  | zero => simp [Term.subst, interpTerm]
  | succ => simp [Term.subst, interpTerm]
  | proj _ _ => simp [Term.subst, interpTerm]
  | comb _ _ _ => simp [Term.subst, interpTerm]
  | prec _ => simp [Term.subst, interpTerm]
  | func _ => simp [Term.subst, interpTerm]
  | zeroX _ => simp [Term.subst, interpTerm]

lemma interpCtxSubst_weaken_eq {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {σ : Ty ι}
    (s : Term.Subst F Γ Δ) (env : interpCtx X Δ) (v : interpTy X σ) :
    interpCtxSubst si (fun w => (s w).weaken) (v, env) = interpCtxSubst si s env := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih =>
    simp only [interpCtxSubst]
    exact Prod.ext (interpTerm_weaken si (s .vz) v env) (ih (fun w => s (.vs w)))

lemma interpCtxSubst_id {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (env : interpCtx X Γ) :
    interpCtxSubst si (fun v => .var v) env = env := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih =>
    obtain ⟨a, env'⟩ := env
    simp only [interpCtxSubst, interpTerm, lookupVar]
    refine Prod.ext rfl ?_
    have : interpCtxSubst si (fun w => ((.var w : Term F _ _)).weaken) (a, env') =
           interpCtxSubst si (fun v => .var v) env' := interpCtxSubst_weaken_eq si _ env' a
    simp only [Term.weaken, Var.weaken] at this
    rw [this, ih env']

lemma interpCtxSubst_ext {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {σ : Ty ι} (s : Term.Subst F Γ Δ)
    (env : interpCtx X Δ) (v : interpTy X σ) :
    interpCtxSubst si (Term.Subst.ext s) (v, env) = (v, interpCtxSubst si s env) := by
  simp only [interpCtxSubst, Term.Subst.ext, interpTerm, lookupVar]
  exact Prod.ext rfl (interpCtxSubst_weaken_eq si s env v)

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
theorem interpTerm_rename {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Δ) (t : Term F Γ τ) (env : interpCtx X Δ) :
    interpTerm si (t.rename r) env =
    interpTerm si t (interpCtxSubst si (fun v => .var (r v)) env) := by
  rw [Term.rename_eq_subst, interpTerm_substF]

lemma interpCtxSubst_subst0_map {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (t : Term F Γ ρ) (env : interpCtx X Γ) :
    interpCtxSubst si (Term.subst0_map t) env = (interpTerm si t env, env) := by
  simp only [interpCtxSubst, Term.subst0_map, interpTerm]
  exact Prod.ext rfl (interpCtxSubst_id si env)

lemma interpCtxSubst_substVar0_map {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (t : Term F (ρ :: Γ) ρ) (v : interpTy X ρ) (env : interpCtx X Γ) :
    interpCtxSubst si (Formula.Term.substVar0_map t) (v, env) = (interpTerm si t (v, env), env) := by
  simp only [interpCtxSubst, Formula.Term.substVar0_map, interpTerm, lookupVar]
  refine Prod.ext rfl ?_
  have h : (fun {τ : Ty ι} (w : Var Γ τ) =>
              (Term.var (Var.vs w) : Term F (ρ :: Γ) τ)) =
           (fun {τ : Ty ι} (w : Var Γ τ) =>
              (Term.var w : Term F Γ τ).weaken) := by funext; rfl
  rw [h, interpCtxSubst_weaken_eq, interpCtxSubst_id]

lemma interpTerm_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ τ : Ty ι}
    (t : Term F (ρ :: Γ) τ) (u : Term F Γ ρ) (env : interpCtx X Γ) :
    interpTerm si (t.subst0 u) env = interpTerm si t (interpTerm si u env, env) := by
  induction t with
  | var v => cases v with
    | vz => simp [Term.subst0, Term.subst, Term.subst0_map, interpTerm, lookupVar]
    | vs w => simp [Term.subst0, Term.subst, Term.subst0_map, interpTerm, lookupVar]
  | app f a ihf iha =>
      change interpTerm si (Term.app (f.subst0 u) (a.subst0 u)) env = _
      simp only [interpTerm, ihf, iha]
  | zero => simp [Term.subst0, Term.subst, interpTerm]
  | succ => simp [Term.subst0, Term.subst, interpTerm]
  | proj _ _ => simp [Term.subst0, Term.subst, interpTerm]
  | comb _ _ _ => simp [Term.subst0, Term.subst, interpTerm]
  | prec _ => simp [Term.subst0, Term.subst, interpTerm]
  | func _ => simp [Term.subst0, Term.subst, interpTerm]
  | zeroX _ => simp [Term.subst0, Term.subst, interpTerm]
