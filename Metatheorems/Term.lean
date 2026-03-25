/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.TypeSystem

/-!
# Terms of WE-HA^{ω,X}

Following Chapter 2 (Definition 2.3.1) of the reference document, we define the
intrinsically typed terms of Weakly Extensional Heyting Arithmetic over T^X.

Terms are combinatory: the primitive constants are 0, S, Π (projector),
Σ (combinator), and R (recursor), plus application. Lambda abstraction is
defined as a derived operation by combinatory compilation (Definition 2.3.19).

## Main Definitions

* `Ctx ι` — Typing contexts (lists of types).
* `Var Γ τ` — Well-typed de Bruijn variable in context Γ of type τ.
* `Term F Γ τ` — Intrinsically typed terms in context Γ of type τ.
* `Term.lam` — Lambda abstraction by combinatory compilation (Def. 2.3.19).
-/

open Ty

/-- A typing context is a list of types. -/
abbrev Ctx (ι : Type) := List (Ty ι)

/-- The type of the single recursor R_ρ (§9.6, equation 9.54). -/
def recTy {ι : Type} (ρ : Ty ι) : Ty ι :=
  ρ →ₜ (ρ →ₜ Ty.nat →ₜ ρ) →ₜ Ty.nat →ₜ ρ

-- ============================================================================
-- Well-typed de Bruijn variables
-- ============================================================================

/-- A well-typed de Bruijn variable in context Γ of type τ.
    `Var.vz` is the most recently bound variable (index 0).
    `Var.vs` shifts past one binding. -/
inductive Var {ι : Type} : Ctx ι → Ty ι → Type where
  | vz : Var (τ :: Γ) τ
  | vs : Var Γ τ → Var (σ :: Γ) τ

namespace Var

variable {ι : Type}

/-- Weaken a variable: embed into an extended context. -/
def weaken : Var Γ τ → Var (σ :: Γ) τ := .vs

end Var

-- ============================================================================
-- Terms
-- ============================================================================

/-- Terms of WE-HA^{ω,X} (Definition 2.3.1) with intrinsic typing.

`Term F Γ τ` is a term of type `τ` in typing context `Γ`, where:
- `ι` is the index set for abstract spaces
- `F : ι → Ty ι` assigns a type to each abstract space function constant -/
inductive Term {ι : Type} (F : ι → Ty ι) : Ctx ι → Ty ι → Type where
  /-- Variable: well-typed de Bruijn index into the context. -/
  | var   : Var Γ τ → Term F Γ τ
  /-- Application. -/
  | app   : Term F Γ (ρ →ₜ τ) → Term F Γ ρ → Term F Γ τ
  /-- Zero constant 0^0. -/
  | zero  : Term F Γ Ty.nat
  /-- Successor S^{0→0}. -/
  | succ  : Term F Γ (Ty.nat →ₜ Ty.nat)
  /-- Projector Π_{ρ,τ} (K combinator): Πxy = x. -/
  | proj  : (ρ τ : Ty ι) → Term F Γ (ρ →ₜ τ →ₜ ρ)
  /-- Combinator Σ_{δ,ρ,τ} (S combinator): Σxyz = xz(yz). -/
  | comb  : (δ ρ τ : Ty ι) →
            Term F Γ ((δ →ₜ ρ →ₜ τ) →ₜ (δ →ₜ ρ) →ₜ δ →ₜ τ)
  /-- Primitive recursor R_ρ. Named `prec` to avoid clash with inductive recursor. -/
  | prec  : (ρ : Ty ι) → Term F Γ (recTy ρ)
  /-- Abstract space function constant f_χ. -/
  | func  : (f : ι) → Term F Γ (F f)
  /-- Zero element 0_{X_i} for base type X_i. -/
  | zeroX : (i : ι) → Term F Γ (Ty.base i)

namespace Term

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Convenience
-- ============================================================================

/-- Apply to two arguments. -/
def app2 (f : Term F Γ (ρ →ₜ τ →ₜ σ)) (a : Term F Γ ρ) (b : Term F Γ τ) : Term F Γ σ :=
  (f.app a).app b

/-- Apply to three arguments. -/
def app3 (f : Term F Γ (ρ →ₜ τ →ₜ σ →ₜ ν)) (a : Term F Γ ρ) (b : Term F Γ τ)
    (c : Term F Γ σ) : Term F Γ ν :=
  ((f.app a).app b).app c

/-- The numeral n as a term. -/
def ofNat : (n : Nat) → Term F Γ Ty.nat
  | 0     => .zero
  | n + 1 => .app .succ (ofNat n)

-- ============================================================================
-- Weakening
-- ============================================================================

/-- Weaken a term: embed from context Γ into extended context (σ :: Γ). -/
def weaken : Term F Γ τ → Term F (σ :: Γ) τ
  | .var v         => .var v.weaken
  | .app f a       => .app f.weaken a.weaken
  | .zero          => .zero
  | .succ          => .succ
  | .proj ρ' τ'    => .proj ρ' τ'
  | .comb δ' ρ' τ' => .comb δ' ρ' τ'
  | .prec ρ'       => .prec ρ'
  | .func f        => .func f
  | .zeroX i       => .zeroX i

-- ============================================================================
-- Lambda abstraction (Definition 2.3.19)
-- ============================================================================

/-- Lambda abstraction by combinatory compilation (Definition 2.3.19).

Given `t : Term F (ρ :: Γ) τ` (term with free variable of type ρ at de Bruijn
index 0), produce `lam t : Term F Γ (ρ →ₜ τ)`.

The cases from the paper:
- (i)   t = var vz: λx.x = Σ_{ρ,0→ρ,ρ} Π_{ρ,0→ρ} Π_{ρ,0}  (identity = SKK)
- (ii)  t doesn't use var vz: λx.t = Π_{τ,ρ} t'  (t' is t with vz removed)
- (iii) t = app u v: λx.(u v) = Σ_{ρ,δ,τ} (λx.u) (λx.v) -/
def lam {ρ : Ty ι} : Term F (ρ :: Γ) τ → Term F Γ (ρ →ₜ τ)
  -- (i) λx.x = I = SKK
  | .var .vz =>
      app2 (Term.comb ρ (Ty.nat →ₜ ρ) ρ) (Term.proj ρ (Ty.nat →ₜ ρ)) (Term.proj ρ Ty.nat)
  -- (ii) λx.y = Π y  (for variables other than vz)
  | .var (.vs v) =>
      (Term.proj _ ρ).app (.var v)
  -- (iii) λx.(f a) = Σ (λx.f) (λx.a)
  | .app f a =>
      app2 (Term.comb ρ _ _) (lam f) (lam a)
  -- λx.c = Π c  (for all constants: they don't depend on x)
  | .zero          => (Term.proj _ ρ).app .zero
  | .succ          => (Term.proj _ ρ).app .succ
  | .proj ρ' τ'    => (Term.proj _ ρ).app (.proj ρ' τ')
  | .comb δ' ρ' τ' => (Term.proj _ ρ).app (.comb δ' ρ' τ')
  | .prec ρ'       => (Term.proj _ ρ).app (.prec ρ')
  | .func f        => (Term.proj _ ρ).app (.func f)
  | .zeroX i       => (Term.proj _ ρ).app (.zeroX i)

end Term
