/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.TypeSystem


namespace Metatheorems

/-!
# Terms of WE-HA^{ω,X}

Following Chapter 2 (Definition 2.3.1) of the reference document, we define the
intrinsically typed terms of Weakly Extensional Heyting Arithmetic over T^X.

The primitive constants are `0`, `S`, `R` (recursor), the space constants `0_X` and `f_χ`,
and the unit/product constructors, plus application and **lambda abstraction**.

**There are no `Π` and `Σ` combinators.** An earlier version of this docstring claimed there
were — that was stale, left over from when combinatory compilation (Def. 2.3.19) was the plan.
Lambda is a primitive constructor instead, and beta reduction `(λx.t) u =_τ t[u/x]` is an
axiom of the proof system (`Derivable.beta_eq`) rather than a consequence of combinator
axioms. So the combinatory sublanguage the reference document works in **does not exist here**;
see the design-table entry in `CLAUDE.md` for what that costs and why it was still the right
call.

## Main Definitions

* `Ctx ι` — Typing contexts (lists of types).
* `Var Γ τ` — Well-typed de Bruijn variable in context Γ of type τ.
* `Term F Γ τ` — Intrinsically typed terms in context Γ of type τ.
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
  /-- Primitive recursor R_ρ. Named `prec` to avoid clash with inductive recursor. -/
  | prec  : (ρ : Ty ι) → Term F Γ (recTy ρ)
  /-- Lambda abstraction: λx^ρ. body. -/
  | lam   : Term F (ρ :: Γ) τ → Term F Γ (ρ →ₜ τ)
  /-- Abstract space function constant f_χ. -/
  | func  : (f : ι) → Term F Γ (F f)
  /-- Zero element 0_{X_i} for base type X_i. -/
  | zeroX : (i : ι) → Term F Γ (Ty.base i)
  /-- The inhabitant of the unit type. -/
  | unitI : Term F Γ Ty.unit
  /-- Pairing. -/
  | mkPair : Term F Γ ρ → Term F Γ τ → Term F Γ (ρ ×ₜ τ)
  /-- First projection. -/
  | fst   : Term F Γ (ρ ×ₜ τ) → Term F Γ ρ
  /-- Second projection. -/
  | snd   : Term F Γ (ρ ×ₜ τ) → Term F Γ τ

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
-- Renamings and weakening
-- ============================================================================

/-- A renaming from context Γ to context Δ: maps each variable in Γ to
    a variable of the same type in Δ. -/
def Renaming (Γ Δ : Ctx ι) : Type :=
  ∀ {τ : Ty ι}, Var Γ τ → Var Δ τ

/-- Extend a renaming under a binder. -/
def Renaming.ext (r : Renaming Γ Δ) : Renaming (σ :: Γ) (σ :: Δ) :=
  fun v => match v with
  | .vz   => .vz
  | .vs w => .vs (r w)

/-- Shift renaming: weakens all variables by one. -/
def Renaming.shift : Renaming Γ (σ :: Γ) := Var.vs

/-- `Renaming.ext` at the two variable shapes. Stated so that `simp` can step through them:
unfolding the definition alone leaves a `match`. -/
@[simp] theorem Renaming.ext_vz {Γ Δ : Ctx ι} {σ : Ty ι} (r : Renaming Γ Δ) :
    Renaming.ext r (σ := σ) (τ := σ) .vz = .vz := rfl

@[simp] theorem Renaming.ext_vs {Γ Δ : Ctx ι} {σ τ : Ty ι} (r : Renaming Γ Δ) (w : Var Γ τ) :
    Renaming.ext r (σ := σ) (.vs w) = .vs (r w) := rfl

/-- Apply a renaming to a term. -/
def rename (r : Renaming Γ Δ) : Term F Γ τ → Term F Δ τ
  | .var v         => .var (r v)
  | .app f a       => .app (rename r f) (rename r a)
  | .lam body      => .lam (rename (Renaming.ext r) body)
  | .zero          => .zero
  | .succ          => .succ
  | .prec ρ'       => .prec ρ'
  | .func f        => .func f
  | .zeroX i       => .zeroX i
  | .unitI         => .unitI
  | .mkPair a b    => .mkPair (rename r a) (rename r b)
  | .fst p         => .fst (rename r p)
  | .snd p         => .snd (rename r p)

/-- Weaken a term: embed from context Γ into extended context (σ :: Γ). -/
def weaken : Term F Γ τ → Term F (σ :: Γ) τ :=
  rename Renaming.shift

end Term

end Metatheorems
