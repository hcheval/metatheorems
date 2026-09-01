/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/

/-!
# The Type System T^X

Following Chapter 1 of the reference document, we define the type system T^X:
a system of simple types over natural numbers, abstract base types {X_i}_{i:ι},
and function types (arrow types).

## Main Definitions

* `Ty ι` — The type system T^X parameterized by an index set `ι` for abstract spaces.
* `Ty.hat` — The hat-map ρ̂, replacing all ground types with `nat` (Def. 1.0.11).
* `Ty.args` — Decomposition ρ = ρ₁ → ... → ρₖ → ρ₀ giving [ρ₁,...,ρₖ] (Prop. 1.0.9).
* `Ty.ground` — The unique ground type ρ₀ of a type (Notation 1.0.10).
-/


namespace Metatheorems

/-- The type system T^X (Definition 1.0.1).

Given an index family `{X_i}_{i ∈ ι}`, the set of all finite types over ℕ and X
is defined inductively:
- `nat`: the type 0, intended to represent natural numbers
- `base i`: the type X_i for `i : ι`
- `arr ρ τ`: the function type ρ → τ

Arrow composition is right-associative: ρ → τ → δ means ρ → (τ → δ). -/
inductive Ty (ι : Type) : Type where
  | nat  : Ty ι
  | base : ι → Ty ι
  | arr  : Ty ι → Ty ι → Ty ι
  /-- The one-element type. Carries the trivial Dialectica witnesses. -/
  | unit : Ty ι
  /-- Product type. Needed so that Dialectica witness/counter *types* are
      object-level types, hence witnesses are `Term`s. -/
  | prod : Ty ι → Ty ι → Ty ι
  deriving DecidableEq, Repr

namespace Ty

variable {ι : Type}

/-- Right-associative arrow notation for types. -/
infixr:25 " →ₜ " => Ty.arr

/-- Product notation for types. -/
infixr:35 " ×ₜ " => Ty.prod

/-- A ground type is either `nat` or a base type `X_i` (not a function type). -/
def isGround : Ty ι → Bool
  | .nat    => true
  | .base _ => true
  | .unit   => true
  | .arr _ _ => false
  -- products are not arrows, so they are "ground" for the ρ₁→…→ρₖ→ρ₀ decomposition
  | .prod _ _ => true

/-- A type is T-based (or "nat-based") if it is built only from `nat` and `arr`,
    with no base types. This characterizes types in the subsystem T ⊂ T^X (Def. 1.0.6). -/
def isNatBased : Ty ι → Bool
  | .nat       => true
  | .base _    => false
  | .unit      => true
  | .arr ρ τ   => ρ.isNatBased && τ.isNatBased
  | .prod ρ τ  => ρ.isNatBased && τ.isNatBased

/-- The hat-map ρ̂ (Definition 1.0.11): replaces all ground types with `nat`.

For any type ρ ∈ T^X, its corresponding 0-based type ρ̂ is defined by:
- If ρ is a ground type, then ρ̂ = 0
- If ρ = τ → δ, then ρ̂ = τ̂ → δ̂ -/
def hat : Ty ι → Ty ι
  | .nat      => .nat
  | .base _   => .nat
  | .unit     => .unit
  | .arr ρ τ  => .arr ρ.hat τ.hat
  | .prod ρ τ => .prod ρ.hat τ.hat

/-- Decompose a type into its argument list (Proposition 1.0.9).

Any type ρ can be uniquely written as ρ = ρ₁ → ... → ρₖ → ρ₀ for some
ρ₁, ..., ρₖ ∈ T^X and some ground type ρ₀. This function returns [ρ₁,...,ρₖ]. -/
def args : Ty ι → List (Ty ι)
  | .arr ρ τ => ρ :: τ.args
  | _        => []

/-- The ground type of a type (Notation 1.0.10).

Given ρ = ρ₁ → ... → ρₖ → ρ₀, returns ρ₀ (the unique ground type). -/
def ground : Ty ι → Ty ι
  | .arr _ τ => τ.ground
  | t        => t

/-- The number of arguments of a type. -/
def arity : Ty ι → Nat
  | .arr _ τ => τ.arity + 1
  | _        => 0

-- ============================================================================
-- Basic lemmas
-- ============================================================================

theorem ground_isGround (τ : Ty ι) : τ.ground.isGround = true := by
  induction τ with
  | nat       => rfl
  | base _    => rfl
  | unit      => rfl
  | prod _ _ _ _ => rfl
  | arr _ _ _ ih => exact ih

theorem hat_isNatBased (τ : Ty ι) : τ.hat.isNatBased = true := by
  induction τ with
  | nat       => rfl
  | base _    => rfl
  | unit      => rfl
  | prod ρ τ ihρ ihτ => simp [hat, isNatBased, ihρ, ihτ]
  | arr ρ τ ihρ ihτ => simp [hat, isNatBased, ihρ, ihτ]

theorem hat_idempotent (τ : Ty ι) : τ.hat.hat = τ.hat := by
  induction τ with
  | nat       => rfl
  | base _    => rfl
  | unit      => rfl
  | prod ρ τ ihρ ihτ => simp [hat, ihρ, ihτ]
  | arr ρ τ ihρ ihτ => simp [hat, ihρ, ihτ]

theorem isNatBased_hat_eq (τ : Ty ι) (h : τ.isNatBased = true) : τ.hat = τ := by
  induction τ with
  | nat       => rfl
  | base _    => simp [isNatBased] at h
  | unit      => rfl
  | prod ρ τ ihρ ihτ =>
    simp [isNatBased, Bool.and_eq_true] at h
    simp [hat, ihρ h.1, ihτ h.2]
  | arr ρ τ ihρ ihτ =>
    simp [isNatBased, Bool.and_eq_true] at h
    simp [hat, ihρ h.1, ihτ h.2]

/-- The degree of a pure type (Definition 8.1.7). -/
def degree : Ty ι → Nat
  | .nat      => 0
  | .base _   => 0
  | .unit     => 0
  | .prod ρ τ => max ρ.degree τ.degree
  | .arr ρ τ  => max ρ.degree (τ.degree + 1)

end Ty

end Metatheorems
