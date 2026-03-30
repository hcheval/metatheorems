/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics

/-!
# Strong Majorizability (total majorizer)

This file defines the "strong" version of majorizability where every semantic
value is majorizable (via a total `majorizer` function), following the Lean 3
formalization. This is stronger than `AbstractMajorizability` (which only
guarantees constants are majorizable), but is the natural assumption for
the general metatheorem.

## Main Definitions

* `Majorizability` — structure with a total majorizer on all semantic values
-/

-- ============================================================================
-- Majorizability (strong version with total majorizer)
-- ============================================================================

/-- Majorizability with a total majorizer on all semantic values.

This is the "strong" version: instead of proving each constant is majorizable
and deriving closed terms, we directly assume every element of the type
structure has a majorant. This matches the Lean 3 formalization and makes
the general metatheorem straightforward to state. -/
structure Majorizability {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) where
  /-- The majorizability relation at type ρ: `maj ρ x_star x` means x* ≥*_ρ x. -/
  maj : (ρ : Ty ι) → interpTy X ρ.hat → interpTy X ρ → Prop
  /-- Property 1: respects the natural number order. -/
  maj_le : ∀ {n m : Nat}, maj .nat n m → n ≥ m
  /-- Property 2: respects term application. -/
  maj_app : ∀ {ρ τ : Ty ι}
    {f_star : interpTy X (ρ →ₜ τ).hat} {f : interpTy X (ρ →ₜ τ)}
    {x_star : interpTy X ρ.hat} {x : interpTy X ρ},
    maj (ρ →ₜ τ) f_star f → maj ρ x_star x → maj τ (f_star x_star) (f x)
  /-- Total majorizer: every semantic value has a majorant. -/
  majorizer : {ρ : Ty ι} → interpTy X ρ → interpTy X ρ.hat
  /-- The majorizer actually majorizes. -/
  majorizer_maj : ∀ {ρ : Ty ι} (x : interpTy X ρ), maj ρ (majorizer x) x
