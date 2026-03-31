/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable
import Metatheorems.RealNumbers

namespace Metatheorems

/-!
# Metric Spaces as Abstract Spaces

Instantiates the WE-HA^{ω,X} framework for a single metric space (X, d).
Following Section 6.1 of the reference document:

* One abstract base type X (so `ι = Unit`)
* One function constant `d_X : X → X → ℝ` (the metric)
* Zero element `0_X : X` (a distinguished point)
* Equality at type X: `x =_X y ≡ d_X(x,y) =_ℝ 0`
* Axioms: symmetry, triangle inequality, non-negativity, reflexivity

## Main Definitions

* `MetricSpace.ι` — the index type `Unit`
* `MetricSpace.F` — the function constant types (`d_X : X → X → ℝ`)
* `MetricSpace.X` — the carrier types (`X ()` = the metric space)
* `MetricSpace.Premises` — the metric space axioms
-/

/-- Index type for a single metric space: one base type. -/
abbrev MetricSpace.ι := Unit

-- In a concrete instantiation, X () would be an actual type (e.g., a complete metric space).

/-- Function constant types for a metric space.
    The single function constant is `d_X : X → X → ℝ` (the metric).
    `ℝ` is encoded as `Ty.nat →ₜ Ty.nat` (type level 1). -/
def MetricSpace.F : MetricSpace.ι → Ty MetricSpace.ι
  | () => Ty.base () →ₜ Ty.base () →ₜ realTy MetricSpace.ι

/-- The type of metric space interpretations. Packages the carrier type,
    the metric function, and the distinguished point. -/
structure MetricSpaceInterp where
  /-- The carrier type of the metric space. -/
  carrier : Type
  /-- The metric function d : X × X → (ℕ → ℕ) (encoded reals). -/
  metric : carrier → carrier → (Nat → Nat)
  /-- The distinguished point 0_X. -/
  zero : carrier

/-- Build a `SpaceInterp` from a `MetricSpaceInterp`. -/
def MetricSpaceInterp.toSpaceInterp (m : MetricSpaceInterp) :
    SpaceInterp (fun () => m.carrier) MetricSpace.F where
  funcInterp := fun () => fun x y => m.metric x y
  zeroInterp := fun () => m.zero

-- ============================================================================
-- Equality at type X
-- ============================================================================

-- Equality at the base type X: `x =_X y ≡ d(x, y) =_ℝ 0`.
-- In the encoded form, this is a purely universal formula:
-- `∀n. d(x,y)(n) = 0_ℝ(n)` (pointwise equality of the Cauchy sequences).
-- TODO: Define EqX concretely once RealNumbers.lean has the encoding.
-- EqX () s t := ∀n. eq0 (app (app (app (func ()) s) t) (var vz)) (real_zero (var vz))

-- ============================================================================
-- Metric space axioms (Premises)
-- ============================================================================

-- The axioms of a metric space theory, expressed as a `PremiseSet`.
-- These are purely universal formulas:
-- * Reflexivity: ∀x. d(x,x) =_ℝ 0
-- * Symmetry: ∀x,y. d(x,y) =_ℝ d(y,x)
-- * Triangle inequality: ∀x,y,z. d(x,z) ≤_ℝ d(x,y) +_ℝ d(y,z)
-- * Non-negativity: ∀x,y. 0 ≤_ℝ d(x,y)
-- TODO: Define concretely once RealNumbers.lean provides =_ℝ, ≤_ℝ, +_ℝ.
-- For now, leave as a parameter that users instantiate.

end Metatheorems
