/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics


namespace Metatheorems

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

/-- The majorizability *relation* and the two properties the metatheorem uses.

This is everything `metatheorem_core` needs apart from the majorants themselves, and
unlike `Majorizability` below it is inhabited — see `bezemRel`. -/
structure MajorizabilityRel {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) where
  /-- The majorizability relation at type ρ: `maj ρ x_star x` means x* ≥*_ρ x. -/
  maj : (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ → Prop
  /-- Property 1: respects the natural number order. -/
  maj_le : ∀ {n m : Nat}, maj .nat n m → n ≥ m
  /-- Property 2: respects term application. -/
  maj_app : ∀ {ρ τ : Ty ι}
    {f_star : Ty.interpret X (ρ →ₜ τ).hat} {f : Ty.interpret X (ρ →ₜ τ)}
    {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ},
    maj (ρ →ₜ τ) f_star f → maj ρ x_star x → maj τ (f_star x_star) (f x)

/-- Majorizability with a total majorizer on all semantic values.

This is the "strong" version: instead of proving each constant is majorizable
and deriving closed terms, we directly assume every element of the type
structure has a majorant. This matches the Lean 3 formalization and makes
the general metatheorem straightforward to state.

**Caution.** Over the full set-theoretic type structure the `majorizer` field is not
satisfiable for any relation that is genuinely a majorization: at type `(nat →ₜ nat) →ₜ nat`
one would need, for each `Φ`, a `Φ*` with `Φ* f* ≥ Φ f` whenever `f*` majorizes `f`; taking
`f* = id` the majorized `f` range over all `f` with `f n ≤ n`, an infinite set on which an
arbitrary `Φ` is unbounded. Degenerate choices (e.g. `maj := Eq` when `ρ.hat = ρ`) do satisfy
it, but then the bound depends on `x` itself and carries no uniformity. Prefer
`MajorizabilityRel` plus explicit majorants — `metatheorem_core_of_majorants`. -/
structure Majorizability {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) extends MajorizabilityRel si where
  /-- Total majorizer: every semantic value has a majorant. -/
  majorizer : {ρ : Ty ι} → Ty.interpret X ρ → Ty.interpret X ρ.hat
  /-- The majorizer actually majorizes. -/
  majorizer_maj : ∀ {ρ : Ty ι} (x : Ty.interpret X ρ), maj ρ (majorizer x) x

-- ============================================================================
-- The Bezem relation: a concrete `MajorizabilityRel`
-- ============================================================================

/-- Strong majorizability à la Bezem, parametric in the relation used at the base types.

At `nat` it is `≥`; at an arrow it is the usual "majorizes pointwise on majorized
arguments". `Ty.hat` sends every base type to `nat`, so `base i` relates a natural to a
point of `X i` — that is Def. 6.0.1's "majorized by a natural relative to a reference
point", and it is exactly the space-specific datum. -/
def bezemMaj {ι : Type} {X : ι → Type} (base : (i : ι) → Nat → X i → Prop) :
    (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ → Prop
  | .nat,     n,       m => @GE.ge Nat _ n m
  | .base i,  n,       x => base i n x
  | .arr ρ τ, f_star,  f =>
      ∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
        bezemMaj base ρ x_star x → bezemMaj base τ (f_star x_star) (f x)

/-- `bezemMaj` satisfies the two properties the metatheorem uses. -/
def bezemRel {ι : Type} {X : ι → Type} {F : ι → Ty ι} (si : SpaceInterp X F)
    (base : (i : ι) → Nat → X i → Prop) : MajorizabilityRel si where
  maj := bezemMaj base
  maj_le h := by simpa [bezemMaj] using h
  maj_app hf hx := by simpa [bezemMaj] using hf _ _ (by simpa [bezemMaj] using hx)

/-- For pure `WE-HA^ω` (`ι = Empty`) there are no base types, so the relation is
determined outright. -/
def bezemRelEmpty {X : Empty → Type} {F : Empty → Ty Empty} (si : SpaceInterp X F) :
    MajorizabilityRel si :=
  bezemRel si (fun i => i.elim)

end Metatheorems
