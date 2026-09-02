/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable
import Metatheorems.RealNumbers
import Metatheorems.Rounding
import Metatheorems.Majorizability

namespace Metatheorems

/-!
# Metric Spaces as Abstract Spaces

Instantiates the WE-HA^{ω,X} framework for a single metric space (X, d).
Following §5.1 (Definition 5.1.2) of the reference document:

* One abstract base type X (so `ι = Unit`)
* One function constant `d_X : X → X → ℝ` (the metric)
* Zero element `0_X : X` (a distinguished point)
* Equality at type X: `x =_X y ≡ d_X(x,y) =_ℝ 0_ℝ`
* Axioms: reflexivity, symmetry, triangle inequality (pseudo-metric)

## Main Definitions

* `MetricSpace.ι` — the index type `Unit`
* `MetricSpace.F` — the function constant types
* `MetricSpace.EqX` — equality at type X via d
* `MetricSpace.Premises` — the pseudo-metric axioms
* `MetricSpace.admissibleEqX` — EqX is admissible
-/

open Formula

-- ============================================================================
-- Basic setup
-- ============================================================================

/-- Index type for a single metric space: one base type. -/
abbrev MetricSpace.ι := Unit

/-- Abbreviation for the base type X. -/
abbrev xTy : Ty MetricSpace.ι := Ty.base ()

/-- Function constant types for a metric space.
    The single function constant is `d_X : X → X → ℝ` (the metric).
    `ℝ` is encoded as `Ty.nat →ₜ Ty.nat` (type level 1). -/
def MetricSpace.F : MetricSpace.ι → Ty MetricSpace.ι
  | () => xTy →ₜ xTy →ₜ realTy MetricSpace.ι

/-- Shorthand for the metric term d_X in any context. -/
abbrev d_X {Γ : Ctx MetricSpace.ι} :
    Term MetricSpace.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.func ()

-- ============================================================================
-- Equality at type X
-- ============================================================================

/-- Equality at the base type X: `x =_X y ≡ d_X(x,y) =_ℝ 0_ℝ`.
    This is a Π₁⁰ (purely universal) formula since `eq_R` is `∀n. (QF body)`. -/
def MetricSpace.EqX : (i : MetricSpace.ι) →
    {Γ : Ctx MetricSpace.ι} →
    Term MetricSpace.F Γ (Ty.base i) →
    Term MetricSpace.F Γ (Ty.base i) →
    Formula MetricSpace.F Γ :=
  fun () {_} s t => eq_R (Term.app (Term.app (Term.func ()) s) t) Term.zero_R

-- ============================================================================
-- Metric space axioms (Premises)
-- ============================================================================

-- Following Definition 5.1.2 of the reference document.

/-- Axiom 1: ∀x^X. d(x,x) =_ℝ 0_ℝ  (reflexivity of the metric).
    Context-polymorphic: axiom is closed (no free variables), valid in any context. -/
def MetricSpace.ax_refl {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy
    (eq_R (Term.app2 d_X (Term.var .vz) (Term.var .vz)) Term.zero_R)

/-- Axiom 2: ∀x^X,y^X. d(x,y) =_ℝ d(y,x)  (symmetry of the metric).
    Context-polymorphic. -/
def MetricSpace.ax_sym {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy (Formula.all xTy
    (eq_R (Term.app2 d_X (Term.var (.vs .vz)) (Term.var .vz))
          (Term.app2 d_X (Term.var .vz) (Term.var (.vs .vz)))))

/-- Axiom 3: ∀x^X,y^X,z^X. d(x,z) ≤_ℝ d(x,y) +_ℝ d(y,z)
    (triangle inequality). Uses le_R_pu for purely universal form.
    Context-polymorphic. -/
def MetricSpace.ax_triangle {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy
    (le_R_pu
      (Term.app2 d_X (Term.var (.vs (.vs .vz))) (Term.var .vz))
      (Term.app2 Term.add_R
        (Term.app2 d_X (Term.var (.vs (.vs .vz))) (Term.var (.vs .vz)))
        (Term.app2 d_X (Term.var (.vs .vz)) (Term.var .vz))))))

-- Verify axioms are purely universal (needed for Premises)
theorem MetricSpace.ax_refl_pu :
    (MetricSpace.ax_refl (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem MetricSpace.ax_sym_pu :
    (MetricSpace.ax_sym (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem MetricSpace.ax_triangle_pu :
    (MetricSpace.ax_triangle (Γ := Γ)).isPurelyUniversal = true := by rfl

/-- The set of metric space axioms as a `PremiseSet`.
    Context-polymorphic: axioms are closed formulas, available at any context. -/
def MetricSpace.Premises : PremiseSet MetricSpace.F :=
  fun ⟨Γ, A⟩ => A = MetricSpace.ax_refl ∨
                 A = MetricSpace.ax_sym ∨
                 A = MetricSpace.ax_triangle

-- ============================================================================
-- Semantic interpretation
-- ============================================================================

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
-- Lemma 17.8(4): `≤` on reals gives strong majorization of the codes
-- ============================================================================

/-! `Rounding.lean` proves Lemma 17.8 parts (2),(3),(5),(6); part (4) was blocked there
because it mentions `s-maj₁`, which lives in `StrongMajorizability.lean`. With the two-clause
`bezemMaj` (2026-09-02) it is a corollary of (2) and (3): at type `1 = nat →ₜ nat` the
relation unfolds to a *pair* of monotonicity statements, and (3) discharges the
self-majorization one outright. -/

open Rounding in
/-- **Lemma 17.8(4)**: if `0 ≤ x ≤ y` then `(y)◦` strongly majorizes `(x)◦` at type `1`.

The first conjunct chains 17.8(2) (`(x)◦ ≤₁ (y)◦`) with 17.8(3) (`(y)◦` monotone in the
precision index); the second conjunct *is* 17.8(3).

`_hx` is unused: only `0 ≤ y` is needed, since `roundR_le₁_of_le` rests on `Nat.floor_mono`,
which does not care about sign. The hypothesis is kept because the book states 17.8 for
`x, y ∈ [0,∞)` and callers will have it anyway. -/
theorem roundR_smaj_of_le {ι : Type} {X : ι → Type}
    {base : (i : ι) → Nat → X i → Prop} {x y : ℝ}
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    bezemMaj (X := X) base (Ty.nat →ₜ Ty.nat) (roundR y) (roundR x) := by
  have hmono : ∀ (a : ℝ), 0 ≤ a → Monotone (roundR a) :=
    fun a ha => monotone_nat_of_le_succ (roundR_mono ha)
  refine ⟨?_, ?_⟩
  · -- majorization: (y)◦(n*) ≥ (x)◦(n) whenever n* ≥ n
    intro n_star n h
    exact Nat.le_trans (roundR_le₁_of_le hxy n) (hmono y hy h)
  · -- self-majorization: (y)◦ is monotone in the precision index
    intro n_star n h
    exact hmono y hy h

-- ============================================================================
-- AdmissibleEqX for the metric space EqX
-- ============================================================================

-- substF_nat: follows from eq_R_substF (proved in RealNumbers)
-- eqx_pu:     eq_R is Π₁⁰ by construction (Formula.all over eq0)
-- eqx_refl/sym/trans: require ordered field axioms (sorry'd in RealNumbers)

def MetricSpace.admissibleEqX : AdmissibleEqX MetricSpace.EqX where
  substF_nat := fun {_ _} () u v σ => by
    simp only [MetricSpace.EqX, eq_R_substF, Term.subst, Term.app2,
      zero_R_closed_subst]
  eqx_refl := sorry
  eqx_sym := sorry
  eqx_trans := sorry
  eqx_pu := fun () {_} _ _ => eq_R_isPurelyUniversal _ _

end Metatheorems
