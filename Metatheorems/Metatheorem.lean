/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.StrongMajorizability
import Metatheorems.NDTranslation

/-!
# General Logical Metatheorem (Theorem 6.1)

The general metatheorem: from a classical proof of
`∀x^ρ (∀u⁰ B(x,u) → ∃v⁰ C(x,v))`, extract a computable bound Φ such that
`∀u ≤ Φ(x*) B(x,u) → ∃v ≤ Φ(x*) C(x,v)` for all x* ≥*_ρ x.

The proof factors into:
1. **Core bound construction** (`metatheorem_core`): given semantic witnesses
   U, V with `∀x, B(x, U(x)) → C(x, V(x))`, construct Φ using majorizability.
2. **Witness extraction**: connect `nd_soundness` to the core via Dialectica
   witness extraction for the specific formula shape.
-/

open Formula

-- ============================================================================
-- General Metatheorem (Theorem 6.1)
-- ============================================================================

/-- **General Logical Metatheorem** (Theorem 6.1).

From a classical derivation of `∀x^ρ (∀u⁰ B₀(u,x) → ∃v⁰ C₀(v,x))`
where B₀, C₀ are QF, extract a computable bound Φ such that for all
x* ≥*_ρ x: `(∀u ≤ Φ(x*), B₀(u,x)) → (∃v ≤ Φ(x*), C₀(v,x))`. -/
def general_metatheorem
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    (mj : Majorizability si)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (prf : Derivable F EqX Allowed.classical
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : interpTy X ρ.hat → Nat //
      ∀ (x : interpTy X ρ) (x_star : interpTy X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → interpFormula si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ interpFormula si C₀ (v, (x, ())) } := by
  -- Step 1: Apply ND-interpretation
  let r := nd_soundness_closed si eqxi adm prf
  -- r : dialecticaRealizer si NT(∀x(∀u B₀ → ∃v C₀))
  -- Extract witness and property
  let w := r.val
  let h := r.property
  -- Step 2: Extract U, V by projecting through the ¬¬ and ∀ layers.
  -- NT(A) = ¬¬ki(A). Dialectica witness of ¬¬P = (W(¬P)→Unit) × (W(¬P)→Unit→C(¬P)).
  -- The .2 component, fed defaults, yields W(ki(A)) via C(¬P) = W(P) × Unit.
  -- Peel outer ¬¬: get W(kurodaInner(A))
  let ki_w := (w.2 (dialecticaDefaultWitness si _) ()).1
  -- ki_w : W(kurodaInner(∀x(∀u B₀ → ∃v C₀)))
  --       = W(∀x(¬¬(∀u(¬¬B₀) → ∃v C₀)))
  --       = interpTy X ρ → W(¬¬(∀u(¬¬B₀) → ∃v C₀))
  -- Peel ∀x and inner ¬¬: for each x, get W(∀u(¬¬B₀) → ∃v C₀)
  let imp_w := fun x => ((ki_w x).2 (dialecticaDefaultWitness si _) ()).1
  -- imp_w x : W(imp (all .nat (¬¬B₀)) (ex .nat C₀))
  --         = (W(∀u ¬¬B₀) → W(∃v C₀)) × (W(∀u ¬¬B₀) → C(∃v C₀) → C(∀u ¬¬B₀))
  -- Extract V: first component gives W(∃v C₀) = ℕ × W(C₀); project .1
  let V : interpTy X ρ → Nat := fun x => ((imp_w x).1 (dialecticaDefaultWitness si _)).1
  -- Extract U: second component gives C(∀u ¬¬B₀) = ℕ × C(¬¬B₀); project .1
  let U : interpTy X ρ → Nat := fun x =>
    ((imp_w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  -- Step 3: Prove B(x, U(x)) → C(x, V(x)) from the Dialectica matrix
  have hUV : ∀ x : interpTy X ρ,
      interpFormula si B₀ (U x, (x, ())) → interpFormula si C₀ (V x, (x, ())) := by
    -- The Dialectica matrix property `h` gives, for each counter y,
    -- a deeply nested ¬¬-wrapped statement about B₀ and C₀.
    -- Extracting the semantic content requires:
    -- 1. Choosing counters that encode (x, hBx)
    -- 2. Classical ¬¬-elimination through multiple layers
    -- 3. A matrix reduction lemma: for QF formulas, dialecticaMatrix ↔ interpFormula
    -- TODO: factor into a general Dialectica matrix reduction lemma
    sorry
  -- Step 4: Construct Φ using majorizability
  exact ⟨fun x_star =>
    Nat.max (mj.majorizer (ρ := ρ →ₜ .nat) U x_star)
            (mj.majorizer (ρ := ρ →ₜ .nat) V x_star),
    fun x x_star hx hB => by
      have hV_le : V x ≤ mj.majorizer (ρ := ρ →ₜ .nat) V x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) V) hx)
      have hU_le : U x ≤ mj.majorizer (ρ := ρ →ₜ .nat) U x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) U) hx)
      exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..),
             hUV x (hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..)))⟩⟩

-- ============================================================================
-- Core bound construction (Theorem 6.1, step 3–5)
-- ============================================================================

/-- **Core of the General Metatheorem** (Theorem 6.1).

Given semantic witness functions `U V : interpTy X ρ → ℕ` satisfying
`∀x, B(x, U(x)) → C(x, V(x))` (the "extracted content" from the
ND-interpretation), construct a computable bound Φ such that for all
`x* ≥*_ρ x`: `(∀u ≤ Φ(x*), B(x,u)) → (∃v ≤ Φ(x*), C(x,v))`. -/
theorem metatheorem_core
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    (mj : Majorizability si)
    {ρ : Ty ι}
    (B C : interpTy X ρ → Nat → Prop)
    (U V : interpTy X ρ → Nat)
    (hUV : ∀ x : interpTy X ρ, B x (U x) → C x (V x)) :
    ∃ Φ : interpTy X ρ.hat → Nat,
    ∀ (x : interpTy X ρ) (x_star : interpTy X ρ.hat),
      mj.maj ρ x_star x →
      (∀ u : Nat, u ≤ Φ x_star → B x u) →
      ∃ v : Nat, v ≤ Φ x_star ∧ C x v := by
  -- Define Φ(x*) = max(U*(x*), V*(x*)) where U* = majorizer(U), V* = majorizer(V)
  refine ⟨fun x_star =>
    Nat.max (mj.majorizer (ρ := ρ →ₜ .nat) U x_star)
            (mj.majorizer (ρ := ρ →ₜ .nat) V x_star), ?_⟩
  intro x x_star hx hB
  -- V(x) ≤ V*(x*) ≤ Φ(x*)
  have hV_le : V x ≤ mj.majorizer (ρ := ρ →ₜ .nat) V x_star :=
    mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) V) hx)
  -- U(x) ≤ U*(x*) ≤ Φ(x*)
  have hU_le : U x ≤ mj.majorizer (ρ := ρ →ₜ .nat) U x_star :=
    mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) U) hx)
  -- B(x, U(x)) holds since U(x) ≤ Φ(x*)
  have hBU : B x (U x) := hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..))
  -- C(x, V(x)) holds by the semantic content
  exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..), hUV x hBU⟩
