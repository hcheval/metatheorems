/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.StrongMajorizability
import Metatheorems.NDTranslation


namespace Metatheorems

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
-- Dialectica matrix reduction for QF ∨-free formulas
-- ============================================================================

/-- For QF ∨-free formulas, the Dialectica matrix equals the formula's
    semantic interpretation, regardless of witness and counter values.
    This is because W(A) and C(A) are subsingletons (all Unit). -/
theorem dialecticaMatrix_iff_interpFormula
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) (hvf : A.isVFree = true)
    (env : Ctx.interpret X Γ) (w : 𝕎 X A) (c : ℂ X A) :
    dialecticaMatrix si A env w c ↔ Formula.interpret si A env :=
  match A, hqf, hvf, env, w, c with
  | .bot, _, _, _, _, _ => Iff.rfl
  | .eq0 .., _, _, _, _, _ => Iff.rfl
  | .and A B, hqf, hvf, env, (wA, wB), (cA, cB) => by
    simp only [isQF, isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    exact Iff.and
      (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA cA)
      (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env wB cB)
  | .or .., _, hvf, _, _, _ => by simp [isVFree] at hvf
  | .imp A B, hqf, hvf, env, (f, g), (wA, cB) => by
    simp only [isQF, isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    constructor
    · intro h hA
      have := (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA (g wA cB)).mpr hA
      exact (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env (f wA) cB).mp (h this)
    · intro h hM
      have := (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA (g wA cB)).mp hM
      exact (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env (f wA) cB).mpr (h this)

-- ============================================================================
-- General Metatheorem (Theorem 6.1)
-- ============================================================================

/-- **General Metatheorem** (Theorem 6.1), Dialectica step.

Takes a derivation in the extended system (post-NT) and applies Dialectica
directly. The matrix has no ¬¬ layers, making extraction clean.
The full metatheorem composes `negTrans_sound` (external) with this. -/
def general_metatheorem
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.extended Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  -- Step 1: Apply Dialectica directly (no NT)
  let r := @dialectica_soundness_ctx' ι X F si EqX eqxi Premises premise_realizer _ _ prf
  -- r : ∀ env, dialecticaRealizerCtx si (all ρ (imp (all .nat B₀) (ex .nat C₀))) env
  -- Specialize to empty env
  let r₀ := r ()
  let w := r₀.val
  let h := r₀.property
  -- Step 2: Extract U, V from the Dialectica witness
  -- w : Ty.interpret X ρ → W(imp (all .nat B₀) (ex .nat C₀))
  -- W(imp P Q) = (W(P) → W(Q)) × (W(P) → C(Q) → C(P))
  -- W(all .nat B₀) = ℕ → W(B₀)
  -- W(ex .nat C₀) = ℕ × W(C₀)
  -- C(ex .nat C₀) = C(C₀)
  -- C(all .nat B₀) = ℕ × C(B₀)
  -- Extract V: feed default W(∀u B₀) into first component, project .1
  let V : Ty.interpret X ρ → Nat := fun x => ((w x).1 (dialecticaDefaultWitness si _)).1
  -- Extract U: feed defaults into second component, project .1
  let U : Ty.interpret X ρ → Nat := fun x =>
    ((w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  -- Step 3: Prove B(x, U(x)) → C(x, V(x)) from the Dialectica matrix
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (U x, (x, ())) → Formula.interpret si C₀ (V x, (x, ())) := by
    intro x hBx
    -- Specialize h to counter (x, (defaultW(all .nat B₀), defaultC(ex .nat C₀)))
    let wP := dialecticaDefaultWitness si (all Ty.nat B₀)
    let cQ := dialecticaDefaultCounter si (ex Ty.nat C₀)
    have h_spec := h (x, (wP, cQ))
    -- h_spec : matrix(imp (all .nat B₀) (ex .nat C₀), (x, ()), w x, (wP, cQ))
    -- which is: matrix(all .nat B₀, ..., wP, (w x).2 wP cQ) → matrix(ex .nat C₀, ..., (w x).1 wP, cQ)
    -- Unfold: matrix(all .nat B₀, (x,()), wP, (U x, ...)) = matrix(B₀, (U x, x, ()), wP(U x), ...)
    -- and:    matrix(ex .nat C₀, (x,()), (V x, ...), cQ) = matrix(C₀, (V x, x, ()), ..., cQ)
    simp only [dialecticaMatrix] at h_spec
    -- Use the QF∨-free reduction for B₀ and C₀
    rw [dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf] at h_spec
    exact h_spec hBx
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
-- Classical version (Theorem 6.1 as in the paper)
-- ============================================================================

/-- **General Metatheorem from classical proof** (Theorem 6.1).

Takes a classical derivation (with LEM + QF-AC) and composes
`nd_soundness` with witness extraction. The ¬¬ layers from the
negative translation are eliminated using `Classical.not_not`. -/
def general_metatheorem_classical
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.classical Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  -- Step 1: Apply ND-interpretation (NT + Dialectica)
  let r := nd_soundness_closed si eqxi adm premise_realizer prf
  let w := r.val
  let h := r.property
  -- h : ∀ y, dialecticaMatrix si NT(∀x(∀u B₀ → ∃v C₀)) () w y
  -- NT introduces ¬¬ layers. Extract through them using Classical.not_not.
  -- Step 2: Extract U, V (same projections as extended version, through ¬¬)
  let ki_w := (w.2 (dialecticaDefaultWitness si _) ()).1
  let imp_w := fun x => ((ki_w x).2 (dialecticaDefaultWitness si _) ()).1
  let V : Ty.interpret X ρ → Nat := fun x =>
    ((imp_w x).1 (dialecticaDefaultWitness si _)).1
  let U : Ty.interpret X ρ → Nat := fun x =>
    ((imp_w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  -- Step 3: Prove B(x, U(x)) → C(x, V(x))
  -- Unfold h through the ¬¬ layers using Classical.not_not
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (U x, (x, ())) → Formula.interpret si C₀ (V x, (x, ())) := by
    -- Need to construct a counter for h that embeds x at the ∀ρ position,
    -- peel ¬¬ layers with Classical.not_not, then apply QF∨-free matrix reduction.
    -- The witnesses U, V extracted here may differ from those used for Φ;
    -- this requires careful counter construction matching the witness extraction.
    sorry
  -- Step 4: Construct Φ (same as extended version)
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

Given semantic witness functions `U V : Ty.interpret X ρ → ℕ` satisfying
`∀x, B(x, U(x)) → C(x, V(x))` (the "extracted content" from the
ND-interpretation), construct a computable bound Φ such that for all
`x* ≥*_ρ x`: `(∀u ≤ Φ(x*), B(x,u)) → (∃v ≤ Φ(x*), C(x,v))`. -/
theorem metatheorem_core
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    (mj : Majorizability si)
    {ρ : Ty ι}
    (B C : Ty.interpret X ρ → Nat → Prop)
    (U V : Ty.interpret X ρ → Nat)
    (hUV : ∀ x : Ty.interpret X ρ, B x (U x) → C x (V x)) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
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

end Metatheorems
