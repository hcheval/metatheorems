/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic

namespace Metatheorems

/-!
# CAT(0) spaces

A CAT(0) space is a W-hyperbolic space satisfying the Bruhat–Tits **CN inequality**

    d(z, W(x,y,½))² ≤ ½·d(z,x)² + ½·d(z,y)² − ¼·d(x,y)²

(Kohlenbach's `A^ω[X,d,W,CAT(0)]`). **Same signature as W-hyperbolic** — no new constant, so
`WHyperbolic.F`, the model's `si`, `abstractMajorizability` and `eqXInterp` are all inherited
verbatim; the only new objects are one axiom, one model field, and the premise set.

## Squares and the constants `½`, `¼`

Squaring is object-level `mul_R t t`. The constants are the constant code sequences
`λn. ⟨2^{-1}⟩ℚ` and `λn. ⟨2^{-2}⟩ℚ`, built from `Term.pow2neg_Q` — no new ℝ-layer machinery.

## The `½` inside `W`

`W` is applied to `clamp01 half_R`, not to `half_R`. The reason is weak extensionality:
`clamp01 half_R =ℝ half_R` is derivable (`clamp01_eq`), but `=ℝ` is not `=₀`, so nothing lets
a derivation rewrite under `W` with it. Stating CN at `clamp01 half_R` is what makes it
composable with (W1)–(W4) instantiated at `λ := half_R`, which is how it is used.
-/

open Formula

-- ============================================================================
-- The two constants
-- ============================================================================

/-- `½` as a real: the constant sequence `⟨2^{-1}⟩ℚ`. -/
abbrev CAT0.half_R {Γ : Ctx MetricSpace.ι} : Term WHyperbolic.F Γ rTy :=
  Term.lam (.app Term.pow2neg_Q (.app .succ .zero))

/-- `¼` as a real: the constant sequence `⟨2^{-2}⟩ℚ`. -/
abbrev CAT0.quarter_R {Γ : Ctx MetricSpace.ι} : Term WHyperbolic.F Γ rTy :=
  Term.lam (.app Term.pow2neg_Q (.app .succ (.app .succ .zero)))

-- ============================================================================
-- The CN inequality
-- ============================================================================

/-- (CN) `∀z x y. d(z, W(x,y,½̃))·d(z, W(x,y,½̃)) ≤ℝ
(½·(d(z,x)·d(z,x)) +ℝ ½·(d(z,y)·d(z,y))) −ℝ ¼·(d(x,y)·d(x,y))`.
De Bruijn: `z = x₂, x = x₁, y = x₀`. -/
def CAT0.ax_CN {Γ : Ctx MetricSpace.ι} : Formula WHyperbolic.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy
    (le_R_pu
      (Term.app2 Term.mul_R
        (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz)))
          (Term.app3 WHyperbolic.W (.var (.vs .vz)) (.var .vz) (.app Term.clamp01 CAT0.half_R)))
        (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz)))
          (Term.app3 WHyperbolic.W (.var (.vs .vz)) (.var .vz) (.app Term.clamp01 CAT0.half_R))))
      (Term.app2 Term.sub_R
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R CAT0.half_R
            (Term.app2 Term.mul_R
              (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz))) (.var (.vs .vz)))
              (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz))) (.var (.vs .vz)))))
          (Term.app2 Term.mul_R CAT0.half_R
            (Term.app2 Term.mul_R
              (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz))) (.var .vz))
              (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz))) (.var .vz)))))
        (Term.app2 Term.mul_R CAT0.quarter_R
          (Term.app2 Term.mul_R
            (Term.app2 WHyperbolic.d (.var (.vs .vz)) (.var .vz))
            (Term.app2 WHyperbolic.d (.var (.vs .vz)) (.var .vz))))))))

theorem CAT0.ax_CN_pu {Γ : Ctx MetricSpace.ι} :
    (CAT0.ax_CN (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem CAT0.ax_CN_vf {Γ : Ctx MetricSpace.ι} :
    (CAT0.ax_CN (Γ := Γ)).isVFree = true := by rfl

-- ============================================================================
-- The premise set: (W1)–(W4) and (CN)
-- ============================================================================

/-- The CAT(0) premise set: the four W-hyperbolic axioms plus CN. -/
def CAT0.Premises : PremiseSet WHyperbolic.F
  | ⟨Γ, A⟩ => WHyperbolic.Premises ⟨Γ, A⟩ ∨ A = CAT0.ax_CN

theorem CAT0.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ'),
      CAT0.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := by
  intro Γ' B h
  rcases h with h | h
  · exact WHyperbolic.premises_pu Γ' B h
  · subst h; rfl

theorem CAT0.premises_vf :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ'),
      CAT0.Premises ⟨Γ', B⟩ → B.isVFree = true := by
  intro Γ' B h
  rcases h with h | h
  · exact WHyperbolic.premises_vf Γ' B h
  · subst h; rfl

-- The five axioms as derivations under the CAT(0) premise set. There is no
-- premise-weakening lemma in the project, so the four W-axioms are re-accessed here rather
-- than transported from `WHyperbolic.W1`–`W4`.

/-- `⊢ (W1)` in the CAT(0) theory. -/
def CAT0.W1 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a CAT0.Premises (WHyperbolic.ax_W1 (Γ := Γ)) :=
  .premise (Or.inl (Or.inl rfl))

/-- `⊢ (W2)` in the CAT(0) theory. -/
def CAT0.W2 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a CAT0.Premises (WHyperbolic.ax_W2 (Γ := Γ)) :=
  .premise (Or.inl (Or.inr (Or.inl rfl)))

/-- `⊢ (W3)` in the CAT(0) theory. -/
def CAT0.W3 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a CAT0.Premises (WHyperbolic.ax_W3 (Γ := Γ)) :=
  .premise (Or.inl (Or.inr (Or.inr (Or.inl rfl))))

/-- `⊢ (W4)` in the CAT(0) theory. -/
def CAT0.W4 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a CAT0.Premises (WHyperbolic.ax_W4 (Γ := Γ)) :=
  .premise (Or.inl (Or.inr (Or.inr (Or.inr rfl))))

/-- `⊢ (CN)`. -/
def CAT0.CN {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a CAT0.Premises (CAT0.ax_CN (Γ := Γ)) :=
  .premise (Or.inr rfl)

-- ============================================================================
-- The model
-- ============================================================================

/-- **A CAT(0) model**: a W-hyperbolic model satisfying CN on Mathlib `ℝ`. -/
structure CAT0Model extends WHyperbolicModel where
  /-- (CN), the Bruhat–Tits inequality. -/
  CN : ∀ (z x y : carrier),
    d z (W x y (1/2)) * d z (W x y (1/2))
      ≤ (1/2) * (d z x * d z x) + (1/2) * (d z y * d z y) - (1/4) * (d x y * d x y)

/-- The premises hold in the model — the W-hyperbolic `AxiomsHold` extended by CN. As there,
not discharged here; see `WHyperbolicModel.AxiomsHold`. -/
def CAT0Model.AxiomsHold (M : CAT0Model) : Prop :=
  ∀ {Γ : Ctx MetricSpace.ι} (A : Formula WHyperbolic.F Γ), CAT0.Premises ⟨Γ, A⟩ →
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env

/-- Premise realizers, by `srealizer_of_pu` — CN is purely universal like the rest. -/
def CAT0Model.spremise (M : CAT0Model) (hax : M.AxiomsHold) :
    ∀ (Γ : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ),
      CAT0.Premises ⟨Γ, B⟩ → SRealizer M.si B :=
  fun Γ B hp =>
    srealizer_of_pu B (CAT0.premises_pu Γ B hp) (CAT0.premises_vf Γ B hp) (hax B hp)

/-- Semantic soundness for a CAT(0) model, given that its axioms hold. -/
theorem CAT0Model.soundness (M : CAT0Model) (hax : M.AxiomsHold)
    {Γ : Ctx MetricSpace.ι} {allowed : Allowed} {A : Formula WHyperbolic.F Γ}
    (h : Derivable WHyperbolic.F allowed CAT0.Premises A) :
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env :=
  M.soundness_gen M.si (fun _ _ => rfl) hax h

-- ============================================================================
-- The CAT(0) metatheorems
-- ============================================================================

/-- **The CAT(0) metatheorem** (extended input). Majorants and equality interpretation are
the W-hyperbolic ones — CN adds a premise, not a constant, so the bound `Φ` is exactly as
uniform as before. -/
theorem CAT0Model.cat0_metatheorem (M : CAT0Model) (hax : M.AxiomsHold)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHyperbolic.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      CAT0.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem M.eqXInterp (M.spremise hax) M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- **The CAT(0) metatheorem, from a classical proof.** -/
theorem CAT0Model.cat0_metatheorem_classical (M : CAT0Model) (hax : M.AxiomsHold)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHyperbolic.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.classical
      CAT0.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem_classical M.eqXInterp
    (ntStable_of_pu CAT0.premises_pu) (M.spremise hax)
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms CAT0.premises_pu
#print axioms CAT0.CN
#print axioms CAT0Model.soundness
#print axioms CAT0Model.cat0_metatheorem
#print axioms CAT0Model.cat0_metatheorem_classical

end Metatheorems
