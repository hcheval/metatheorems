/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs
import Metatheorems.Dialectica.Lemmas


namespace Metatheorems

/-!
# Gödel's Dialectica Interpretation — Soundness (Theorem 3.0.7)

This file assembles the definitions (from `Dialectica/Defs.lean`) and
per-case lemmas (from `Dialectica/Lemmas.lean`) into the final soundness
theorem.

Splitting across three files avoids the circular import:
`Defs ← Lemmas ← Dialectica` (each imports only earlier layers).
-/

/-- Generalized soundness for any context: derivable formulas satisfy
    the Dialectica interpretation at every environment. -/
def dialectica_soundness_ctx
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {Γ : Ctx ι} (A : Formula F Γ) (env : Ctx.interpret X Γ)
    (h : @Derivable ι F Allowed.extended Premises Γ A)
    : dialecticaRealizerCtx si A env :=
  @dialectica_soundness_ctx' ι X F si eqxi Premises premise_realizer Γ A h env

/-- **Dialectica Soundness Theorem** (Theorem 3.0.7).

    If `T^ω[X,F] + AC + IP^ω_∀ + M^ω ⊢ A`, then one can construct a
    Lean-computable realizer for the Dialectica translation of `A`. -/
def dialectica_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (A : Formula F ([] : Ctx ι))
    (h : @Derivable ι F Allowed.extended Premises [] A)
    : dialecticaRealizer si A :=
  @dialectica_soundness' ι X F si eqxi Premises premise_realizer A h

end Metatheorems
