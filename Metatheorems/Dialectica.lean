/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs
import Metatheorems.Dialectica.Lemmas

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
noncomputable def dialectica_soundness_ctx
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Γ : Ctx ι} (A : Formula F Γ) (env : interpCtx X Γ)
    (h : Derivable F EqX Allowed.extended A)
    : dialecticaRealizerCtx si A env :=
  dialectica_soundness_ctx' si eqxi A env h

/-- **Dialectica Soundness Theorem** (Theorem 3.0.7).

    If `T^ω[X,F] + AC + IP^ω_∀ + M^ω ⊢ A`, then one can construct a
    Lean-computable realizer for the Dialectica translation of `A`. -/
noncomputable def dialectica_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (A : Formula F ([] : Ctx ι))
    (h : Derivable F EqX Allowed.extended A)
    : dialecticaRealizer si A :=
  dialectica_soundness' si eqxi A h
