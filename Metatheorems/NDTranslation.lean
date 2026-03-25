/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica
import Metatheorems.NegTrans

/-!
# ND-Interpretation (Negative + Dialectica)

The ND-interpretation composes two translations:

1. **Kuroda's negative translation** (NT): maps a classical proof of `A`
   in `WE-HA^{ω,X} + LEM + QF-AC` (`DerivableClass`) to an intuitionistic
   proof of `NT(A) = ¬¬nt(A)` in `WE-HA^{ω,X} + QF-AC + M^ω` (`DerivableExt`).

2. **Dialectica interpretation** (D): maps a proof of `NT(A)` in `DerivableExt`
   to a Lean-computable realizer for the Dialectica translation of `NT(A)`.

The composition gives: from a **classical** proof of `A`, extract a
Lean-computable Dialectica realizer for `NT(A)`.

This is the key metatheorem (Theorem 10.7 of the reference document):
from `WE-HA^{ω,X}_c + QF-AC ⊢ A` one can extract explicit witnesses
via the functional interpretation of `NT(A)`.

**Note**: `nd_soundness` depends on `negTrans_sound`, which currently has
27 `sorry` stubs. The type signature is correct; completing `NegTrans.lean`
will yield a fully verified theorem.
-/

open Formula

/-- **ND-Interpretation** (Theorem 10.7): from a classical derivation of `A`,
    extract a Lean-computable Dialectica realizer for `NT(A)`.

    Proof: compose Kuroda's NT soundness with Dialectica soundness.
    - `negTrans_sound h  : DerivableExt F EqX A.negTrans`
    - `dialectica_soundness_ctx ... : dialecticaRealizerCtx si A.negTrans env` -/
noncomputable def nd_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : DerivableClass F EqX A)
    (env : interpCtx X Γ)
    : dialecticaRealizerCtx si A.negTrans env :=
  dialectica_soundness_ctx si eqxi A.negTrans env (negTrans_sound h)

/-- Closed-formula variant: the realizer lives at the empty environment. -/
noncomputable def nd_soundness_closed
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {A : Formula F ([] : Ctx ι)}
    (h : DerivableClass F EqX A)
    : dialecticaRealizer si A.negTrans :=
  nd_soundness si eqxi h ()
