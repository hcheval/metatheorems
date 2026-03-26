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
   in `Derivable F EqX Allowed.classical` to an intuitionistic
   proof of `NT(A) = ¬¬nt(A)` in `Derivable F EqX Allowed.extended`.

2. **Dialectica interpretation** (D): maps a proof of `NT(A)` in the extended system
   to a Lean-computable realizer for the Dialectica translation of `NT(A)`.

The composition gives: from a **classical** proof of `A`, extract a
Lean-computable Dialectica realizer for `NT(A)`.
-/

open Formula

/-- **ND-Interpretation**: from a classical derivation of `A`,
    extract a Lean-computable Dialectica realizer for `NT(A)`. -/
noncomputable def nd_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F EqX Allowed.classical A)
    (env : interpCtx X Γ)
    : dialecticaRealizerCtx si A.negTrans env :=
  dialectica_soundness_ctx si eqxi A.negTrans env
    ((negTrans_sound adm h).castAllowed (by constructor <;> decide))

/-- Closed-formula variant: the realizer lives at the empty environment. -/
noncomputable def nd_soundness_closed
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    {A : Formula F ([] : Ctx ι)}
    (h : Derivable F EqX Allowed.classical A)
    : dialecticaRealizer si A.negTrans :=
  nd_soundness si eqxi adm h ()

