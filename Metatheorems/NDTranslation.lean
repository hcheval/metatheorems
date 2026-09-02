/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica
import Metatheorems.NegTrans


namespace Metatheorems

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
def nd_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Premises : PremiseSet F}
    (adm : AdmissibleEqX EqX Premises)
    (nts : NTStableD EqX Premises)
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : @Derivable ι F EqX Allowed.classical Premises Γ A)
    (env : Ctx.interpret X Γ)
    : dialecticaRealizerCtx si Aᴺᵀ env :=
  dialectica_soundness_ctx si eqxi premise_realizer Aᴺᵀ env
    ((negTrans_sound adm nts h).castAllowed (by constructor <;> decide))

/-- Closed-formula variant: the realizer lives at the empty environment. -/
def nd_soundness_closed
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Premises : PremiseSet F}
    (adm : AdmissibleEqX EqX Premises)
    (nts : NTStableD EqX Premises)
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {A : Formula F ([] : Ctx ι)}
    (h : @Derivable ι F EqX Allowed.classical Premises [] A)
    : dialecticaRealizer si Aᴺᵀ :=
  nd_soundness si eqxi adm nts premise_realizer h ()
#print axioms nd_soundness 

end Metatheorems
