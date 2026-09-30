/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MonotoneMetatheorem
import Metatheorems.ProofMode.MCT
import Metatheorems.Probes.TinyBoundDemo
import Metatheorems.Probes.MonotoneLaneB

/-!
# Gate G3: `mct_p2`'s `Φ`, named — and where its evaluation stops

**Question.** `mct_p2` (`ProofMode/MCT.lean`) is the proof-mode-written ℕ-MCT derivation;
`mct_bound_p2` is `∃`-valued, so MCT has never produced a number (CLAUDE.md Track D2). With
`monotone_general_metatheorem_at` (`MonotoneMetatheorem.lean`) its `Φ` can be *named*:
`mct_bound_p2_at` below, and `mctPhi` at `ι = Empty` with `bezemConstMajorantsEmpty`. Does
it *evaluate* at a concrete majorant of the fused functional?

**RESULT: NAMED AND TYPE-CHECKED; NOT EVALUATED.** `mctPhi` elaborates instantly; its
evaluation at `x* = λ_ _. 1` is `std::bad_alloc` at 12 GB (kernel) and a `whnf` timeout
(`Meta`). Two controls are kernel-checked below (`indFinal`, and the proof-mode layer); what
remains as the cause is the `Eq.mpr`/`seq_cast` nodes.
-/

namespace Metatheorems
namespace MonotoneMCT

open Formula
open TinyBoundDemo (tXE tFE tSiE tEqxiE tPremE tSpremiseE tB0 tC0)
open MonotoneLaneA (derivSizeA)
open MonotoneLaneB (walk)

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type} {Premises : PremiseSet F}

-- B3: `mct_bound_p2_at` — MCT's Φ, named, for any model

/-- **`mct_bound_p2` with the bound as data**, computed by the monotone functional
interpretation. Same statement as `ProofMode.mct_bound_p2`, `Subtype` for `∃`, a
`ConstMajorants` in place of the bare `AbstractMajorizability` (forced, as for
`syntactic_general_metatheorem_at`). This is the first time MCT's `Φ` has a name. -/
def mct_bound_p2_at (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B) :
    { Φ : Ty.interpret X (mctTy ι).hat → Nat //
      ∀ (x : Ty.interpret X (mctTy ι)) (x_star : Ty.interpret X (mctTy ι).hat),
        am.toRel.maj (mctTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si mctB₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si mctC₀ (v, (x, ())) } :=
  monotone_general_metatheorem_at eqxi spremise cm rfl rfl rfl rfl
    (ProofMode.mct_p2 (al := Allowed.extended))

-- At ι = Empty

def mctD : @Derivable Empty Empty tFE Allowed.extended tPremE [] mctStatement :=
  ProofMode.mct_p2 (al := Allowed.extended)

def cmE : ConstMajorants (bezemAbstractEmpty tSiE) := bezemConstMajorantsEmpty tSiE

/-- **MCT's `Φ`, named**, at `ι = Empty` with the Bezem majorants. Type-checks instantly. -/
def mctPhi : Ty.interpret tXE (mctTy Empty).hat → ℕ :=
  (mct_bound_p2_at tSiE tEqxiE cmE tSpremiseE).val

/-- The smallest sensible majorant of the fused functional: `K = 1`, constant `g`, `a ≤ 1`. -/
def xstar : Ty.interpret tXE (mctTy Empty).hat := fun _ _ => (1 : ℕ)

open Lean Meta in
#eval show MetaM Unit from walk ``Metatheorems.ProofMode.mct_p2

-- Control: Lane A's `induction` case on a real `pinduction`

/-- `∀x (∀u (u =₀ u) → ∃v (v =₀ x))` by **induction on `x`**, witness `x` itself at every
step — the smallest derivation whose bound goes through `MRealizer.induction` (`recMaj`). -/
def indFinal : @Derivable Empty Empty tFE Allowed.extended tPremE []
    (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) := by
  pmode
  pinduction
  · pintro h
    pexists Term.zero
    pthm Derivable.refl0
  · pforall
    pintro ih
    pintro h
    pexists (Term.app Term.succ (Term.var Var.vz))
    pthm Derivable.refl0

#eval derivSizeA indFinal    -- 368

def rI : MRealizer cmE (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) :=
  monotone_soundness tEqxiE tSpremiseE cmE indFinal

def five : Ty.interpret tXE Ty.nat.hat := (5 : ℕ)
def nine : Ty.interpret tXE Ty.nat.hat := (9 : ℕ)

/-- Through `recMaj`: the witness majorant at `x* = 5` is `5`. -/
theorem ind_V_5 : (5 : ℕ) = mfiV cmE rI five := by kernel_rfl
/-- …and it moves with `x*`. -/
theorem ind_V_9 : (9 : ℕ) = mfiV cmE rI nine := by kernel_rfl
/-- The premise is never consulted, so `U = 0`. -/
theorem ind_U_5 : (0 : ℕ) = mfiU cmE rI five := by kernel_rfl

/-- `Φ` through `monotone_general_metatheorem_at`: `max 0 5 = 5`. -/
theorem ind_phi_5 : (5 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    rfl rfl rfl rfl indFinal).val five := by kernel_rfl

theorem ind_V_5_ne_4 : (4 : ℕ) ≠ mfiV cmE rI five := by rw [← ind_V_5]; decide
theorem ind_V_5_ne_6 : (6 : ℕ) ≠ mfiV cmE rI five := by rw [← ind_V_5]; decide
theorem ind_V_9_ne_5 : (5 : ℕ) ≠ mfiV cmE rI nine := by rw [← ind_V_9]; decide

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms mct_bound_p2_at
#print axioms mctPhi
#print axioms indFinal
#print axioms ind_V_5
#print axioms ind_V_9
#print axioms ind_U_5
#print axioms ind_phi_5
#print axioms ind_V_5_ne_4
#print axioms ind_V_5_ne_6
#print axioms ind_V_9_ne_5

end MonotoneMCT
end Metatheorems
