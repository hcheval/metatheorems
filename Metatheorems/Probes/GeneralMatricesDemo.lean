/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Majorizability
import Metatheorems.Terms.Real

/-!
# General-matrix demo: a `le_R_pu` premise through the metatheorem

**The point.** `syntactic_general_metatheorem` requires its premise matrix `B₀` to be
quantifier-free. The motivating case it therefore *rejects* is a premise stated with
`le_R_pu` — the purely universal `≤ℝ`, which is literally `∀n. ¬(…)`, i.e. Kohlenbach's
`B∀ = ∀b̲ B₀`. `syntactic_general_metatheorem_gen` accepts it. This file shows both, on the
statement

    ∀x^{ℕ→ℕ} ( ∀u⁰ (⟨u⟩ℝ ≤ℝ x)_pu  →  ∃v⁰ ∃c⁰ (c =₀ x(v)) )

at `ι = Empty` (pure `WE-HA^ω`, the `TinyBoundDemo` model). The derivation is trivial on
purpose — the premise is discarded and the conclusion witnessed by `v := 0`, `c := x(0)` —
because what is being demonstrated is the *shape* the metatheorem accepts, not the bound.

Two things are checked by the kernel here:

* `demoB.isQF = false` (`rfl`) — the old entry point cannot even be *stated* on this input:
  its `hB_qf : B₀.isQF = true` is an uninhabited type.
* `demoB.isPurelyUniversal = true` (`rfl`) — and the new entry point goes through, for both
  the extended and the classical input, with the conclusion reading
  `∀u ≤ Φ(x*) (⟨u⟩ℝ ≤ℝ x) → ∃v ≤ Φ(x*) ∃c (c = x(v))`.

Not imported by anything; built as part of `Metatheorems.lean` so it cannot rot.
-/

namespace Metatheorems
namespace GeneralMatricesDemo

open Formula

-- ============================================================================
-- The `ι = Empty` model (same recipe as `TinyBoundDemo`, distinct names)
-- ============================================================================

def gXE : Empty → Type := fun i => i.elim
def gFE : Empty → Ty Empty := fun i => i.elim

def gSiE : SpaceInterp gXE gFE where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

def gEqxiE : EqXInterp gXE gFE gSiE where
  realize             := fun i => i.elim
  extract             := fun i => i.elim
  dist_comm_holds     := fun i => i.elim
  dist_tri_holds      := fun i => i.elim

def gPremE : PremiseSet gFE := fun _ => False

def gSpremiseE : ∀ (Γ' : Ctx Empty) (B : Formula gFE Γ'), gPremE ⟨Γ', B⟩ → SRealizer gSiE B :=
  fun _ _ h => h.elim

def gNtsE : NTStableD gPremE := fun _ _ h => h.elim

-- ============================================================================
-- The statement
-- ============================================================================

/-- `x : ℕ → ℕ`, a real-number code. -/
abbrev gR : Ty Empty := realTy Empty

/-- The premise matrix `B := (⟨u⟩ℝ ≤ℝ x)_pu`, in context `[u : nat, x : ℝ]`.
A genuine ∀-formula: `le_R_pu` unfolds to `∀n. ¬(… =₀ 0)`. -/
def demoB : Formula gFE [Ty.nat, gR] :=
  le_R_pu (Term.app Term.embed_nat_R (.var .vz)) (.var (.vs .vz))

/-- The conclusion matrix `C := ∃c⁰ (c =₀ x(v))`, in context `[v : nat, x : ℝ]`.
A genuine ∃-formula. -/
def demoC : Formula gFE [Ty.nat, gR] :=
  Formula.ex Ty.nat
    (Formula.eq0 (.var .vz) (Term.app (.var (.vs (.vs .vz))) (.var (.vs .vz))))

/-- **The old entry point cannot take this premise**: its `hB_qf : demoB.isQF = true` is
uninhabited. -/
theorem demoB_not_qf : demoB.isQF = false := rfl

/-- The old entry point cannot take this conclusion either. -/
theorem demoC_not_qf : demoC.isQF = false := rfl

/-- …but it is a ∀-formula, which is what 17.52 asks for. -/
theorem demoB_pu : demoB.isPurelyUniversal = true := rfl
theorem demoB_vf : demoB.isVFree = true := rfl
/-- …and the conclusion is an ∃-formula. -/
theorem demoC_pe : demoC.isPurelyExistential = true := rfl
theorem demoC_vf : demoC.isVFree = true := rfl

-- ============================================================================
-- The derivation, raw `Derivable` constructors only
-- ============================================================================

/-! The derivation uses only base constructors, so it is stated for every `a : Allowed` and
instantiated at `Allowed.extended` and `Allowed.classical` below. (`castAllowed` cannot go
from extended to classical: the extended system has Markov/IP/AC, the classical one does not.) -/

section Derivation
variable {a : Allowed}

/-- `∃c (c =₀ x(0))` in context `[x : ℝ]`, by `refl0` at `c := x(0)`. -/
def gExC :
    @Derivable Empty Empty gFE a gPremE [gR]
      (Formula.ex Ty.nat (Formula.eq0 (.var .vz) (Term.app (.var (.vs .vz)) Term.zero))) :=
  by
    refine Derivable.mp ?_
      (Derivable.exist_ax (Term.app (.var .vz) Term.zero)
        (Formula.eq0 (.var .vz) (Term.app (.var (.vs .vz)) Term.zero)))
    exact Derivable.refl0

/-- `∃v ∃c (c =₀ x(v))` in context `[x : ℝ]`, by `exist_ax` at `v := 0`. The body
`demoC.subst0 0` is `∃c (c =₀ x(0))` definitionally. -/
def gExVC :
    @Derivable Empty Empty gFE a gPremE [gR] (Formula.ex Ty.nat demoC) :=
  Derivable.mp gExC (Derivable.exist_ax Term.zero demoC)

/-- Discard the (never used) premise `∀u demoB`. -/
def gInner :
    @Derivable Empty Empty gFE a gPremE [gR]
      (Formula.all Ty.nat demoB →ᶠ Formula.ex Ty.nat demoC) :=
  Derivable.mp gExVC (Derivable.exportation Derivable.and_weak)

def gDummy : Formula gFE ([] : Ctx Empty) := Formula.eq0 Term.zero Term.zero

def gInnerW :
    @Derivable Empty Empty gFE a gPremE [gR]
      (Formula.weakenBy gR gDummy →ᶠ (Formula.all Ty.nat demoB →ᶠ Formula.ex Ty.nat demoC)) :=
  Derivable.mp gInner (Derivable.exportation Derivable.and_weak)

/-- The closed statement `∀x (∀u demoB → ∃v demoC)`, in any system `a`. -/
def gFinalA :
    @Derivable Empty Empty gFE a gPremE []
      (Formula.all gR (Formula.all Ty.nat demoB →ᶠ Formula.ex Ty.nat demoC)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule gInnerW)

end Derivation

/-- Extended input. -/
def gFinal :
    @Derivable Empty Empty gFE Allowed.extended gPremE []
      (Formula.all gR (Formula.all Ty.nat demoB →ᶠ Formula.ex Ty.nat demoC)) := gFinalA

/-- Classical input. -/
def gFinalC :
    @Derivable Empty Empty gFE Allowed.classical gPremE []
      (Formula.all gR (Formula.all Ty.nat demoB →ᶠ Formula.ex Ty.nat demoC)) := gFinalA

-- ============================================================================
-- Through the general-matrix metatheorem
-- ============================================================================

/-- **Extended input.** The conclusion is 17.52's, with the ∀-premise intact:
`∀u ≤ Φ(x*) (⟨u⟩ℝ ≤ℝ x) → ∃v ≤ Φ(x*) ∃c (c = x(v))`. -/
theorem demo_bound :
    ∃ Φ : Ty.interpret gXE gR.hat → Nat,
      ∀ (x : Ty.interpret gXE gR) (x_star : Ty.interpret gXE gR.hat),
        (bezemAbstractEmpty gSiE).toRel.maj gR x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret gSiE demoB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret gSiE demoC (v, (x, ())) :=
  syntactic_general_metatheorem_gen gEqxiE gSpremiseE (bezemAbstractEmpty gSiE)
    demoB_pu demoB_vf demoC_pe demoC_vf gFinal

/-- **Classical input**, through `classical_to_prenex_extended_gen`. -/
theorem demo_bound_classical :
    ∃ Φ : Ty.interpret gXE gR.hat → Nat,
      ∀ (x : Ty.interpret gXE gR) (x_star : Ty.interpret gXE gR.hat),
        (bezemAbstractEmpty gSiE).toRel.maj gR x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret gSiE demoB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret gSiE demoC (v, (x, ())) :=
  syntactic_general_metatheorem_classical_gen gEqxiE gNtsE gSpremiseE
    (bezemAbstractEmpty gSiE) demoB_pu demoB_vf demoC_pe demoC_vf gFinalC

/-- **The bound as data**, via `ConstMajorants` at `ι = Empty`. -/
def demo_bound_at :
    { Φ : Ty.interpret gXE gR.hat → Nat //
      ∀ (x : Ty.interpret gXE gR) (x_star : Ty.interpret gXE gR.hat),
        (bezemAbstractEmpty gSiE).toRel.maj gR x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret gSiE demoB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret gSiE demoC (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen gEqxiE gSpremiseE (bezemConstMajorantsEmpty gSiE)
    demoB_pu demoB_vf demoC_pe demoC_vf gFinal

#print axioms demo_bound
#print axioms demo_bound_classical
#print axioms demo_bound_at

end GeneralMatricesDemo
end Metatheorems
