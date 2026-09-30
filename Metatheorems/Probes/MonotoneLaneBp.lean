/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.Probes.UPremiseDemo
import Metatheorems.Probes.MonotoneLaneB

/-!
# Lane B': the `Eq.mpr` entry for the monotone functional interpretation, and its reach

`Dialectica/MonotoneMemo.lean` adds `MRealizer.transport` and the three commutation lemmas
`monotone_soundness_eqmpr`/`_eqmp`/`_subst`. This file exercises them.

**Result.** *Positive* where the cast is reachable: `castU` (`UPremiseDemo`'s premise-consuming
derivation, matrix carrying `mul_Q`, two `Eq.mp` casts on the syllogism's middle formula)
reduces to `U = 901`, moving with `x*`, once `simp only [monotone_soundness_eqmp …]` rewrites the
casts to `MRealizer.transport`. *Negative* where the casts are buried under the `pm_*`/`seq_*`
layer (`le_R_pu_of_le_R`, gates G-B'2 and G-B'3: the `simp` route is a 12 GB `std::bad_alloc`).
The bare-kernel control, the cast inventory and the details are in the notes.

## Part C0 — the classical route under MFI (measurement only)

See `Probes/ClassicalMfiProbe.lean`.
-/

namespace Metatheorems
namespace MonotoneLaneBp

open Formula
open UPremiseDemo (pTy uWit uCm uDummyOuter)
open MetricSpace (ι)
-- `kernel_rfl` is a tactic from `Probes.MonotoneLaneB`, available globally via the import.

-- G-B'1: a directly-reachable heavy ℚ cast on the premise-consuming counter path

/-- Matrix carrying the heaviest ℚ constant: `u =₀ mul_Q(u,u)`. QF and ∨-free, so `wTy` is
`unit` — the cast on it is invisible to `U`, which is the whole point. -/
def mP : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var .vz) (Term.app2 Term.mul_Q (Term.var .vz) (Term.var .vz))

/-- The normalised middle formula `uWit =₀ mul_Q(uWit, uWit)`. -/
def mClean : Formula WHyperbolic.F [pTy] :=
  Formula.eq0 uWit (Term.app2 Term.mul_Q uWit uWit)

/-- Cheap by `closed_subst`; a full `mul_Q` delta by kernel `rfl`. -/
theorem mcEq : mP.subst0 uWit = mClean := by
  simp only [mP, mClean, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map_vz,
    Term.app2, closed_subst]

abbrev D (Γ : Ctx ι) (A : Formula WHyperbolic.F Γ) :=
  @Derivable ι WHyperbolic.κ WHyperbolic.F Allowed.extended WHyperbolic.Premises Γ A

/-- Instantiate `∀u mP` at `uWit`, then cast the (dirty) middle to the clean form — `Eq.mp`. -/
def uInstC : D [pTy] (Formula.all Ty.nat mP →ᶠ mClean) :=
  Eq.mp (congrArg (D [pTy]) (congrArg (fun M => Formula.all Ty.nat mP →ᶠ M) mcEq))
    (Derivable.forall_ax (A := mP) uWit)

/-- Existential intro with the clean middle as antecedent — the matching `Eq.mp`. -/
def uGenC : D [pTy] (mClean →ᶠ Formula.ex Ty.nat mP) :=
  Eq.mp (congrArg (D [pTy]) (congrArg (fun M => M →ᶠ Formula.ex Ty.nat mP) mcEq))
    (Derivable.exist_ax uWit mP)

/-- Compose: the premise is *consumed* through both casts (no `refl0`). -/
def uInnerC : D [pTy] (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP) :=
  Derivable.syllogism uInstC uGenC

def uInnerWC : D [pTy] (Formula.weakenBy pTy uDummyOuter →ᶠ
    (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  Derivable.mp uInnerC (Derivable.exportation Derivable.and_weak)

def uFinalC : D [] (Formula.all pTy (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule uInnerWC)

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

noncomputable def mrC : MRealizer (uCm M h) (Formula.all pTy
    (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  monotone_soundness M.eqXInterp M.spremise (uCm M h) uFinalC

/-- **G-B'1.** `U = 901` through two heavy `mul_Q` `Eq.mp` casts on the premise-consuming
counter path, via `monotone_soundness_eqmp` + the kernel. The `simp` step rewrites both casts
to `MRealizer.transport`, whose data cast collapses structurally (`wTy (eq0 …) = unit`);
`kernel_rfl` then evaluates. Bare `kernel_rfl` (no `simp`) is a `std::bad_alloc` at 12 GB
(see header). -/
theorem castU (g : ℕ → ℕ) :
    (901 : ℕ) = mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
  simp only [mrC, uFinalC, uInnerWC, uInnerC, uInstC, uGenC, monotone_soundness,
    monotone_soundness_eqmp (hB := congrArg (fun M' => Formula.all Ty.nat mP →ᶠ M') mcEq),
    monotone_soundness_eqmp (hB := congrArg (fun M' => M' →ᶠ Formula.ex Ty.nat mP) mcEq)]
  kernel_rfl

/-- `U` moves with `x*`: `1273` at `(7, g)` (as `UPremiseDemo.uUt_at_7`). -/
theorem castU_at_7 (g : ℕ → ℕ) :
    (1273 : ℕ) = mfiU (uCm M h) (mrC M h) ((7 : ℕ), g) := by
  simp only [mrC, uFinalC, uInnerWC, uInnerC, uInstC, uGenC, monotone_soundness,
    monotone_soundness_eqmp (hB := congrArg (fun M' => Formula.all Ty.nat mP →ᶠ M') mcEq),
    monotone_soundness_eqmp (hB := congrArg (fun M' => M' →ᶠ Formula.ex Ty.nat mP) mcEq)]
  kernel_rfl

/-- Non-degeneracy: the `simp`+kernel really evaluates, and `902` is refuted. -/
theorem castU_ne_902 (g : ℕ → ℕ) :
    (902 : ℕ) ≠ mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
  rw [← castU M h g]; decide

theorem castU_at_7_ne_901 (g : ℕ → ℕ) :
    (901 : ℕ) ≠ mfiU (uCm M h) (mrC M h) ((7 : ℕ), g) := by
  rw [← castU_at_7 M h g]; decide

end Model

-- Axiom hygiene

#print axioms castU
#print axioms castU_at_7
#print axioms castU_ne_902

end MonotoneLaneBp
end Metatheorems
