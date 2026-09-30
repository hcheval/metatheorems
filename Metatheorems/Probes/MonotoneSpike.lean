/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Monotone
import Metatheorems.Probes.ConjBoundDemo

/-!
# Spike G0: the monotone functional interpretation on `acFinal`'s nine constructors

**"Spike"** is used here in the software sense: a deliberately throwaway prototype built to
answer one feasibility question fast — here, *does the monotone functional interpretation
clear the `and_contract` stall that blocked the term route?* Nine of the (then) 36
`Derivable` constructors were implemented, just enough to run `ConjBoundDemo.acFinal`, and the
rest fell back to the term route. It did clear it (`1709` in ≈207 ms where the term route was
a `whnf` timeout), and that result is why MFI was adopted. Elsewhere in the docs "the spike"
always means this file.

**STATUS (2026-09-05, Lane A): the recursion has moved into the library**
(`Metatheorems/Dialectica/Monotone.lean`). This file **re-runs the spike's gate against the
library recursion** — same statements, same numbers, same normal forms. The full-recursion gate
G1 (`tFinalTwice`, a genuine crossing `max`) is `Probes/MonotoneLaneA.lean`.

**Question.** `ConjBoundDemo.acFinal` is a 13-constructor derivation with one `and_contract`
whose counter-side bound `acUt_at_5_9` is a kernel `whnf` timeout (`Eq.rec ↦ 60474`,
`Term.rename ↦ 10504` — the kernel executing renamings over dependent indices on the way to
a 2,529-node term, `SizeProbe.lean`). Does computing a **majorant of the realizer by recursion
on the derivation**, as a semantic value at the hat type — Kohlenbach's monotone functional
interpretation, *Applied Proof Theory* Thm 9.1, pp. 141–145 — with the realizer itself only
existentially quantified, clear the stall?

**RESULT: THE GATE PASSES.** `mfi_acFinal_U_at_5_9 : 1709 = mfiU (triCm M h) (acSpike M h) (5,9)`
closes by `have hval : … = max (pairN …) 0 := rfl; rw [hval]; decide`, kernel-checked, at
`[propext, Classical.choice, Quot.sound]`, in **≈0.2 s of elaboration** (`rfl` ≈ 207 ms, `decide`
≈ 2 ms, kernel type-checking ≈ 40–70 ms; `set_option profiler true`, 2026-09-05) — against a
200 000-heartbeat `whnf` timeout for the same number on the term route. The witness side
`mfi_acFinal_V_at_5_9 = 1709` agrees with the term route's `cVtTwice_at_5_9`.

The definition of `MRealizer` (now `Metatheorems.MRealizer`: the mixed hypothesis is `MajEnv`,
the existential is hoisted outside the environment, a self-majorization conjunct is carried),
the nine cases and the `MaxCompat` facts, and the measured gate table (including why the `max`
is `max(1709, 0)`) are in the notes.
-/

namespace Metatheorems
namespace MonotoneSpike

open Formula
open TriangleBoundDemo (pTy triCm)
open ConjBoundDemo (tB acFinal tFinalOnce)

/-- Constructor count, copied from `SizeProbe.derivSize` (that file is not imported here). -/
def derivSizeSpike {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Nat
  | _, _, .mp a b          => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .syllogism a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .exportation a   => 1 + derivSizeSpike a
  | _, _, .importation a   => 1 + derivSizeSpike a
  | _, _, .expansion a     => 1 + derivSizeSpike a
  | _, _, .forall_rule a   => 1 + derivSizeSpike a
  | _, _, .exist_rule a    => 1 + derivSizeSpike a
  | _, _, .univ_gen a      => 1 + derivSizeSpike a
  | _, _, .qfer _ _ a      => 1 + derivSizeSpike a
  | _, _, .induction a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, _                => 1

/-- The scale of the gate: `acFinal` is thirteen constructors. -/
theorem derivSize_acFinal : derivSizeSpike acFinal = 13 := rfl

/-- The monotone realizer of `acFinal`, at the W-hyperbolic model with `d(a, 0_X) ≤ 5` —
now through the library's full recursion. -/
noncomputable def acSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) acFinal

/-- The same for the contraction-free control `tFinalOnce`. -/
noncomputable def onceSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) tFinalOnce

/-- **THE GATE (re-run).** The counter-side bound of `acFinal` — the one that is a `whnf`
timeout on the term route (`ConjBoundDemo.acUt_at_5_9`) — through the library's monotone
interpretation. -/
theorem mfi_acFinal_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The witness side of the same derivation, agreeing with `cVtTwice_at_5_9`'s term-route
value. -/
theorem mfi_acFinal_V_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The bound moves with `x*`: at `(5,1)` it is `349`, `s₁`'s majorant there
(`ConjBoundDemo.witM1_at_5_1`). -/
theorem mfi_acFinal_U_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The contraction-free control `tFinalOnce` through the same interpretation: the same
`1709`, and — visibly in the `hval` normal form — **no `max`**. -/
theorem mfi_once_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- Permanent refutation controls: the gate value is exact from below and above. -/
theorem mfi_acFinal_U_ne_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

theorem mfi_acFinal_U_ne_1710 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1710 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

/-- The `U` is not `0` — the premise is consulted. -/
theorem mfi_acFinal_U_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms derivSize_acFinal
#print axioms mfi_acFinal_U_at_5_9
#print axioms mfi_acFinal_V_at_5_9
#print axioms mfi_acFinal_U_at_5_1
#print axioms mfi_once_U_at_5_9
#print axioms mfi_acFinal_U_ne_1708
#print axioms mfi_acFinal_U_ne_1710
#print axioms mfi_acFinal_U_ne_zero

end MonotoneSpike
end Metatheorems
