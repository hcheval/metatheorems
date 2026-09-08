/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Demo.Walkthrough

/-!
# The guard on `Demo/Walkthrough.lean`'s §6 — every commented extraction, run for real

`Demo/Walkthrough.lean` is the file a presenter scrolls through on stage. Its extraction
commands are **commented out** there, so that a live audience sees them being run rather than
sitting already-green in the build, and so that a slow one cannot make the file expensive to
open.

Commented code rots. Two probes in this repo broke unnoticed exactly that way (`BoundProbe`
and `SeqMpBoundProbe` carried a stale `@Derivable` arity for weeks, because `Probes/` was not
reachable from the umbrella). So every extraction in §6 that runs in **under ten seconds** is
restated here, uncommented, against the Walkthrough's **own** derivations — this file imports
`Demo.Walkthrough`, it does not re-copy anything — and this file is in the `Probes.lean`
sweep. If a commented line in §6 stops working, `scripts/build.sh Probes` says so.

**What is deliberately NOT here**, and is therefore unguarded:

* `exp_V_8` (`V = 256` at `k* = 8`) — an `INTERNAL PANIC: out of memory` at the 12 GB cap.
  It is in the Walkthrough as the *marked ceiling*, not as something to run.
* `#hilbert contract_pm all depth 10` — 1844 steps, ≈15 s. Correct, but too slow to sit in
  every build; the depth-0 and depth-4 listings are uncommented in the Walkthrough itself and
  cover the same point.

Everything else in §6 appears below.

## Instrument

`kernel_rfl` (`Probes/MonotoneLaneB.lean`) assigns `Eq.refl` and lets the kernel decide the
equation — the evaluator of record at this scale; `#eval` appears nowhere, so nothing here
rests on compiler trust. Each block ends with a **refutation control**, a `decide` that the
neighbouring value is *not* the bound: without one, a `rfl` that stalls and a `rfl` that
computes are indistinguishable from a green build.
-/

-- Serial elaboration is **required** here, not cosmetic: with Lean's default parallel
-- elaboration the twenty `kernel_rfl`s below run concurrently and the file dies with
-- `std::bad_alloc` at the 12 GB cap (measured). `ContentExampleNat.lean` sets the same option
-- for the same reason. No limit is raised anywhere.
set_option Elab.async false

namespace Metatheorems
namespace DemoChecks

open Metatheorems.Demo (linearR doublingR at5 at9 xs ys doubling)
open MonotoneMCT (cmE)
open TinyBoundDemo (tEqxiE tSpremiseE)

-- ============================================================================
-- §6a — the LINEAR bound: witness is the induction variable, nothing iterates
-- ============================================================================

theorem lin_V_5 : (5 : ℕ) = mfiV cmE linearR at5 := by kernel_rfl
theorem lin_V_9 : (9 : ℕ) = mfiV cmE linearR at9 := by kernel_rfl
theorem lin_U_5 : (0 : ℕ) = mfiU cmE linearR at5 := by kernel_rfl

theorem lin_V_5_ne_4 : (4 : ℕ) ≠ mfiV cmE linearR at5 := by rw [← lin_V_5]; decide
theorem lin_V_9_ne_5 : (5 : ℕ) ≠ mfiV cmE linearR at9 := by rw [← lin_V_9]; decide

-- ============================================================================
-- §6b — the EXPONENTIAL bound: witness built from the previous witness
-- ============================================================================

theorem exp_V_0 : (1 : ℕ) = mfiV cmE doublingR (xs 0) := by kernel_rfl
theorem exp_V_3 : (8 : ℕ) = mfiV cmE doublingR (xs 3) := by kernel_rfl
theorem exp_V_5 : (32 : ℕ) = mfiV cmE doublingR (xs 5) := by kernel_rfl

theorem exp_V_3_ne_7 : (7 : ℕ) ≠ mfiV cmE doublingR (xs 3) := by rw [← exp_V_3]; decide
theorem exp_V_5_ne_8 : (8 : ℕ) ≠ mfiV cmE doublingR (xs 5) := by rw [← exp_V_5]; decide

/-- The bound tracks the *function* majorant too, not only the index: `f*(0) = 3` triples
every value. -/
theorem exp_V_ys_0 : (3 : ℕ) = mfiV cmE doublingR (ys 0) := by kernel_rfl
theorem exp_V_ys_2 : (12 : ℕ) = mfiV cmE doublingR (ys 2) := by kernel_rfl
theorem exp_V_ys_2_ne_4 : (4 : ℕ) ≠ mfiV cmE doublingR (ys 2) := by rw [← exp_V_ys_2]; decide

/-- `U(k*) = k* − 1`, sharp — so `U` is visibly not a copy of `V`. -/
theorem exp_U_0 : (0 : ℕ) = mfiU cmE doublingR (xs 0) := by kernel_rfl
theorem exp_U_2 : (1 : ℕ) = mfiU cmE doublingR (xs 2) := by kernel_rfl
theorem exp_U_3 : (2 : ℕ) = mfiU cmE doublingR (xs 3) := by kernel_rfl
theorem exp_U_5 : (4 : ℕ) = mfiU cmE doublingR (xs 5) := by kernel_rfl

theorem exp_U_3_ne_1 : (1 : ℕ) ≠ mfiU cmE doublingR (xs 3) := by rw [← exp_U_3]; decide
theorem exp_U_3_ne_3 : (3 : ℕ) ≠ mfiU cmE doublingR (xs 3) := by rw [← exp_U_3]; decide

/-- `Φ` through the metatheorem's own entry point: `Φ = max U V`. -/
theorem exp_Phi_3 : (8 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    ContentExampleNat.eB_qf ContentExampleNat.eB_vf
    ContentExampleNat.eC_qf ContentExampleNat.eC_vf doubling).val (xs 3) := by kernel_rfl

theorem exp_Phi_5 : (32 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    ContentExampleNat.eB_qf ContentExampleNat.eB_vf
    ContentExampleNat.eC_qf ContentExampleNat.eC_vf doubling).val (xs 5) := by kernel_rfl

theorem exp_Phi_3_ne_16 : (16 : ℕ) ≠ (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    ContentExampleNat.eB_qf ContentExampleNat.eB_vf
    ContentExampleNat.eC_qf ContentExampleNat.eC_vf doubling).val (xs 3) := by
  rw [← exp_Phi_3]; decide

-- ============================================================================
-- §6c — the ceiling, at the last value that still finishes
-- ============================================================================

/-- `k* = 7` is the largest input this derivation's bound reduces at: `2^7 = 128`, ≈9 s of
kernel time. At `k* = 8` the same `kernel_rfl` is out of memory at the 12 GB cap — which is
why `exp_V_8` exists nowhere, in this file or the Walkthrough. The ceiling is the **value**,
not the derivation: `recMaj` iterates value-many times with nothing shared. -/
theorem exp_V_7 : (128 : ℕ) = mfiV cmE doublingR (xs 7) := by kernel_rfl

theorem exp_V_7_ne_127 : (127 : ℕ) ≠ mfiV cmE doublingR (xs 7) := by rw [← exp_V_7]; decide

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms lin_V_5
#print axioms lin_V_9
#print axioms lin_U_5
#print axioms exp_V_0
#print axioms exp_V_3
#print axioms exp_V_5
#print axioms exp_V_7
#print axioms exp_V_ys_0
#print axioms exp_V_ys_2
#print axioms exp_U_0
#print axioms exp_U_2
#print axioms exp_U_3
#print axioms exp_U_5
#print axioms exp_Phi_3
#print axioms exp_Phi_5

end DemoChecks
end Metatheorems
