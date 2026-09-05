/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneND
import Metatheorems.Probes.LemBoundDemo
import Metatheorems.Probes.MonotoneLaneB

/-!
# The synthetic classical-syllogism chain (Lane C's ×5 datum), for the sharing experiment

`Probes/ClassicalMfiProbe.lean`'s STATUS block records, from a scratch run:

> a bare chain of k classical `syllogism`s (`I_comb`s composed, no `lem`): kernel time
> k=2 **140 ms**, k=4 **3.68 s**, k=8 **OOM** — ≈ ×5 per syllogism.

and, on the compiled evaluator, `5` at k=0 and k=2 in ≈0 s of compute, no result for k=3 in
400 s or k=4 in 240 s. The construction itself was never committed. This file reconstructs
it so the before/after of the `let`-sharing experiment in `Dialectica/Monotone.lean` is
measured on one fixed object.

`chained k` is `⊢ ∃v (v =₀ x)` proved by composing `k+1` identity implications with
`syllogism` and applying the result to the direct proof — logically `exD` itself, so the
answer is the same at every `k` and only the *nesting* changes. `wit k xs` is the `∃v`
index read off the monotone realizer of the **negatively translated** statement, through
the surviving `¬¬` exactly as `ClassicalMfi.cU`/`cV` do; it should be `xs`.

## BEFORE the sharing experiment (`Dialectica/Monotone.lean` unmodified, 2026-09-06)

Kernel type-checking time of `theorem wk : (5 : ℕ) = wit k 5 := by kernel_rfl`
(`set_option profiler true`, 12 GB cap, machine shared with three other Lean builds):

| k (syllogisms in the chain) | 0 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| kernel | <0.1 s | 0.16 s | 0.71 s | 2.9 s | 9.4 s | **`std::bad_alloc` @ 12 GB** |

≈ ×3.7 per level — Lane C's "≈ ×5 per syllogism", re-measured on a committed construction.
The compiled evaluator is worse: `#eval wit 0 5` alone is already `std::bad_alloc` at 12 GB
(so the k = 0 `#eval` reported in `ClassicalMfiProbe`'s header does not reproduce here; the
call-by-value route is not usable at all on this construction).
-/

namespace Metatheorems
namespace SharingProbe

open Formula
open LemBoundDemo (lXE lFE lSiE lEqxiE lPremE lSpremiseE lB0 lC0 lCmE)

/-- `∃v (v =₀ x)` in context `[x : ℕ]`. -/
abbrev SE : Formula lFE [Ty.nat] := Formula.ex Ty.nat lC0

/-- `⊢ ∃v (v =₀ x)`, witness `x` — the `V = 5` of `LemBoundDemo`. -/
def exD : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] SE :=
  Derivable.mp Derivable.refl0 (Derivable.exist_ax (Term.var Var.vz) lC0)

def idD : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] (SE →ᶠ SE) :=
  I_comb

/-- `k+1` identity implications composed by `syllogism`: nesting depth `k+1`, no `lem`. -/
def chn : Nat → @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] (SE →ᶠ SE)
  | 0 => idD
  | k + 1 => Derivable.syllogism (chn k) idD

/-- The chain applied: `⊢ ∃v (v =₀ x)` again, through `k+1` nested `syllogism`s. -/
def chained (k : Nat) : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] SE :=
  Derivable.mp exD (chn k)

/-- The premise set is empty, so its negatively translated realizer is vacuous. -/
def spnd : ∀ (Γ' : Ctx Empty) (B : Formula lFE Γ'), lPremE ⟨Γ', B⟩ → MRealizer lCmE (Bᴺᵀ) :=
  fun _ _ h => h.elim

/-- The fused negative-translation + MFI realizer of the chain. -/
def mr (k : Nat) : MRealizer lCmE (SEᴺᵀ) :=
  monotone_nd_soundness lEqxiE lSpremiseE lCmE spnd (chained k)

/-- `¬(∃v (v =₀ x))` — the challenge fed to the surviving `¬¬`. -/
abbrev SEn : Formula lFE [Ty.nat] := ¬ᶠ SE

/-- The `∃v` index majorant, read through the `¬¬` as `ClassicalMfi.cU`/`cV` do. -/
def wit (k : Nat) (xs : Ty.interpret lXE Ty.nat.hat) : ℕ :=
  (((mr k).val (bezemAbstractEmpty lSiE).N (xs, ())).2
      (Ty.interpret_default lSiE (wTy SEn).hat) ()).1.1

#print axioms mr
#print axioms wit

-- ============================================================================
-- The measurements (kernel; `set_option profiler` gives the per-declaration time)
-- ============================================================================

set_option profiler true

theorem w0 : (5 : ℕ) = wit 0 (5 : ℕ) := by kernel_rfl
theorem w2 : (5 : ℕ) = wit 2 (5 : ℕ) := by kernel_rfl
theorem w3 : (5 : ℕ) = wit 3 (5 : ℕ) := by kernel_rfl
theorem w4 : (5 : ℕ) = wit 4 (5 : ℕ) := by kernel_rfl
theorem w5 : (5 : ℕ) = wit 5 (5 : ℕ) := by kernel_rfl
-- k = 6 is `std::bad_alloc` at the 12 GB cap (Lean exits 134); kept out of the build:
--   theorem w6 : (5 : ℕ) = wit 6 (5 : ℕ) := by kernel_rfl


end SharingProbe
end Metatheorems
