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

## RESULT (2026-09-06): the `let`-sharing experiment changes NOTHING. Hypothesis refuted.

`Dialectica/Monotone.lean` on this branch binds each repeated sub-majorant once with `let`
(`MRealizer.syllogism`: `hAB.val n e` was used 3× and `hBC.val n e` 2×;
`MRealizer.exportation`: `h.val n e` 3×; `MRealizer.forallRule`: the closure and the two
type equations). The change is definitionally transparent — **no proof needed editing**, the
full build is green (8110 jobs) and every axiom list is unchanged.

Kernel type-checking time of `theorem wk : (5 : ℕ) = wit k 5 := by kernel_rfl`
(`set_option profiler true`, 12 GB cap, machine shared with three other Lean builds; the
before/after runs are interleaved on the same machine, `Monotone.lean` reverted in between so
that the only difference is the `let`s):

| k (syllogisms in the chain) | 0 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| kernel, **before** | <0.1 s | 0.16 s | 0.71 s | 2.9 s | 9.4 s | `std::bad_alloc` @ 12 GB |
| kernel, **after**  | <0.1 s | 0.17 s | 0.65 s | 2.8 s | 11.7 s | `std::bad_alloc` @ 12 GB |
| evaluator (`#eval`), **before** | 14.1 s¹ | 0.22 s | — | — | — | — |
| evaluator (`#eval`), **after**  | 13.5 s¹ | 0.22 s | — | — | — | — |

¹ the first `#eval` in the module pays the interpreter/JIT warm-up; `wit 1` and `wit 2` are
0.22 s each on both sides. `#eval wit 4 5` produced **no result in 50 minutes** (CPU-bound at
100 %, RSS flat at 7 GB) before and after — so the evaluator's own wall is at k ≈ 3, exactly
where `ClassicalMfiProbe`'s header put it.

The growth is ≈ ×3.7 per level on both sides, and the OOM is at the same k. **So the ×5 per
level is not closure reconstruction, and `let` at the definition site cannot remove it.**
Two reasons, and they are independent:

1. **Lean's kernel zeta-reduces `let` by substitution.** `whnf` of `let x := v; b` is
   `b[v/x]`, so after one step the three occurrences are back. `let` buys sharing in the
   *compiled* code, never in the kernel — and the kernel is where every `kernel_rfl` bound
   is decided.
2. **The evaluator already shared these values by pointer.** `hAB.val n e` is one closure
   call per level whose *result* call-by-value shares; what does not share is the
   **application** `a.1 xA` — evaluated at a different `xA` in the witness component and in
   the counter component, and again inside the counter's own body. That is the inherent ×2
   the brief asked about, and it is per Dialectica *pair projection*, not per closure.

A fix therefore has to change what is *applied*, not where it is bound: memoise on the
argument (staged evaluation keyed by `(n, e, xA)`), or emit a majorant representation in
which the counter component does not call the witness component at all.
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

#eval wit 0 (5 : ℕ)
#eval wit 1 (5 : ℕ)
#eval wit 2 (5 : ℕ)
-- `#eval wit 4 5` produced no result in 50 minutes (CPU-bound at 100 %, RSS flat at 7 GB).


end SharingProbe
end Metatheorems
