/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Demo.Walkthrough

/-!
# `#bound` measured — what the two modes cost, and which one is safe on a real proof

`Metatheorems/BoundPrint.lean` adds

    #bound <ident> [depth n] [eval] [cap n] [to "path"]

with a **structural** default (walk the derivation `n` inference-rule levels, printing the
`MRealizer.*` combinator each rule maps to, citing everything deeper by name) and an
**evaluative** `eval` mode (the capped kernel reducer of `Probes/ExprBound.lean`). This file
runs both on `Demo.linearInduction` (368 constructors), `Demo.doubling` (145) and
`ProofMode.real_mct_p2` (655 lines, the derivation with real-analysis content).

## Structural mode — measured 2026-09-08, all on this machine

| target | depth 0 | 1 | 2 | 3 | 6 |
|---|---|---|---|---|---|
| `Demo.linearInduction` | 3 nodes, 4 ms | 7, 3 ms | 14, 4 ms | 20, 4 ms | 40, 8 ms |
| `Demo.doubling` | 3, 0 ms | 4, 0 ms | 6, 1 ms | 9, 1 ms | 19, 2 ms |
| `ProofMode.real_mct_p2` | 3, 1 ms | 6, 2 ms | 8, 1 ms | 11, 3 ms | — |

…and pushed on the large one, which is the claim worth measuring:

| `real_mct_p2` depth | 8 | 10 | 12 | 15 | 20 | 25 | 30 | 40 |
|---|---|---|---|---|---|---|---|---|
| nodes | 69 | 140 | 268 | 661 | 2241 | 5652 | 11978 | **20001 (cap)** |
| wall | 11 ms | 21 ms | 30 ms | 55 ms | 149 ms | 331 ms | 675 ms | 1208 ms |

**Structural mode is safe on any proof, and this is what "safe" means**: the node cap
(`Cfg.maxNodes = 20000`) is an absolute bound on the output, growth to it is smooth (≈×2 per
2–5 levels), nothing is ever evaluated, and the whole depth sweep above on the project's
largest derivation costs under 4 s in total. At depth 40 the cap fires, the listing says so,
and the command still returns in 1.2 s.

**Where it stops being READABLE is far below that**: depth 3 (11 nodes) is a slide; depth 8
(69 nodes) is a page; depth 12 (268) is a reference listing you scroll; beyond ≈15 it is data,
not a display. So the useful dial on `real_mct_p2` is 1–8, and the cap is a guard rail rather
than a working range.

`#bound Demo.stepOnceR depth 3` gives byte-identical output to `#bound Demo.stepOnce
depth 3` (20 nodes): the command peels `monotone_soundness` so the realizer and the derivation
are the same target.

## Evaluative mode — measured 2026-09-08, default cap 4000 visits

| target | point | wall | visits | capAbort | `numObjs` | result |
|---|---|---|---|---|---|---|
| `mfiV … linearR` | `5` | 2.42 s | 1 | false | 1 | `5` |
| `mfiV … linearR` | symbolic `n` | 2.75 s | 74 | false | 2988 | stuck `Nat.rec` iteration |
| `mfiU … linearR` | symbolic `n` | 2.86 s | 75 | false | 2989 | the same, `.2` side |
| `mfiV … stepOnceR` (2026-09-09) | symbolic `xs` | 0.83 s | 6 | false | 24 | `fun xs ↦ xs.2 xs.1` — the bound as a term |
| `mfiU … stepOnceR` (2026-09-09) | symbolic `xs` | 9.25 s | 106 | false | 44915 | converges, but a nested `Decidable.rec` decision tree: the counter side is case analysis, not a readable term |
| `mfiV … doublingR` | `xs 0` | 0.07 s | 1 | false | 1 | `1` |
| `mfiV … doublingR` | `xs 1` | 0.67 s | 1 | false | 1 | `2` |
| `mfiV … doublingR` | `xs 3` | 1.34 s | 1 | false | 1 | `8` |
| `mfiV … doublingR` | `(1, g)` symbolic | 2.17 s | 39 | false | 9840 | `max (g 0 ⊕ g 0) (g 0)` |

**These reproduce `Probes/SymbolicBound.lean`'s independently measured runs.** Its `tgtI`
(the same `pinduction` argument, over `MonotoneMCT.rI`) is 4.24 s / **74 visits** / 2,962
objects against 2.75 s / **74** / 2,988 here; its `tgtE` at `k = 1` (the same doubling
argument, over `ContentExampleNat.rE`) is 3.46 s / **39 visits** / 9,735 objects against
2.17 s / **39** / 9,840 here. Visit counts agree exactly; the object counts differ by <1 %
because the derivations are the Demo's own copies, and the times are the same machine on a
different day. The numerals (`5`, `1`, `2`, `8`) agree with `Probes/DemoChecks.lean`'s
`kernel_rfl` theorems, which is the check that the reducer is not lying.

The symbolic doubling display is the readable one, and it is the bound as arithmetic:

    fun g => Decidable.rec (fun h => Nat.rec (g 0) (fun k ih => maxT nat (Nat.succ ih) ih) (g 0))
                           (fun h => g 0) (…decLe…)

i.e. `max (g 0 + g 0) (g 0)` — `V(1, f*) = 2·f*(0)`, the `k = 1` case of `2^k · f*(0)`.

## The evaluative mode on `real_mct_p2` — NEGATIVE, and the cap does not save it

`mfiV PureWEHA.cm rmR ((fun _ n => n), ((fun n => n+1), 2))` with `rmR = monotone_soundness …
real_mct_p2` (which *elaborates* instantly): `std::bad_alloc` at the 12 GB ulimit after ≈70 s.

**`cap 1` dies the same way**, which locates it exactly: the cap counts *visits*, and the
very first `Lean.Kernel.whnf` call — on the root — is already the whole reduction. A kernel
`whnf` consumes no heartbeats and cannot be interrupted, so **no cap in this design bounds the
work of one call**; only the ulimit does. That is the same wall the MFI lanes record for
`real_mct_p2` (ARCHITECTURE §14.7), reached here through a different instrument, and it is why
the structural mode exists.

Reproduction (NOT in the file — a file of errors is not a green build; run under
`scripts/lean.sh`, which carries the 12 GB cap):

```lean
def rmD : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (Γ := [])
    RealMCT.rmStatement := ProofMode.real_mct_p2
def rmR := monotone_soundness PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm rmD
def rmV : ℕ := mfiV PureWEHA.cm rmR
  (((fun _ n => n) : ℕ → ℕ → ℕ), (((fun n => n + 1) : ℕ → ℕ), (2 : ℕ)))
#bound rmV eval          -- std::bad_alloc at 12 GB, ≈70 s; `cap 1` identical
```

## Two mechanical facts about the command, each of which cost time

- **`depth` counts inference rules, not `Expr` unfoldings.** The first version charged one
  level per definitional unfolding, and then `depth 3` on `real_mct_p2` showed
  `pm_enter → pm_allI → seq_allI` and no rule at all — the budget was spent getting through
  the proof-mode layer. Unfolding to reach a rule is now free (bounded per node by
  `unfoldFuel = 60`), and `depth 0` prints the root rule of a proof-mode derivation.
- **The modifier words are reserved tokens** for every importer, as `#hilbert`'s are. Inside
  `BoundPrint.lean` itself that bites immediately: `{ depth := d }` no longer parses after the
  `syntax` command, which is why `structuralAt` exists.
-/

namespace Metatheorems
namespace BoundPrintDemo

-- ============================================================================
-- Structural mode — safe on every one of these, nothing is evaluated
-- ============================================================================

-- `Demo.linearInduction`, the target the header's linear rows were measured on, was replaced
-- in the demo on 2026-09-09 by `Demo.stepOnce` (same premise as `doubling`, no induction);
-- those rows stand as measurements of a derivation that now exists nowhere.
#bound Demo.stepOnce
#bound Demo.stepOnce depth 1
#bound Demo.stepOnce depth 2
#bound Demo.stepOnce depth 3

#bound Demo.doubling
#bound Demo.doubling depth 1
#bound Demo.doubling depth 2
#bound Demo.doubling depth 3

-- The realizer names the same target as its derivation.
#bound Demo.stepOnceR depth 3

-- `unfold` (added 2026-09-09): each combinator opened to the majorant it builds; nothing
-- evaluated. `induction` shows the recursor `R[…]` under `termMajorizer`.
#bound Demo.stepOnce depth 1 unfold
#bound Demo.doubling depth 2 unfold
#bound ProofMode.real_mct_p2 depth 2 unfold

-- The large derivation, to the point where the listing stops being a display.
#bound ProofMode.real_mct_p2
#bound ProofMode.real_mct_p2 depth 1
#bound ProofMode.real_mct_p2 depth 2
#bound ProofMode.real_mct_p2 depth 3
#bound ProofMode.real_mct_p2 depth 8
#bound ProofMode.real_mct_p2 depth 12

-- ============================================================================
-- Evaluative mode — the capped kernel reducer, on the Demo realizers
-- ============================================================================

/-- `V` of the one-step derivation at the majorant `x* = (5, λn.n+1)`. -/
def linV5 : ℕ := mfiV PureWEHA.cm Demo.stepOnceR (Demo.xs 5)
/-- The same, left symbolic in the point: the bound as a function, `xs.2 xs.1`. -/
def linVsym := mfiV PureWEHA.cm Demo.stepOnceR
/-- Its counter side, `xs.1`. -/
def linUsym := mfiU PureWEHA.cm Demo.stepOnceR

/-- `V` of the doubling derivation at `x* = (k*, λn.n+1)`. -/
def dblV (k : ℕ) : ℕ := mfiV PureWEHA.cm Demo.doublingR (Demo.xs k)
/-- The same at `k* = 1`, symbolic in the function majorant: `2 · g 0`. -/
def dblVsym1 (g : ℕ → ℕ) : ℕ := mfiV PureWEHA.cm Demo.doublingR ((1 : ℕ), g)

def dblV0 : ℕ := dblV 0
def dblV1 : ℕ := dblV 1
def dblV3 : ℕ := dblV 3

#bound linV5 eval
#bound linVsym eval
#bound linUsym eval
#bound dblV0 eval
#bound dblV1 eval
#bound dblV3 eval
#bound dblVsym1 eval

end BoundPrintDemo
end Metatheorems
