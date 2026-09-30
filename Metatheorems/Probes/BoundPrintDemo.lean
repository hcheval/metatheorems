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

The measurements — node counts and wall times of the structural mode, the visit counts and
results of the evaluative mode, and the negative result on `real_mct_p2` — are in the notes.
-/

namespace Metatheorems
namespace BoundPrintDemo

-- Structural mode — safe on every one of these, nothing is evaluated

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

-- Evaluative mode — the capped kernel reducer, on the Demo realizers

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
