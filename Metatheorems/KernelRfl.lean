/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean

/-!
# `kernel_rfl` — let the kernel decide an equation

The evaluator of record for extracted bounds. `Meta.isDefEq` (what bare `rfl` runs) has no
cache on terms with free variables and recomputes `Ty.interpret` at every step; the kernel
caches by structure and consumes no heartbeats. Measured in `Probes/MonotoneLaneB.lean`: the
same `U = 901` is a 200 000-heartbeat `whnf` timeout under `rfl` and ≈2 s under `kernel_rfl`,
and every `KERNEL` run in `Probes/SymbolicBound.lean` converges where every `Meta` run aborts.

It is sound because the kernel checks the assignment when the declaration is added — the
tactic does no checking of its own, which is the whole point. Its non-vacuity control is that
the kernel **rejects** a wrong numeral: `MonotoneLaneB.e1_U_900`, "(kernel) declaration type
mismatch", 1.8 s.

Moved here from `Probes/MonotoneLaneB.lean` on 2026-09-08 so that `Demo/` and the library can
use it without importing a probe.
-/

namespace Metatheorems

open Lean Elab Tactic in
/-- Assign `Eq.refl lhs` to a goal `lhs = rhs` with **no** `Meta`-level defeq check: the
kernel alone decides `lhs ≡ rhs` when the declaration is added. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := t.eq? | throwError "kernel_rfl: the goal is not an equation"
  let u ← Meta.getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

end Metatheorems
