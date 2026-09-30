/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean

/-!
# `kernel_rfl` — let the kernel decide an equation

The evaluator of record for extracted bounds: the tactic `kernel_rfl` assigns `Eq.refl` to a
goal `lhs = rhs` and leaves the decision `lhs ≡ rhs` to the kernel, with no `Meta`-level
defeq check.
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
