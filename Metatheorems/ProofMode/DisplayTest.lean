/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Display

namespace Metatheorems
namespace ProofMode

/-!
# Rendering tests

`#guard_msgs` pins the rendered goal, so a regression in the delaborator is a build error
rather than something noticed later by eye.

Note also what these tests do *not* need: no coercion anywhere. `SeqD` is reducible, so the
packaging kit applies straight through it — the display layer costs the proof layer nothing.
-/

variable {ι : Type} {F : ι → Ty ι}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B : Formula F Γ}

open Formula

-- The names line up with `Δ` positionally, and the box shows them oldest-first: `Δ` is
-- `[B, A]` with `B` most recent, so `h : B` prints last.
/--
trace: ι : Type
F : ι → Ty ι
a : Allowed
Premises : PremiseSet F
Γ : Ctx ι
A B : Formula F Γ
⊢ ⟪Γ⟫
      k : A
      h : B
      ────────────────────
      A ∧ᶠ B
-/
#guard_msgs in
example : SeqD ["h", "k"] F a Premises [B, A] (A ∧ᶠ B) := by
  trace_state
  exact seq_andI (seq_id (.hs .hz)) (seq_id .hz)

-- No hypotheses: just the bar and the goal.
/--
trace: ι : Type
F : ι → Ty ι
a : Allowed
Premises : PremiseSet F
Γ : Ctx ι
A B : Formula F Γ
⊢ ⟪Γ⟫
      ────────────────────
      A →ᶠ A
-/
#guard_msgs in
example : SeqD [] F a Premises [] (A →ᶠ A) := by
  trace_state
  exact I_comb

-- Fewer names than hypotheses — the state a tactic leaves behind before it has labelled
-- everything. The unnamed positions print as `_` instead of the renderer giving up.
/--
trace: ι : Type
F : ι → Ty ι
a : Allowed
Premises : PremiseSet F
Γ : Ctx ι
A B : Formula F Γ
⊢ ⟪Γ⟫
      _ : A
      h : B
      ────────────────────
      A ∧ᶠ B
-/
#guard_msgs in
example : SeqD ["h"] F a Premises [B, A] (A ∧ᶠ B) := by
  trace_state
  exact seq_andI (seq_id (.hs .hz)) (seq_id .hz)

end ProofMode
end Metatheorems
