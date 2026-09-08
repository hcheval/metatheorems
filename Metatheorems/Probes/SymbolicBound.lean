/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.ExprBound
import Metatheorems.Probes.ContentExampleNat

/-!
# `Φ` as an EXPRESSION — the symbolic route, on the two induction targets

`Probes/ExprBound.lean` recovered the *shape* of a bound on a 13-constructor derivation at a
space. This file runs the same instrument, in its fuel-free form (`ExprBound.pr2`), on the two
derivations whose bounds are *recursions*: `MonotoneMCT.rI` (a proof-mode `pinduction`, bound
`V(n) = n`) and `ContentExampleNat.rE` (a raw `Derivable.induction` with a doubling witness,
bound `V(k, f*) = 2^k · f*(0)`).

Findings and figures are in the per-section comments; the headline is at the top of each.
-/

set_option linter.unusedTactic false
set_option Elab.async false

namespace Metatheorems
namespace SymbolicBound

open ExprBound (run run2 run2p run2e blocked pr pr2 prCap)
open MonotoneMCT (cmE)
open Lean Lean.Meta Lean.Elab

-- ============================================================================
-- Target 1 — the proof-mode `pinduction`, symbolic in the point
-- ============================================================================

/-- `MonotoneMCT.rI`'s witness bound, left symbolic in the point `n`. Kernel-checked at
`n = 5, 9` in `MonotoneMCT` (`ind_V_5`, `ind_V_9`), giving `5` and `9`. -/
def tgtI (n : ℕ) : ℕ := mfiV cmE MonotoneMCT.rI n

/-- The counter side of the same, also symbolic. `mfiU cmE rI 5 = 0` (`ind_U_5`). -/
def tgtIU (n : ℕ) : ℕ := mfiU cmE MonotoneMCT.rI n

-- Cap sweep: if the rendered result stops changing as the cap rises, the fuel-free reduction
-- has converged; if it keeps growing, it has not.
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtI 1200 500
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtI 1200 2000
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtI 1200 8000

-- ============================================================================
-- Target 2 — the raw `Derivable.induction` whose bound is exponential
-- ============================================================================

/-- **The Gate-2 target.** `ContentExampleNat.rE`'s witness bound, symbolic in BOTH components
of the point: `k` the induction variable and `g` the majorant of the function parameter.
Kernel-checked at `(3, λn.n+1) ↦ 8`, `(5, λn.n+1) ↦ 32`, `(2, λn.n+3) ↦ 12`. -/
def tgtE (k : ℕ) (g : ℕ → ℕ) : ℕ := mfiV cmE ContentExampleNat.rE (k, g)

/-- The counter side: `U(k) = k − 1` at the checked points. -/
def tgtEU (k : ℕ) (g : ℕ → ℕ) : ℕ := mfiU cmE ContentExampleNat.rE (k, g)

#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtE 1500 500

/-- The same bound with the induction variable a **literal** and the function majorant `g`
still symbolic: the recursion unrolls, and what is left should be arithmetic in `g`. -/
def tgtE0 (g : ℕ → ℕ) : ℕ := tgtE 0 g
def tgtE1 (g : ℕ → ℕ) : ℕ := tgtE 1 g
def tgtE2 (g : ℕ → ℕ) : ℕ := tgtE 2 g
def tgtE3 (g : ℕ → ℕ) : ℕ := tgtE 3 g

-- Widened vocabulary: keep `termMajorizer` symbolic. The unwidened runs above show the
-- reduction reaching `recMaj …` at the head and then exploding *inside its base and step
-- arguments*, which are `termMajorizer` applied to the realizer terms of the derivation.
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtE0 2500 prCap
  [``Metatheorems.termMajorizer]
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtE1 2500 prCap
  [``Metatheorems.termMajorizer]
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtE3 2500 prCap
  [``Metatheorems.termMajorizer]
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtE 2500 prCap
  [``Metatheorems.termMajorizer]
#eval show MetaM Unit from run2p ``Metatheorems.SymbolicBound.tgtI 2500 prCap
  [``Metatheorems.termMajorizer]

-- ============================================================================
-- Gate 3 — the closed form as a THEOREM, universally quantified in the majorant
-- ============================================================================

/-- **`V(0, f*) = f*(0)`, for EVERY `f*`** — not a numeral at a point but a closed form in the
input majorant. This is the base of the recursion the display above shows as `(g 0, ⋆)`. -/
theorem V_closed_0 (g : ℕ → ℕ) : tgtE 0 g = g 0 := by kernel_rfl


end SymbolicBound
end Metatheorems
