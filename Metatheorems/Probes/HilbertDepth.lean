/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Hilbert

/-!
# `#hilbert … depth n` — how far into the proof-mode layer a listing can actually go

`Hilbert.lean`'s `shouldUnfold` was a **binary** predicate: `all` unfolded everything except
the whole `Metatheorems.ProofMode` namespace, because unfolding that namespace on a real
derivation never finished. `shouldUnfoldAt` replaces it with a fueled one, `depth n`, plus a
`keeping` stop set. This file is the driver *and* the measurement; building it regenerates
everything under `hilbert-out/`. Timings are wall-clock from `#hilbert`'s own report, on a
loaded 15 GB machine running three lanes, so treat them as order-of-magnitude.

## What `depth n` means, and the design error it cost to find

**The fuel is per proof step, not per path.** The first implementation counted `ProofMode`
unfoldings along the path from the root, which is the obvious reading and is useless here: a
proof-mode derivation is a *chain*, `pm_cut a b`'s derivation arguments being the earlier steps
of the same script, so the path from the root to a leaf runs through every step of the proof
and the fuel is spent entirely on the spine. Measured, `depth 1` and `depth 2` on `mct_body`
then differed from `depth 0` in **one line each** and in nothing else — 18 steps against 19,
with `pm_intro` becoming `seq_intro`. The fix is one line, in `subProofs`: restore the budget
when descending into a premise, so the fuel counts *consecutive* unfoldings of one step's head
constant. `depth n` then reads as "expand every proof-mode step `n` definition levels, cite
what it has become".

This is the same trap `Probes/ExprBound.lean` records one level down — *if output does not
change with fuel, suspect the traversal, not convergence* — in its other form: here the output
did change, by one line, which is if anything more misleading than not changing at all.

## The controls: it converges, and it reaches raw axioms

`HilbertScratch.contract_pm` below is a six-tactic proof-mode derivation of `(A → A → B) →
A → B` over **abstract** formulas — the cheapest possible proof-mode target, since no ℕ or ℚ
constant can enter the rendering.

| depth | steps | wall |
|---|---|---|
| 0 | 12 | 66 ms |
| 1 | 18 | 128 ms |
| 2 | 54 | 239 ms |
| 3 | 96 | 825 ms |
| 4 | 117 | 1.3 s |
| 6 | **120** | 1.1 s |
| 10 | **120** | 0.7 s |
| 10, `all` | 1844 | 15.3 s |

It **converges** — a fixed point at depth 6, reached again at 10, and the fixed point is a
genuine Hilbert derivation: 30 modus ponens, 24 `S`, 20 `pintro`'s `weaken_intro_h`, 4 `I`,
2 `K`, and no `ProofMode` name anywhere. With `all` on top, the combinators expand too and the
same proof is 1844 raw-axiom steps. So the tool does what the request asked for; whether it
*terminates in budget* is a property of the target, measured next.

## The real target: `mct_body`, and what actually blocks it

Bare `#hilbert ProofMode.mct_body depth 1` is a heartbeat timeout (`whnf`, sometimes `delab` —
whichever the budget runs out in first). No limit was raised; the timeout is the measurement.

The reason is not the proof-mode layer as such. `mct_body` cites `mct_descent`, a 112-step
`pinduction`, and unfolding a `def` *once* exposes its whole derivation — after which every one
of its steps gets its own fresh budget. So `depth 1` on a wrapper means "expand everything
reachable, one level", and the wrapper's size is no guide at all.

`keeping` is what makes that controllable, and it is why the option exists:

| invocation | steps | wall |
|---|---|---|
| `mct_body` (depth 0) | 19 | 60 ms |
| `mct_body keeping mct_descent depth 1` | 37 | 236 ms |
| `mct_body keeping mct_descent depth 2` | 169 | 6.3 s |
| `mct_body keeping mct_descent depth 3` | — | **timeout at `delab`** |
| `mct_body keeping seq_id mct_descent depth 2` | 120 | 4.9 s |
| `mct_body keeping seq_id mct_descent depth 3` | — | **timeout at `whnf`** |
| `mct_body keeping seq_id depth 1` | **1790** | 17.5 s |
| `mct_descent` (depth 0) | 112 | 1.3 s |
| `mct_descent depth 1` | — | **timeout at `whnf`** |
| `mct_descent keeping seq_id depth 1` | 1766 | 18.5 s |
| `mct_p2 keeping mct_body depth 1 / 2 / 3 / 5` | 3 / 2 / 8 / **8** | ≤ 53 ms |

**`seq_id` is the wall, and that is the sharp finding here.** Keeping that one constant — and
nothing else — turns `mct_descent depth 1` from a heartbeat timeout into 1766 steps in 18.5 s.
`seq_id` is hypothesis lookup: it recurses on the hypothesis context through `HVar.rec` with a
dependent cast at each level, and it is cited 35 times in `mct_descent`'s 112 steps. The
diagnostic profile of the stalling run is `Eq.rec ↦ 2802`, `Term.Renaming ↦ 1858`,
`List.rec ↦ 1157`, then `seq_id ↦ 442` = `HVar.rec ↦ 442` = `List.noConfusion ↦ 442` — one
`seq_id` unfolding per hypothesis position per occurrence, each dragging its casts. Every other
tactic expands without trouble.

That corrects `Hilbert.lean`'s old docstring, which blamed "every `pintro`/`prw`" collectively.
It is one combinator, it is the one that has to look at the context, and `Probes/
SeqMpBoundProbe.lean` names the same three primitives (`seq_of_thm`, `seq_mp`, `seq_id`) as
where the bound-extraction cost lives. `wit_seq_id` exists there precisely so `termMajorizer`
never has to reduce it; the display side has no such lemma and pays the reduction.

## The answer to "what is the useful depth"

- On an **abstract-formula** proof-mode derivation: unbounded. It converges to raw axioms in
  120 steps and under a second.
- On **`mct_body`/`mct_descent`** — a real derivation with ℕ arithmetic in every formula —
  the useful depth is **1 with `keeping seq_id`** (1790 steps, 17.5 s: the whole MCT proof one
  level below the tactics, which is what the request asked for), or **2 with `keeping
  mct_descent`** (169 steps, readable). **Depth 3 does not exist at any `keeping` tried.**
- The listing that is actually *readable* is still depth 0 or 1. 1790 steps is a proof of
  concept, not slide material; 37 is.

Two limits worth stating rather than working around:

- The wall at the top is the **delaborator**, not the traversal. Rendering one `pack Δ B`
  conclusion in full was enough to exhaust the budget on its own, before this file recognised
  that shape (see `conclusionOf`); with that fixed the cost is split between `delab` and
  `whnf` and either can run out first, which is why the two timeouts above are both reported.
- The fuel-keyed memo (`State.cache`) costs a little sharing: a node reached mid-chain and
  again at premise level renders twice. Measured on the 120-step fixed point, exactly **one**
  duplicated line out of 120. Not worth a fix; keying the memo on the fuel is what makes the
  option correct at all.
-/

namespace Metatheorems
namespace HilbertScratch

open ProofMode Formula

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}
variable {Γ : Ctx ι} {A B : Formula F Γ}

/-- A six-tactic proof-mode derivation over **abstract** formulas: contraction. Abstract on
purpose — it is the control that separates "the proof-mode layer is deep" from "the formulas
in this particular proof are large". -/
def contract_pm : Derivable F al Premises ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) := by
  pmode
  pintro h
  pintro ha
  papply h in ha with h1
  papply h1 in ha with h2
  pexact h2

end HilbertScratch

-- ============================================================================
-- The abstract control: the ladder converges, and the fixed point is raw.
-- ============================================================================

#hilbert HilbertScratch.contract_pm             to "hilbert-out/depth/contract_pm_d0"
#hilbert HilbertScratch.contract_pm depth 1     to "hilbert-out/depth/contract_pm_d1"
#hilbert HilbertScratch.contract_pm depth 2     to "hilbert-out/depth/contract_pm_d2"
#hilbert HilbertScratch.contract_pm depth 4     to "hilbert-out/depth/contract_pm_d4"
#hilbert HilbertScratch.contract_pm depth 10    to "hilbert-out/depth/contract_pm_d10"
#hilbert HilbertScratch.contract_pm all depth 10 to "hilbert-out/depth/contract_pm_all_d10"

-- ============================================================================
-- The wrapper: converges to eight raw steps, `mct_body` cited as one lemma.
-- ============================================================================

#hilbert ProofMode.mct_p2 keeping ProofMode.mct_body depth 5
  to "hilbert-out/depth/mct_p2_d5"

-- ============================================================================
-- The real derivation. Depth 2 is the readable one; depth 3 does not exist.
-- ============================================================================

#hilbert ProofMode.mct_body keeping ProofMode.mct_descent depth 1
  to "hilbert-out/depth/mct_body_d1"
#hilbert ProofMode.mct_body keeping ProofMode.mct_descent depth 2
  to "hilbert-out/depth/mct_body_d2"

-- Everything `mct_body` reaches, `mct_descent` included, one level below the tactics — the
-- literal answer to "unfold the ProofMode lemmas to full proofs". 1790 steps: a demonstration
-- that it terminates, not a listing anyone reads. Only `seq_id` is held back, and holding it
-- back is the whole difference between this and a heartbeat timeout.
#hilbert ProofMode.mct_body keeping ProofMode.seq_id depth 1
  to "hilbert-out/depth/mct_body_full_d1"

end Metatheorems
