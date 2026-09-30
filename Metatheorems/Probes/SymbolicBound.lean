/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.ExprBound
import Metatheorems.Probes.ContentExampleNat

/-!
# `Φ` as an EXPRESSION — the symbolic route, on the two induction targets

Every number this project reports is `Φ` **applied at a point**, and several of them are
Cantor pairing codes rather than magnitudes. But a metatheorem produces a *function*. This
file displays two of them as functions.

## The two targets, and which proof each bound comes from

| target | input proof | route | bound at points |
|---|---|---|---|
| `tgtI` | `MonotoneMCT.indFinal` — `∀x(∀u(u=u) → ∃v(v=x))` by **proof-mode `pinduction`**, witness `x` itself, 368 constructors | MFI (`rI = monotone_soundness … indFinal`) | `V(5)=5`, `V(9)=9` |
| `tgtE` | `ContentExampleNat.eFinal` — `∀x(∀u (f(Su) =₀ f u +ᵗ f u) → ∃v (f k =₀ v))` by **raw `Derivable.induction`**, witness at `k+1` built from the previous witness, 145 constructors | MFI (`rE = monotone_soundness … eFinal`) | `V = 2^k·f*(0)`: 1, 8, 32, 128 |

Same induction rule; the bounds differ because the witness is a *projection* in the first and
a *function of the previous witness* in the second. That is the whole content of "bounds are
properties of proofs, not theorems", and it is visible in the displays below.

## RESULT — the kernel is the reducer, not `Meta`

`ExprBound.knf`/`runK` (`Lean.Kernel.whnf` plus the blocklist) converges on both targets;
`ExprBound.pr`/`pr2` (the `Meta`-level reducers) do not. **Every `KERNEL` run below reports
`capAbort=false`; every `Meta` run reports `capAbort=true` or `hbAbort=true`.** The kernel
consumes no heartbeats and has a structural cache `Meta.whnf` lacks — the same asymmetry
`MonotoneLaneB` records for `kernel_rfl` being the evaluator of record.

Only `V_closed_0` (`mfiV cmE rE (0, g) = g 0` for every `g`) is proved; the general form
`V(k, f*) = 2^k · f*(0)` is a conjecture read off the displays. The timing table (unrolling is
superlinear in `k`) and the retraction note are in the notes.
-/

set_option linter.unusedTactic false
set_option Elab.async false

namespace Metatheorems
namespace SymbolicBound

open ExprBound (run run2 run2p run2e blocked pr pr2 prCap)
open MonotoneMCT (cmE)
open Lean Lean.Meta Lean.Elab

-- Target 1 — the proof-mode `pinduction`, symbolic in the point

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

-- Target 2 — the raw `Derivable.induction` whose bound is exponential

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

-- Gate 3 — the closed form as a THEOREM, universally quantified in the majorant

/-- **`V(0, f*) = f*(0)`, for EVERY `f*`** — not a numeral at a point but a closed form in the
input majorant. This is the base of the recursion the display above shows as `(g 0, ⋆)`. -/
theorem V_closed_0 (g : ℕ → ℕ) : tgtE 0 g = g 0 := by kernel_rfl

/-- The majorant of the object-level `+ᵗ`, as the kernel display exhibits it: `Term.add` is a
`Term.prec`, so its majorant iterates `max (·+1) ·` — `dblMaj v m` is `v` incremented `m`
times with a running maximum. This is the shape `mfiV … (1, g)` normalises to, with both
arguments `g 0`; the doubling of the *proof* is exactly this iteration. -/
def dblMaj (v : ℕ) : ℕ → ℕ
  | 0 => v
  | m + 1 => max (dblMaj v m + 1) (dblMaj v m)

/-- …and the arithmetic half, by ordinary induction: the iteration IS addition. -/
theorem dblMaj_eq (v : ℕ) : ∀ m, dblMaj v m = v + m
  | 0 => rfl
  | m + 1 => by rw [dblMaj, dblMaj_eq v m]; omega

-- **NOT PROVED, 2026-09-08 — the k = 1 closed form is OPEN.** Both of the following were
-- written and REJECTED BY THE KERNEL (`(kernel) declaration type mismatch`), so they are
-- recorded here as the candidates that fail rather than kept as theorems:
--
--     theorem V_shape_1 (g) : tgtE 1 g = dblMaj (g 0) (g 0) := by kernel_rfl
--     theorem V_closed_1 (g) : tgtE 1 g = 2 * g 0 := by rw [V_shape_1, dblMaj_eq]; omega
--
-- `dblMaj` and `dblMaj_eq` are kept because the kernel *display* of `tgtE1` (see the `runK`
-- output above) is that iteration; what has not been pinned down is the exact spelling — the
-- `max`/`maxT` instance and the placement of `recMaj`'s running maximum. Use `#kdefeq` below
-- to settle a candidate BEFORE spending a build on it; a `#kdefeq` reading of `true` on a
-- multi-line probe must be attributed to the right line (the reported line is the FIRST line
-- of the command), which is where this attempt went wrong.

open Lean Elab Command Term in
/-- `#kdefeq a ≟ b` — ask the **kernel** whether two closed terms are definitionally equal,
and report yes/no instead of failing. `Kernel.isDefEqGuarded` returns `false` on any kernel
exception, so a candidate closed form can be probed without a failed build; `kernel_rfl` is
then used to turn a confirmed candidate into a theorem. -/
elab "#kdefeq " a:term " ≟ " b:term : command => do
  liftTermElabM do
    let ea ← elabTerm a none
    let eb ← elabTerm b none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ea ← instantiateMVars ea
    let eb ← instantiateMVars eb
    let t0 ← IO.monoMsNow
    let r := Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) ea eb
    logInfo m!"kernel defeq = {r}  ({(← IO.monoMsNow) - t0}ms)"

-- Controls for the instrument itself: a true and a false arithmetic pair, and the
-- k = 0 case that `V_closed_0` proves.
#kdefeq ((2 : ℕ) + 2) ≟ (4 : ℕ)
#kdefeq ((2 : ℕ) + 2) ≟ (5 : ℕ)
#kdefeq (fun g : ℕ → ℕ => tgtE 0 g) ≟ (fun g : ℕ → ℕ => g 0)

open Lean Elab Command Term in
/-- `#kwhnfg f` — apply `f : (ℕ → ℕ) → ℕ` to a **free variable** `g` and print the KERNEL's
weak head normal form. The kernel is the evaluator of record here (`MonotoneLaneB`); this is
its read-out, and it is what identifies the shape a closed-form candidate must match. -/
elab "#kwhnfg " a:term : command => do
  liftTermElabM do
    let f ← elabTerm a none
    Term.synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    let nn := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)
    Meta.withLocalDeclD `g nn fun gv => do
      let e := mkApp f gv
      let t0 ← IO.monoMsNow
      match Lean.Kernel.whnf (← getEnv) (← getLCtx) e with
      | .ok r => logInfo m!"kernel whnf ({(← IO.monoMsNow) - t0}ms): {r}"
      | .error _ => logInfo m!"kernel whnf: EXCEPTION ({(← IO.monoMsNow) - t0}ms)"

#kwhnfg (fun g : ℕ → ℕ => tgtE 0 g)
#kwhnfg (fun g : ℕ → ℕ => tgtE 1 g)
#kwhnfg (fun g : ℕ → ℕ => tgtE 2 g)

-- **The kernel-driven reducer.** `recMaj` unblocked, so the recursion unrolls at a literal
-- `k`; arithmetic (`+`, `max`, `Nat.rec`) blocked, so the result is arithmetic in `g`.
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtE0 2000 3000 []
  [``Metatheorems.recMaj]
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtE1 2000 3000 []
  [``Metatheorems.recMaj]
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtE2 2000 3000 []
  [``Metatheorems.recMaj]
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtE3 2000 3000 []
  [``Metatheorems.recMaj]

-- …and with `recMaj` BLOCKED, at a symbolic `k`: the bound as a recursion.
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtE 2500 3000
#eval show MetaM Unit from ExprBound.runK ``Metatheorems.SymbolicBound.tgtI 2500 3000

#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟ (fun g : ℕ → ℕ => g 0 + g 0)
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟ (fun g : ℕ → ℕ => max (g 0 + g 0) (g 0))
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟ (fun g : ℕ → ℕ => g 0)
-- Candidates matching the kernel display of `tgtE1`.
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟ (fun g : ℕ → ℕ => max (dblMaj (g 0) (g 0)) (g 0))
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟ (fun g : ℕ → ℕ => dblMaj (g 0) (g 0))
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟
  (fun g : ℕ → ℕ => max (Nat.rec (motive := fun _ => ℕ) (g 0)
    (fun _ ih => max (ih + 1) ih) (g 0)) (g 0))
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟
  (fun g : ℕ → ℕ => Nat.rec (motive := fun _ => ℕ) (g 0)
    (fun _ ih => max (ih + 1) ih) (g 0))
-- The same shape one and two steps further up: is the recursion literally iterated?
#kdefeq (fun g : ℕ → ℕ => tgtE 2 g) ≟
  (fun g : ℕ → ℕ => dblMaj (dblMaj (g 0) (g 0)) (dblMaj (g 0) (g 0)))
#kdefeq (fun g : ℕ → ℕ => tgtE 3 g) ≟
  (fun g : ℕ → ℕ => dblMaj (dblMaj (dblMaj (g 0) (g 0)) (dblMaj (g 0) (g 0)))
    (dblMaj (dblMaj (g 0) (g 0)) (dblMaj (g 0) (g 0))))
#kdefeq (fun g : ℕ → ℕ => tgtE 1 g) ≟
  (fun g : ℕ → ℕ => maxT (X := TinyBoundDemo.tXE) Ty.nat
    (Nat.rec (motive := fun _ => ℕ) (g 0) (fun _ ih => maxT (X := TinyBoundDemo.tXE) Ty.nat
      (Nat.succ ih) ih) (g 0)) (g 0))


end SymbolicBound
end Metatheorems
