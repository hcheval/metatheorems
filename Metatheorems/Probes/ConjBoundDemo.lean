/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic
import Metatheorems.Probes.TriangleBoundDemo

/-!
# A premise consumed **twice, at two different terms** — and the wall that stops it

`Probes/TriangleBoundDemo.lean` mines `U = V = Φ = 901` from a derivation that instantiates a
space-axiom premise **once**. The obvious next rung is a derivation that consumes the premise
**twice, at two different terms**, so that the extracted `U` has to *combine* two different
majorants rather than report one. This file builds that derivation and runs it through
`syntactic_general_metatheorem_at_gen`.

**The headline is negative, and it is sharp.** The two-instantiation `U` does **not** reduce to
a numeral: it is a `(deterministic) timeout at whnf`. Four controls localise the cause exactly,
and each rules out a hypothesis that would have been the natural guess:

| variant | premise matrix | instantiations | `U` reduces? |
|---|---|---|---|
| `cFinalOnce` | `triB ∧ triB0` (two triangle inequalities) | `s₁` | **yes**, `1709` |
| `cFinalTwice` | `triB ∧ triB0` | `s₁`, `s₂` | no — whnf timeout |
| `tFinalTwice` | `u =₀ u` (tautology) | `s₁`, `s₂` | no |
| `sFinalTwice` | `u =₀ u` | `0`, `S 0` | no |
| `acFinal` | `u =₀ u` | `s₁` only, **plus one bare `and_contract`** | no |

So the obstruction is **not** the size of the matrix (a tautology stalls too), **not** the
magnitude of the numbers (`0` and `S 0` stall too), and **not** `pair_h`'s duplicating
plumbing (`acFinal` uses none of it). It is **one `Derivable.and_contract` at the premise
formula**, whose Dialectica realizer `sAndContract` is the only rule in the system whose
*counter* component must merge two challenges into one, via
`Term.natCase (matrixTerm …) (.snd y) (.fst y)`.

And the localisation is one-sided: `cVtTwice_at_5_9` below evaluates the **witness** functional
`V` of the very same two-instantiation derivation to the literal `1709`. Witness side fine,
counter side stuck — exactly the split `SeqMpBoundProbe`/`CounterSideProbe` predicted, now
observed on a whole extraction rather than on a lemma.

## What the diagnostics say — and one correction to CLAUDE.md

`set_option diagnostics true` on the stalling `acUt_at_5_9` (run live, recorded here, option
removed) reports:

    [reduction] unfolded declarations (max: 60474, num: 16):
      Eq.rec ↦ 60474      Term.rec ↦ 10847      Term.rename ↦ 10504
      syntactic_soundness ↦ 7389                Derivable.rec ↦ 7389
      SRealizer.imp ↦ 7353                      Term.weaken ↦ 3260
      sAndWeak ↦ 2430     tInst1 ↦ 2188         sAndContract ↦ 2187
      sForallAx ↦ 2187    List.rec ↦ 1006       Term.Renaming.ext ↦ 720
      sSyllogism ↦ 513
    [reduction] unfolded reducible declarations: Eq.ndrec ↦ 60474, Term.casesOn ↦ 10847,
      Subtype.val ↦ 7389, Derivable.casesOn ↦ 7389, Ty.casesOn ↦ 2908, …

CLAUDE.md (Track A item 1) records the Stage-B stall as *"a `whnf` heartbeat timeout from
unfolding `Term.monus`/`Term.pd` under an unrestricted `termMajorizer`"*. **Neither
`Term.monus` nor `Term.pd` appears anywhere in this profile, and neither does `matrixTerm`.**
What dominates is `Eq.rec`/`Eq.ndrec` — 60,474 unfoldings, five times the next entry — with
`Term.rename`/`Term.weaken` behind it. So on this instance the cost is **dependent-cast and
renaming traffic inside `sAndContract`'s own plumbing**, and whnf never even reaches the
arithmetic constants the earlier note blames. The counts also grow steadily rather than
diverging, which suggests the stall is quantitative (a constant factor over the budget), not a
genuine non-termination — but the fix is restructuring, never a raised limit.

## The statement

At `ρ := pTy := X ×ₜ X`, reusing `TriangleBoundDemo`'s `pTy`, `xL`, `zL`, `yL`, `dxz`, `dsum`,
`triB` and `triCm` verbatim:

    ∀p^(X ×ₜ X) (  ∀u (B₁(u) ∧ B₂(u))  →  ∃v (B₁(v) ∧ B₂(v))  )

* `B₁` = `triB`, the QF body of `d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)` — depends on **both**
  components of `p`;
* `B₂` = `triB0`, the QF body of `d(x,0_X) ≤ℝ d(x,0_X) +ℝ d(0_X,0_X)` — depends on the
  **first** component only.

`triAll_eq` / `triB0_all_eq` are the honesty checks: `Formula.all Ty.nat Bᵢ` *is* the
corresponding `le_R_pu`, so each conjunct is a genuine space axiom that `Derivable.dist_tri`
proves verbatim. `isPurelyUniversal` and `isPurelyExistential` are both closed under `∧`, so
`cB := B₁ ∧ᶠ B₂` passes all four of `_at_gen`'s side conditions (checked by `rfl` below).

Conclusion matrix `C := B`, as in `TriangleBoundDemo`; one existential variable, shared by both
conjuncts. **Nested existentials `∃v ∃w (C₁(v) ∧ C₂(w))` were considered and rejected** — see
"Design choices" at the foot of the file; the reason is a substitution *composition*
(`substF ∘ substF ∘ renameF` over terms containing `cauchyfy`/`le_Q_dec`) which is the
documented delta-expansion trap, and it would have obscured the finding rather than produced
one.

## The derivation — the whole point

    ∀u cB  →ᶠ  cB[s₁]                       forall_ax s₁
    ∀u cB  →ᶠ  cB[s₂]                       forall_ax s₂        (a DIFFERENT term)
    -------------------------------------------------- pair_h  (⇒ and_contract at `∀u cB`)
    ∀u cB  →ᶠ  cB[s₁] ∧ cB[s₂]
    ∀u cB  →ᶠ  cB[s₁]                       and_weak            (the s₂ half is a detour)
    ∀u cB  →ᶠ  ∃v cB                        exist_ax s₁

with

    s₁ := (d ⬝ x ⬝ z)   ⬝ 0        majorant  (n₁ + n₂)∘  at index 0
    s₂ := (d ⬝ x ⬝ 0_X) ⬝ 0        majorant  (n₁ + 5)∘   at index 0

The `s₂` branch is *logically redundant* — it is derived and then dropped by `and_weak`. That
is deliberate and is the interesting case for proof mining: a **redundant use of the premise at
a second index still has to inflate `U`**, because the realizer's counter component cannot know
the branch was discarded. Whether it does inflate it is precisely what this file could not
measure.

## What IS established here

1. **The two numbers `U` would have to combine, and that they cross over.** `witM1_at_5_9`,
   `witM2_at_5_9`, `witM1_at_5_1`, `witM2_at_5_1`: `s₁` majorizes to `1709` at `x* = (5,9)` and
   to `349` at `(5,1)`, while `s₂` majorizes to `901` at both. So at `(5,9)` the first
   instantiation dominates and at `(5,1)` the second does — a `max` of the two is a genuinely
   different function from either. (These are majorants of the *instantiation terms*, computed
   by the same `closedMajorizer` under the same `ConstMajorants`; they are **not** `U`.)
2. **The one-instantiation `U` for this premise formula**: `1709` at `(5,9)`, `349` at `(5,1)` —
   it tracks `s₁` alone, as it must.
3. **The two-instantiation `V`**: `1709`. The witness side of the very derivation whose `U`
   stalls goes through unchanged.
4. **The extraction itself never fails.** `cUtTwice`, `tUtTwice`, `sUtTwice`, `acUt` all
   elaborate and type-check as closed `Term`s; `cBoundTwice` elaborates as a `Subtype`. Only the
   *evaluation* of the counter-side majorant stalls.

## What is NOT established

**That `U` is a `max`.** It may be; it may also be something coarser. Nothing here shows
either way, and the file deliberately does not guess. Closing this is CLAUDE.md Track A item 1's
"concrete-numeral half (Stage B)", now with a sharper profile of what has to be restructured:
`Eq.rec`/`Term.rename` traffic through `sAndContract`, not arithmetic.
-/

namespace Metatheorems
namespace ConjBoundDemo

open Formula
open TriangleBoundDemo (pTy xL zL yL dxz dsum triB triCm)

-- ============================================================================
-- The second conjunct: a second, degenerate triangle inequality
-- ============================================================================

/-- `d(x,0_X)`. -/
def dx0 : Term WHyperbolic.F [pTy] (realTy MetricSpace.ι) :=
  Term.app2 (Term.dist ()) xL yL

/-- `d(x,0_X) +ℝ d(0_X,0_X)`. -/
def dsum0 : Term WHyperbolic.F [pTy] (realTy MetricSpace.ι) :=
  Term.app2 Term.add_R (Term.app2 (Term.dist ()) xL yL) (Term.app2 (Term.dist ()) yL yL)

/-- **The second matrix**: the quantifier-free body of `le_R_pu dx0 dsum0`, i.e. of
`d(x,0_X) ≤ℝ d(x,0_X) +ℝ d(0_X,0_X)` — the triangle inequality at `(x, 0_X, 0_X)`. Same shape
as `TriangleBoundDemo.triB`; it mentions the **first** component of `p` only. -/
def triB0 : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.imp
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy dx0.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy dsum0.weaken) (Term.app .succ (.var .vz)))))
      Term.zero)
    ⊥ᶠ

/-- Honesty check, exactly `TriangleBoundDemo.triAll_eq`'s: `∀n triB0` **is** the triangle
inequality at `(x, 0_X, 0_X)`, on the nose, so `Derivable.dist_tri () xL yL yL` proves it. -/
theorem triB0_all_eq : Formula.all Ty.nat triB0 = le_R_pu dx0 dsum0 := rfl

/-- And it really is derivable from the space axiom, with no premise at all. -/
def triB0_derivable :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy] (Formula.all Ty.nat triB0) :=
  Derivable.dist_tri () xL yL yL

/-- The conjoined matrix, used as **both** `B∀` and `C∃`. -/
def cB : Formula WHyperbolic.F [Ty.nat, pTy] := triB ∧ᶠ triB0

/-! The metatheorem's four side conditions, by `rfl`, before anything is built on them.
`isPurelyUniversal` and `isPurelyExistential` are each closed under `∧` (`Language.lean`) and
both conjuncts are quantifier-free, so the conjunction passes both. -/

theorem cB_pu : cB.isPurelyUniversal = true := rfl
theorem cB_pe : cB.isPurelyExistential = true := rfl
theorem cB_vf : cB.isVFree = true := rfl
theorem cB_qf : cB.isQF = true := rfl

-- ============================================================================
-- The two instantiation terms
-- ============================================================================

/-- `s₁ := (d ⬝ x ⬝ z) ⬝ 0`. Its majorant grows with **both** components of `x_star`. -/
def wit1 : Term WHyperbolic.F [pTy] Ty.nat := Term.app dxz Term.zero

/-- `s₂ := (d ⬝ x ⬝ 0_X) ⬝ 0`. Its majorant grows with the **first** component only; the
second slot is the fixed `n₀ = 5` of `0_X`. -/
def wit2 : Term WHyperbolic.F [pTy] Ty.nat := Term.app dx0 Term.zero

/-- `λp. s₁`, closed, so `closedMajorizer` applies to it directly. -/
def witF1 : Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) := Term.lam wit1

/-- `λp. s₂`, closed. -/
def witF2 : Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) := Term.lam wit2

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def cDummy : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) :=
  Formula.eq0 Term.zero Term.zero

-- ============================================================================
-- The derivations — raw `Derivable` constructors only, no proof mode
-- ============================================================================

/-- Instantiate the premise at `s₁`. -/
def inst1 :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (cB.subst0 wit1)) :=
  Derivable.forall_ax (A := cB) wit1

/-- Instantiate the premise at `s₂` — a **different** term. -/
def inst2 :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (cB.subst0 wit2)) :=
  Derivable.forall_ax (A := cB) wit2

/-- **The step this file exists for.** In a Hilbert system with no deduction theorem, going
from `P →ᶠ Q` and `P →ᶠ R` to `P →ᶠ Q ∧ R` *must* contract `P`; `pair_h`
(`PropositionalLemmas.lean`) is that move, and its `and_contract` sits at the premise formula
`∀u cB`. That contraction is where the Dialectica realizer has to merge two challenges into
one, and it is the step that does not reduce. -/
def instBoth :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB)
        (Formula.and (cB.subst0 wit1) (cB.subst0 wit2))) :=
  pair_h inst1 inst2

/-- Keep the `s₁` half; the `s₂` half is a **detour** — derived and then dropped. -/
def instProj :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (cB.subst0 wit1)) :=
  Derivable.syllogism instBoth Derivable.and_weak

/-- Existentially generalise at `s₁`. -/
def cGen :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (cB.subst0 wit1) (Formula.ex Ty.nat cB)) :=
  Derivable.exist_ax wit1 cB

/-- The two-instantiation inner implication. -/
def cInnerTwice :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB)) :=
  Derivable.syllogism instProj cGen

/-- The **one**-instantiation inner implication — the control. Same premise formula, same
conclusion formula; the only difference is that `∀u cB` is consulted once, at `s₁`. -/
def cInnerOnce :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB)) :=
  Derivable.syllogism inst1 cGen

/-- Weaken by the dummy outer premise, so `forall_rule` can fire. -/
def weakenIt
    (h : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB))) :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.weakenBy pTy cDummy)
        (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB))) :=
  Derivable.mp h (Derivable.exportation Derivable.and_weak)

/-- **The statement, proved with two instantiations.** -/
def cFinalTwice :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (weakenIt cInnerTwice))

/-- **The same statement, proved with one instantiation.** The controlled contrast: same
premise *formula* `cB` (not merely the same conclusion — the trap `TriangleBoundDemo` records),
same model, same majorants, same witness term. Only the number of premise instantiations
changes. -/
def cFinalOnce :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (weakenIt cInnerOnce))

/-- That the two really are derivations of one formula, checked by the elaborator. -/
example :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat cB) (Formula.ex Ty.nat cB))) :=
  cFinalTwice

-- ============================================================================
-- Through the metatheorem
-- ============================================================================

/-- The extracted `U` of the two-instantiation derivation. **It elaborates**; what fails is
evaluating its majorant (see the negative section). -/
noncomputable def cUtTwice (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := cB) (C₀ := cB) cFinalTwice

/-- The extracted `U` of the one-instantiation derivation. -/
noncomputable def cUtOnce (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := cB) (C₀ := cB) cFinalOnce

/-- The extracted `V` of the two-instantiation derivation. -/
noncomputable def cVtTwice (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := cB) (C₀ := cB) cFinalTwice

/-- The extracted `V` of the one-instantiation derivation. -/
noncomputable def cVtOnce (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := cB) (C₀ := cB) cFinalOnce

/-- The bound as data, from the **two**-instantiation derivation. This elaborates; its `.val`
is what does not reduce. -/
noncomputable def cBoundTwice (M : WHyperbolicModel)
    (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si cB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si cB (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen M.eqXInterp M.spremise (triCm M h)
    cB_pu cB_vf cB_pe cB_vf cFinalTwice

/-- The bound as data, from the **one**-instantiation derivation. -/
noncomputable def cBoundOnce (M : WHyperbolicModel)
    (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si cB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si cB (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen M.eqXInterp M.spremise (triCm M h)
    cB_pu cB_vf cB_pe cB_vf cFinalOnce

-- ============================================================================
-- The numerals that DO reduce
-- ============================================================================

-- DAG measurement only (`numObjs`, never `sizeWithoutSharing`). Fresh token, so it clashes
-- with neither `WBoundDemo.goal_size`, `UPremiseDemo.goal_size'` nor
-- `TriangleBoundDemo.goal_size_tri`.
open Lean Elab Tactic in
elab "goal_size_conj" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

set_option linter.unusedTactic false

/-! ### The two majorants `U` would have to combine, and their crossover

These are majorants of the **instantiation terms**, not of `U`. They are computed by the same
`closedMajorizer` under the same `ConstMajorants` value `triCm M h`, so they are exactly the
two numbers a `max` would be taken over. The point of the four is that neither dominates: at
`x* = (5,9)` the first is larger, at `x* = (5,1)` the second is. A `U` that reported only one
of them would therefore be a visibly different function from a `U` that combined both — which
is what makes the stall below worth recording rather than shrugging off. -/

theorem witM1_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) witF1 ((5 : ℕ), (9 : ℕ)) := by
  goal_size_conj
  have hval : closedMajorizer (triCm M h) witF1 ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

theorem witM2_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (triCm M h) witF2 ((5 : ℕ), (9 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) witF2 ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

theorem witM1_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = closedMajorizer (triCm M h) witF1 ((5 : ℕ), (1 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) witF1 ((5 : ℕ), (1 : ℕ))
      = Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

theorem witM2_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (triCm M h) witF2 ((5 : ℕ), (1 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) witF2 ((5 : ℕ), (1 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- **The crossover, as a single checked statement**: the first instantiation's majorant beats
the second at `(5,9)` and loses to it at `(5,1)`. Neither term dominates, so `max` is not a
disguised projection. -/
theorem majorants_cross (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    Nat.lt (closedMajorizer (triCm M h) witF2 ((5 : ℕ), (9 : ℕ)))
           (closedMajorizer (triCm M h) witF1 ((5 : ℕ), (9 : ℕ))) ∧
    Nat.lt (closedMajorizer (triCm M h) witF1 ((5 : ℕ), (1 : ℕ)))
           (closedMajorizer (triCm M h) witF2 ((5 : ℕ), (1 : ℕ))) := by
  rw [← witM1_at_5_9 M h, ← witM2_at_5_9 M h, ← witM1_at_5_1 M h, ← witM2_at_5_1 M h]
  exact ⟨(by decide : (901 : ℕ) < 1709), (by decide : (349 : ℕ) < 901)⟩

/-! ### The one-instantiation extraction -/

/-- The one-instantiation `U`, at `x* = (5,9)`: it reports `s₁`'s majorant, `1709`. -/
theorem cUtOnce_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  goal_size_conj
  have hval : closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- …and at `(5,1)` it drops to `349` — i.e. it follows `s₁` and **not** `max s₁ s₂`, which
would be `901` here. So the one-instantiation control is not accidentally already a max. -/
theorem cUtOnce_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (1 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (1 : ℕ))
      = Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The one-instantiation `V`. -/
theorem cVtOnce_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (cVtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (cVtOnce M) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- `Φ = coreBound U* V* = max 1709 1709 = 1709`, for the one-instantiation derivation. -/
theorem cBoundOnce_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = (cBoundOnce M h).val ((5 : ℕ), (9 : ℕ)) := by
  goal_size_conj
  have hval : (cBoundOnce M h).val ((5 : ℕ), (9 : ℕ))
      = Nat.max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

/-! ### The two-instantiation extraction: the WITNESS side goes through -/

/-- **The one-sidedness, checked.** `V` of the *two*-instantiation derivation — the derivation
whose `U` does not reduce — evaluates to the literal `1709`. So `syntactic_soundness`,
`extractedVTerm`, `termMajorizer` and `closedMajorizer` all run to completion on this
derivation; nothing about it is globally unreducible. The obstruction is confined to the
counter component. -/
theorem cVtTwice_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (cVtTwice M) ((5 : ℕ), (9 : ℕ)) := by
  goal_size_conj
  have hval : closedMajorizer (triCm M h) (cVtTwice M) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

-- ============================================================================
-- Non-vacuity: permanent refutation theorems
-- ============================================================================

/-- The one-instantiation `U` is not `0` — the derivation really consults the premise. -/
theorem cUtOnce_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) ≠ closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  rw [← cUtOnce_at_5_9 M h]; decide

/-- The numeral is exact from above… -/
theorem cUtOnce_ne_1710 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1710 : ℕ) ≠ closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  rw [← cUtOnce_at_5_9 M h]; decide

/-- …and from below. -/
theorem cUtOnce_ne_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) ≠ closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  rw [← cUtOnce_at_5_9 M h]; decide

/-- **The one-instantiation `U` is NOT the max of the two majorants at `(5,1)`.** `901` — the
value a two-instantiation `U` would have to be at least — is refuted for `cUtOnce`. This is the
statement that the file's target quantity is genuinely different from what it measured. -/
theorem cUtOnce_ne_901_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) ≠ closedMajorizer (triCm M h) (cUtOnce M) ((5 : ℕ), (1 : ℕ)) := by
  rw [← cUtOnce_at_5_1 M h]; decide

/-- The two instantiation terms' majorants are distinct at `(5,9)`, so "consumed twice at two
different terms" is not two names for one number. -/
theorem witM_distinct (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    ((closedMajorizer (triCm M h) witF1 ((5 : ℕ), (9 : ℕ))) : ℕ)
      ≠ ((closedMajorizer (triCm M h) witF2 ((5 : ℕ), (9 : ℕ))) : ℕ) := by
  rw [← witM1_at_5_9 M h, ← witM2_at_5_9 M h]
  exact (by decide : (1709 : ℕ) ≠ 901)

/-- The bound is exact. -/
theorem cBoundOnce_ne_1710 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1710 : ℕ) ≠ (cBoundOnce M h).val ((5 : ℕ), (9 : ℕ)) := by
  rw [← cBoundOnce_at_5_9 M h]; decide

/-- **The mined statement itself**, read off `.property` of the one-instantiation bound. -/
example (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (x : Ty.interpret (fun () => M.carrier) pTy)
    (xs : Ty.interpret (fun () => M.carrier) pTy.hat)
    (hxs : xs = ((5 : ℕ), (9 : ℕ)))
    (hmaj : M.abstractMajorizability.toRel.maj pTy xs x)
    (hprem : ∀ u : Nat, u ≤ 1709 → Formula.interpret M.si cB (u, (x, ()))) :
    ∃ v : Nat, v ≤ 1709 ∧ Formula.interpret M.si cB (v, (x, ())) := by
  have hb := (cBoundOnce M h).property x xs hmaj
  rw [hxs, ← cBoundOnce_at_5_9 M h] at hb
  exact hb hprem

-- ============================================================================
-- The controls that isolate the stall — their DERIVATIONS, which all elaborate
-- ============================================================================

/-! Each of the three definitions below is a variant of `cFinalTwice` with one ingredient
removed. Their `U` terms extract; none of their `U` *majorants* evaluate. Keeping the
definitions (rather than only prose) means the controls are re-runnable: re-add the four
theorem statements quoted in the negative section and the timeouts reappear. -/

/-- The tautologous matrix `u =₀ u`. -/
def tB : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)

theorem tB_pu : tB.isPurelyUniversal = true := rfl
theorem tB_pe : tB.isPurelyExistential = true := rfl
theorem tB_vf : tB.isVFree = true := rfl

def tInst1 :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat tB) (tB.subst0 wit1)) :=
  Derivable.forall_ax (A := tB) wit1

def tInst2 :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat tB) (tB.subst0 wit2)) :=
  Derivable.forall_ax (A := tB) wit2

def tGen :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (tB.subst0 wit1) (Formula.ex Ty.nat tB)) :=
  Derivable.exist_ax wit1 tB

def tWeakenIt
    (hd : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.weakenBy pTy cDummy)
        (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  Derivable.mp hd (Derivable.exportation Derivable.and_weak)

/-- **Control 1**: trivial matrix, the same two instantiation terms. -/
def tFinalTwice :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (tWeakenIt
    (Derivable.syllogism
      (Derivable.syllogism (pair_h tInst1 tInst2) Derivable.and_weak) tGen)))

def sWit1 : Term WHyperbolic.F [pTy] Ty.nat := Term.zero
def sWit2 : Term WHyperbolic.F [pTy] Ty.nat := Term.app Term.succ Term.zero

/-- **Control 2**: trivial matrix *and* the smallest possible instantiation terms, `0` and
`S 0`, whose majorants are `0` and `1`. -/
def sFinalTwice :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (tWeakenIt
    (Derivable.syllogism
      (Derivable.syllogism
        (pair_h (Derivable.forall_ax (A := tB) sWit1) (Derivable.forall_ax (A := tB) sWit2))
        Derivable.and_weak)
      (Derivable.exist_ax sWit1 tB))))

/-- **Control 3, the decisive one**: trivial matrix, a *single* instantiation, no `pair_h` —
just one bare `Derivable.and_contract` at the premise formula, immediately undone by
`and_weak`. Logically this is the identity; the derivation is `cFinalOnce`'s with one
contraction spliced in. Its `U` still does not reduce, which is what pins the cause on
`and_contract` alone. -/
def acFinal :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (tWeakenIt
    (Derivable.syllogism
      (Derivable.syllogism (Derivable.and_contract (A := Formula.all Ty.nat tB))
        Derivable.and_weak)
      (Derivable.syllogism tInst1 tGen))))

/-- **Control 4**: the same derivation as `acFinal` with the `and_contract`/`and_weak` pair
removed. This one's `U` *does* reduce — see `tUtOnce_at_5_9`. The pair is the only difference
between them. -/
def tFinalOnce :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule (tWeakenIt
    (Derivable.syllogism tInst1 tGen)))

noncomputable def tUtTwice (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := tB) (C₀ := tB) tFinalTwice

noncomputable def sUtTwice (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := tB) (C₀ := tB) sFinalTwice

noncomputable def acUt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := tB) (C₀ := tB) acFinal

noncomputable def tUtOnce (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := tB) (C₀ := tB) tFinalOnce

/-- **The positive half of control 3/4.** `tFinalOnce` differs from `acFinal` by exactly one
`and_contract` + `and_weak` pair (a logical identity), and its `U` evaluates to `1709` without
trouble. Together with the recorded timeout on `acUt`, this is the file's cleanest isolation:
**one derivation, one splice, reducible ⟶ not reducible.** -/
theorem tUtOnce_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (tUtOnce M) ((5 : ℕ), (9 : ℕ)) := by
  goal_size_conj
  have hval : closedMajorizer (triCm M h) (tUtOnce M) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-!
### The negative result, in reproducible form

Each of the four statements below was written, run, and produced a
`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached`
at the `rfl` closing the `have hval`. They are quoted rather than kept, because a file with
errors is not a green file; re-paste any one of them to reproduce. **No limit was raised.**

```lean
theorem cUtTwice_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (cUtTwice M) ((5 : ℕ), (9 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (cUtTwice M) ((5 : ℕ), (9 : ℕ))
      = Nat.max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]; decide                                                    -- ← timeout at `rfl`

theorem tUtTwice_at_5_9 … (tUtTwice M) … = Nat.max … := rfl            -- ← timeout
theorem sUtTwice_small  … (sUtTwice M) … = Nat.max 1 0 := rfl          -- ← timeout
theorem acUt_at_5_9     … (acUt M)     … = Rounding.pairN … := rfl     -- ← timeout
```

The goal at the point of reduction is small in every case: `numObjs = 70, approxDepth = 12`,
identical to the goals of the theorems that *do* reduce (also `70`/`12`). So the residual
blow-up is entirely inside `whnf`, not in the statement — which is why `numObjs` on the goal
cannot see it, and why the diagnostics profile in the module header is the measurement that
matters.

The head symbol of the stalling side is `closedMajorizer`, i.e. `termMajorizer cm t 0 ()` with
`t = extractedUTerm … `; the profile shows whnf descending through `syntactic_soundness` →
`SRealizer.imp` → `sAndContract` and then spending 60,474 steps in `Eq.rec`/`Eq.ndrec` and
10,504 in `Term.rename`.

### Design choices, and one that was rejected

**Nested existentials were rejected.** The task's ideal conclusion is
`∃v ∃w (C₁(v) ∧ C₂(w))` — one existential per instantiation term, which is still purely
existential and so still legal for `_at_gen`. It was not built, for a reason that is worth
recording because it is structural rather than a matter of effort: the two `exist_ax` steps
compose their substitutions, so the middle formula the elaborator must unify is
`C₀.substF (ext σ₁) |>.substF σ₂` against `B₁.subst0 s₁ ∧ᶠ B₂.subst0 s₂`. Unifying those forces
`Term.subst` through `Term.cauchyfy`, `Term.le_Q_dec` and `Term.sub_Q` — the delta-expansion
pathology CLAUDE.md's "Build cost" section documents at 28 s per instance, here under two
binders. `TriangleBoundDemo` escapes it only because every formula in it is a `.subst0` at a
*single* term, matched against itself; that escape is unavailable as soon as two different
terms are substituted into one formula.

The single-existential form used instead keeps the escape and still consumes the premise twice,
at the cost of making the second branch a **detour** — derived, then dropped by `and_weak`. For
the question being asked that is not a loss: the realizer's counter component has no way to know
a branch was discarded, so a detour must still be paid for in `U`. It also makes the control
sharper, since `cFinalOnce` differs from `cFinalTwice` only by the detour.

**Note on `Ty` products.** They do not help here. `∃v^(nat ×ₜ nat)` would give one binder for
two witnesses, but the two conjuncts would then read `fst v` / `snd v`, and the derivation would
need `Term.fst (Term.mkPair a b) = a` as a *derivable* equation — which the proof system does
not have (`beta_eq` covers `lam` only; CLAUDE.md, `general_metatheorem_classical` section).

### Controls actually run

* **Permanent, positive** (`decide` *refutes* in every build): `cUtOnce_ne_zero`,
  `cUtOnce_ne_1710`, `cUtOnce_ne_1708`, `cUtOnce_ne_901_at_5_1`, `witM_distinct`,
  `cBoundOnce_ne_1710`. The fourth is the informative one — it refutes, for the
  one-instantiation derivation, exactly the value a max would force at `(5,1)`.
* **Live, run as an edit and then reverted**: claiming `1708 = closedMajorizer (triCm M h)
  (cUtOnce M) ((5,9))`. The `have hval … := rfl` step **still succeeded** — so the pipeline
  genuinely reduces to a closed ℕ expression and the `rfl` is not a both-sides-stuck no-op
  (trap 12) — and then

      error: Tactic `decide` proved that the proposition
        1708 = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)
      is false

  Refutation, not merely "the proof did not go through".
* **Live, the four stalling variants**, quoted above with their exact error text.
* **Live, diagnostics** on `acUt_at_5_9`, quoted in the module header; the `set_option` lines
  were removed afterwards.

### Cost, measured

| goal | numObjs | approxDepth | outcome |
|---|---|---|---|
| `witM1_at_5_9` | 69 | 12 | reduces |
| `cUtOnce_at_5_9` | 70 | 12 | reduces |
| `cVtTwice_at_5_9` | 70 | 12 | reduces |
| `tUtOnce_at_5_9` | 70 | 12 | reduces |
| `cBoundOnce_at_5_9` | 154 | 23 | reduces |
| `cUtTwice` / `tUtTwice` / `sUtTwice` / `acUt` | 70 | 12 | **whnf timeout** |

Module wall clock, `lake build Metatheorems.Probes.ConjBoundDemo` with all dependencies built:
**23 s**, against `TriangleBoundDemo`'s 21.9 s — so the extra derivations and the eighteen
numeral/refutation theorems cost about a second over its nine. The stalling variants each burn
a full 200,000-heartbeat budget before failing, so a file that *keeps* them costs far more
(the exploratory version with four of them took 40 s and produced no theorems).
-/

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms triB0_all_eq
#print axioms triB0_derivable
#print axioms cFinalTwice
#print axioms cFinalOnce
#print axioms acFinal
#print axioms cBoundOnce
#print axioms cBoundTwice
#print axioms witM1_at_5_9
#print axioms witM2_at_5_9
#print axioms witM1_at_5_1
#print axioms witM2_at_5_1
#print axioms majorants_cross
#print axioms cUtOnce_at_5_9
#print axioms cUtOnce_at_5_1
#print axioms cVtOnce_at_5_9
#print axioms cVtTwice_at_5_9
#print axioms cBoundOnce_at_5_9
#print axioms tUtOnce_at_5_9
#print axioms cUtOnce_ne_zero
#print axioms cUtOnce_ne_1710
#print axioms cUtOnce_ne_1708
#print axioms cUtOnce_ne_901_at_5_1
#print axioms witM_distinct
#print axioms cBoundOnce_ne_1710

end ConjBoundDemo
end Metatheorems
