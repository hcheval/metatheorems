/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Monotone
import Metatheorems.Probes.ConjBoundDemo

/-!
# Gate G1: a premise consumed twice, through the full monotone recursion

**Question.** The spike (`Probes/MonotoneSpike.lean`, gate G0) cleared `acFinal`, whose
contraction `max` is `max(1709, 0)` — one copy of the premise is weakened away. The genuine
test of contraction is `ConjBoundDemo.tFinalTwice`: the premise `∀u tB` instantiated at **two
different terms** `s₁ = (d x z) 0`, `s₂ = (d x 0_X) 0` through `pair_h` (`and_contract`,
`and_perm`, `importation`, `exportation`, `syllogism`, `and_weak`), so `U` must be a real
`max` of two different majorants — and `ConjBoundDemo.majorants_cross` records that they
cross: `s₁ ↦ 1709, s₂ ↦ 901` at `x* = (5,9)`; `s₁ ↦ 349, s₂ ↦ 901` at `(5,1)`. Does the
library recursion `monotone_soundness` (`Dialectica/Monotone.lean`, every constructor, no
fallback) compute it, and is it the `max`?

**RESULT: THE GATE PASSES, AND THE `max` CROSSES OVER.**

`g1_U_at_5_9 = 1709` and `g1_U_at_5_1 = 901`: `U` is `max s₂* (max s₁* 0)`, so the first
instantiation wins at `(5,9)` and the second at `(5,1)`. `V` is `1709` and `349`. Refutations
(`g1_U_at_5_1_ne_349` in particular) pin the `max`. The normal forms, how they were read off, the
cost table (1.5 s elaboration for 29 constructors) and the non-vacuity list are in the notes.
-/

namespace Metatheorems
namespace MonotoneLaneA

open Formula
open TriangleBoundDemo (pTy triCm)
open ConjBoundDemo (tB acFinal tFinalTwice)

-- Tools: constructor count and the arithmetic normal-form read-out

/-- Constructor count, copied from `SizeProbe.derivSize` (that file pulls in `LemBoundDemo`;
not imported here). -/
def derivSizeA {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Nat
  | _, _, .mp a b          => 1 + derivSizeA a + derivSizeA b
  | _, _, .syllogism a b   => 1 + derivSizeA a + derivSizeA b
  | _, _, .exportation a   => 1 + derivSizeA a
  | _, _, .importation a   => 1 + derivSizeA a
  | _, _, .expansion a     => 1 + derivSizeA a
  | _, _, .forall_rule a   => 1 + derivSizeA a
  | _, _, .exist_rule a    => 1 + derivSizeA a
  | _, _, .univ_gen a      => 1 + derivSizeA a
  | _, _, .qfer _ _ a      => 1 + derivSizeA a
  | _, _, .induction a b   => 1 + derivSizeA a + derivSizeA b
  | _, _, _                => 1

/-- The scale of the gate. -/
theorem derivSize_tFinalTwice : derivSizeA tFinalTwice = 29 := rfl

open Lean Meta Elab Tactic in
/-- Reduce to an *arithmetic* head normal form: unfold everything except the arithmetic
vocabulary (`max`, `pairN`, `+`, `*`, `^`, `-`, `/`, numerals), recursing into their
arguments. Type, `Prop` and instance arguments are left alone. -/
partial def arithNF (e : Expr) : MetaM Expr := do
  let stop : Array Name := #[``Max.max, ``Nat.max, ``max, ``Rounding.pairN, ``HAdd.hAdd,
    ``HMul.hMul, ``HPow.hPow, ``HSub.hSub, ``HDiv.hDiv, ``OfNat.ofNat, ``Nat.succ, ``Nat.zero,
    ``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.pow, ``Nat.div]
  let rec loop (e : Expr) : MetaM Expr := do
    let e ← whnfCore e
    if e.isRawNatLit then return e
    match e.getAppFn with
    | .const n _ =>
      if stop.contains n then return e
      match ← unfoldDefinition? e with
      | some e' => loop e'
      | none => return e
    | _ => return e
  let e ← loop e
  match e.getAppFn with
  | .const n _ =>
    if stop.contains n then
      let args ← e.getAppArgs.mapM fun a => do
        let ty ← inferType a
        if (← isProp ty) || ty.isSort || (← isClass? ty).isSome then pure a else arithNF a
      return mkAppN e.getAppFn args
    else return e
  | _ => return e

open Lean Meta Elab Tactic in
/-- Print the arithmetic normal form of the goal's right-hand side. Read-out only; the goal
is untouched. -/
elab "arith_nf_rhs" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let some (_, _, rhs) := g.eq? | throwError "arith_nf_rhs: the goal is not an equation"
  let r ← arithNF rhs
  logInfo m!"arith NF: {r}"

set_option linter.unusedTactic false

-- The monotone realizers

/-- The monotone realizer of `tFinalTwice`, at the W-hyperbolic model with `d(a, 0_X) ≤ 5`,
through the library's full recursion. -/
noncomputable def twiceM (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) tFinalTwice

/-- The spike's gate derivation, through the same recursion. -/
noncomputable def acM (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) acFinal

-- GATE G1

/-- **THE GATE.** `U` of the two-instantiation derivation at `x* = (5,9)`: the `max` of the
two instantiation majorants, won by `s₁`'s `1709`. -/
theorem g1_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (9 : ℕ)) := by
  arith_nf_rhs
  have hval : mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
          (max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0) := rfl
  rw [hval]
  decide

/-- **THE CROSSOVER.** The same `U` at `x* = (5,1)`: the same `max`, now won by `s₂`'s
`901` — the other instantiation. -/
theorem g1_U_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ)) := by
  arith_nf_rhs
  have hval : mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
          (max (Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0) := rfl
  rw [hval]
  decide

/-- The witness side at `(5,9)`: `s₁`'s majorant, agreeing with the term route's
`cVtTwice_at_5_9`. -/
theorem g1_V_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiV (triCm M h) (twiceM M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiV (triCm M h) (twiceM M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The witness side at `(5,1)`: `349`, `s₁`'s majorant there — the witness is produced at
`s₁` only (`tGen = exist_ax s₁`), so no `max` on this side. -/
theorem g1_V_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = mfiV (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ)) := by
  have hval : mfiV (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ))
      = Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- Gate G0 re-run against the library recursion: `acFinal`'s `U`, same value and same
normal form as the spike recorded. -/
theorem g1_acFinal_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (acM M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (acM M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

-- Refutation controls

theorem g1_U_at_5_9_ne_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) ≠ mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← g1_U_at_5_9 M h]; decide

theorem g1_U_at_5_1_ne_900 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (900 : ℕ) ≠ mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ)) := by
  rw [← g1_U_at_5_1 M h]; decide

/-- **The important control.** `349` is `s₁`'s majorant at `(5,1)` — the value a `U` that
followed one instantiation only would report (`ConjBoundDemo.cUtOnce_at_5_1`). The
two-instantiation `U` is not that: the second instantiation is paid for. -/
theorem g1_U_at_5_1_ne_349 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) ≠ mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ)) := by
  rw [← g1_U_at_5_1 M h]; decide

/-- And it is not the `(5,9)` value either: `U` moves with `x*`. -/
theorem g1_U_at_5_1_ne_1709 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) ≠ mfiU (triCm M h) (twiceM M h) ((5 : ℕ), (1 : ℕ)) := by
  rw [← g1_U_at_5_1 M h]; decide

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms derivSize_tFinalTwice
#print axioms g1_U_at_5_9
#print axioms g1_U_at_5_1
#print axioms g1_V_at_5_9
#print axioms g1_V_at_5_1
#print axioms g1_acFinal_U_at_5_9
#print axioms g1_U_at_5_9_ne_1708
#print axioms g1_U_at_5_1_ne_900
#print axioms g1_U_at_5_1_ne_349
#print axioms g1_U_at_5_1_ne_1709

end MonotoneLaneA
end Metatheorems
