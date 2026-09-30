/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic
import Metatheorems.Probes.WBoundDemo

/-!
# An extraction where the **premise bound `U` is not zero**

`Probes/WBoundDemo.lean` mines `Φ = 901` from a derivation at a W-hyperbolic space, but its
`wUt_is_zero` records that the extracted `U` is `0`. `U` is the bound on the *premise*
variable — how far into `∀u B₀` the proof reaches — and `0` there means the derivation never
touched the premise at all: `wEx` proves `∃v C₀` outright and `wInner` weakens the unused
`∀u B₀` in front of it. Half of the metatheorem's output was therefore vacuous.

This file is the one-step variation that fixes that. Everything is held fixed — the same
`pTy = X ×ₜ ℝ`, the same model, the same `wCm`-style majorants, the same twelve-ish raw
`Derivable` constructors — and **only the route through the implication changes**:

    WBoundDemo:  prove `∃v C₀` outright, then weaken the premise away   ⇒  U = 0
    here:        instantiate `∀u P` at `s`, then existentially generalise ⇒  U = |s|

## The statement

    ∀p^(X ×ₜ ℝ) ( ∀u^ℕ (u =₀ u)  →  ∃v^ℕ (v =₀ v) )

with the *same* witness term as `WBoundDemo`,

    s(p) := (d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X) ⬝ 0,   p₁ := fst p,  p₂ := snd p.

`s` is now used **twice, on both sides of the implication**: as the instance of the universal
premise (`forall_ax s`) and as the existential witness (`exist_ax s`). That is what makes the
two extracted functionals coincide, and it is why the headline number `901` appears on the
premise side, where `WBoundDemo` has `0`.

## The derivation — the whole point

    ∀u P  →ᶠ  P[s]      Derivable.forall_ax s        (premise instantiation)
    P[s]  →ᶠ  ∃v P      Derivable.exist_ax s P       (existential introduction)
    ------------------------------------------- syllogism
    ∀u P  →ᶠ  ∃v P

Nothing closes the conclusion independently: `refl0` appears **only** to discharge the dummy
outer premise that lets `forall_rule` fire (exactly as in `WBoundDemo`), never to prove
`P[s]`. `P[s]` is obtained *from the premise*, which is what the extraction then reports.

The matrix `P := u =₀ u` is deliberately shallow — the task is about the **route**, not the
depth of the matrix. Both `B₀` and `C₀` are the same formula value `uP`, which is what lets
`syllogism` compose the two axioms with no cast.
-/

namespace Metatheorems
namespace UPremiseDemo

open Formula

-- The statement

/-- The quantified type: a space point paired with a real parameter. Same as `WBoundDemo`. -/
abbrev pTy : Ty MetricSpace.ι := xTy ×ₜ realTy MetricSpace.ι

/-- The matrix, used as **both** `B₀` and `C₀`: `x =₀ x` in context `[x:ℕ, p:X ×ₜ ℝ]`. -/
def uP : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)

/-- The term the premise is instantiated at, and the existential witness — literally
`WBoundDemo.wWit`: `(d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X) ⬝ 0`. -/
def uWit : Term WHyperbolic.F [pTy] Ty.nat :=
  Term.app
    (Term.app2 (Term.dist ())
      (Term.app3 (Term.func ())
        (Term.fst (Term.var Var.vz)) (Term.fst (Term.var Var.vz))
        (Term.snd (Term.var Var.vz)))
      (Term.zeroX ()))
    Term.zero

/-! The metatheorem's four side conditions, by `rfl`, before anything is built on them.
`B₀` and `C₀` are the same formula here, so each is checked once. -/

theorem uP_qf : uP.isQF = true := rfl
theorem uP_vf : uP.isVFree = true := rfl

/-- The substitution computes: `P[s/x]` is literally `s =₀ s`. This is what makes
`forall_ax` and `exist_ax` compose by `syllogism` with no cast in between. -/
theorem uP_subst0 : uP.subst0 uWit = Formula.eq0 uWit uWit := rfl

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def uDummyOuter : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) :=
  Formula.eq0 Term.zero Term.zero

-- The derivation — raw `Derivable` constructors only, no proof mode

/-- Step 1: **instantiate the premise.** `(∀u P) →ᶠ P[s]`. -/
def uInst :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat uP →ᶠ uP.subst0 uWit) :=
  Derivable.forall_ax (A := uP) uWit

/-- Step 2: **existentially generalise.** `P[s] →ᶠ (∃v P)`. -/
def uGen :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (uP.subst0 uWit →ᶠ Formula.ex Ty.nat uP) :=
  Derivable.exist_ax uWit uP

/-- Step 3: compose. `(∀u P) →ᶠ (∃v P)` — the implication, **routed through the premise**.
There is no `refl0` here: `P[s]` is never proved, it is *consumed* from the antecedent and
handed to `exist_ax`. -/
def uInner :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat uP →ᶠ Formula.ex Ty.nat uP) :=
  Derivable.syllogism uInst uGen

/-- Step 4: weaken by the dummy outer premise, so `forall_rule` can fire. -/
def uInnerWeakened :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.weakenBy pTy uDummyOuter →ᶠ
        (Formula.all Ty.nat uP →ᶠ Formula.ex Ty.nat uP)) :=
  Derivable.mp uInner (Derivable.exportation Derivable.and_weak)

/-- Step 5: `forall_rule`, then discharge the dummy with `refl0`. -/
def uFinal :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.all Ty.nat uP →ᶠ Formula.ex Ty.nat uP)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule uInnerWeakened)

-- Through the metatheorem, at a W-hyperbolic model

/-- `M.constMajorants 5 h` with `distM` in kernel-computable form — verbatim
`WBoundDemo.wCm`, repeated here so this file stands alone (`WBoundDemo` is not imported).
`MetricModel.distMajorant` routes through the `noncomputable` `Rounding.roundR`, so nothing
downstream of it reduces; `MetricModel.distMajorant_apply` is the **proved** identity giving
its value as a closed ℕ-expression. No number changes and nothing is assumed. -/
noncomputable def uCm (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    ConstMajorants M.abstractMajorizability :=
  { M.constMajorants 5 h with
    distM := fun _ _ => fun (n₁ : ℕ) (n₂ : ℕ) (k : ℕ) =>
      Rounding.pairN (2 * ((n₁ + n₂) * 2 ^ (k + 1))) (2 ^ (k + 1) - 1)
    distM_maj := by
      intro i n hn
      have hEq : (fun (n₁ : ℕ) (n₂ : ℕ) (k : ℕ) =>
          Rounding.pairN (2 * ((n₁ + n₂) * 2 ^ (k + 1))) (2 ^ (k + 1) - 1))
          = M.distMajorant := by
        funext n₁ n₂ k; exact (M.distMajorant_apply n₁ n₂ k).symm
      rw [hEq]
      exact (M.constMajorants 5 h).distM_maj i n hn }

/-- The bound as data, from `uFinal`. `M` and `h` are variables. -/
noncomputable def uBound (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si uP (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si uP (v, (x, ())) } :=
  syntactic_general_metatheorem_at M.eqXInterp M.spremise (uCm M h)
    uP_qf uP_vf uP_qf uP_vf uFinal

/-- The extracted `U` functional as a closed `Term` — **the bound on the premise variable**,
i.e. the index at which `∀u P` must hold for the conclusion to follow. -/
noncomputable def uUt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := uP) (C₀ := uP) uFinal

/-- The extracted `V` functional as a closed `Term` — the bound on the witness. -/
noncomputable def uVt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := uP) (C₀ := uP) uFinal

-- The numerals

-- DAG measurement only (`numObjs`, never `sizeWithoutSharing`: the sharing ratio here is
-- ≈10⁵). Named `goal_size'` so it does not collide with `WBoundDemo`'s `goal_size` token.
open Lean Elab Tactic in
elab "goal_size'" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

set_option linter.unusedTactic false

/-- **The point of the file.** The majorant of the extracted **premise** functional is the
literal `901`, not `0`: the derivation instantiates `∀u P` at `s`, so `U` is the majorant of
`s`, which at `x_star = (5, g)` is `(5 + 5)°` read at index `0`.

Contrast `WBoundDemo.wUt_is_zero`, which is the same model, the same majorants and the same
witness term, differing **only** in that its derivation weakens the premise away. -/
theorem uUt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (901 : ℕ) = closedMajorizer (uCm M h) (uUt M) ((5 : ℕ), g) := by
  goal_size'
  have hval : closedMajorizer (uCm M h) (uUt M) ((5 : ℕ), g)
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The witness side, for comparison: the same `901`, since the same `s` is the existential
witness. -/
theorem uVt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (901 : ℕ) = closedMajorizer (uCm M h) (uVt M) ((5 : ℕ), g) := by
  goal_size'
  have hval : closedMajorizer (uCm M h) (uVt M) ((5 : ℕ), g)
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- `Φ = coreBound U* V* = max 901 901 = 901`. Both components now carry information. -/
theorem uBound_at_5 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (901 : ℕ) = (uBound M h).val ((5 : ℕ), g) := by
  goal_size'
  have hval : (uBound M h).val ((5 : ℕ), g)
      = Nat.max (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

-- Non-vacuity

/-- **`U` genuinely tracks the derivation, not a default path.** At `x_star = (7, g)` the
*premise* bound moves to `1273`, exactly as `WBoundDemo`'s *witness* bound does: `W` majorizes
to `max 7 7 = 7`, so `d ⬝ · ⬝ 0_X` gives `(7 + 5)°` and index `0` picks
`pairN (2·(12·2)) (2−1) = 1273`.

A `U` produced by a default or degenerate path could not depend on `x_star` at all — and
`WBoundDemo`'s `U`, which is `0`, does not. -/
theorem uUt_at_7 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (1273 : ℕ) = closedMajorizer (uCm M h) (uUt M) ((7 : ℕ), g) := by
  have hval : closedMajorizer (uCm M h) (uUt M) ((7 : ℕ), g)
      = Rounding.pairN (2 * ((7 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- **`U` is not zero** — the headline, in refutation form: `0` is provably *not* its value.
This is the direct negation of `WBoundDemo.wUt_is_zero` for this derivation. -/
theorem uUt_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (0 : ℕ) ≠ closedMajorizer (uCm M h) (uUt M) ((5 : ℕ), g) := by
  rw [← uUt_is_901 M h g]; decide

/-- The numeral is exact, not an upper estimate: `902` is provably not the value. -/
theorem uUt_ne_902 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (902 : ℕ) ≠ closedMajorizer (uCm M h) (uUt M) ((5 : ℕ), g) := by
  rw [← uUt_is_901 M h g]; decide

/-- The bound is exact too. -/
theorem uBound_ne_902 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (902 : ℕ) ≠ (uBound M h).val ((5 : ℕ), g) := by
  rw [← uBound_at_5 M h g]; decide

/-- **The controlled comparison, with the majorants held fixed as a single term.**
`WBoundDemo`'s own extracted `U`, evaluated under *this* file's `uCm` — one and the same
`ConstMajorants` **value** applied to the two derivations' `U` terms. It is `0`; `uUt_is_901`
says this file's is `901`.

This is stronger than comparing the two files' numbers as reported, which would leave open
that the majorants differed somewhere: here the majorant argument is literally the same
expression in both statements, so the only thing that varies is the derivation. Note it holds
by bare `rfl` — `WBoundDemo`'s `U` does not depend on `x_star` at all. -/
theorem wUt_is_zero_under_uCm (M : WHyperbolicModel)
    (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) (g : ℕ → ℕ) :
    (0 : ℕ) = closedMajorizer (uCm M h) (WBoundDemo.wUt M) ((5 : ℕ), g) := rfl

/-- A third value of `x_star`, ruling out a coincidence of the `5`/`7` pair: `U` moves again,
to `pairN (2·(14·2)) 1 = 1709`. -/
theorem uUt_at_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (1709 : ℕ) = closedMajorizer (uCm M h) (uUt M) ((9 : ℕ), g) := by
  have hval : closedMajorizer (uCm M h) (uUt M) ((9 : ℕ), g)
      = Rounding.pairN (2 * ((9 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- **The mined statement itself**, read off `.property`: for any `x` majorized by `(5, g)`,
if the premise holds up to `901` then there is a witness `v ≤ 901`. Both sides of the
implication now carry the same live bound — in `WBoundDemo` the premise side is `0` and the
hypothesis is therefore vacuous. -/
example (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) (g : ℕ → ℕ)
    (x : Ty.interpret (fun () => M.carrier) pTy)
    (xs : Ty.interpret (fun () => M.carrier) pTy.hat)
    (hxs : xs = ((5 : ℕ), g))
    (hmaj : M.abstractMajorizability.toRel.maj pTy xs x)
    (hprem : ∀ u : Nat, u ≤ 901 → Formula.interpret M.si uP (u, (x, ()))) :
    ∃ v : Nat, v ≤ 901 ∧ Formula.interpret M.si uP (v, (x, ())) := by
  have hb := (uBound M h).property x xs hmaj
  rw [hxs, ← uBound_at_5 M h g] at hb
  exact hb hprem

/-- **The derivation really is of the stated formula.** `uFinal`'s type is checked here
against the statement written out in full, with no abbreviation in the way. -/
example :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all (xTy ×ₜ realTy MetricSpace.ι)
        (Formula.all Ty.nat (Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)) →ᶠ
         Formula.ex Ty.nat (Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)))) :=
  uFinal

/-!
### What the comparison with `WBoundDemo` isolates

Only the middle of the implication changes. `U` at `(5,g)` is `901` here against `0` in
`WBoundDemo`, `V` and `Φ` are `901` in both, and `U` moves with `x_star` (`1273` at 7, `1709`
at 9); `wUt_is_zero_under_uCm` makes the comparison airtight by evaluating `WBoundDemo`'s `U`
under this file's own `uCm`. The table, the controls run and the cost are in the notes.
-/

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms uFinal
#print axioms uP_subst0
#print axioms uBound
#print axioms uUt_is_901
#print axioms uVt_is_901
#print axioms uBound_at_5
#print axioms uUt_at_7
#print axioms uUt_ne_zero
#print axioms uUt_ne_902
#print axioms uBound_ne_902
#print axioms wUt_is_zero_under_uCm
#print axioms uUt_at_9

end UPremiseDemo
end Metatheorems
