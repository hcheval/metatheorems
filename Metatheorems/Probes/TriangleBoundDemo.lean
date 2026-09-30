/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic
import Metatheorems.Probes.UPremiseDemo

/-!
# A bound whose premise is the **genuine triangle inequality**

`Probes/WBoundDemo.lean` mines `Φ = 901` from a derivation at a W-hyperbolic space, but its
premise bound `U` is `0` — the derivation never touches the premise. `Probes/UPremiseDemo.lean`
fixes the *route* (`forall_ax s` ⟶ `exist_ax s`, so `U = 901` is live), but both matrices are
still the tautology `u =₀ u`. `Probes/GeneralMatricesDemo.lean` demos a `le_R_pu` premise, but
at `ι = Empty` and with **no bound extracted**.

This file is the three of them combined: a live premise-consuming route, at a space, with the
premise matrix being **the triangle inequality of the space itself**, through
`syntactic_general_metatheorem_at_gen` (Kohlenbach 17.52's general-matrix form).

## Why this statement fits, exactly

`le_R_pu f g` is literally `Formula.all Ty.nat B` for a quantifier-free `B`, so the
metatheorem's own premise variable `u` *is* the Cauchy index and `Formula.all .nat triB` is the
triangle inequality on the nose (`triAll_eq`, by `rfl`); `Derivable.dist_tri` is a free
constructor proving it verbatim. `U` is then the precision at which the inequality must be
known. The three facts in full are in the notes.

## The statement

At `ρ := pTy := X ×ₜ X` (two space points `x := fst p`, `z := snd p`), with `y := 0_X`:

    ∀p^(X ×ₜ X) (  ∀n ( d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z) )ₙ   →   ∃v (…)ᵥ  )

with `C := B` (the same quantifier-free body, its index now the existential witness). That
identification is what lets `forall_ax` and `exist_ax` compose by `syllogism` with no cast.

The instantiation/witness term is
`s(p) := (d ⬝ x ⬝ z) ⬝ 0` — the 0th ℚ-code of the distance between the two components.

## The derivation

    ∀n triB  →ᶠ  triB[s]     Derivable.forall_ax s
    triB[s]  →ᶠ  ∃v triB     Derivable.exist_ax s triB
    -------------------------------------------- syllogism
    ∀n triB  →ᶠ  ∃v triB

`refl0` appears **only** to discharge the dummy outer premise that lets `forall_rule` fire
(exactly as in `WBoundDemo`/`UPremiseDemo`), never to prove `triB[s]`: that is *consumed* from
the antecedent.

## What is and is not established

**Established.** The pipeline reduces to a literal numeral through a matrix containing
`cauchyfy`, `sub_Q`, `le_Q_dec` and `pow2neg_Q`, because `U` and `V` are read off the
instantiation term and `whnf` never enters the matrix; and `triUncond` is the first derivation
to consume a space axiom. **Not established:** any mathematics *about* the space (the conclusion
is the premise). Discussion in the notes.
-/

namespace Metatheorems
namespace TriangleBoundDemo

open Formula

-- The statement

/-- The quantified type: an ordered **pair of space points**. `x := fst p`, `z := snd p`. -/
abbrev pTy : Ty MetricSpace.ι := xTy ×ₜ xTy

/-- `x := fst p`, in context `[p : X ×ₜ X]`. -/
abbrev xL : Term WHyperbolic.F [pTy] xTy := Term.fst (Term.var Var.vz)

/-- `z := snd p`. -/
abbrev zL : Term WHyperbolic.F [pTy] xTy := Term.snd (Term.var Var.vz)

/-- `y := 0_X`, the reference point — the middle point of the triangle. -/
abbrev yL : Term WHyperbolic.F [pTy] xTy := Term.zeroX ()

/-- `d(x,z)` — the left-hand side of the triangle inequality. -/
def dxz : Term WHyperbolic.F [pTy] (realTy MetricSpace.ι) :=
  Term.app2 (Term.dist ()) xL zL

/-- `d(x,0_X) +ℝ d(0_X,z)` — the right-hand side. -/
def dsum : Term WHyperbolic.F [pTy] (realTy MetricSpace.ι) :=
  Term.app2 Term.add_R (Term.app2 (Term.dist ()) xL yL) (Term.app2 (Term.dist ()) yL zL)

/-- **The matrix**, used as both `B∀` and `C∃`: the quantifier-free body of
`le_R_pu dxz dsum`, in context `[n:ℕ, p:X ×ₜ X]`. Written out rather than projected out of
`le_R_pu`, because `Formula` has no eliminator that would give the body — the identification
is instead *proved*, by `triAll_eq`. -/
def triB : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.imp
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy dxz.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy dsum.weaken) (Term.app .succ (.var .vz)))))
      Term.zero)
    ⊥ᶠ

/-- **The honesty check for the whole design.** `∀n triB` is not merely *like* the triangle
inequality: it is, on the nose, the formula `Derivable.dist_tri` concludes, at
`x := fst p`, `y := 0_X`, `z := snd p`. Hence the metatheorem's premise variable `u` *is* the
Cauchy index of `≤ℝ`, and `U` is the precision at which the inequality must be known. -/
theorem triAll_eq : Formula.all Ty.nat triB = le_R_pu dxz dsum := rfl

/-! The metatheorem's four side conditions, by `rfl`, before anything is built on them.
`B` and `C` are the same formula, so `B` is checked as purely universal and as purely
existential. -/

theorem triB_pu : triB.isPurelyUniversal = true := rfl
theorem triB_pe : triB.isPurelyExistential = true := rfl
theorem triB_vf : triB.isVFree = true := rfl
theorem triB_qf : triB.isQF = true := rfl

/-- The instantiation term = the existential witness: `(d ⬝ x ⬝ z) ⬝ 0`, the 0th ℚ-code of
the distance between the two components of `p`. Its majorant is `distM`'s, which is the same
family of numbers `WBoundDemo`/`UPremiseDemo` reach. -/
def triWit : Term WHyperbolic.F [pTy] Ty.nat := Term.app dxz Term.zero

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def triDummy : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) :=
  Formula.eq0 Term.zero Term.zero

/-- The tautologous matrix `u =₀ u`, used **only** by the unconditional variant below, where
the triangle inequality has already been discharged and there is nothing left to assume. -/
def trivB : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)

theorem trivB_pu : trivB.isPurelyUniversal = true := rfl
theorem trivB_vf : trivB.isVFree = true := rfl

-- The derivation — raw `Derivable` constructors only, no proof mode

/-- Step 1: **instantiate the premise** at `s`. `(∀n triB) →ᶠ triB[s]`. -/
def triInst :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat triB →ᶠ triB.subst0 triWit) :=
  Derivable.forall_ax (A := triB) triWit

/-- Step 2: **existentially generalise**. `triB[s] →ᶠ (∃v triB)`. -/
def triGen :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (triB.subst0 triWit →ᶠ Formula.ex Ty.nat triB) :=
  Derivable.exist_ax triWit triB

/-- Step 3: compose. `(∀n triB) →ᶠ (∃v triB)`, **routed through the premise** — `triB[s]` is
never proved, only consumed. -/
def triInner :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat triB →ᶠ Formula.ex Ty.nat triB) :=
  Derivable.syllogism triInst triGen

/-- Step 4: weaken by the dummy outer premise, so `forall_rule` can fire. -/
def triInnerWeakened :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.weakenBy pTy triDummy →ᶠ
        (Formula.all Ty.nat triB →ᶠ Formula.ex Ty.nat triB)) :=
  Derivable.mp triInner (Derivable.exportation Derivable.and_weak)

/-- Step 5: `forall_rule`, then discharge the dummy with `refl0`.

    ⊢ ∀p ( ∀n (d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z))ₙ  →  ∃v (…)ᵥ )
-/
def triFinal :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.all Ty.nat triB →ᶠ Formula.ex Ty.nat triB)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule triInnerWeakened)

/-- **The derivation really is of the stated formula**, with the premise spelled out as
`le_R_pu` rather than as `Formula.all Ty.nat triB` — i.e. as the triangle inequality. -/
example :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (le_R_pu dxz dsum →ᶠ Formula.ex Ty.nat triB)) :=
  triFinal

-- The unconditional version — the first use of a SPACE AXIOM in a derivation

/-- **The triangle inequality itself**, at `x := fst p`, `y := 0_X`, `z := snd p`, in context
`[p]`. This is `Derivable.dist_tri`, a *free constructor* of `Derivable` — a genuine axiom of
the theory of (pseudo)metric spaces, not a logical rule and not a `.premise`. Its type is
stated here as `Formula.all Ty.nat triB`, which `triAll_eq` shows is the same formula. -/
def triHyp :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy] (Formula.all Ty.nat triB) :=
  Derivable.dist_tri () xL yL zL

/-- **The first derivation in this project that consumes a space axiom.** Discharging
`triInner`'s premise with `triHyp` gives `∃v triB` outright, with no hypothesis at all. -/
def triExUnc :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy] (Formula.ex Ty.nat triB) :=
  Derivable.mp triHyp triInner

/-- `triExUnc` weakened by the dummy outer premise, so `forall_rule` can fire. -/
def triExUncWeakened :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.weakenBy pTy triDummy →ᶠ Formula.ex Ty.nat triB) :=
  Derivable.mp triExUnc (Derivable.exportation Derivable.and_weak)

/-- The unconditional statement: `⊢ ∀p ∃v (…)ᵥ`. No premise; the triangle inequality has been
used and discharged inside. -/
def triUncond :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.ex Ty.nat triB)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule triExUncWeakened)

/-- `triExUnc` with the *tautologous* premise `∀u (u =₀ u)` weakened in. -/
def triUncInner :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat trivB →ᶠ Formula.ex Ty.nat triB) :=
  Derivable.mp triExUnc (Derivable.exportation Derivable.and_weak)

/-- …and by the dummy outer premise on top of that. -/
def triUncInnerWeakened :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.weakenBy pTy triDummy →ᶠ
        (Formula.all Ty.nat trivB →ᶠ Formula.ex Ty.nat triB)) :=
  Derivable.mp triUncInner (Derivable.exportation Derivable.and_weak)

/-- The unconditional derivation re-shaped for the metatheorem: `⊢ ∀p (∀u (u =₀ u) → ∃v (…)ᵥ)`.
The mathematics is `triUncond`; the premise is there only because the metatheorem's shape has
a slot for one. Its extracted `U` is `0` — correctly, since nothing is assumed. -/
def triUncondFinal :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.all Ty.nat trivB →ᶠ Formula.ex Ty.nat triB)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule triUncInnerWeakened)

-- Through the metatheorem, at a W-hyperbolic model

/-- `M.constMajorants 5 h` with `distM` in kernel-computable form — verbatim
`UPremiseDemo.uCm` / `WBoundDemo.wCm`, repeated so the numbers below are produced by a
`ConstMajorants` value defined in *this* file. `MetricModel.distMajorant` routes through the
`noncomputable` `Rounding.roundR`, so nothing downstream of it reduces;
`MetricModel.distMajorant_apply` is the **proved** identity giving its value as a closed
ℕ-expression. No number changes and nothing is assumed. -/
noncomputable def triCm (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
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

/-- **The bound as data**, from `triFinal`, through the *general-matrix* metatheorem
`syntactic_general_metatheorem_at_gen`. `M` and `h` are variables, so this holds of every
W-hyperbolic model with `d(a, 0_X) ≤ 5`. -/
noncomputable def triBound (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si triB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si triB (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen M.eqXInterp M.spremise (triCm M h)
    triB_pu triB_vf triB_pe triB_vf triFinal

/-- The extracted `U` as a closed `Term` — **the precision at which the triangle inequality
must be known**. -/
noncomputable def triUt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := triB) (C₀ := triB) triFinal

/-- The extracted `V` as a closed `Term` — the bound on the existential witness. -/
noncomputable def triVt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := triB) (C₀ := triB) triFinal

/-- The extracted `U` of the **unconditional** derivation, for contrast. -/
noncomputable def triUncUt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := trivB) (C₀ := triB) triUncondFinal

/-- The extracted `V` of the unconditional derivation. -/
noncomputable def triUncVt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := trivB) (C₀ := triB) triUncondFinal

-- The numerals

-- DAG measurement only (`numObjs`, never `sizeWithoutSharing`: the sharing ratio in this
-- pipeline is ≈10⁵). Fresh token, so it does not clash with `WBoundDemo.goal_size` or
-- `UPremiseDemo.goal_size'`.
open Lean Elab Tactic in
elab "goal_size_tri" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

set_option linter.unusedTactic false

/-- **The headline.** The premise bound is the literal `901` at `x_star = (5,5)` — the index
to which `d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)` must be verified. It is *not* `0`: the derivation
consumes the triangle inequality rather than weakening it away.

The number is `distM (5) (5)` read at index `0`, i.e.
`pairN (2·((5+5)·2)) (2−1) = triagN 41 + 40 = 901` — the same family `WBoundDemo` and
`UPremiseDemo` hit, as it must be: the term is the same shape and the majorants are the same.
Nothing here was retargeted to produce a familiar number. -/
theorem triUt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (5 : ℕ)) := by
  goal_size_tri
  have hval : closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The witness side: the same `901`, since the same term serves as instance and witness. -/
theorem triVt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (triCm M h) (triVt M) ((5 : ℕ), (5 : ℕ)) := by
  goal_size_tri
  have hval : closedMajorizer (triCm M h) (triVt M) ((5 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- `Φ = coreBound U* V* = max 901 901 = 901`. -/
theorem triBound_at_5 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = (triBound M h).val ((5 : ℕ), (5 : ℕ)) := by
  goal_size_tri
  have hval : (triBound M h).val ((5 : ℕ), (5 : ℕ))
      = Nat.max (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

-- Non-vacuity

/-- **`U` tracks `x_star`**, so it is read off the derivation and not supplied by a default
path: at `(7,5)` the premise bound moves to `1273`. -/
theorem triUt_at_7_5 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1273 : ℕ) = closedMajorizer (triCm M h) (triUt M) ((7 : ℕ), (5 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (triUt M) ((7 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((7 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- It tracks the **second** component too — so both points of the pair reach the bound, i.e.
the majorization really goes through `d(x,z)` and not through one argument only. -/
theorem triUt_at_5_7 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1273 : ℕ) = closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (7 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (7 : ℕ))
      = Rounding.pairN (2 * ((5 + 7) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- **`U` is not zero** — the direct negation of `WBoundDemo.wUt_is_zero`'s claim for this
derivation, in permanently-checked refutation form. -/
theorem triUt_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) ≠ closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (5 : ℕ)) := by
  rw [← triUt_is_901 M h]; decide

/-- The numeral is exact, not an upper estimate: `902` is refuted. -/
theorem triUt_ne_902 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (902 : ℕ) ≠ closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (5 : ℕ)) := by
  rw [← triUt_is_901 M h]; decide

/-- And `900` is refuted, so the value is pinned from both sides. -/
theorem triUt_ne_900 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (900 : ℕ) ≠ closedMajorizer (triCm M h) (triUt M) ((5 : ℕ), (5 : ℕ)) := by
  rw [← triUt_is_901 M h]; decide

/-- The bound is exact too. -/
theorem triBound_ne_902 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (902 : ℕ) ≠ (triBound M h).val ((5 : ℕ), (5 : ℕ)) := by
  rw [← triBound_at_5 M h]; decide

/-- The unconditional derivation's premise bound is `0`, under the same `ConstMajorants` value
`triCm M h`.

**Read this one carefully — on its own it is weaker than it looks.** `triUncondFinal`'s premise
slot holds the *tautology* `trivB = (u =₀ u)`, not `triB`, so this `0` and `triUt_is_901`'s
`901` bound **different formulas**. The `0` here arises for exactly the same structural reason
as `WBoundDemo.wUt_is_zero`: a premise that is never consulted. It is not, by itself, evidence
that proving the inequality is what dropped the bound.

The genuinely controlled statement is `triUncUtB_is_zero` below, which holds the premise matrix
fixed at `triB` and varies only whether the proof consults it. -/
theorem triUncUt_is_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) = closedMajorizer (triCm M h) (triUncUt M) ((5 : ℕ), (5 : ℕ)) := rfl

/-- The unconditional derivation's *witness* bound is still `901` — the conclusion is
unchanged, only the premise is. -/
theorem triUncVt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (triCm M h) (triUncVt M) ((5 : ℕ), (5 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (triUncVt M) ((5 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

-- The controlled contrast: same premise formula, only the proof varies

/-! `triUncondFinal` fills the metatheorem's premise slot with the tautology `trivB`, so its
`U = 0` is not comparable with `triUt_is_901` — the two bound different formulas. The three
definitions below repair that. `Derivable.exportation Derivable.and_weak` does not care *what*
is weakened in, so putting `triB` there instead of `trivB` costs one line and yields a
derivation of the **same formula as `triFinal`**, proved differently:

    triFinal          : consults the premise   (forall_ax ⟶ exist_ax ⟶ syllogism)
    triUncondFinalB   : ignores it, using dist_tri instead

Same statement, same model, same majorants, same premise matrix `triB`, same conclusion. The
only variable is the proof. -/

/-- `triExUnc` weakened by `∀u triB` — the triangle inequality present as a hypothesis but
never consulted, since `triExUnc` already proved the conclusion via `dist_tri`. -/
def triUncInnerB :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.all Ty.nat triB) (Formula.ex Ty.nat triB)) :=
  Derivable.mp triExUnc (Derivable.exportation Derivable.and_weak)

/-- …and by the dummy outer premise on top of that. -/
def triUncInnerBW :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.imp (Formula.weakenBy pTy triDummy)
        (Formula.imp (Formula.all Ty.nat triB) (Formula.ex Ty.nat triB))) :=
  Derivable.mp triUncInnerB (Derivable.exportation Derivable.and_weak)

/-- **The same formula `triFinal` proves, proved without consulting the premise.** -/
def triUncondFinalB :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy
        (Formula.imp (Formula.all Ty.nat triB) (Formula.ex Ty.nat triB))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule triUncInnerBW)

/-- That the two really are derivations of one formula, checked by the elaborator. -/
example :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy
        (Formula.imp (Formula.all Ty.nat triB) (Formula.ex Ty.nat triB))) :=
  triFinal

noncomputable def triUncUtB (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := triB) (C₀ := triB) triUncondFinalB

/-- **The controlled contrast, and the file's sharpest claim.** One formula, two proofs, one
majorant value, one premise matrix `triB`: the premise bound is `901` when the proof consults
the triangle inequality (`triUt_is_901`) and `0` when it discharges it with `dist_tri`.

Unlike `triUncUt_is_zero`, nothing here varies except the derivation — so this is the statement
that `U` reports a property of the **proof**, not of the theorem. -/
theorem triUncUtB_is_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) = closedMajorizer (triCm M h) (triUncUtB M) ((5 : ℕ), (5 : ℕ)) := rfl

/-- **The cross-file control, majorants held fixed as a single value.** `WBoundDemo`'s own
extracted `U` — from a derivation over a *different* quantified type `X ×ₜ ℝ` — evaluated
under `WBoundDemo`'s majorant object, is `0`; this file's is `901`. The two `ConstMajorants`
are the same expression (`M.constMajorants 5 h` with the same `distM` rewrite), so the only
thing that varies is the derivation. Note this one holds by bare `rfl`: `WBoundDemo`'s `U`
does not depend on `x_star` at all. -/
theorem wbound_U_is_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (0 : ℕ) = closedMajorizer (WBoundDemo.wCm M h) (WBoundDemo.wUt M) ((5 : ℕ), g) := rfl

/-- **The mined statement itself**, read off `.property`: for every `x` majorized by `(5,5)`,
if the triangle inequality holds at every index `≤ 901`, then it holds at some index `≤ 901`.
Both sides carry the same live bound. -/
example (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (x : Ty.interpret (fun () => M.carrier) pTy)
    (xs : Ty.interpret (fun () => M.carrier) pTy.hat)
    (hxs : xs = ((5 : ℕ), (5 : ℕ)))
    (hmaj : M.abstractMajorizability.toRel.maj pTy xs x)
    (hprem : ∀ u : Nat, u ≤ 901 → Formula.interpret M.si triB (u, (x, ()))) :
    ∃ v : Nat, v ≤ 901 ∧ Formula.interpret M.si triB (v, (x, ())) := by
  have hb := (triBound M h).property x xs hmaj
  rw [hxs, ← triBound_at_5 M h] at hb
  exact hb hprem

/-!
### What this file adds over `UPremiseDemo`

The premise matrix is the substantive change: `U` is now the index at which a real statement
about the space must be known (`901` at `(5,5)`, as in `UPremiseDemo`), and `triUncond` is the
first derivation to use a space axiom. The delta-expansion pathology did not bite, since `U` and
`V` are read off the instantiation term and not the matrix. The comparison table, the controls
run (permanent refutations, the wrong-middle-point rejection, `triUncUtB_is_zero` against
`triUt_is_901`) and the cost (21.9 s) are in the notes.
-/

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms triAll_eq
#print axioms triFinal
#print axioms triHyp
#print axioms triUncond
#print axioms triUncondFinal
#print axioms triBound
#print axioms triUt_is_901
#print axioms triVt_is_901
#print axioms triBound_at_5
#print axioms triUt_at_7_5
#print axioms triUt_at_5_7
#print axioms triUt_ne_zero
#print axioms triUt_ne_902
#print axioms triUt_ne_900
#print axioms triBound_ne_902
#print axioms triUncUt_is_zero
#print axioms triUncondFinalB
#print axioms triUncUtB_is_zero
#print axioms triUncVt_is_901
#print axioms wbound_U_is_zero

end TriangleBoundDemo
end Metatheorems
