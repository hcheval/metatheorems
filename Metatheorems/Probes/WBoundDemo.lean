/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic

/-!
# The first bound extracted from a derivation **at a space**

Everything the project had before this file was one of two things:

* `Probes/TinyBoundDemo.lean` — the full pipeline
  `Derivable → syntactic_soundness → extractUTerm/VTerm → closedMajorizer → numeral`,
  but at `ι = Empty`, on a statement about naturals, with no space anywhere;
* the `ComputesDemo` sections of `MetricSpaces.lean` / `WHyperbolic.lean` / `Normed.lean` —
  literal numerals at a space, but obtained by applying `closedMajorizer` to **hand-written
  closed terms**, with *no `Derivable` anywhere*. They start at the last stage of the pipeline.

This file connects the two: a derivation over `WHyperbolic.F` / `WHyperbolic.Premises`, at
`Allowed.extended`, carried through `syntactic_general_metatheorem_at` (the `Subtype`-valued
version, so `Φ` is data) with `M.constMajorants 5 h`, down to the literal `901` —
**the same numeral `WHyperbolic.lean`'s `ComputesDemo` gets by hand, this time reached through
a proof.**

(Precisely: with `wCm M h`, which is `M.constMajorants 5 h` with its `distM` field replaced by
the closed ℕ-expression `MetricModel.distMajorant_apply` *proves* equal to it. That changes no
number and assumes nothing; it is what makes the pipeline reduce in the kernel at all. See
`wCm`.)

## The statement

    ∀p^(X ×ₜ ℝ) ( ∀u^ℕ (u =₀ u)  →  ∃v^ℕ ( v =₀ (d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X) ⬝ 0 ) )

with `p₁ := Term.fst p : X` and `p₂ := Term.snd p : ℝ`.

`realTy = nat →ₜ nat`, so `d ⬝ a ⬝ b` is a Cauchy sequence of ℚ-codes and `(d ⬝ a ⬝ b) ⬝ 0`
is a plain natural — the 0th code. That is what lets a *space-typed* variable reach a
**quantifier-free, ∨-free** `C₀`, which is what the metatheorem requires (checked by `rfl`
below). The conclusion is trivially true — the witness is the value itself — but it is
genuinely of the metatheorem's shape, the derivation is a real one, and the bound really is
computed from it.

## Why the real parameter is `Term.snd p` and not a free `Term F [] rTy`

A free `f : Term WHyperbolic.F [] rTy` does not typecheck: `C₀.subst0 wit` would have to be
definitionally `wit =₀ wit`, but `Term.subst` is stuck at an opaque variable. Making the real
parameter the second component of the universally quantified `p` removes the problem, and is
strictly stronger (`Φ = 901` for every second-component majorant `g`). The measured failure and
the argument are in the notes.
-/

namespace Metatheorems
namespace WBoundDemo

open Formula

-- The statement

/-- The quantified type: a space point paired with a real parameter. -/
abbrev pTy : Ty MetricSpace.ι := xTy ×ₜ realTy MetricSpace.ι

/-- `B₀ := u =₀ u`, in context `[u:ℕ, p:X ×ₜ ℝ]`. Does not mention `p`. -/
def wB0 : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)

/-- The witness term, in context `[p : X ×ₜ ℝ]`: `(d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X) ⬝ 0`, the
0th rational code of the distance from the convex combination `W(p₁, p₁, p₂)` to `0_X`. -/
def wWit : Term WHyperbolic.F [pTy] Ty.nat :=
  Term.app
    (Term.app2 (Term.dist ())
      (Term.app3 (Term.func ())
        (Term.fst (Term.var Var.vz)) (Term.fst (Term.var Var.vz))
        (Term.snd (Term.var Var.vz)))
      (Term.zeroX ()))
    Term.zero

/-- `C₀ := v =₀ (d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X) ⬝ 0`, in context `[v:ℕ, p:X ×ₜ ℝ]`. -/
def wC0 : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var Var.vz)
    (Term.app
      (Term.app2 (Term.dist ())
        (Term.app3 (Term.func ())
          (Term.fst (Term.var (Var.vs Var.vz))) (Term.fst (Term.var (Var.vs Var.vz)))
          (Term.snd (Term.var (Var.vs Var.vz))))
        (Term.zeroX ()))
      Term.zero)

/-! Both matrices are quantifier-free and ∨-free — the metatheorem's side conditions,
all four by `rfl`, verified before anything is built on them. -/

theorem wB0_qf : wB0.isQF = true := rfl
theorem wB0_vf : wB0.isVFree = true := rfl
theorem wC0_qf : wC0.isQF = true := rfl
theorem wC0_vf : wC0.isVFree = true := rfl

/-- The substitution really does compute: `C₀[wit/v]` is literally `wit =₀ wit`, so `refl0`
closes it with no cast. This is the step that fails for a free `f` (see the header). -/
theorem wC0_subst0 : wC0.subst0 wWit = Formula.eq0 wWit wWit := rfl

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def wDummyOuter : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) :=
  Formula.eq0 Term.zero Term.zero

-- The derivation — raw `Derivable` constructors only, no proof mode

/-- Step 1: `∃v C₀` in context `[p]`. `exist_ax wWit wC0` gives
`C₀[wWit/v] →ᶠ ∃v C₀`, and `C₀[wWit/v]` is `wWit =₀ wWit` (`wC0_subst0`), i.e. `refl0`. -/
def wEx :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy] (Formula.ex Ty.nat wC0) :=
  Derivable.mp Derivable.refl0 (Derivable.exist_ax wWit wC0)

/-- Step 2: weaken into `(∀u B₀) →ᶠ (∃v C₀)`; the antecedent is never used. -/
def wInner :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.all Ty.nat wB0 →ᶠ Formula.ex Ty.nat wC0) :=
  Derivable.mp wEx (Derivable.exportation Derivable.and_weak)

/-- Step 3: weaken again by the dummy premise, so `forall_rule` can fire. -/
def wInnerWeakened :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [pTy]
      (Formula.weakenBy pTy wDummyOuter →ᶠ
        (Formula.all Ty.nat wB0 →ᶠ Formula.ex Ty.nat wC0)) :=
  Derivable.mp wInner (Derivable.exportation Derivable.and_weak)

/-- Step 4: `forall_rule`, then discharge the dummy with `refl0`. Twelve raw constructors,
exactly `TinyBoundDemo.tFinal`'s shape — only the witness term differs. -/
def wFinal :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all pTy (Formula.all Ty.nat wB0 →ᶠ Formula.ex Ty.nat wC0)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule wInnerWeakened)

-- Through the metatheorem, at a W-hyperbolic model

/-- **`M.constMajorants 5 h` with `distM` in computable form.**

`MetricModel.distMajorant` is `fun n₁ n₂ => Rounding.roundR ((n₁ + n₂ : ℕ) : ℝ)`, and
`Rounding.roundR` is `noncomputable` (Mathlib `ℝ`, `Nat.floor`), so nothing downstream of it
reduces in the kernel. `MetricModel.distMajorant_apply` is the **proved** identity giving its
value as a closed ℕ-expression; substituting it changes no number and assumes nothing — the
`distM_maj` field is discharged by transporting the original proof along that equality.

This is what lets the numerals below reduce at all: the `simp only` route stalls on the
dependent `match`es that `Term.rename`/`Ctx.lookupHat` generate inside the *extracted*
realizer (measured, see the file's closing note), whereas the kernel's `whnf` goes straight
through them. `WHyperbolic.lean`'s `ComputesDemo` can use `simp only` because its terms are
hand-written and contain no renamings at all. -/
noncomputable def wCm (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
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

/-- **The bound as data.** `syntactic_general_metatheorem_at` applied to `wFinal`, with the
majorants `wCm M h`. `M` and `h` are variables, so this is `Φ` for *any* W-hyperbolic model
with `d(a, 0_X) ≤ 5`. -/
noncomputable def wBound (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si wB0 (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si wC0 (v, (x, ())) } :=
  syntactic_general_metatheorem_at M.eqXInterp M.spremise (wCm M h)
    wB0_qf wB0_vf wC0_qf wC0_vf wFinal

/-- The extracted `U` functional, as a closed `Term` — the bound on the premise variable. -/
noncomputable def wUt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedUTerm M.eqXInterp M.spremise (B₀ := wB0) (C₀ := wC0) wFinal

/-- The extracted `V` functional, as a closed `Term` — the bound on the witness. -/
noncomputable def wVt (M : WHyperbolicModel) :
    Term WHyperbolic.F ([] : Ctx MetricSpace.ι) (pTy →ₜ Ty.nat) :=
  extractedVTerm M.eqXInterp M.spremise (B₀ := wB0) (C₀ := wC0) wFinal

-- The numerals

-- Measure the goal as a DAG (heap objects) and by depth. Meta-level only — nothing
-- object-level is evaluated. Never use `sizeWithoutSharing` here: the measured sharing ratio
-- in this pipeline is ≈10⁵ and materialising it is what drives the machine into swap.
open Lean Elab Tactic in
elab "goal_size" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

-- `goal_size` deliberately does not change the goal; it only reports.
set_option linter.unusedTactic false

/-- The majorant of the extracted **premise** functional is `0`: `B₀ := u =₀ u` does not
mention `p`, so nothing needs to be checked. -/
theorem wUt_is_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (0 : ℕ) = closedMajorizer (wCm M h) (wUt M) ((5 : ℕ), g) := by
  goal_size
  rfl

/-- **The point of the file.** The majorant of the extracted witness functional, at a
majorant `(5, g)` of `p`, is the literal `901` — for **every** `g`, i.e. uniformly in the
real parameter, and for every W-hyperbolic model `M` with `d(a, 0_X) ≤ 5`.

`W ⬝ p₁ ⬝ p₁ ⬝ p₂` majorizes to `max 5 5 = 5` (`WMajorant` discards its real argument), then
`d ⬝ · ⬝ 0_X` to `(5 + 5)°` and index `0` picks the numeral. Identical to the number
`WHyperbolic.lean`'s `ComputesDemo` reaches by hand — but reached here from `wFinal`. -/
theorem wVt_is_901 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (901 : ℕ) = closedMajorizer (wCm M h) (wVt M) ((5 : ℕ), g) := by
  goal_size
  have hval : closedMajorizer (wCm M h) (wVt M) ((5 : ℕ), g)
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- **The bound itself.** `Φ = coreBound U* V* = max (U* x*) (V* x*) = max 0 901 = 901`. -/
theorem wBound_at_5 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (901 : ℕ) = (wBound M h).val ((5 : ℕ), g) := by
  goal_size
  have hval : (wBound M h).val ((5 : ℕ), g)
      = Nat.max 0 (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

-- Non-vacuity

/-- **`Φ` is a genuine function of the majorant of `x`, not a constant fallback.** At
`x_star = (7, g)` the bound is `1273`, not `901`: `W ⬝ p₁ ⬝ p₁ ⬝ p₂` majorizes to
`max 7 7 = 7`, so `d ⬝ · ⬝ 0_X` gives `(7 + 5)°`, i.e.
`pairN (2·(12·2)) (2 − 1) = triagN 49 + 48 = 1273`.

This is the control that matters most: a `Φ` produced by some default or degenerate path
could not track `x_star`. It does. -/
theorem wBound_at_7 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (1273 : ℕ) = (wBound M h).val ((7 : ℕ), g) := by
  have hval : (wBound M h).val ((7 : ℕ), g)
      = Nat.max 0 (Rounding.pairN (2 * ((7 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

/-- **The numeral is exact, not an upper estimate**: `902` is provably *not* the value. -/
theorem wBound_ne_902 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (g : ℕ → ℕ) :
    (902 : ℕ) ≠ (wBound M h).val ((5 : ℕ), g) := by
  rw [← wBound_at_5 M h g]; decide

/-!
### Controls, provenance and cost

Two controls were run and reverted (`902` and `901` at `x_star = 7` are both refuted by
`decide`), `wUt_is_zero`/`wVt_is_901` differ as the two matrices do, and the goals are 71 to 157
objects. Two reusable findings: `simp only` cannot reduce this pipeline but `rfl` can, and a
`rfl` that dies of recursion depth is doing arithmetic, not traversal (hence
`have hval : … := rfl; rw [hval]; decide`). At a space the cost that is new is computability:
`distM` routes through `noncomputable` `Rounding.roundR`, so `wCm` brings it back to ℕ by hand.
Details, the wall-clock table and the failing controls are in the notes.
-/

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms wFinal
#print axioms wC0_subst0
#print axioms wBound
#print axioms wUt_is_zero
#print axioms wVt_is_901
#print axioms wBound_at_5
#print axioms wBound_at_7
#print axioms wBound_ne_902

end WBoundDemo
end Metatheorems
