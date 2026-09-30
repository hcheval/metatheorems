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

The task this file answers asked for `f` as a **free Lean-level variable** of type
`Term WHyperbolic.F [] rTy`, so that independence of `f` is visible. That does not typecheck,
and the reason is worth recording rather than working around silently.

`Derivable.exist_ax t C₀ : Derivable (C₀.subst0 t →ᶠ Formula.ex ρ C₀)`, so the derivation
needs `Derivable (C₀.subst0 wit)`, closed by `refl0` — which requires `C₀.subst0 wit` to be
**definitionally** `wit =₀ wit`. With `f` free, `C₀` must contain `Term.weaken f`, and
`Term.subst` is defined by structural recursion on constructors (`Subst.lean:47`): at an
opaque variable `f` it is stuck. The identity it needs, `Term.weaken_subst0`
(`Subst.lean:195`), is a *propositional* lemma proved by `simp`, not `rfl`. Measured, not
guessed: with `f : Term WHyperbolic.F [] rTy` a section variable and `C₀` built with
`Term.weaken f`, the goal `(C0B f).subst0 (witB f) = (witB f =₀ witB f)` fails with

    Tactic `rfl` failed: The left-hand side
      (C0B f).subst0 (witB f)
    is not definitionally equal to the right-hand side
      witB f =₀ witB f

whereas the `Term.snd (Term.var vz)` form below closes the corresponding goal (`wC0_subst0`)
by `rfl` with no axioms at all.

Discharging it would put an `Eq.mpr`/`Eq.rec` cast **inside** a `Type`-valued `Derivable`,
and `syntactic_soundness` pattern-matches on `Derivable`'s constructors, so the extraction
would then be stuck one layer higher (the `Eq.mpr` problem `CombinatorLemmas.lean` meets for
`anorm`). So the free-variable form is not merely inconvenient here; it moves the obstruction
into the pipeline.

Making the real parameter the **second component of the universally quantified `p`** removes
the problem outright — `Term.snd (Term.var vz)` is a constructor tree, so `subst0` computes —
and it is *strictly stronger* than what was asked for: the parameter is now universally
quantified inside the theorem rather than fixed outside it, and `Φ` is shown below to be
`901` for **every** second-component majorant `g`, not merely for each fixed `f`. Nothing is
weakened; the quantifier moved inward.
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
### Controls actually run, and how they failed

Both were run as edits to this file and then reverted; the failure text is recorded because a
control that is not run is not a control.

* Claiming `902 = (wBound M h).val ((5 : ℕ), g)`. The `have hval … := rfl` step still
  succeeds — the pipeline does reduce — and then `decide` reports

      Tactic `decide` proved that the proposition
        902 = Nat.max 0 (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
      is false

  This is the strongest available form: not "the proof did not go through" but "the claim is
  refuted". `wBound_ne_902` above is the same fact in positive, permanently-checked form.
* Claiming `901 = (wBound M h).val ((7 : ℕ), g)` — likewise refuted, against
  `Nat.max 0 (Rounding.pairN (2 * ((7 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))` = `1273`.
  So the bound is not constant in `x_star`.

### That `Φ` came from *this* derivation

`wBound` is `syntactic_general_metatheorem_at … wFinal` with no other input, and `wFinal`'s
type is the statement spelled out at the top of this file — so there is no path by which a
default or trivial `Φ` could be substituted. Two further checks that the *derivation* is the
source of the number rather than the model constants:

* `wUt_is_zero` and `wVt_is_901` differ, and they differ in the way the two matrices differ:
  `B₀` does not mention `p`, so `U` is `0`; `C₀`'s witness is the distance term, so `V` is
  `901`. A `Φ` insensitive to the derivation could not separate them.
* `wBound_at_7` tracks `x_star` through `WMajorant`'s `max`, which only the extracted witness
  term reaches.

### Cost, measured

Goal `numObjs` at the point of reduction (DAG size, never `sizeWithoutSharing` — the sharing
ratio in this pipeline is ≈10⁵):

| goal | numObjs | approxDepth |
|---|---|---|
| `wUt_is_zero` | 71 | 12 |
| `wVt_is_901`  | 71 | 12 |
| `wBound_at_5` | 157 | 23 |

These are the goals as stated, before reduction; the reduction itself is `rfl`, so nothing
intermediate is ever materialised as an `Expr`. Two things were learned getting there, and
both are reusable.

**1. `simp only` cannot reduce this pipeline; `rfl` can.** The first version of this file used
the `ComputesDemo` simp set widened by `syntactic_soundness`, the `s*` combinators,
`extractUTerm`/`extractVTerm`, `SRealizer.imp` and `Term.rename`/`Renaming.ext`/`shift`. It
**stalled** — goal `numObjs` 860 → 4522 → 2462 across three widenings — ending stuck on
`Ctx.lookupHat` applied to a dependent `match` on `Var`, generated by the renamings *inside
the extracted realizer*, with `M` and `g` still free (so `decide` reported *"Expected type
must not contain free variables"*). `simp` does not reduce those dependent matches; the
kernel's `whnf` walks straight through them. `WHyperbolic.lean`'s `ComputesDemo` gets away
with `simp only` only because its terms are hand-written and contain no renamings at all —
which is exactly the difference between starting from a term and starting from a derivation.
So: **reduce with `rfl`, and spend the effort on making every constant reachable by `whnf`**
— here that meant one thing, `wCm`.

**2. Split the structural reduction from the arithmetic.** A single `rfl` on the `901` goals
fails with `maximum recursion depth has been reached`, and `maxRecDepth` must not be raised.
The cause is not the pipeline but the *last* step: evaluating `Rounding.triagN 41` inside
`isDefEq` costs elaborator recursion depth, while the same evaluation in the kernel via
`decide` is free. Hence the shape used throughout:

    have hval : <pipeline expression> = <closed ℕ expression> := rfl
    rw [hval]; decide

`rfl` does the structural half (through `syntactic_soundness`, the extraction and
`termMajorizer`) and stops at a closed ℕ expression it never evaluates; `decide` does the
arithmetic. Note `wUt_is_zero` needs no split — its value is `0`, so no `triagN` is reached.
That asymmetry is the diagnostic: **a `rfl` that dies of recursion depth here is doing
arithmetic, not traversal.** This is worth knowing because the obvious reading — "the
extraction is too big" — is wrong, and would send someone to unfold the wrong layer.

**Does `ι = Unit` with the `W` constant cost more than `TinyBoundDemo`'s `ι = Empty`?** Yes —
about 5× at this size — but the factor splits in two, and neither half is a blow-up.
Wall-clock, `lake env lean <file>` with dependencies already built:

| file | setting | witness term | wall |
|---|---|---|---|
| `TinyBoundDemo` | `ι = Empty` | `Term.var vz` | 4.4 s |
| (control, since deleted) | `ι = Unit`, `W` in signature | `Term.zero` | 9.5 s |
| `WBoundDemo` | `ι = Unit`, `W` in signature | `d ⬝ (W ⬝ p₁ ⬝ p₁ ⬝ p₂) ⬝ 0_X ⬝ 0` | 23.3 s |

The control is this file with the existential witness replaced by `Term.zero` and everything
else — model, `wCm`, premise set, the 12-constructor derivation shape — held fixed. So:

* **`ι = Empty` → a space, at equal witness: ~2×**, of which 2.7 s is `import` of the
  `WHyperbolic`/Mathlib-`ℝ` stack, i.e. not elaboration at all.
* **Trivial witness → the real distance witness: a further ~2.5×**, and this is a property of
  the *term*, not of `ι`: the witness is a four-node application spine, so `syntactic_soundness`
  and `termMajorizer` each traverse correspondingly more. It would cost the same at
  `ι = Empty` with a term of the same size.

Profiling puts essentially all of it in the `rfl` steps (two `refine`s at ~17 s cumulative,
one `eqRefl` at 2.5 s) — i.e. in pushing `whnf` through the extracted realizer, exactly where
the work is. Note the count of numeral theorems matters: each one re-traverses the whole
pipeline independently, and this file has five.

The cost that is *qualitatively* new at a space is not time but **computability**, and it is
paid once per model rather than once per proof. At `ι = Empty` every majorant is ℕ-valued
outright and a bare `rfl` closes the goal; at a metric model `distM` routes through
`Rounding.roundR` on Mathlib `ℝ`, which is `noncomputable`, so **nothing downstream of it
reduces until it is brought back to ℕ by hand** (`wCm`). That is the single substantive
difference between `ι = Empty` and a space.
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
