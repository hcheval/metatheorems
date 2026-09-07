/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Theory
import Metatheorems.MetricSpaces

/-!
# `theory … endtheory`, demonstrated on a toy space

The smallest theory with content: a metric space with one function constant `f : X → X`,
axiomatised as **nonexpansive** with `0_X` as a **fixed point**.  Two axioms, one constant,
one base type — the shape of `WHyperbolic.lean` with the arithmetic removed.

Everything below the `theory` block is `#check`s and `example`s against the *generated*
declarations; nothing is written by hand.  Compare `WHyperbolic.lean` lines 62–208, which is
the same material for four axioms and spells out every de Bruijn index by hand.

The second half of the file is the **negative** demonstration: two theories whose axioms the
command rejects, with the error captured by `#guard_msgs` so that the rejection is part of a
green build rather than a comment claiming one.
-/

set_option linter.style.emptyLine false

namespace Metatheorems

open Formula

/-- A metric space with a nonexpansive self-map fixing `0_X`.

`abbrev d := Term.dist ()` is a *syntactic* alias: the structural metric is not a function
constant, so it gets no generated `abbrev`, and without the alias every axiom body would have
to spell `(Term.dist ())` out. -/
theory Nonexp
  index MetricSpace.ι
  types X := xTy

  abbrev d := Term.dist ()
  abbrev zeroX := Term.zeroX ()

  constants f : X →ₜ X

  axioms nonexp (x y : X) :
    le_R_pu (Term.app2 d (.app f x) (.app f y)) (Term.app2 d x y)

  axioms fixpt :
    eqAtType X (.app f zeroX) zeroX
endtheory

-- ============================================================================
-- What was generated
-- ============================================================================

section Generated

/-- The signature: one constant, at the type it was declared with. -/
example : Nonexp.F Nonexp.κ.f = (xTy →ₜ xTy) := rfl

/-- The constant, usable in any context. -/
example {Γ : Ctx MetricSpace.ι} : Term Nonexp.F Γ (xTy →ₜ xTy) := Nonexp.f

/-- The de Bruijn indices the command computed.  `nonexp` binds `x` then `y`, so inside the
body `x` is index 1 and `y` is index 0 — written out here to show the substitution is the one
a person would have written. -/
example : (Nonexp.ax_nonexp (Γ := ([] : Ctx MetricSpace.ι)))
    = Formula.all xTy (Formula.all xTy
        (le_R_pu
          (Term.app2 (Term.dist ())
            (.app Nonexp.f (.var (.vs .vz))) (.app Nonexp.f (.var .vz)))
          (Term.app2 (Term.dist ()) (.var (.vs .vz)) (.var .vz)))) := rfl

/-- An axiom with no binders is emitted unwrapped. -/
example : (Nonexp.ax_fixpt (Γ := ([] : Ctx MetricSpace.ι)))
    = eqAtType xTy (.app Nonexp.f (Term.zeroX ())) (Term.zeroX ()) := rfl

-- The admissibility theorems.
example : (Nonexp.ax_nonexp (Γ := ([] : Ctx MetricSpace.ι))).isPurelyUniversal = true :=
  Nonexp.ax_nonexp_pu
example : (Nonexp.ax_nonexp (Γ := ([] : Ctx MetricSpace.ι))).isVFree = true :=
  Nonexp.ax_nonexp_vf
example : (Nonexp.ax_fixpt (Γ := ([] : Ctx MetricSpace.ι))).isPurelyUniversal = true :=
  Nonexp.ax_fixpt_pu

/-- The premise set, and the two facts every metatheorem asks of it. -/
example : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Nonexp.F Γ'),
    Nonexp.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := Nonexp.premises_pu
example : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Nonexp.F Γ'),
    Nonexp.Premises ⟨Γ', B⟩ → B.isVFree = true := Nonexp.premises_vf

/-- Each axiom as a derivation, at every `Allowed` and in every context. -/
example {Γ : Ctx MetricSpace.ι} {al : Allowed} :
    Derivable Nonexp.F al Nonexp.Premises (Nonexp.ax_nonexp (Γ := Γ)) := Nonexp.nonexp
example {Γ : Ctx MetricSpace.ι} {al : Allowed} :
    Derivable Nonexp.F al Nonexp.Premises (Nonexp.ax_fixpt (Γ := Γ)) := Nonexp.fixpt

end Generated

-- ============================================================================
-- The generated obligations, and what they buy
-- ============================================================================

section Obligations

variable {X : MetricSpace.ι → Type} {si : SpaceInterp X Nonexp.F}

/-- `Obligations` is a structure with one field per axiom, named after it: exactly the
statement `WHyperbolicModel.axiomsHold` has to prove, one axiom at a time. -/
example (o : Nonexp.Obligations si) {Γ : Ctx MetricSpace.ι}
    (env : Ctx.interpret X Γ) :
    Formula.interpret si (Nonexp.ax_nonexp (Γ := Γ)) env := o.nonexp env

/-- Discharging those fields is the *whole* model-side obligation: `axiomsHold` in the shape
`MetricModel.soundness_gen`'s `hprem` wants, and premise realizers, both generated. -/
example (o : Nonexp.Obligations si) :
    ∀ {Γ' : Ctx MetricSpace.ι} (B : Formula Nonexp.F Γ'), Nonexp.Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', Formula.interpret si B env :=
  Nonexp.axiomsHold o

example (o : Nonexp.Obligations si) :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Nonexp.F Γ'),
      Nonexp.Premises ⟨Γ', B⟩ → SRealizer si B :=
  Nonexp.spremise o

/-- The majorant obligations: one majorant and one majorization proof per constant, delivered
in exactly the shape `ConstMajorants.funcM` / `funcM_maj` demand.  **The command supplies the
shape and nothing else** — `m.f` is the user's to write, and for a nonexpansive map fixing
`0_X` the mathematics says it is the identity `λn.n`, which no elaborator can know. -/
example {am : AbstractMajorizability si} (m : Nonexp.Majorants am) :
    (c : Nonexp.κ) → Nat → Ty.interpret X (Nonexp.F c).hat := Nonexp.Majorants.funcM m

example {am : AbstractMajorizability si} (m : Nonexp.Majorants am) :
    ∀ (c : Nonexp.κ), ∀ n ≥ am.N,
      am.maj (Nonexp.F c) (Nonexp.Majorants.funcM m c n) (si.funcInterp c) :=
  Nonexp.Majorants.funcM_maj m

end Obligations

-- ============================================================================
-- Generated `ι`: the other mode
-- ============================================================================

/-- With no `index` clause the index type is generated too: two base types, one constant
between them, two axioms — the second a **conjunction**, which `isPurelyUniversal` admits
(it is closed under `∧` since the 2026-09-01 products merge) and which therefore has to pass
the admissibility check. -/
theory TwoSorted
  types A
  types B

  abbrev dA := Term.dist TwoSorted.ι.A

  constants g : A →ₜ B

  axioms g_const (x y : A) :
    eqAtType B (.app g x) (.app g y)

  axioms g_isom (x y : A) :
    le_R_pu (Term.app2 dA x y) (Term.app2 dA x y)
      ∧ᶠ le_R_pu (Term.app2 dA y x) (Term.app2 dA y x)
endtheory

example : TwoSorted.A = Ty.base TwoSorted.ι.A := rfl
example : TwoSorted.F TwoSorted.κ.g = (TwoSorted.A →ₜ TwoSorted.B) := rfl
example {Γ : Ctx TwoSorted.ι} {al : Allowed} :
    Derivable TwoSorted.F al TwoSorted.Premises (TwoSorted.ax_g_const (Γ := Γ)) :=
  TwoSorted.g_const
example {Γ : Ctx TwoSorted.ι} {al : Allowed} :
    Derivable TwoSorted.F al TwoSorted.Premises (TwoSorted.ax_g_isom (Γ := Γ)) :=
  TwoSorted.g_isom
example : (TwoSorted.ax_g_isom (Γ := ([] : Ctx TwoSorted.ι))).isPurelyUniversal = true :=
  TwoSorted.ax_g_isom_pu

-- ============================================================================
-- The degenerate corners
-- ============================================================================

/-- **No function constants** — `MetricSpaces.lean`'s own shape, where the metric is
structural.  `κ` is `Empty` and `Majorants` is `PUnit`. -/
theory NoConstants
  index MetricSpace.ι
  types X := xTy
  abbrev d := Term.dist ()

  axioms self (x : X) : le_R_pu (Term.app2 d x x) (Term.app2 d x x)
endtheory

example : NoConstants.κ = Empty := rfl
example {Γ : Ctx MetricSpace.ι} {al : Allowed} :
    Derivable NoConstants.F al NoConstants.Premises (NoConstants.ax_self (Γ := Γ)) :=
  NoConstants.self

/-- **No axioms** — the premise set is `False`, so `premises_pu` and `axiomsHold` are proved
by `False.elim` and `Obligations` is `True`.  A model owes nothing. -/
theory NoAxioms
  index MetricSpace.ι
  types X := xTy
  constants h : X →ₜ X
endtheory

example {X : MetricSpace.ι → Type} {si : SpaceInterp X NoAxioms.F} :
    NoAxioms.Obligations si := trivial
example {X : MetricSpace.ι → Type} {si : SpaceInterp X NoAxioms.F}
    (o : NoAxioms.Obligations si) :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula NoAxioms.F Γ'),
      NoAxioms.Premises ⟨Γ', B⟩ → SRealizer si B :=
  NoAxioms.spremise o

-- ============================================================================
-- Rejection: the admissibility check, and what it says
-- ============================================================================

/-!
The command evaluates `Formula.isPurelyUniversal` and `Formula.isVFree` on each axiom before
emitting the `_pu` / `_vf` theorems, and fails naming the axiom.  Both failures are captured
by `#guard_msgs` below, so the *rejection* is part of a green build rather than a comment
claiming one.  Note that the declarations generated before the failing axiom (`BadEx.ι`,
`BadEx.κ`, `BadEx.F`, `BadEx.f`, `BadEx.ax_surj`) do survive: the command aborts at the
offending axiom, it does not roll back.
-/

-- An existential premise.
/--
error: theory: axiom `surj` is NOT purely universal, so the metatheorems cannot take it as a premise.
A premise must be a block of `∀` (and `∧`) over a quantifier-free matrix: no `∃`, and no `→` or `∨` above a quantifier.  Checked by evaluating `Formula.isPurelyUniversal BadEx.ax_surj`, which is `false`.
-/
#guard_msgs in
theory BadEx
  index MetricSpace.ι
  types X := xTy
  constants f : X →ₜ X
  axioms surj (y : X) :
    Formula.ex Ty.nat (Formula.eq0 (.var .vz) (.var .vz))
endtheory

-- A disjunctive premise: purely universal, but not ∨-free.
/--
error: theory: axiom `split` is NOT ∨-free, so the metatheorems cannot take it as a premise.
The Dialectica interpretation of a disjunction carries a decision, so premises must be ∨-free.  Replace the `∨ᶠ` by a quantifier-free decision term, or split the two cases into separate axioms.  Checked by evaluating `Formula.isVFree BadOr.ax_split`, which is `false`.
-/
#guard_msgs in
theory BadOr
  index MetricSpace.ι
  types X := xTy
  constants f : X →ₜ X
  axioms split (y : X) :
    Formula.or (Formula.eq0 Term.zero Term.zero) (Formula.eq0 Term.zero Term.zero)
endtheory

-- And the mode check: a `types` item with no `:=` under an `index` clause has no constructor
-- to be, and is rejected before anything is generated.
/--
error: theory: with an `index` clause every `types` item needs `:= <Ty expression>` (there is no generated inductive to add a constructor to)
-/
#guard_msgs in
theory BadMode
  index MetricSpace.ι
  types X
endtheory

end Metatheorems
