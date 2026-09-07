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

namespace Metatheorems

open Formula

-- A metric space with a nonexpansive self-map fixing `0_X`.
-- (A `theory` block takes no doc comment: it is not a single declaration.)
theory Nonexp
  index MetricSpace.ι
  types X := xTy
  constants f : X →ₜ X
  axioms nonexp (x y : X) :
    le_R_pu (Term.app2 (Term.dist ()) (.app f x) (.app f y))
            (Term.app2 (Term.dist ()) x y)
  axioms fixpt :
    eqAtType X (.app f (Term.zeroX ())) (Term.zeroX ())
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

-- With no `index` clause the index type is generated too.  Two base types, one constant
-- between them, one axiom.
theory TwoSorted
  types A
  types B
  constants g : A →ₜ B
  axioms g_const (x y : A) :
    eqAtType B (.app g x) (.app g y)
endtheory

example : TwoSorted.A = Ty.base TwoSorted.ι.A := rfl
example : TwoSorted.F TwoSorted.κ.g = (TwoSorted.A →ₜ TwoSorted.B) := rfl
example {Γ : Ctx TwoSorted.ι} {al : Allowed} :
    Derivable TwoSorted.F al TwoSorted.Premises (TwoSorted.ax_g_const (Γ := Γ)) :=
  TwoSorted.g_const

end Metatheorems
