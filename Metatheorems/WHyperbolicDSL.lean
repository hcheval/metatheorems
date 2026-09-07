/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Theory
import Metatheorems.WHyperbolic

/-!
# W-hyperbolic spaces, re-expressed in the `theory` DSL

`WHyperbolic.lean` lines 62–208 — signature, four axioms, premise set, the eight `_pu`/`_vf`
theorems, `premises_pu`/`premises_vf`, and the four `.premise` accessors — restated as one
`theory … endtheory` block.  **`WHyperbolic.lean` is not touched**; this is a parallel
declaration set, used to check the command against the hand-written original.

## What is and is not checked here

The generated formulas cannot be compared to `WHyperbolic.ax_W1` and friends by `rfl`,
because they live over a **different signature**: the command generates its own `WHypDSL.κ`
(an inductive with one constructor `W`) and `WHypDSL.F`, where the hand-written file uses
`κ = Unit`.  `Formula WHypDSL.F Γ` and `Formula WHyperbolic.F Γ` are different types, so no
equation between them is even well-formed, and transporting one to the other would need a
signature isomorphism that nothing in the project has.

What *is* checked, and it is the property that matters, is that the command produces
**exactly the de Bruijn spelling a person would have written**.  `expW1` … `expW4` below are
`WHyperbolic.ax_W1` … `ax_W4` transcribed character for character, with the two substitutions
`WHyperbolic.d ↦ (Term.dist ())` and `WHyperbolic.W ↦ WHypDSL.W` — nothing else is changed,
including every `Var.vs` chain — and each `example` closes `WHypDSL.ax_Wᵢ = expWᵢ` by `rfl`.
So the index arithmetic, which a reader of `WHyperbolic.lean` has to verify by counting
`.vs`es against a comment, is checked mechanically here.

The model side is **not** re-expressed.  `WHyperbolicModel.W1_holds` … `W4_holds` and
`axiomsHold` are stated over `WHyperbolic.F` terms, so discharging `WHypDSL.Obligations` for
a `WHyperbolicModel` would mean re-proving them at the new signature, not reusing them.  That
is a real cost of generating a fresh `κ`, and the reason a future version of the command
should be able to take an existing signature instead of generating one.
-/

set_option linter.style.emptyLine false

namespace Metatheorems

open Formula

/-- W-hyperbolic spaces: `ι = MetricSpace.ι`, one constant `W : X →ₜ X →ₜ ℝ →ₜ X`, the four
axioms of `WHyperbolic.lean` at `clamp01 λ`.

This block replaces `WHyperbolic.lean` lines 62–208 and contains **no de Bruijn index at
all** — the binder names `z x y λ` are written where the original writes
`.var (.vs (.vs (.vs .vz)))`. -/
theory WHypDSL
  index MetricSpace.ι
  types X := xTy
  types R := realTy MetricSpace.ι

  abbrev d := Term.dist ()
  abbrev clamp := Term.clamp01

  constants W : X →ₜ X →ₜ R →ₜ X

  axioms W1 (z x y : X) (l : R) :
    le_R_pu
      (Term.app2 d z (Term.app3 W x y (.app clamp l)))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app clamp l))
          (Term.app2 d z x))
        (Term.app2 Term.mul_R (.app clamp l) (Term.app2 d z y)))

  axioms W2 (x y : X) (l m : R) :
    eq_R
      (Term.app2 d
        (Term.app3 W x y (.app clamp l))
        (Term.app3 W x y (.app clamp m)))
      (Term.app2 Term.mul_R
        (.app Term.abs_R (Term.app2 Term.sub_R (.app clamp l) (.app clamp m)))
        (Term.app2 d x y))

  axioms W3 (x y : X) (l : R) :
    eqAtType X
      (Term.app3 W x y (.app clamp l))
      (Term.app3 W y x (Term.app2 Term.sub_R Term.one_R (.app clamp l)))

  axioms W4 (x y z w : X) (l : R) :
    le_R_pu
      (Term.app2 d
        (Term.app3 W x z (.app clamp l))
        (Term.app3 W y w (.app clamp l)))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app clamp l))
          (Term.app2 d x y))
        (Term.app2 Term.mul_R (.app clamp l) (Term.app2 d z w)))
endtheory

-- ============================================================================
-- The generated formulas, against `WHyperbolic.lean`'s own de Bruijn spellings
-- ============================================================================

namespace WHypDSL.Expected

/-- `WHyperbolic.ax_W1`, transcribed verbatim (`d ↦ (Term.dist ())`, `W ↦ WHypDSL.W`). -/
def expW1 {Γ : Ctx MetricSpace.ι} : Formula WHypDSL.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all rTy
    (le_R_pu
      (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz))))
        (Term.app3 WHypDSL.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))
          (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))))
        (Term.app2 Term.mul_R (.app Term.clamp01 (.var .vz))
          (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))))))))

/-- `WHyperbolic.ax_W2`, transcribed verbatim. -/
def expW2 {Γ : Ctx MetricSpace.ι} : Formula WHypDSL.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all rTy (Formula.all rTy
    (eq_R
      (Term.app2 (Term.dist ())
        (Term.app3 WHypDSL.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var (.vs .vz))))
        (Term.app3 WHypDSL.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.mul_R
        (.app Term.abs_R
          (Term.app2 Term.sub_R (.app Term.clamp01 (.var (.vs .vz)))
            (.app Term.clamp01 (.var .vz))))
        (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))))))))

/-- `WHyperbolic.ax_W3`, transcribed verbatim. -/
def expW3 {Γ : Ctx MetricSpace.ι} : Formula WHypDSL.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all rTy
    (eqAtType xTy
      (Term.app3 WHypDSL.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
        (.app Term.clamp01 (.var .vz)))
      (Term.app3 WHypDSL.W (.var (.vs .vz)) (.var (.vs (.vs .vz)))
        (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))))))

/-- `WHyperbolic.ax_W4`, transcribed verbatim. -/
def expW4 {Γ : Ctx MetricSpace.ι} : Formula WHypDSL.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all rTy
    (le_R_pu
      (Term.app2 (Term.dist ())
        (Term.app3 WHypDSL.W (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var .vz)))
        (Term.app3 WHypDSL.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))
          (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs (.vs .vz)))))
            (.var (.vs (.vs (.vs .vz))))))
        (Term.app2 Term.mul_R (.app Term.clamp01 (.var .vz))
          (Term.app2 (Term.dist ()) (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))))

end WHypDSL.Expected

section DeBruijn

open WHypDSL.Expected

variable {Γ : Ctx MetricSpace.ι}

/-- **The check.**  The command's output and `WHyperbolic.lean`'s hand-written de Bruijn
spelling are the same formula, at every context. -/
example : (WHypDSL.ax_W1 (Γ := Γ)) = expW1 := rfl
example : (WHypDSL.ax_W2 (Γ := Γ)) = expW2 := rfl
example : (WHypDSL.ax_W3 (Γ := Γ)) = expW3 := rfl
example : (WHypDSL.ax_W4 (Γ := Γ)) = expW4 := rfl

end DeBruijn

-- ============================================================================
-- The rest of the boilerplate, generated
-- ============================================================================

section Generated

/-- The signature. -/
example : WHypDSL.F WHypDSL.κ.W = (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy) := rfl

-- The eight admissibility theorems `WHyperbolic.lean:144–160` writes out by hand.
example : (WHypDSL.ax_W1 (Γ := ([] : Ctx MetricSpace.ι))).isPurelyUniversal = true :=
  WHypDSL.ax_W1_pu
example : (WHypDSL.ax_W2 (Γ := ([] : Ctx MetricSpace.ι))).isVFree = true := WHypDSL.ax_W2_vf
example : (WHypDSL.ax_W3 (Γ := ([] : Ctx MetricSpace.ι))).isPurelyUniversal = true :=
  WHypDSL.ax_W3_pu
example : (WHypDSL.ax_W4 (Γ := ([] : Ctx MetricSpace.ι))).isVFree = true := WHypDSL.ax_W4_vf

-- `WHyperbolic.lean:175–186`.
example : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHypDSL.F Γ'),
    WHypDSL.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := WHypDSL.premises_pu
example : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHypDSL.F Γ'),
    WHypDSL.Premises ⟨Γ', B⟩ → B.isVFree = true := WHypDSL.premises_vf

-- The four `.premise` accessors, `WHyperbolic.lean:191–208`, with their `Or.inr` chains.
example {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHypDSL.F a WHypDSL.Premises (WHypDSL.ax_W1 (Γ := Γ)) := WHypDSL.W1
example {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHypDSL.F a WHypDSL.Premises (WHypDSL.ax_W2 (Γ := Γ)) := WHypDSL.W2
example {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHypDSL.F a WHypDSL.Premises (WHypDSL.ax_W3 (Γ := Γ)) := WHypDSL.W3
example {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHypDSL.F a WHypDSL.Premises (WHypDSL.ax_W4 (Γ := Γ)) := WHypDSL.W4

/-- And the obligations `WHyperbolic.lean` discharges by hand as `W1_holds` … `W4_holds`:
four named fields, generated, plus the `axiomsHold` and `spremise` that consume them. -/
example {X : MetricSpace.ι → Type} {si : SpaceInterp X WHypDSL.F}
    (o : WHypDSL.Obligations si) :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHypDSL.F Γ'),
      WHypDSL.Premises ⟨Γ', B⟩ → SRealizer si B :=
  WHypDSL.spremise o

/-- The majorant obligation, in the shape `WHyperbolicModel.constMajorants` fills in.  What
it does **not** supply is `WMajorant = λn₁ n₂ _.max n₁ n₂` or its proof: those come from
(W1) at the reference point, and are the mathematics of the instantiation. -/
example {X : MetricSpace.ι → Type} {si : SpaceInterp X WHypDSL.F}
    {am : AbstractMajorizability si} (m : WHypDSL.Majorants am) :
    ∀ (c : WHypDSL.κ), ∀ (n : Nat), n ≥ am.N →
      am.maj (WHypDSL.F c) (WHypDSL.Majorants.funcM m c n) (si.funcInterp c) :=
  WHypDSL.Majorants.funcM_maj m

end Generated

end Metatheorems
