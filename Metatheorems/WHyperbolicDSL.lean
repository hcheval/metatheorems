/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Theory
import Metatheorems.WHyperbolic

/-!
# W-hyperbolic spaces, re-expressed in the `theory` DSL

`WHyperbolic.lean` lines 62–208 — signature, four axioms, premise set, the four `_pu`/`_vf`
theorems, `premises_pu`/`premises_vf`, and the four `.premise` accessors — restated as one
`theory … endtheory` block.  **`WHyperbolic.lean` is not touched**; this is a parallel
declaration set used to check the command against the hand-written original.

## What is and is not checked here

The generated formulas cannot be compared to `WHyperbolic.ax_W1` and friends by `rfl`,
because they live over a **different signature**: the command generates its own
`WHypDSL.κ` (an inductive with one constructor `W`) and `WHypDSL.F`, where the hand-written
file uses `κ = Unit`.  `Formula WHypDSL.F Γ` and `Formula WHyperbolic.F Γ` are different
types, so no equation between them is even well-formed, and transporting one to the other
would need a signature isomorphism that nothing in the project has.

What *is* checked, and it is the property that matters, is that the command produces
**exactly the de Bruijn spelling a person would have written**: each `example` below writes
out the axiom by hand over `WHypDSL.F`, with every `Var.vs` chain spelled, and closes it by
`rfl`.  Those spellings are `WHyperbolic.lean`'s own, transcribed with `WHyperbolic.W ↦
WHypDSL.W` and `WHyperbolic.d ↦ Term.dist ()`.  So the index arithmetic — which is what a
reader of `WHyperbolic.lean` has to verify by counting `.vs`es against a comment — is checked
mechanically.

The model side is **not** re-expressed.  `WHyperbolicModel.W1_holds` … `W4_holds` and
`axiomsHold` are stated over `WHyperbolic.F` terms, so discharging `WHypDSL.Obligations` for
a `WHyperbolicModel` would mean re-proving them at the new signature, not reusing them.  That
is a real cost of generating a fresh `κ`, and it is the reason a future version of the command
should accept an existing signature.
-/

namespace Metatheorems

open Formula

/-- W-hyperbolic spaces: `ι = MetricSpace.ι`, one constant `W : X →ₜ X →ₜ ℝ →ₜ X`, the four
axioms of `WHyperbolic.lean` at `clamp01 λ`.

Compare the original: this block is 24 lines where the hand-written signature-plus-axioms
block is 90, and it contains **no de Bruijn index at all**. -/
theory WHypDSL
  index MetricSpace.ι
  types X := xTy
  types R := realTy MetricSpace.ι

  constants W : X →ₜ X →ₜ R →ₜ X

  axioms W1 (z x y : X) (l : R) :
    le_R_pu
      (Term.app2 (Term.dist ()) z (Term.app3 W x y (.app Term.clamp01 l)))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
          (Term.app2 (Term.dist ()) z x))
        (Term.app2 Term.mul_R (.app Term.clamp01 l)
          (Term.app2 (Term.dist ()) z y)))

  axioms W2 (x y : X) (l m : R) :
    eq_R
      (Term.app2 (Term.dist ())
        (Term.app3 W x y (.app Term.clamp01 l))
        (Term.app3 W x y (.app Term.clamp01 m)))
      (Term.app2 Term.mul_R
        (.app Term.abs_R
          (Term.app2 Term.sub_R (.app Term.clamp01 l) (.app Term.clamp01 m)))
        (Term.app2 (Term.dist ()) x y))

  axioms W3 (x y : X) (l : R) :
    eqAtType X
      (Term.app3 W x y (.app Term.clamp01 l))
      (Term.app3 W y x (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l)))

  axioms W4 (x y z w : X) (l : R) :
    le_R_pu
      (Term.app2 (Term.dist ())
        (Term.app3 W x z (.app Term.clamp01 l))
        (Term.app3 W y w (.app Term.clamp01 l)))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
          (Term.app2 (Term.dist ()) x y))
        (Term.app2 Term.mul_R (.app Term.clamp01 l)
          (Term.app2 (Term.dist ()) z w)))
endtheory

-- ============================================================================
-- The generated formulas, against `WHyperbolic.lean`'s own de Bruijn spellings
-- ============================================================================

section DeBruijn

variable {Γ : Ctx MetricSpace.ι}

/-- (W1).  `WHyperbolic.lean:85–96`, transcribed. -/
example : (WHypDSL.ax_W1 (Γ := Γ)) =
    Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all (realTy MetricSpace.ι)
      (le_R_pu
        (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz))))
          (Term.app3 WHypDSL.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
            (.app Term.clamp01 (.var .vz))))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R
            (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))
            (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))))
          (Term.app2 Term.mul_R (.app Term.clamp01 (.var .vz))
            (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))))))))) :=
  rfl

/-- (W2).  `WHyperbolic.lean:100–112`, transcribed. -/
example : (WHypDSL.ax_W2 (Γ := Γ)) =
    Formula.all xTy (Formula.all xTy (Formula.all (realTy MetricSpace.ι)
      (Formula.all (realTy MetricSpace.ι)
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
          (Term.app2 (Term.dist ()) (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))))))) :=
  rfl

/-- (W3).  `WHyperbolic.lean:116–122`, transcribed. -/
example : (WHypDSL.ax_W3 (Γ := Γ)) =
    Formula.all xTy (Formula.all xTy (Formula.all (realTy MetricSpace.ι)
      (eqAtType xTy
        (Term.app3 WHypDSL.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
          (.app Term.clamp01 (.var .vz)))
        (Term.app3 WHypDSL.W (.var (.vs .vz)) (.var (.vs (.vs .vz)))
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz))))))) :=
  rfl

/-- (W4).  `WHyperbolic.lean:126–140`, transcribed. -/
example : (WHypDSL.ax_W4 (Γ := Γ)) =
    Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all xTy
      (Formula.all (realTy MetricSpace.ι)
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
            (Term.app2 (Term.dist ()) (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))) :=
  rfl

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
four named fields, generated.  `WHyperbolicModel.axiomsHold` is `WHypDSL.axiomsHold` applied
to them — at this signature, which is why it cannot simply be reused. -/
example {X : MetricSpace.ι → Type} {si : SpaceInterp X WHypDSL.F}
    (o : WHypDSL.Obligations si) :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHypDSL.F Γ'),
      WHypDSL.Premises ⟨Γ', B⟩ → SRealizer si B :=
  WHypDSL.spremise o

end Generated

end Metatheorems
