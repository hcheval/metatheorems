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

## Two theories

**`WHypDSL`** (first half) lets the command generate its own `κ` and `F`; it is compared
with `WHyperbolic.lean` by `rfl` on the de Bruijn spelling (`expW1` … `expW4`).

**`WHypSig`** (second half) uses the `signature` clause to take `WHyperbolic.κ` and
`WHyperbolic.F`, so the comparison is direct: `WHypSig.ax_Wᵢ = WHyperbolic.ax_Wᵢ` and
`WHypSig.Premises = WHyperbolic.Premises` by `rfl`, and `WHyperbolicModel.w_metatheorem` comes
back out of the generated `WHypSig.metatheorem` applied to a model.

The model, `si`, `W1_holds` … `W4_holds`, `WMajorant`, `abstractMajorizability` and
`constMajorants` remain hand-written in `WHyperbolic.lean`.
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

-- The generated formulas, against `WHyperbolic.lean`'s own de Bruijn spellings

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

-- The rest of the boilerplate, generated

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

/-- **`WHyperbolicModel.w_metatheorem`, generated.**  Statement for statement the same, with
the model's three contributions — `M.eqXInterp`, `M.axiomsHold`, `M.abstractMajorizability` —
appearing as the three explicit hypotheses instead of being supplied by the model.  Feeding
it a `WHyperbolicModel` is the step this file does not take (see the header): the model's
`W1_holds` … `W4_holds` are over `WHyperbolic.F`, not `WHypDSL.F`. -/
example {X : MetricSpace.ι → Type} {si : SpaceInterp X WHypDSL.F}
    (eqxi : EqXInterp X WHypDSL.F si) (o : WHypDSL.Obligations si)
    (am : AbstractMajorizability si)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHypDSL.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHypDSL.κ WHypDSL.F Allowed.extended WHypDSL.Premises []
      (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀) (Formula.ex Ty.nat C₀)))) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        am.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) :=
  WHypDSL.metatheorem eqxi o am hB_qf hB_vf hC_qf hC_vf prf

end Generated

-- The `signature` clause: the same theory OVER `WHyperbolic.F` itself

/-!
`WHypDSL` above generates its own `κ` and `F`, which is what makes it a parallel declaration
set rather than a replacement.  With a `signature` clause the command generates neither, and
takes the existing ones instead — so the formulas it emits are `Formula WHyperbolic.F Γ` on
the nose and every comparison below is a `rfl` against `WHyperbolic.lean`'s own declarations.
-/

/-- W-hyperbolic spaces again, this time over `WHyperbolic.κ` / `WHyperbolic.F`. -/
theory WHypSig
  index MetricSpace.ι
  signature WHyperbolic.κ := WHyperbolic.F

  types X := xTy
  types R := realTy MetricSpace.ι

  abbrev d := Term.dist ()
  abbrev clamp := Term.clamp01

  constants W : X →ₜ X →ₜ R →ₜ X := ()

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

section AgainstTheOriginal

variable {Γ : Ctx MetricSpace.ι}

/-- **The four axioms are `WHyperbolic.lean`'s, on the nose.**  Not "the same up to a
signature isomorphism" — the same term. -/
example : (WHypSig.ax_W1 (Γ := Γ)) = WHyperbolic.ax_W1 := rfl
example : (WHypSig.ax_W2 (Γ := Γ)) = WHyperbolic.ax_W2 := rfl
example : (WHypSig.ax_W3 (Γ := Γ)) = WHyperbolic.ax_W3 := rfl
example : (WHypSig.ax_W4 (Γ := Γ)) = WHyperbolic.ax_W4 := rfl

/-- And therefore so is the premise set. -/
example : WHypSig.Premises = WHyperbolic.Premises := rfl

/-- So derivations pass between the two without transport: the hand-written accessor proves
the generated axiom and vice versa. -/
example {al : Allowed} :
    Derivable WHypSig.F al WHypSig.Premises (WHypSig.ax_W1 (Γ := Γ)) := WHyperbolic.W1
example {al : Allowed} :
    Derivable WHyperbolic.F al WHyperbolic.Premises (WHyperbolic.ax_W4 (Γ := Γ)) :=
  WHypSig.W4

/-- **And the model discharges the generated obligations.**  `WHyperbolicModel.axiomsHold` —
proved once, by hand, in `WHyperbolic.lean` — inhabits the structure the command emitted,
with no transport and no re-proof. -/
def WHyperbolicModel.whypSigObligations (M : WHyperbolicModel) : WHypSig.Obligations M.si where
  W1 := fun env => M.axiomsHold _ (Or.inl rfl) env
  W2 := fun env => M.axiomsHold _ (Or.inr (Or.inl rfl)) env
  W3 := fun env => M.axiomsHold _ (Or.inr (Or.inr (Or.inl rfl))) env
  W4 := fun env => M.axiomsHold _ (Or.inr (Or.inr (Or.inr rfl))) env

/-- **The generated metatheorem, applied to a real model.**  This is
`WHyperbolicModel.w_metatheorem` obtained from the `theory` block plus the model, rather than
written out — the DSL replacing `WHyperbolic.lean`'s syntactic half rather than paralleling
it. -/
theorem WHyperbolicModel.w_metatheorem_dsl (M : WHyperbolicModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHypSig.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHypSig.κ WHypSig.F Allowed.extended WHypSig.Premises []
      (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀) (Formula.ex Ty.nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  WHypSig.metatheorem M.eqXInterp M.whypSigObligations M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

end AgainstTheOriginal

#print axioms WHypSig.premises_pu
#print axioms WHypSig.W1
#print axioms WHypSig.metatheorem
#print axioms WHyperbolicModel.whypSigObligations
#print axioms WHyperbolicModel.w_metatheorem_dsl

end Metatheorems
