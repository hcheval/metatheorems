/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Rewrite

/-!
# Probe RwBase: rewriting at a base type

`prw` used to hardcode the *pattern's* type to `nat` — `let ρ := Ty.nat` in `prwCore` — even
though `Derivable.qfer` was always general in it. This is the case that hardcoding excluded,
and it is the one metric spaces need: the points live in `X`, the distances in `ℕ`, so a
rewrite `s ↦ s'` has a base-typed pattern inside a numeric goal.

One base type and one function symbol `f : X → ℕ`, which is the shape of a metric `d` with
one argument fixed. These are regression tests, so they are in the build.
-/

namespace Metatheorems
namespace Probes

open Formula ProofMode

/-- One base type `X`; the single function symbol has type `X → ℕ`. -/
private abbrev ιX := Unit

private def FX : ιX → Ty ιX := fun _ => Ty.base () →ₜ Ty.nat

/-- `f`, standing in for a metric with one argument fixed. -/
private abbrev fX {Γ : Ctx ιX} : Term FX Γ (Ty.base () →ₜ Ty.nat) := Term.func ()

variable
  {al : Allowed} {Premises : PremiseSet FX} {Γ : Ctx ιX}

/-- The pattern is at `Ty.base ()`, the goal at `nat`. Equality at a base type used to be the
abstract `EqX () s s'`, identified by comparing the head against the goal's own `EqX`
parameter; with `EqX` gone it is a genuine `eqAtType` application, and the folded match in
`eqView?` covers it. -/
example (s s' : Term FX Γ (Ty.base ()))
    (h : Derivable FX al Premises (eqAtType (Ty.base ()) s s')) :
    Derivable FX al Premises
      (Formula.eq0 (Term.app fX s) (Term.app fX s')) := by
  pmode
  prw h
  prefl

/-- The same rule spelled through `eqAtType`, the other folded presentation. -/
example (s s' : Term FX Γ (Ty.base ()))
    (h : Derivable FX al Premises (eqAtType (Ty.base ()) s s')) :
    Derivable FX al Premises
      (Formula.eq0 (Term.app fX s) (Term.app fX s')) := by
  pmode
  prw h
  prefl

/-- A base-typed rewrite under arithmetic: the pattern occurs twice, on both sides. -/
example (s s' t : Term FX Γ (Ty.base ()))
    (h : Derivable FX al Premises (eqAtType (Ty.base ()) s s')) :
    Derivable FX al Premises
      (Formula.eq0 (Term.app2 Term.add (Term.app fX s) (Term.app fX t))
                   (Term.app2 Term.add (Term.app fX s') (Term.app fX t))) := by
  pmode
  prw h
  prefl

/-- `nat` rewriting is unchanged — the same tactic, the same path, `Formula.eq0` spelling. -/
example (x y : Term FX Γ Ty.nat)
    (h : Derivable FX al Premises (Formula.eq0 x y)) :
    Derivable FX al Premises
      (Formula.eq0 (Term.app2 Term.add x x) (Term.app2 Term.add y y)) := by
  pmode
  prw h
  prefl

end Probes
end Metatheorems
