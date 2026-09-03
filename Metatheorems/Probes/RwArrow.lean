/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Rewrite

/-!
# Probe RwArrow: rewriting at an *arrow* type

`RwBase.lean` exercised `prw` with a pattern at a base type `Ty.base ()`. The real-number
layer needs the other untested case: a pattern at `nat →ₜ nat`, because `eq_R f g` compares
`cauchyfy f` with `cauchyfy g` and `cauchyfy` takes its argument as a *function*.

`eqAtType (nat →ₜ nat) f g` unfolds to `∀x. f x =₀ g x`, so pointwise equality of two
sequences is literally the arrow-type instance of QF-ER. This file checks that `prw` can
actually consume such a rule.

**Result: `prw` works; `prwby` cannot and never will.** `prwby` instantiates QF-ER's premise
`A₀` with the hypothesis's own formula and discharges `A₀.isQF = true` by `rfl`; at an arrow
type that formula is a `Formula.all`, so it is not quantifier-free. Function-typed rewriting
is therefore available only from *closed* rules (`prw`), never from a hypothesis.
-/

namespace Metatheorems
namespace Probes

open Formula ProofMode

variable {ι κ : Type} {F : κ → Ty ι}
  {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- The shape the reals need: a pointwise rule pushed under a function-typed argument
position. `k` stands for `cauchyfy`, `n` for the index. -/
example (f g : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ ((Ty.nat →ₜ Ty.nat) →ₜ Ty.nat →ₜ Ty.nat)) (n : Term F Γ Ty.nat)
    (h : Derivable F al Premises (eqAtType (Ty.nat →ₜ Ty.nat) f g)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app (Term.app k f) n) (Term.app (Term.app k g) n)) := by
  pmode
  prw h
  prefl

/-- The rule spelled in its unfolded `∀x. f x =₀ g x` form — this is what an actual
derivation will have, since `eqAtType` is a `def` by recursion on the type. -/
example (f g : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ ((Ty.nat →ₜ Ty.nat) →ₜ Ty.nat →ₜ Ty.nat)) (n : Term F Γ Ty.nat)
    (h : Derivable F al Premises
      (Formula.all Ty.nat (Formula.eq0
        (Term.app f.weaken (.var .vz)) (Term.app g.weaken (.var .vz))))) :
    Derivable F al Premises
      (Formula.eq0 (Term.app (Term.app k f) n) (Term.app (Term.app k g) n)) := by
  pmode
  prw (show Derivable F al Premises (eqAtType (Ty.nat →ₜ Ty.nat) f g) from h)
  prefl

/-- Two occurrences, one on each side of the goal, under arithmetic. -/
example (f g h' : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ ((Ty.nat →ₜ Ty.nat) →ₜ Ty.nat →ₜ Ty.nat)) (n : Term F Γ Ty.nat)
    (h : Derivable F al Premises (eqAtType (Ty.nat →ₜ Ty.nat) f g)) :
    Derivable F al Premises
      (Formula.eq0
        (Term.app2 Term.add (Term.app (Term.app k f) n) (Term.app (Term.app k h') n))
        (Term.app2 Term.add (Term.app (Term.app k g) n) (Term.app (Term.app k h') n))) := by
  pmode
  prw h
  prefl

end Probes
end Metatheorems
