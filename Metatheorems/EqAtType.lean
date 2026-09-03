/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Terms.ClosedSubst

namespace Metatheorems

/-!
# Higher-type equality

Split out of `Language.lean` because equality at a base type is **defined** as
`d_i(s,t) =ℝ 0ℝ`, so this file must sit above the ℚ/ℝ term layer — while `Language.lean`,
which defines `Formula`, must sit below it. `eqAtType` was the last declaration in
`Language.lean` and had no dependants inside it, so only this 30-line tail moved.

The old `EqX` parameter is gone. It used to let each theory choose its own base-type
equality, at the cost of an `AdmissibleEqX` record threaded through ~2,700 call sites whose
refl/sym/trans fields could not be discharged for a *defined* equality without circularity.
With `Term.dist` structural and the pseudometric axioms as constructors of `Derivable`,
those three become ordinary theorems. See ARCHITECTURE.md.
-/

/-- Higher-type equality at type ρ (Definition 2.2.3 / Definition 2.3.3).

For terms s, t of type ρ = ρ₁ → ... → ρₖ → ρ₀ (where ρ₀ is ground):
  s =_ρ t  :≡  ∀x₁^ρ₁. ... ∀xₖ^ρₖ. (s x₁ ... xₖ =_{ρ₀} t x₁ ... xₖ)

At ground type 0, this is s =₀ t.
At base type X_i, this is `d_i(s,t) =ℝ 0ℝ` — Kohlenbach's definition of `=_X`, no longer a
parameter. It is Π⁰₁ by construction, which is what the negative translation needs. -/
def eqAtType {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} :
    (ρ : Ty ι) → Term F Γ ρ → Term F Γ ρ → Formula F Γ
  | Ty.nat,      s, t => Formula.eq0 s t
  | Ty.base i,   s, t => eq_R (Term.app2 (Term.dist i) s t) Term.zero_R
  -- all inhabitants of `unit` are equal, so this is trivially true
  | Ty.unit,     _, _ => Formula.eq0 Term.zero Term.zero
  | Ty.prod ρ τ, s, t =>
      Formula.and (eqAtType ρ (Term.fst s) (Term.fst t))
        (eqAtType τ (Term.snd s) (Term.snd t))
  | Ty.arr ρ τ,  s, t =>
      -- ∀x^ρ. (s x =_τ t x)
      Formula.all ρ (eqAtType τ
        (Term.app s.weaken (.var .vz))
        (Term.app t.weaken (.var .vz)))

/-- Equality at a base type is purely universal — `eq_R` is `∀n. QF` by construction.

This was the `eqx_pu` field of `AdmissibleEqX`; with `EqX` fixed it is a theorem. -/
theorem eqAtType_base_isPurelyUniversal {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} (i : ι)
    (s t : Term F Γ (Ty.base i)) :
    (eqAtType (Ty.base i) s t).isPurelyUniversal = true := by rfl

/-- Equality at a base type commutes with substitution.

This was the `substF_nat` field of `AdmissibleEqX`; with `EqX` fixed to `d_i(·,·) =ℝ 0ℝ` it
is a theorem, from `eq_R_substF` plus the fact that `Term.dist i` and `Term.zero_R` are
closed. It is the base case of `eqAtType_substF` in `Arithmetic.lean`. -/
theorem eqAtType_base_substF {ι κ : Type} {F : κ → Ty ι} {Γ Δ : Ctx ι} (i : ι)
    (u v : Term F Γ (Ty.base i)) (σ : Term.Subst F Γ Δ) :
    (eqAtType (Ty.base i) u v).substF σ
      = eqAtType (Ty.base i) (u.subst σ) (v.subst σ) := by
  simp only [eqAtType, eq_R_substF, Term.app2, Term.subst, zero_R_closed_subst]

end Metatheorems
