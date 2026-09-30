/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RationalNumbers
import Metatheorems.Terms.Real

namespace Metatheorems

/-!
# Real Numbers in WE-HA^{ω}

Real numbers are encoded as rapidly converging Cauchy sequences of rationals.
Following §real-numbers of the reference document, the type of reals is
`1 = 0 → 0` (functions ℕ → ℕ), where `x(n)` encodes a rational approximation
to within 2^{-n}.

## Structure

1. **Cauchyfication**: `cauchyfy` (f ↦ f̂)
2. **Real operations**: `zero_R`, `one_R`, `add_R`, `neg_R`, `sub_R`, `mul_R`, `abs_R`
3. **Real formulas**: `eq_R`, `lt_R`, `le_R`, `le_R_pu`
4. **Ordered field axioms** — all proved; the ℝ layer has no `sorry`
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}

-- The term definitions (`cauchyfy`, `zero_R`, …, `abs_R`) and the formulas `eq_R`, `lt_R`,
-- `le_R`, `le_R_pu` live in `Metatheorems/Terms/Real.lean`.

namespace Term

end Term

-- Closed term substitution lemmas (real-level)

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

-- `cauchyfy_closed_subst`, `zero_R_closed_subst` and `one_R_closed_subst` live in
-- `Metatheorems/Terms/ClosedSubst.lean`.

@[simp] theorem embed_nat_R_closed_subst :
    (Term.embed_nat_R : Term F Γ _).subst σ = Term.embed_nat_R := by rfl
@[simp] theorem neg_R_closed_subst :
    (Term.neg_R : Term F Γ _).subst σ = Term.neg_R := by rfl
@[simp] theorem add_R_closed_subst :
    (Term.add_R : Term F Γ _).subst σ = Term.add_R := by
  simp only [Term.add_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_Q_closed_subst, cauchyfy_closed_subst]
@[simp] theorem sub_R_closed_subst :
    (Term.sub_R : Term F Γ _).subst σ = Term.sub_R := by
  simp only [Term.sub_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_R_closed_subst, neg_R_closed_subst]
@[simp] theorem mul_R_closed_subst :
    (Term.mul_R : Term F Γ _).subst σ = Term.mul_R := by
  simp only [Term.mul_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift, Term.ofNat,
    mul_Q_closed_subst, cauchyfy_closed_subst, add_closed_subst]
@[simp] theorem abs_R_closed_subst :
    (Term.abs_R : Term F Γ _).subst σ = Term.abs_R := by
  simp only [Term.abs_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    abs_Q_closed_subst, cauchyfy_closed_subst]

end ClosedSubst

-- The `cauchyfy` recursion, named
--
-- `cauchyfy` is a `prec` over a `pair(value, violation flag)` state, buried under two
-- lambdas. Nothing can be said about it until that state is a term one can name, so these
-- three definitions expose it, and `cauchyfy_unfold` is the single beta step that connects
-- them to `Term.cauchyfy` itself.

namespace Term

variable {Γ : Ctx ι}

/-- The base of `cauchyfy`'s recursion: `pair(f 0, 0)` — value `f 0`, flag clear. -/
def cauchyBase (f : Term F Γ (realTy ι)) : Term F Γ Ty.nat :=
  Term.app2 Term.pair (.app f .zero) .zero

/-- The step of `cauchyfy`'s recursion, as a function of `(state, index)`. -/
def cauchyStep (f : Term F Γ (realTy ι)) :
    Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
      (Term.app3 Term.ite_nat
        (.app Term.sg_bar (cauchy_check_at (f.weaken.weaken) (.var .vz)))
        (Term.app2 Term.pair
          (.app (f.weaken.weaken) (.app .succ (.var .vz))) .zero)
        (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
          (.app .succ .zero)))))

/-- The state of the recursion after `n` steps. `cauchyfy f n` is its first component. -/
def cauchyState (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app3 (.prec Ty.nat) (cauchyBase f) (cauchyStep f) n

-- The state's two components are `fst_pair (cauchyState f n)` — the value, which is
-- `cauchyfy f n` — and `snd_pair (cauchyState f n)` — the violation flag, `0` while the
-- Cauchy check has held at every index so far and `1` from the first failure onwards.
-- They are deliberately *not* given names: `prw` finds its pattern by descending through
-- `Term.app`/`app2`/`app3` nodes, and a named wrapper would hide `cauchyState` from it.

end Term

-- Following Kohlenbach's condition (m): (ℕ^ℕ, +_ℝ, ·_ℝ, 0_ℝ, 1_ℝ, <_ℝ) is an Archimedean
-- ordered RING, provably in WE-HA^ω — condition (m) minus division.

variable {al : Allowed} {Premises : PremiseSet F}

-- Notation: real-typed variables in context
abbrev rTy := realTy ι
-- In context [rTy, Γ]: f = var vz
-- In context [rTy, rTy, Γ]: f = var (vs vz), g = var vz
-- In context [rTy, rTy, rTy, Γ]: f = var (vs (vs vz)), g = var (vs vz), h = var vz

end Metatheorems
