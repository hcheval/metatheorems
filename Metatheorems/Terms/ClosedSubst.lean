/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Terms.Real
import Metatheorems.SimpSets

namespace Metatheorems

/-!
# Closed-substitution lemmas for the arithmetic / ℚ / ℝ term layer

Every constant in `Terms/Arith.lean`, `Terms/Rational.lean` and `Terms/Real.lean` is a
closed term, so `subst σ` leaves it alone. These lemmas say so, and they seed the
`closed_subst` simp set. Also `eq_R_substF` / `le_R_pu_substF` and the two purely-universal
facts, which `eqAtType_substF` (`Arithmetic.lean`) needs below the ℚ/ℝ proof layer.

Do not prove `subst σ X = X` by `rfl` for a nested closed constant: that forces its whole
delta-expansion. The proofs below unfold one level and stop at constants already known
closed, so the `closed_subst` set is built up as the proofs go.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

-- Arithmetic constants

/-- `Term.pd` is closed. Public: proof scripts need it in the goal-normalising simp set. -/
theorem pd_closed_subst :
    Term.subst σ (Term.pd : Term F Γ _) = Term.pd := by rfl

/-- The terms defined in `Terms/Arith.lean` are closed, so substitution leaves them alone.
Public because a proof script has to see through the substitutions that `induction` leaves in
a goal — see `ProofMode/Arith.lean`. -/
theorem mul_closed_subst :
    (Term.mul : Term F Γ _).subst σ = Term.mul := by rfl

theorem monus_closed_subst :
    (Term.monus : Term F Γ _).subst σ = Term.monus := by rfl

theorem abs_diff_closed_subst :
    (Term.abs_diff : Term F Γ _).subst σ = Term.abs_diff := by rfl

theorem sg_bar_closed_subst :
    (Term.sg_bar : Term F Γ _).subst σ = Term.sg_bar := by rfl

/-- `Term.add` is closed, so substitution leaves it alone. Public for the same reason. -/
theorem add_closed_subst :
    Term.subst σ (Term.add : Term F Γ _) = Term.add := by rfl

attribute [closed_subst] pd_closed_subst mul_closed_subst monus_closed_subst
  abs_diff_closed_subst sg_bar_closed_subst add_closed_subst

-- Rational constants

attribute [simp] add_closed_subst mul_closed_subst monus_closed_subst abs_diff_closed_subst
  pd_closed_subst sg_bar_closed_subst
@[simp] theorem sg_closed_subst :
    (Term.sg : Term F Γ _).subst σ = Term.sg := by rfl
@[simp] theorem isEven_closed_subst :
    (Term.isEven : Term F Γ _).subst σ = Term.isEven := by rfl
@[simp] theorem isOdd_closed_subst :
    (Term.isOdd : Term F Γ _).subst σ = Term.isOdd := by rfl
@[simp] theorem triag_closed_subst :
    (Term.triag : Term F Γ _).subst σ = Term.triag := by rfl
@[simp] theorem exp2_closed_subst :
    (Term.exp2 : Term F Γ _).subst σ = Term.exp2 := by rfl
@[simp] theorem ite_nat_closed_subst :
    (Term.ite_nat : Term F Γ _).subst σ = Term.ite_nat := by rfl
@[simp] theorem geq_closed_subst :
    (Term.geq : Term F Γ _).subst σ = Term.geq := by rfl
@[simp] theorem max_closed_subst :
    (Term.max : Term F Γ _).subst σ = Term.max := by rfl
@[simp] theorem min_closed_subst :
    (Term.min : Term F Γ _).subst σ = Term.min := by rfl
@[simp] theorem pair_closed_subst :
    (Term.pair : Term F Γ _).subst σ = Term.pair := by rfl
@[simp] theorem inv_triag_closed_subst :
    (Term.inv_triag : Term F Γ _).subst σ = Term.inv_triag := by rfl
@[simp] theorem fst_pair_closed_subst :
    (Term.fst_pair : Term F Γ _).subst σ = Term.fst_pair := by rfl
@[simp] theorem snd_pair_closed_subst :
    (Term.snd_pair : Term F Γ _).subst σ = Term.snd_pair := by rfl

-- From here the definitions nest, so the proofs are compositional: unfold one level, push
-- `subst` through the application spine, and stop at the constants already known closed.
attribute [closed_subst] sg_closed_subst isEven_closed_subst isOdd_closed_subst
  triag_closed_subst exp2_closed_subst ite_nat_closed_subst geq_closed_subst
  max_closed_subst min_closed_subst pair_closed_subst inv_triag_closed_subst
  fst_pair_closed_subst snd_pair_closed_subst

@[simp] theorem div2_closed_subst :
    (Term.div2 : Term F Γ _).subst σ = Term.div2 := by
  simp only [Term.div2, Term.subst, Term.Subst.ext, Term.app2, Term.app3, closed_subst]
  all_goals rfl
@[simp] theorem rat_num_closed_subst :
    (Term.rat_num : Term F Γ _).subst σ = Term.rat_num := by
  simp only [Term.rat_num, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl
@[simp] theorem rat_den_closed_subst :
    (Term.rat_den : Term F Γ _).subst σ = Term.rat_den := by
  simp only [Term.rat_den, Term.subst, Term.Subst.ext, closed_subst]
  all_goals rfl
@[simp] theorem rat_sign_closed_subst :
    (Term.rat_sign : Term F Γ _).subst σ = Term.rat_sign := by
  simp only [Term.rat_sign, Term.subst, Term.Subst.ext, closed_subst]
  all_goals rfl
@[simp] theorem rat_encode_closed_subst :
    (Term.rat_encode : Term F Γ _).subst σ = Term.rat_encode := by
  simp only [Term.rat_encode, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl

attribute [closed_subst] div2_closed_subst rat_num_closed_subst rat_den_closed_subst
  rat_sign_closed_subst rat_encode_closed_subst

@[simp] theorem neg_Q_closed_subst :
    (Term.neg_Q : Term F Γ _).subst σ = Term.neg_Q := by
  simp only [Term.neg_Q, Term.subst, Term.Subst.ext, Term.app2, Term.app3, closed_subst]
  all_goals rfl
@[simp] theorem add_Q_closed_subst :
    (Term.add_Q : Term F Γ _).subst σ = Term.add_Q := by
  simp only [Term.add_Q, Term.subst, Term.Subst.ext, Term.app2, Term.app3, closed_subst]
  all_goals rfl

attribute [closed_subst] neg_Q_closed_subst add_Q_closed_subst

@[simp] theorem sub_Q_closed_subst :
    (Term.sub_Q : Term F Γ _).subst σ = Term.sub_Q := by
  simp only [Term.sub_Q, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl
@[simp] theorem mul_Q_closed_subst :
    (Term.mul_Q : Term F Γ _).subst σ = Term.mul_Q := by
  simp only [Term.mul_Q, Term.subst, Term.Subst.ext, Term.app2, Term.app3, closed_subst]
  all_goals rfl
@[simp] theorem abs_Q_closed_subst :
    (Term.abs_Q : Term F Γ _).subst σ = Term.abs_Q := by
  simp only [Term.abs_Q, Term.subst, Term.Subst.ext, Term.app3, closed_subst]
  all_goals rfl

attribute [closed_subst] sub_Q_closed_subst mul_Q_closed_subst abs_Q_closed_subst

@[simp] theorem lt_Q_dec_closed_subst :
    (Term.lt_Q_dec : Term F Γ _).subst σ = Term.lt_Q_dec := by
  simp only [Term.lt_Q_dec, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl
@[simp] theorem le_Q_dec_closed_subst :
    (Term.le_Q_dec : Term F Γ _).subst σ = Term.le_Q_dec := by
  simp only [Term.le_Q_dec, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl
@[simp] theorem eq_Q_dec_closed_subst :
    (Term.eq_Q_dec : Term F Γ _).subst σ = Term.eq_Q_dec := by
  simp only [Term.eq_Q_dec, Term.subst, Term.Subst.ext, Term.app2, closed_subst]
  all_goals rfl
@[simp] theorem encode_nat_Q_closed_subst :
    (Term.encode_nat_Q : Term F Γ _).subst σ = Term.encode_nat_Q := by rfl
@[simp] theorem pow2neg_Q_closed_subst :
    (Term.pow2neg_Q : Term F Γ _).subst σ = Term.pow2neg_Q := by rfl
@[simp] theorem zero_Q_closed_subst :
    (Term.zero_Q : Term F Γ _).subst σ = Term.zero_Q := by rfl
@[simp] theorem one_Q_closed_subst :
    (Term.one_Q : Term F Γ _).subst σ = Term.one_Q := by rfl

/-- Numerals are closed. -/
@[simp] theorem ofNat_closed_subst (n : Nat) :
    (Term.ofNat n : Term F Γ Ty.nat).subst σ = Term.ofNat n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [Term.ofNat, Term.subst, ih]

attribute [closed_subst] lt_Q_dec_closed_subst le_Q_dec_closed_subst eq_Q_dec_closed_subst
  encode_nat_Q_closed_subst pow2neg_Q_closed_subst zero_Q_closed_subst one_Q_closed_subst
  ofNat_closed_subst

-- Real constants

@[simp] theorem cauchyfy_closed_subst :
    (Term.cauchyfy : Term F Γ _).subst σ = Term.cauchyfy := by
  simp only [Term.cauchyfy, Term.subst, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken, Term.rename, Term.Renaming.ext, Term.Renaming.shift,
    fst_pair_closed_subst, pair_closed_subst, snd_pair_closed_subst,
    lt_Q_dec_closed_subst, abs_Q_closed_subst, sub_Q_closed_subst,
    pow2neg_Q_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst]

attribute [closed_subst] cauchyfy_closed_subst
@[simp] theorem zero_R_closed_subst :
    (Term.zero_R : Term F Γ _).subst σ = Term.zero_R := by rfl
@[simp] theorem one_R_closed_subst :
    (Term.one_R : Term F Γ _).subst σ = Term.one_R := by rfl

end ClosedSubst

-- Naturality of the ℝ formulas

/-- `eq_R` is quantifier-free under the ∀n wrapper, so the whole formula
    is purely universal (Π₁⁰). -/
theorem eq_R_isPurelyUniversal {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) :
    (eq_R f g).isPurelyUniversal = true := by rfl

/-- `eq_R` commutes with substitution: naturality for the real equality formula.
    This is what makes `eqAtType_substF`'s base case go through. -/
theorem eq_R_substF {Γ Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (eq_R f g).substF σ = eq_R (f.subst σ) (g.subst σ) := by
  simp only [eq_R, Formula.substF, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext,
    lt_Q_dec_closed_subst, abs_Q_closed_subst, sub_Q_closed_subst,
    cauchyfy_closed_subst, pow2neg_Q_closed_subst]

theorem le_R_pu_isPurelyUniversal {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) :
    (le_R_pu f g).isPurelyUniversal = true := by rfl

/-- `le_R_pu` commutes with substitution. -/
theorem le_R_pu_substF {Γ Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (le_R_pu f g).substF σ = le_R_pu (f.subst σ) (g.subst σ) := by
  simp only [le_R_pu, Formula.substF, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext,
    le_Q_dec_closed_subst, sub_Q_closed_subst, cauchyfy_closed_subst,
    pow2neg_Q_closed_subst]

end Metatheorems
