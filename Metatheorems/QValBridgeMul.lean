/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.QValBridge

namespace Metatheorems

/-!
# The evaluation bridge, continued: `mul_Q` and the ℝ-layer operations

Continuing `QValBridge.lean` past `add_R`, this file adds

* `mulQN` / `interpret_mul_Q_fun` / `qval_mulQN` — the missing S2 rung;
* the application-level evaluation of every ℝ-layer constant the axioms use:
  `mul_R`, `neg_R`, `sub_R`, `abs_R`, `one_R`, `zero_R`.

Method unchanged: one constant per unfold, S1 lemmas for the rest.
-/

namespace QBridge

open Rounding

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type}

-- Section 1: `mul_Q`

/-- Mirror of `Term.mul_Q`, transcribed clause for clause: `sign = sg_bar |s₁ − s₂|`,
`num = p₁·p₂`, `den−1 = d₁·d₂ − 1`. In the exact shape the interpretation residual takes,
so `interpret_mul_Q_fun` closes by `rfl`. -/
def mulQN (m n : ℕ) : ℕ :=
  ratEncodeN
    (sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)))
    (ratNumN m * ratNumN n)
    (ratDenN m * ratDenN n - 1)

theorem interpret_mul_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.mul_Q (F := F) (Γ := Δ)) env = mulQN := by
  funext m n
  simp only [Term.mul_Q, Term.app2, Term.app3, Term.interpret,
    interpret_rat_sign_fun, interpret_rat_num_fun, interpret_rat_den_fun,
    interpret_mul_fun, interpret_sg_bar_fun, interpret_abs_diff_fun,
    interpret_rat_encode_fun, interpret_pd_fun']
  rfl

/-- **The S2 lemma for multiplication**: `Term.mul_Q` really denotes `*` on the rationals. -/
theorem qval_mulQN (m n : ℕ) : qval (mulQN m n) = qval m * qval n := by
  have hd₁ : 0 < ratDenN m := ratDenN_pos m
  have hd₂ : 0 < ratDenN n := ratDenN_pos n
  have hq₁ : (ratDenN m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq₂ : (ratDenN n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdd : 1 ≤ ratDenN m * ratDenN n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hden : ((ratDenN m * ratDenN n - 1 : ℕ) : ℚ) + 1
      = (ratDenN m : ℚ) * (ratDenN n : ℚ) := by
    push_cast [Nat.cast_sub hdd]
    ring
  rcases ratSignN_cases m with h₁ | h₁ <;> rcases ratSignN_cases n with h₂ | h₂
  · -- both negative: the product is positive
    have hs : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 1 := by
      simp only [sgBarN]; omega
    simp only [mulQN, hs]
    rw [qval_ratEncodeN, hden, qval_eq_of_parts m, qval_eq_of_parts n,
      if_neg (by omega : ¬ ratSignN m = 1), if_neg (by omega : ¬ ratSignN n = 1),
      if_pos (by norm_num : (1 : ℕ) % 2 = 1)]
    push_cast
    field_simp
  · -- m negative, n positive
    have hs : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
      simp only [sgBarN]; omega
    simp only [mulQN, hs]
    rw [qval_ratEncodeN, hden, qval_eq_of_parts m, qval_eq_of_parts n,
      if_neg (by omega : ¬ ratSignN m = 1), if_pos h₂,
      if_neg (by norm_num : ¬ (0 : ℕ) % 2 = 1)]
    push_cast
    field_simp
  · -- m positive, n negative
    have hs : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
      simp only [sgBarN]; omega
    simp only [mulQN, hs]
    rw [qval_ratEncodeN, hden, qval_eq_of_parts m, qval_eq_of_parts n,
      if_pos h₁, if_neg (by omega : ¬ ratSignN n = 1),
      if_neg (by norm_num : ¬ (0 : ℕ) % 2 = 1)]
    push_cast
    field_simp
  · -- both positive
    have hs : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 1 := by
      simp only [sgBarN]; omega
    simp only [mulQN, hs]
    rw [qval_ratEncodeN, hden, qval_eq_of_parts m, qval_eq_of_parts n,
      if_pos h₁, if_pos h₂, if_pos (by norm_num : (1 : ℕ) % 2 = 1)]
    push_cast
    field_simp

theorem qval_interpret_mul_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ)
    (a b : ℕ) :
    qval (Term.interpret si (Term.mul_Q (F := F) (Γ := Δ)) env a b) = qval a * qval b := by
  rw [interpret_mul_Q_fun]
  exact qval_mulQN a b

-- Section 2: the ℝ-layer constants, function-level
--
-- Each is a thin `lam` wrapper over ℚ constants that already have their S1/S2
-- lemma, so each proof unfolds exactly the one wrapper. Stated function-level
-- (like `interpret_add_Q_fun`) so that they fire on the head of an application
-- spine; `interpret_add_R_app2` in `QValBridge.lean` is the application-level
-- special case of `interpret_add_R_fun`.

theorem interpret_add_R_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.add_R (F := F) (Γ := Δ)) env
      = fun f g n => addQN (cauchyfyN f (n + 1)) (cauchyfyN g (n + 1)) := by
  funext f g n
  simp only [Term.add_R, Term.app2, Term.interpret, interpret_add_Q_fun, interpret_cauchyfy_fun]
  rfl

/-- `mul_R f g n = mul_Q (f̂(n+b), ĝ(n+b))` with `b = f(0) + g(0) + 2` — the index shift is
part of the statement. -/
theorem interpret_mul_R_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.mul_R (F := F) (Γ := Δ)) env
      = fun f g n => mulQN (cauchyfyN f (n + (f 0 + g 0 + 2)))
          (cauchyfyN g (n + (f 0 + g 0 + 2))) := by
  funext f g n
  simp only [Term.mul_R, Term.app2, Term.interpret, interpret_mul_Q_fun, interpret_cauchyfy_fun,
    interpret_add_fun, interpret_ofNat]
  rfl

/-- `neg_R` negates the code pointwise — with **no** `cauchyfy` on its argument. -/
theorem interpret_neg_R_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.neg_R (F := F) (Γ := Δ)) env = fun f n => negQN (f n) := by
  funext f n
  simp only [Term.neg_R, Term.interpret, interpret_neg_Q_fun']
  rfl

theorem interpret_sub_R_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.sub_R (F := F) (Γ := Δ)) env
      = fun f g n => addQN (cauchyfyN f (n + 1)) (cauchyfyN (fun k => negQN (g k)) (n + 1)) := by
  funext f g n
  simp only [Term.sub_R, Term.app2, Term.interpret, interpret_add_R_fun, interpret_neg_R_fun]
  rfl

theorem interpret_abs_R_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.abs_R (F := F) (Γ := Δ)) env
      = fun f n => absQN (cauchyfyN f n) := by
  funext f n
  simp only [Term.abs_R, Term.interpret, interpret_abs_Q_fun, interpret_cauchyfy_fun]
  rfl

theorem interpret_one_R {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.one_R (F := F) (Γ := Δ)) env = fun _ => pairN 2 0 := by
  funext n
  simp only [Term.one_R, Term.interpret, interpret_one_Q]

theorem interpret_zero_R {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.zero_R (F := F) (Γ := Δ)) env = fun _ => pairN 0 0 := by
  funext n
  simp only [Term.zero_R, Term.interpret, interpret_zero_Q]

-- Axiom hygiene

#print axioms interpret_mul_Q_fun
#print axioms qval_mulQN
#print axioms qval_interpret_mul_Q
#print axioms interpret_add_R_fun
#print axioms interpret_mul_R_fun
#print axioms interpret_neg_R_fun
#print axioms interpret_sub_R_fun
#print axioms interpret_abs_R_fun
#print axioms interpret_one_R
#print axioms interpret_zero_R

end QBridge

end Metatheorems
