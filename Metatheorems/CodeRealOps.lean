/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.QValBridgeMul
import Metatheorems.CodeReal
import Metatheorems.RealNumbers.Interval

namespace Metatheorems

/-!
# `codeReal` is a homomorphism for the ℝ-layer operations

`CodeReal.lean` defines `codeReal f`, the real a code `f : ℕ → ℕ` denotes, and proves it is
bounded. This file makes it *usable* as the meaning of the object-level ℝ-layer:

1. **The approximation bound.** For **every** code `f` (Cauchy or not),
   `|qval (cauchyfyN f n) − codeReal f| < 2^{-n}` (`abs_qval_cauchyfyN_sub_codeReal_lt`).
   Strictness is essential and cheap: the non-strict bound at `n+1` plus one strict
   `cauchyfyN_step` gives the strict bound at `n`.
2. **The formula-level consequences.** `codeReal ⟦f⟧ ≤ codeReal ⟦g⟧` makes `f ≤ℝ g` true in
   the model, and `=` makes `f =ℝ g` true (`interpret_le_R_pu_of_codeReal_le`,
   `interpret_eq_R_of_codeReal_eq`). Both consume the bound at `n+1` on each side, and
   `2·2^{-(n+1)} = 2^{-n}` is exactly the budget — nothing to spare, nothing needed. This is
   the semantic mirror of CLAUDE.md's tightness triage for `eq_R`.
3. **The homomorphism lemmas.** `codeReal` of the code `add_R`/`mul_R`/`neg_R`/`abs_R`/
   `clamp01` produce is the corresponding real operation on `codeReal` of the arguments
   (`codeReal_addR`, `codeReal_mulR`, …). Each is one pattern: the produced sequence passes
   every Cauchy check (`IsCauchyCode`), so `cauchyfy` fixes it and `codeReal` is the limit of
   its rational values, which is the obvious one by continuity.

Together with `QValBridgeMul.lean`'s evaluation lemmas this is what lets a model fact on
Mathlib `ℝ` discharge an object-level axiom mentioning `·ℝ`, `−ℝ`, `|·|ℝ` and `clamp01` —
`WHyperbolicModel.axiomsHold` is the first client.
-/

open Rounding QBridge Filter Topology

-- ============================================================================
-- Section 1: the `clamp01` mirror
-- ============================================================================

namespace QBridge

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type}

@[simp] theorem iteN_one (x y : ℕ) : iteN 1 x y = x := by simp [iteN]
@[simp] theorem iteN_zero (x y : ℕ) : iteN 0 x y = y := by simp [iteN]

/-- Mirror of `Term.clamp01_Q`, clause for clause. -/
def clamp01QN (q : ℕ) : ℕ :=
  iteN (sgBarN (leQdecN q (pairN 0 0))) (pairN 0 0)
    (iteN (sgBarN (leQdecN (pairN 2 0) q)) (pairN 2 0) q)

theorem interpret_clamp01_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.clamp01_Q (F := F) (Γ := Δ)) env = clamp01QN := by
  funext q
  simp only [Term.clamp01_Q, Term.app2, Term.app3, Term.interpret, interpret_ite_nat_fun,
    interpret_sg_bar_fun, interpret_le_Q_dec_fun, interpret_zero_Q, interpret_one_Q]
  rfl

theorem interpret_clamp01_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.clamp01 (F := F) (Γ := Δ)) env
      = fun f n => clamp01QN (cauchyfyN f n) := by
  funext f n
  simp only [Term.clamp01, Term.app2, Term.interpret, interpret_clamp01_Q_fun,
    interpret_cauchyfy_fun]
  rfl

/-- The clamp on `ℚ`: `max 0 (min 1 q)`. -/
def clampQ (q : ℚ) : ℚ := max 0 (min 1 q)

/-- `Term.clamp01_Q` really clamps. -/
theorem qval_clamp01QN (q : ℕ) : qval (clamp01QN q) = clampQ (qval q) := by
  by_cases h0 : qval q ≤ 0
  · have hd : leQdecN q (pairN 0 0) = 0 :=
      (leQdecN_eq_zero_iff _ _).mpr (by rw [qval_zero_code]; exact h0)
    simp only [clamp01QN, hd, sgBarN, Nat.sub_zero, iteN_one, clampQ, qval_zero_code]
    rw [max_eq_left ((min_le_right _ _).trans h0)]
  · have hd : leQdecN q (pairN 0 0) ≠ 0 := fun h => h0 (by
      have := (leQdecN_eq_zero_iff _ _).mp h
      rwa [qval_zero_code] at this)
    have hs : sgBarN (leQdecN q (pairN 0 0)) = 0 := by simp only [sgBarN]; omega
    simp only [clamp01QN, hs, iteN_zero]
    push_neg at h0
    by_cases h1 : 1 ≤ qval q
    · have hd1 : leQdecN (pairN 2 0) q = 0 :=
        (leQdecN_eq_zero_iff _ _).mpr (by rw [qval_one_code]; exact h1)
      simp only [hd1, sgBarN, Nat.sub_zero, iteN_one, clampQ, qval_one_code]
      rw [min_eq_left h1, max_eq_right zero_le_one]
    · have hd1 : leQdecN (pairN 2 0) q ≠ 0 := fun h => h1 (by
        have := (leQdecN_eq_zero_iff _ _).mp h
        rwa [qval_one_code] at this)
      have hs1 : sgBarN (leQdecN (pairN 2 0) q) = 0 := by simp only [sgBarN]; omega
      simp only [hs1, iteN_zero, clampQ]
      push_neg at h1
      rw [min_eq_right h1.le, max_eq_right h0.le]

/-- Clamping is 1-Lipschitz. -/
theorem clampQ_lipschitz (a b : ℚ) : |clampQ a - clampQ b| ≤ |a - b| := by
  unfold clampQ
  calc |max 0 (min 1 a) - max 0 (min 1 b)|
      = |max (min 1 a) 0 - max (min 1 b) 0| := by rw [max_comm 0, max_comm 0]
    _ ≤ |min 1 a - min 1 b| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |(1 : ℚ) - 1| |a - b| := abs_min_sub_min_le_max _ _ _ _
    _ = |a - b| := by rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]

end QBridge

-- ============================================================================
-- Section 2: codes passing every check, and `codeReal` as a limit
-- ============================================================================

/-- A code passing the sharp Cauchy check at every index — exactly the hypothesis of
`cauchyfyN_id_of_cauchy`. -/
def IsCauchyCode (g : ℕ → ℕ) : Prop :=
  ∀ k, |qval (g k) - qval (g (k + 1))| < 1 / 2 ^ (k + 1)

/-- `cauchyfy` always produces one. -/
theorem isCauchyCode_cauchyfyN (f : ℕ → ℕ) : IsCauchyCode (cauchyfyN f) := fun k => by
  rw [abs_sub_comm]; exact cauchyfyN_step f k

theorem cauchyfyN_of_isCauchyCode {g : ℕ → ℕ} (hg : IsCauchyCode g) : cauchyfyN g = g :=
  funext (cauchyfyN_id_of_cauchy g hg)

theorem tendsto_qval_of_isCauchyCode {g : ℕ → ℕ} (hg : IsCauchyCode g) :
    Tendsto (fun n => ((qval (g n) : ℚ) : ℝ)) atTop (𝓝 (codeReal g)) := by
  have h := codeReal_tendsto g
  rwa [cauchyfyN_of_isCauchyCode hg] at h

/-- **The identification principle**: a Cauchy code denotes whatever its rational values
converge to. -/
theorem codeReal_eq_of_tendsto {g : ℕ → ℕ} (hg : IsCauchyCode g) {L : ℝ}
    (hL : Tendsto (fun n => ((qval (g n) : ℚ) : ℝ)) atTop (𝓝 L)) : codeReal g = L :=
  tendsto_nhds_unique (tendsto_qval_of_isCauchyCode hg) hL

-- ============================================================================
-- Section 3: the approximation bound, for every code
-- ============================================================================

theorem two_halves_Q (n : ℕ) : (1 : ℚ) / 2 ^ (n + 1) + 1 / 2 ^ (n + 1) = 1 / 2 ^ n := by
  rw [pow_succ]; field_simp; norm_num

theorem two_halves_R (n : ℕ) : (1 : ℝ) / 2 ^ (n + 1) + 1 / 2 ^ (n + 1) = 1 / 2 ^ n := by
  rw [pow_succ]; field_simp; norm_num

/-- Telescoped `cauchyfyN_step`: from index `n` on, the value moves by less than `2^{-n}`
in total, with `2^{-(n+k)}` to spare. -/
theorem cauchyfyN_tail_le (f : ℕ → ℕ) (n : ℕ) : ∀ k : ℕ,
    |qval (cauchyfyN f (n + k)) - qval (cauchyfyN f n)| ≤ 1 / 2 ^ n - 1 / 2 ^ (n + k)
  | 0 => by simp
  | k + 1 => by
      have ih := cauchyfyN_tail_le f n k
      have hs := cauchyfyN_step f (n + k)
      have hh := two_halves_Q (n + k)
      change |qval (cauchyfyN f (n + k + 1)) - qval (cauchyfyN f n)|
          ≤ 1 / 2 ^ n - 1 / 2 ^ (n + k + 1)
      calc |qval (cauchyfyN f (n + k + 1)) - qval (cauchyfyN f n)|
          = |(qval (cauchyfyN f (n + k + 1)) - qval (cauchyfyN f (n + k)))
              + (qval (cauchyfyN f (n + k)) - qval (cauchyfyN f n))| := by
            rw [sub_add_sub_cancel]
        _ ≤ |qval (cauchyfyN f (n + k + 1)) - qval (cauchyfyN f (n + k))|
              + |qval (cauchyfyN f (n + k)) - qval (cauchyfyN f n)| := abs_add_le _ _
        _ ≤ 1 / 2 ^ (n + k + 1) + (1 / 2 ^ n - 1 / 2 ^ (n + k)) := add_le_add hs.le ih
        _ = 1 / 2 ^ n - 1 / 2 ^ (n + k + 1) := by linarith

/-- `|f̂(n) − codeReal f| ≤ 2^{-n}`, by passing `cauchyfyN_tail_le` to the limit. -/
theorem abs_qval_cauchyfyN_sub_codeReal_le (f : ℕ → ℕ) (n : ℕ) :
    |((qval (cauchyfyN f n) : ℚ) : ℝ) - codeReal f| ≤ 1 / 2 ^ n := by
  have hlim : Tendsto
      (fun m => |((qval (cauchyfyN f n) : ℚ) : ℝ) - ((qval (cauchyfyN f m) : ℚ) : ℝ)|)
      atTop (𝓝 |((qval (cauchyfyN f n) : ℚ) : ℝ) - codeReal f|) :=
    (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub (codeReal_tendsto f))
  refine le_of_tendsto hlim ?_
  rw [Filter.eventually_atTop]
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hq : |qval (cauchyfyN f n) - qval (cauchyfyN f (n + k))| ≤ 1 / 2 ^ n := by
    rw [abs_sub_comm]
    refine (cauchyfyN_tail_le f n k).trans ?_
    have : (0 : ℚ) ≤ 1 / 2 ^ (n + k) := by positivity
    linarith
  have hr : ((|qval (cauchyfyN f n) - qval (cauchyfyN f (n + k))| : ℚ) : ℝ)
      ≤ ((1 / 2 ^ n : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hr
  exact hr

/-- **The approximation bound, strict**: `|f̂(n) − codeReal f| < 2^{-n}` for every code `f`.
One strict step plus the non-strict bound one index up. -/
theorem abs_qval_cauchyfyN_sub_codeReal_lt (f : ℕ → ℕ) (n : ℕ) :
    |((qval (cauchyfyN f n) : ℚ) : ℝ) - codeReal f| < 1 / 2 ^ n := by
  have h1 := abs_qval_cauchyfyN_sub_codeReal_le f (n + 1)
  have h2 : |((qval (cauchyfyN f n) : ℚ) : ℝ) - ((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ)|
      < 1 / 2 ^ (n + 1) := by
    have h := cauchyfyN_step f n
    rw [abs_sub_comm] at h
    have h' : ((|qval (cauchyfyN f n) - qval (cauchyfyN f (n + 1))| : ℚ) : ℝ)
        < ((1 / 2 ^ (n + 1) : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  calc |((qval (cauchyfyN f n) : ℚ) : ℝ) - codeReal f|
      = |(((qval (cauchyfyN f n) : ℚ) : ℝ) - ((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ))
          + (((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ) - codeReal f)| := by
        rw [sub_add_sub_cancel]
    _ ≤ |((qval (cauchyfyN f n) : ℚ) : ℝ) - ((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ)|
          + |((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ) - codeReal f| := abs_add_le _ _
    _ < 1 / 2 ^ (n + 1) + 1 / 2 ^ (n + 1) := add_lt_add_of_lt_of_le h2 h1
    _ = 1 / 2 ^ n := two_halves_R n

-- ============================================================================
-- Section 4: the formula-level consequences
-- ============================================================================

section Formulas

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type} {si : SpaceInterp X F} {Γ : Ctx ι}

/-- **`≤` on the denoted reals makes `≤ℝ` true.** The bound at `n+1` on each side is
consumed exactly. -/
theorem interpret_le_R_pu_of_codeReal_le (f g : Term F Γ (realTy ι))
    (env : Ctx.interpret X Γ)
    (h : codeReal (Term.interpret si f env) ≤ codeReal (Term.interpret si g env)) :
    Formula.interpret si (le_R_pu f g) env := by
  rw [interpret_le_R_pu]
  intro n
  have h1 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si f env) (n + 1)
  have h2 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si g env) (n + 1)
  rw [abs_lt] at h1 h2
  have hh := two_halves_R n
  refine (Rat.cast_lt (K := ℝ)).mp ?_
  push_cast
  linarith [h1.2, h2.1]

/-- **`=` on the denoted reals makes `=ℝ` true.** -/
theorem interpret_eq_R_of_codeReal_eq (f g : Term F Γ (realTy ι))
    (env : Ctx.interpret X Γ)
    (h : codeReal (Term.interpret si f env) = codeReal (Term.interpret si g env)) :
    Formula.interpret si (eq_R f g) env := by
  rw [interpret_eq_R]
  intro n
  have h1 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si f env) (n + 1)
  have h2 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si g env) (n + 1)
  rw [abs_lt] at h1 h2
  have hh := two_halves_R n
  refine (Rat.cast_lt (K := ℝ)).mp ?_
  push_cast
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Formulas

-- ============================================================================
-- Section 5: `codeReal` of the sequences the ℝ-layer constants build
-- ============================================================================

/-- A constant code passes every check. -/
theorem isCauchyCode_const (q : ℕ) : IsCauchyCode (fun _ => q) := fun _ => by
  rw [sub_self, abs_zero]; positivity

/-- A constant code denotes its rational. -/
theorem codeReal_const (q : ℕ) : codeReal (fun _ => q) = qval q :=
  codeReal_eq_of_tendsto (isCauchyCode_const q) tendsto_const_nhds

/-- `(x)◦` denotes `x`, for `x ≥ 0`. -/
theorem codeReal_roundR (x : ℝ) (hx : 0 ≤ x) : codeReal (roundR x) = x :=
  codeReal_eq_of_tendsto (fun k => roundR_cauchy x hx k) (roundR_tendsto x hx)

/-- The sequence `add_R` builds: its `codeReal` is the sum, for **all** `f g`. -/
theorem codeReal_addR (f g : ℕ → ℕ) :
    codeReal (fun n => addQN (cauchyfyN f (n + 1)) (cauchyfyN g (n + 1)))
      = codeReal f + codeReal g := by
  refine codeReal_eq_of_tendsto ?_ ?_
  · intro k
    simp only [qval_addQN]
    have ha := cauchyfyN_step f (k + 1)
    have hb := cauchyfyN_step g (k + 1)
    have hh := two_halves_Q (k + 1)
    rw [abs_sub_comm] at ha hb
    rw [abs_lt] at ha hb ⊢
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · simp only [qval_addQN]
    push_cast
    exact ((codeReal_tendsto f).comp (tendsto_add_atTop_nat 1)).add
      ((codeReal_tendsto g).comp (tendsto_add_atTop_nat 1))

/-- The product estimate behind `mul_R`'s Cauchy rate, on bare rationals. -/
private theorem mul_est {a₁ a₂ c₁ c₂ A C ε δ : ℚ}
    (ha : |a₁ - a₂| < ε) (hc : |c₁ - c₂| < ε) (hA : |a₂| ≤ A) (hC : |c₁| ≤ C)
    (hε : 0 < ε) (hApos : 0 < A) (hbnd : ε * C + A * ε ≤ δ) :
    |a₁ * c₁ - a₂ * c₂| < δ := by
  have h1 : |a₁ - a₂| * |c₁| ≤ ε * C := mul_le_mul ha.le hC (abs_nonneg _) hε.le
  have h2 : |a₂| * |c₁ - c₂| < A * ε :=
    calc |a₂| * |c₁ - c₂| ≤ A * |c₁ - c₂| := mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ < A * ε := mul_lt_mul_of_pos_left hc hApos
  calc |a₁ * c₁ - a₂ * c₂|
      = |(a₁ - a₂) * c₁ + a₂ * (c₁ - c₂)| := by congr 1; ring
    _ ≤ |(a₁ - a₂) * c₁| + |a₂ * (c₁ - c₂)| := abs_add_le _ _
    _ = |a₁ - a₂| * |c₁| + |a₂| * |c₁ - c₂| := by rw [abs_mul, abs_mul]
    _ < ε * C + A * ε := add_lt_add_of_le_of_lt h1 h2
    _ ≤ δ := hbnd

/-- **The sequence `mul_R` builds passes every check**, for **all** `f g`. The index shift
`b = f(0) + g(0) + 2` is what makes it so: `|f̂| ≤ f(0)+1`, `|ĝ| ≤ g(0)+1`, and `b ≤ 2^b`.
Named separately from `codeReal_mulR` because `codeReal_subR` asks for a check-passing
subtrahend, and CAT(0)'s CN axiom subtracts a `mul_R` term. -/
theorem isCauchyCode_mulR (f g : ℕ → ℕ) :
    IsCauchyCode (fun n => mulQN (cauchyfyN f (n + (f 0 + g 0 + 2)))
        (cauchyfyN g (n + (f 0 + g 0 + 2)))) := by
  intro k
  simp only [qval_mulQN]
  have e : k + 1 + (f 0 + g 0 + 2) = k + (f 0 + g 0 + 2) + 1 := by omega
  rw [e]
  have ha := cauchyfyN_step f (k + (f 0 + g 0 + 2))
  have hc := cauchyfyN_step g (k + (f 0 + g 0 + 2))
  rw [abs_sub_comm] at ha hc
  have hA := abs_qval_cauchyfyN_le f (k + (f 0 + g 0 + 2) + 1)
  have hC := abs_qval_cauchyfyN_le g (k + (f 0 + g 0 + 2))
  refine mul_est ha hc hA hC (by positivity) (by positivity) ?_
  have hb2 : ((f 0 + g 0 + 2 : ℕ) : ℚ) ≤ 2 ^ (f 0 + g 0 + 2) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := f 0 + g 0 + 2)).le
  have hsum : (1 / 2 ^ (k + (f 0 + g 0 + 2) + 1)) * ((g 0 : ℚ) + 1)
      + ((f 0 : ℚ) + 1) * (1 / 2 ^ (k + (f 0 + g 0 + 2) + 1))
      = ((f 0 + g 0 + 2 : ℕ) : ℚ) / 2 ^ (k + (f 0 + g 0 + 2) + 1) := by
    push_cast; ring
  rw [hsum, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((f 0 + g 0 + 2 : ℕ) : ℚ) * 2 ^ (k + 1)
      ≤ 2 ^ (f 0 + g 0 + 2) * 2 ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hb2 (by positivity)
    _ = 1 * 2 ^ (k + (f 0 + g 0 + 2) + 1) := by ring

/-- The sequence `mul_R` builds — with its index shift `b = f(0) + g(0) + 2` — denotes the
product, for **all** `f g`. -/
theorem codeReal_mulR (f g : ℕ → ℕ) :
    codeReal (fun n => mulQN (cauchyfyN f (n + (f 0 + g 0 + 2)))
        (cauchyfyN g (n + (f 0 + g 0 + 2))))
      = codeReal f * codeReal g := by
  refine codeReal_eq_of_tendsto (isCauchyCode_mulR f g) ?_
  · simp only [qval_mulQN]
    push_cast
    exact ((codeReal_tendsto f).comp (tendsto_add_atTop_nat _)).mul
      ((codeReal_tendsto g).comp (tendsto_add_atTop_nat _))

/-- `neg_R` negates the code pointwise with no `cauchyfy`, so its `codeReal` is the negation
only when the argument already passes the check — which is all the axioms need. -/
theorem codeReal_negR_of_isCauchyCode {g : ℕ → ℕ} (hg : IsCauchyCode g) :
    codeReal (fun n => negQN (g n)) = - codeReal g := by
  refine codeReal_eq_of_tendsto ?_ ?_
  · intro k
    simp only [qval_negQN]
    rw [neg_sub_neg, abs_sub_comm]
    exact hg k
  · simp only [qval_negQN]
    push_cast
    exact (tendsto_qval_of_isCauchyCode hg).neg

/-- The sequence `sub_R` builds. -/
theorem codeReal_subR (f : ℕ → ℕ) {g : ℕ → ℕ} (hg : IsCauchyCode g) :
    codeReal (fun n => addQN (cauchyfyN f (n + 1)) (cauchyfyN (fun k => negQN (g k)) (n + 1)))
      = codeReal f - codeReal g := by
  rw [codeReal_addR, codeReal_negR_of_isCauchyCode hg]
  ring

/-- The sequence `abs_R` builds. -/
theorem codeReal_absR (f : ℕ → ℕ) :
    codeReal (fun n => absQN (cauchyfyN f n)) = |codeReal f| := by
  refine codeReal_eq_of_tendsto ?_ ?_
  · intro k
    simp only [qval_absQN]
    exact lt_of_le_of_lt (abs_abs_sub_abs_le _ _) (isCauchyCode_cauchyfyN f k)
  · simp only [qval_absQN]
    push_cast
    exact (continuous_abs.tendsto _).comp (codeReal_tendsto f)

theorem isCauchyCode_clamp01 (f : ℕ → ℕ) :
    IsCauchyCode (fun n => clamp01QN (cauchyfyN f n)) := fun k => by
  simp only [qval_clamp01QN]
  exact lt_of_le_of_lt (clampQ_lipschitz _ _) (isCauchyCode_cauchyfyN f k)

/-- The sequence `clamp01` builds denotes the clamped real. -/
theorem codeReal_clamp01 (f : ℕ → ℕ) :
    codeReal (fun n => clamp01QN (cauchyfyN f n)) = clampReal (codeReal f) := by
  refine codeReal_eq_of_tendsto (isCauchyCode_clamp01 f) ?_
  simp only [qval_clamp01QN]
  have hcont : Continuous clampReal := continuous_const.max (continuous_const.min continuous_id)
  refine ((hcont.tendsto _).comp (codeReal_tendsto f)).congr ?_
  intro n
  simp only [Function.comp_apply, clampReal, clampQ, Rat.cast_max, Rat.cast_min, Rat.cast_zero,
    Rat.cast_one]

-- ============================================================================
-- Section 6: the same, on interpreted terms
-- ============================================================================

section Interp

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type} {si : SpaceInterp X F} {Γ : Ctx ι}

theorem codeReal_interp_add_R (f g : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.app2 Term.add_R f g) env)
      = codeReal (Term.interpret si f env) + codeReal (Term.interpret si g env) := by
  simp only [Term.app2, Term.interpret, interpret_add_R_fun]
  exact codeReal_addR _ _

theorem codeReal_interp_mul_R (f g : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.app2 Term.mul_R f g) env)
      = codeReal (Term.interpret si f env) * codeReal (Term.interpret si g env) := by
  simp only [Term.app2, Term.interpret, interpret_mul_R_fun]
  exact codeReal_mulR _ _

/-- A `mul_R` term passes every check — what `codeReal_interp_sub_R` needs of a subtrahend
that is a product (CAT(0)'s CN axiom). -/
theorem isCauchyCode_interp_mul_R (f g : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    IsCauchyCode (Term.interpret si (Term.app2 Term.mul_R f g) env) := by
  simp only [Term.app2, Term.interpret, interpret_mul_R_fun]
  exact isCauchyCode_mulR _ _

theorem codeReal_interp_sub_R (f g : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hg : IsCauchyCode (Term.interpret si g env)) :
    codeReal (Term.interpret si (Term.app2 Term.sub_R f g) env)
      = codeReal (Term.interpret si f env) - codeReal (Term.interpret si g env) := by
  simp only [Term.app2, Term.interpret, interpret_sub_R_fun]
  exact codeReal_subR _ hg

theorem codeReal_interp_abs_R (f : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.app Term.abs_R f) env)
      = |codeReal (Term.interpret si f env)| := by
  simp only [Term.interpret, interpret_abs_R_fun]
  exact codeReal_absR _

theorem codeReal_interp_one_R (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.one_R (F := F) (Γ := Γ)) env) = 1 := by
  rw [interpret_one_R, codeReal_const, qval_one_code, Rat.cast_one]

theorem codeReal_interp_zero_R (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.zero_R (F := F) (Γ := Γ)) env) = 0 := by
  rw [interpret_zero_R, codeReal_const, qval_zero_code, Rat.cast_zero]

/-- `1ℝ` is a constant code, so it passes every check — what `codeReal_interp_neg_R` asks of
its argument when the argument is `1ℝ` (the normed-space `−1ℝ`). -/
theorem isCauchyCode_interp_one_R (env : Ctx.interpret X Γ) :
    IsCauchyCode (Term.interpret si (Term.one_R (F := F) (Γ := Γ)) env) := by
  rw [interpret_one_R]; exact isCauchyCode_const _

/-- `neg_R` on a check-passing argument denotes the negation. Same side condition as
`codeReal_interp_sub_R`, for the same reason: `neg_R` never `cauchyfy`s its argument. -/
theorem codeReal_interp_neg_R (r : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hr : IsCauchyCode (Term.interpret si r env)) :
    codeReal (Term.interpret si (Term.app Term.neg_R r) env)
      = - codeReal (Term.interpret si r env) := by
  simp only [Term.interpret, interpret_neg_R_fun]
  exact codeReal_negR_of_isCauchyCode hr

theorem isCauchyCode_interp_clamp01 (r : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    IsCauchyCode (Term.interpret si (Term.app Term.clamp01 r) env) := by
  simp only [Term.interpret, interpret_clamp01_fun]
  exact isCauchyCode_clamp01 _

theorem codeReal_interp_clamp01 (r : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.app Term.clamp01 r) env)
      = clampReal (codeReal (Term.interpret si r env)) := by
  simp only [Term.interpret, interpret_clamp01_fun]
  exact codeReal_clamp01 _

end Interp

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms QBridge.interpret_clamp01_fun
#print axioms QBridge.qval_clamp01QN
#print axioms abs_qval_cauchyfyN_sub_codeReal_lt
#print axioms interpret_le_R_pu_of_codeReal_le
#print axioms interpret_eq_R_of_codeReal_eq
#print axioms codeReal_roundR
#print axioms isCauchyCode_const
#print axioms codeReal_addR
#print axioms isCauchyCode_mulR
#print axioms codeReal_mulR
#print axioms isCauchyCode_interp_mul_R
#print axioms codeReal_negR_of_isCauchyCode
#print axioms codeReal_absR
#print axioms codeReal_clamp01
#print axioms codeReal_interp_mul_R
#print axioms codeReal_interp_clamp01
#print axioms isCauchyCode_interp_one_R
#print axioms codeReal_interp_neg_R

end Metatheorems
