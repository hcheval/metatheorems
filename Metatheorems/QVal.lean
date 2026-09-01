/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Rounding

namespace Metatheorems

/-!
# `qval` — the meaning of a `ℚ`-code, and Kohlenbach's Lemma 17.8(1)

`RationalNumbers.lean` encodes a rational as a *natural number* via Cantor pairing:

    n  ↦  ± ⌈j₁(n)/2⌉ / (j₂(n) + 1),   sign `+` iff `j₁(n)` is even

(`Term.rat_num`, `Term.rat_den`, `Term.rat_sign`). That whole layer is object-level `Term`s,
so there was no Lean-level function saying *which rational* a code denotes. `qval` is that
function, and it is what the phrase "`(x)◦` is a representative of `x`" needs in order to be
a statement at all.

This file is on the **semantic** side, like `Rounding.lean`: `ℕ`, `ℚ` and `ℝ` here are
Mathlib's, not the encoded ones. Nothing here is a `Derivable`.

## Contents

* `invTriagN`, `fstN`, `sndN` — the Cantor decoding, matching `Term.inv_triag`,
  `Term.fst_pair`, `Term.snd_pair`, with `fstN (pairN a b) = a` and `sndN (pairN a b) = b`.
* `qval : ℕ → ℚ` — the rational denoted by a code.
* `qval_roundR` — `(x)◦(n)` denotes `⌊x·2^{n+1}⌋ / 2^{n+1}`.
* `qval_roundR_dist_le` — `|(x)◦(n) − x| ≤ 2^{-(n+1)}`, and `qval_roundR_lt` for the strict
  one-sided form.
* `roundR_cauchy` — **Lemma 17.8(1)**, the Cauchy condition (4.2), in the sharp form
  `|(x)◦(n+1) − (x)◦(n)| < 2^{-(n+1)}` that `RealNumbers.cauchy_check_at` uses; the form
  `< 2^{-n}` quoted by Leuştean follows (`roundR_cauchy_weak`).
* `roundR_tendsto` — `(x)◦` really converges to `x`.

## What this does NOT do

It does not connect `qval` to `Term.interpret` of `Term.rat_num`/`Term.lt_Q_dec`. That is a
separate bridge (evaluating the object-level `prec`-recursions `div2`, `inv_triag`, … in the
standard model) and is not attempted here. So the Cauchy condition below is stated at the
level of *actual rationals*, which is what Leuştean's (4.2) means mathematically, not at the
level of the object-level decision term `lt_Q_dec`.
-/

namespace Rounding

-- ============================================================================
-- Decoding the Cantor pairing
-- ============================================================================

theorem le_triagN (n : ℕ) : n ≤ triagN n := by
  induction n with
  | zero => simp [triagN]
  | succ n ih => simp only [triagN]; omega

theorem triagN_lt_succ (n : ℕ) : triagN n < triagN (n + 1) := by
  simp only [triagN]; omega

theorem triagN_strictMono : StrictMono triagN := strictMono_nat_of_lt_succ triagN_lt_succ

/-- Inverse triangular map: the largest `k` with `triagN k ≤ n`. Matches `Term.inv_triag`. -/
def invTriagN (n : ℕ) : ℕ := Nat.findGreatest (fun k => triagN k ≤ n) n

/-- First Cantor projection. Matches `Term.fst_pair`: `n ∸ triag (inv_triag n)`. -/
def fstN (n : ℕ) : ℕ := n - triagN (invTriagN n)

/-- Second Cantor projection. Matches `Term.snd_pair`: `inv_triag n ∸ fst_pair n`. -/
def sndN (n : ℕ) : ℕ := invTriagN n - fstN n

theorem le_pairN (a b : ℕ) : a + b ≤ pairN a b := by
  have := le_triagN (a + b)
  unfold pairN
  omega

theorem invTriagN_pairN (a b : ℕ) : invTriagN (pairN a b) = a + b := by
  refine Nat.findGreatest_eq_iff.2 ⟨le_pairN a b, ?_, ?_⟩
  · intro _
    exact Nat.le_add_right _ _
  · intro k hk _ hkle
    have h1 : triagN (a + b + 1) ≤ triagN k := triagN_strictMono.monotone (by omega)
    have h2 : triagN (a + b + 1) = triagN (a + b) + (a + b + 1) := by simp [triagN]
    simp only [pairN] at hkle
    omega

@[simp] theorem fstN_pairN (a b : ℕ) : fstN (pairN a b) = a := by
  unfold fstN
  rw [invTriagN_pairN]
  simp [pairN]

@[simp] theorem sndN_pairN (a b : ℕ) : sndN (pairN a b) = b := by
  simp [sndN, invTriagN_pairN]

-- ============================================================================
-- The meaning of a code
-- ============================================================================

/-- The signed numerator carried by the first Cantor component: `j₁` even means the
non-negative numerator `j₁/2`, `j₁` odd the negative numerator `−(j₁+1)/2`. This is
`Term.rat_sign` and `Term.rat_num` read together. -/
def qnumZ (j : ℕ) : ℤ := if j % 2 = 0 then ((j / 2 : ℕ) : ℤ) else -(((j + 1) / 2 : ℕ) : ℤ)

/-- **The rational denoted by a `ℚ`-code**, matching the encoding of
`RationalNumbers.lean`: `n ↦ ±⌈j₁(n)/2⌉ / (j₂(n) + 1)`. -/
def qval (n : ℕ) : ℚ := (qnumZ (fstN n) : ℚ) / ((sndN n : ℚ) + 1)

theorem qval_pairN (a b : ℕ) : qval (pairN a b) = (qnumZ a : ℚ) / ((b : ℚ) + 1) := by
  simp [qval]

@[simp] theorem qnumZ_two_mul (a : ℕ) : qnumZ (2 * a) = (a : ℤ) := by
  simp [qnumZ, Nat.mul_div_cancel_left a (by norm_num : 0 < 2)]

/-- A code with an even first component denotes the non-negative rational `a / (b+1)`. -/
theorem qval_pairN_even (a b : ℕ) : qval (pairN (2 * a) b) = (a : ℚ) / ((b : ℚ) + 1) := by
  rw [qval_pairN, qnumZ_two_mul]
  norm_num

/-- A code with an odd first component denotes `−(a+1) / (b+1)`. -/
theorem qval_pairN_odd (a b : ℕ) :
    qval (pairN (2 * a + 1) b) = -((a : ℚ) + 1) / ((b : ℚ) + 1) := by
  rw [qval_pairN]
  congr 1
  have h : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  simp only [qnumZ, h]
  norm_num

-- ============================================================================
-- Sanity: the `ℚ` constants of `RationalNumbers.lean` denote what they should
-- ============================================================================

/-- `Term.zero_Q = pair 0 0` denotes `0`. -/
@[simp] theorem qval_zero_code : qval (pairN 0 0) = 0 := by
  have : pairN 0 0 = pairN (2 * 0) 0 := by norm_num
  rw [this, qval_pairN_even]
  norm_num

/-- `Term.one_Q = pair 2 0` denotes `1`. -/
@[simp] theorem qval_one_code : qval (pairN 2 0) = 1 := by
  have : pairN 2 0 = pairN (2 * 1) 0 := by norm_num
  rw [this, qval_pairN_even]
  norm_num

/-- `Term.encode_nat_Q n = pair (2·n) 0` denotes `n`. -/
theorem qval_encode_nat_code (a : ℕ) : qval (pairN (2 * a) 0) = (a : ℚ) := by
  rw [qval_pairN_even]; norm_num

/-- `Term.pow2neg_Q n = pair 2 (2^n − 1)` denotes `2^{-n}`. -/
theorem qval_pow2neg_code (n : ℕ) : qval (pairN 2 (2 ^ n - 1)) = 1 / 2 ^ n := by
  have h1 : (1:ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have : pairN 2 (2 ^ n - 1) = pairN (2 * 1) (2 ^ n - 1) := by norm_num
  rw [this, qval_pairN_even]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring

/-- The majorant `M(b)` of Definition 17.7(2) codes the *constant* rational `b` at every
precision. (A useful cross-check on both `Mmaj` and `qval`.) -/
theorem qval_Mmaj (b n : ℕ) : qval (Mmaj b n) = (b : ℚ) := by
  have h1 : (1:ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have he : b * 2 ^ (n + 2) = 2 * (b * 2 ^ (n + 1)) := by ring
  rw [Mmaj, he, qval_pairN_even]
  have : ((2 ^ (n + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (n + 1) - 1 := by
    push_cast [Nat.cast_sub h1]; ring
  rw [this]
  push_cast
  field_simp
  ring

-- ============================================================================
-- What `(x)◦` denotes
-- ============================================================================

/-- **Deliverable 2**: the rational denoted by `(x)◦(n)` is `⌊x·2^{n+1}⌋ / 2^{n+1}`. -/
theorem qval_roundR (x : ℝ) (n : ℕ) :
    qval (roundR x n) = (k0 x n : ℚ) / 2 ^ (n + 1) := by
  have h1 : (1:ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  rw [roundR, qval_pairN_even]
  congr 1
  have : ((2 ^ (n + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (n + 1) - 1 := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [this]
  ring

/-- `(x)◦(n)`, as a real. -/
theorem qval_roundR_real (x : ℝ) (n : ℕ) :
    ((qval (roundR x n) : ℚ) : ℝ) = (⌊x * 2 ^ (n + 1)⌋₊ : ℝ) / 2 ^ (n + 1) := by
  rw [qval_roundR]
  push_cast [k0]
  ring

/-- `(x)◦(n)` never overshoots: it is at most `x`. -/
theorem qval_roundR_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((qval (roundR x n) : ℚ) : ℝ) ≤ x := by
  rw [qval_roundR_real]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ (n + 1))]
  exact Nat.floor_le (by positivity)

/-- …and it undershoots by strictly less than `2^{-(n+1)}`. -/
theorem qval_roundR_lt (x : ℝ) (n : ℕ) :
    x - 1 / 2 ^ (n + 1) < ((qval (roundR x n) : ℚ) : ℝ) := by
  rw [qval_roundR_real]
  have hpos : (0:ℝ) < 2 ^ (n + 1) := by positivity
  have h2 : (⌊x * 2 ^ (n + 1)⌋₊ : ℝ) / 2 ^ (n + 1) + 1 / 2 ^ (n + 1)
      = ((⌊x * 2 ^ (n + 1)⌋₊ : ℝ) + 1) / 2 ^ (n + 1) := by ring
  rw [sub_lt_iff_lt_add, h2, lt_div_iff₀ hpos]
  exact Nat.lt_floor_add_one (x * 2 ^ (n + 1))

/-- **Deliverable 3**: `|(x)◦(n) − x| ≤ 2^{-(n+1)}`. -/
theorem qval_roundR_dist_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    |((qval (roundR x n) : ℚ) : ℝ) - x| ≤ 1 / 2 ^ (n + 1) := by
  have h1 := qval_roundR_le x hx n
  have h2 := qval_roundR_lt x n
  rw [abs_le]
  constructor <;> linarith

-- ============================================================================
-- Lemma 17.8(1): the Cauchy condition (4.2)
-- ============================================================================

/-- **Lemma 17.8(1)**, sharp form: `(x)◦` satisfies the Cauchy condition in the shape used by
`RealNumbers.cauchy_check_at`, namely `|f(n) −ℚ f(n+1)| <ℚ 2^{-(n+1)}`. -/
theorem roundR_cauchy (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    |qval (roundR x n) - qval (roundR x (n + 1))| < 1 / 2 ^ (n + 1) := by
  have key : |((qval (roundR x n) : ℚ) : ℝ) - ((qval (roundR x (n+1)) : ℚ) : ℝ)|
      < 1 / 2 ^ (n + 1) := by
    have h1 := qval_roundR_le x hx n
    have h2 := qval_roundR_lt x n
    have h3 := qval_roundR_le x hx (n + 1)
    have h4 := qval_roundR_lt x (n + 1)
    have hlt : (1:ℝ) / 2 ^ (n + 2) < 1 / 2 ^ (n + 1) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      have : (2:ℝ) ^ (n+1) * 1 < 2 ^ (n+1) * 2 := by
        have : (0:ℝ) < 2 ^ (n+1) := by positivity
        nlinarith
      calc (2:ℝ) ^ (n+1) = 2 ^ (n+1) * 1 := by ring
        _ < 2 ^ (n+1) * 2 := this
        _ = 2 ^ (n+2) := by ring
    rw [abs_lt]
    constructor <;> linarith
  -- transport the strict inequality from ℝ back to ℚ
  have hcast : ((|qval (roundR x n) - qval (roundR x (n+1))| : ℚ) : ℝ)
      = |((qval (roundR x n) : ℚ) : ℝ) - ((qval (roundR x (n+1)) : ℚ) : ℝ)| := by
    push_cast
    ring_nf
  have : ((|qval (roundR x n) - qval (roundR x (n+1))| : ℚ) : ℝ)
      < ((1 / 2 ^ (n + 1) : ℚ) : ℝ) := by
    rw [hcast]
    push_cast
    exact key
  exact_mod_cast this

/-- **Lemma 17.8(1)**, in Leuştean's (4.2) shape `|f(n+1) −ℚ f(n)| <ℚ 2^{-n}`. -/
theorem roundR_cauchy_weak (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    |qval (roundR x (n + 1)) - qval (roundR x n)| < 1 / 2 ^ n := by
  have h := roundR_cauchy x hx n
  rw [abs_sub_comm] at h
  refine lt_of_lt_of_le h ?_
  apply one_div_le_one_div_of_le (by positivity)
  calc (2:ℚ) ^ n = 2 ^ n * 1 := by ring
    _ ≤ 2 ^ n * 2 := by nlinarith [pow_pos (by norm_num : (0:ℚ) < 2) n]
    _ = 2 ^ (n + 1) := by ring

/-- `(x)◦` is a representative *of `x`*: the rationals it codes converge to `x`. -/
theorem roundR_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Filter.Tendsto (fun n => ((qval (roundR x n) : ℚ) : ℝ)) Filter.atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1:ℝ) < 2)
  refine ⟨N, fun n hn => ?_⟩
  have hb := qval_roundR_dist_le x hx n
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hb ?_
  have hmono : (2:ℝ) ^ N ≤ 2 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0:ℝ) < 2 ^ (n + 1) := by positivity
  rw [div_lt_iff₀ hpos]
  have h1 : 1 / ε < 2 ^ (n + 1) := lt_of_lt_of_le hN hmono
  rw [div_lt_iff₀ hε] at h1
  linarith

-- Axiom audit. `Classical.choice` is expected throughout: `qval` lands in Mathlib's `ℚ`,
-- and `k0` is `Nat.floor` on Mathlib's `ℝ`. What matters is the absence of `sorryAx`.
#print axioms invTriagN_pairN
#print axioms fstN_pairN
#print axioms sndN_pairN
#print axioms qval_pairN_even
#print axioms qval_pairN_odd
#print axioms qval_Mmaj
#print axioms qval_pow2neg_code
#print axioms qval_roundR
#print axioms qval_roundR_dist_le
#print axioms roundR_cauchy
#print axioms roundR_cauchy_weak
#print axioms roundR_tendsto

end Rounding

end Metatheorems
