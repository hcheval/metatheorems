/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.QValBridge
import Mathlib.Analysis.SpecificLimits.Basic

namespace Metatheorems

/-!
# The real a code denotes

Kohlenbach's `r_f`: the real number represented by a code `f : ℕ → ℕ` of type `1`, read
through `cauchyfy` — so that **every** code denotes a real, not only the Cauchy ones. This is
what a model needs in order to interpret a function constant with a real argument
(`W : X →ₜ X →ₜ ℝ →ₜ X` in a W-hyperbolic space, scalar multiplication in a normed space).

* `codeReal f` is the limit of `n ↦ qval (cauchyfyN f n)`;
* `clampReal` is the semantic `[0,1]`-retraction, the model-side counterpart of `clamp01`.

This file is the semantic side; it uses Mathlib `ℝ` freely and is `noncomputable`, as every
model-side file is.
-/

open Rounding QBridge

/-- **The real number a code denotes**: the limit of the rational values of its cauchyfied
sequence. `cauchyfyN f` is Cauchy for *every* `f` (that is what `cauchyfy` is for), so this is
a genuine limit for every code; `limUnder` is used so that the definition needs no proof of
that fact at the point of definition. -/
noncomputable def codeReal (f : ℕ → ℕ) : ℝ :=
  limUnder Filter.atTop (fun n => ((qval (cauchyfyN f n) : ℚ) : ℝ))

/-- The semantic retraction onto `[0,1]`: `max 0 (min 1 r)`. -/
noncomputable def clampReal (r : ℝ) : ℝ := max 0 (min 1 r)

theorem clampReal_nonneg (r : ℝ) : 0 ≤ clampReal r := le_max_left _ _

theorem clampReal_le_one (r : ℝ) : clampReal r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clampReal_of_mem (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : clampReal r = r := by
  unfold clampReal
  rw [min_eq_right h1, max_eq_right h0]

-- The magnitude of a code, and of the real it denotes

/-! The one fact a majorant for a real-argument constant needs: the real a code `f` denotes is
bounded by `f(0) + 1`. It is the semantic mirror of `cauchyfy_mag_le` (`RealNumbers/Bounds.lean`,
`|f̂(y)| ≤ ⟨f(0)⟩ + 1`) together with `abs_le_encode` (a code dominates the magnitude it
encodes), followed to the limit. Kohlenbach's `≽`-majorant for scalar multiplication is built
on exactly this bound. -/

/-- A natural, read as a `ℚ`-code, denotes a rational of magnitude at most itself. -/
theorem abs_qval_le_self (m : ℕ) : |qval m| ≤ (m : ℚ) := by
  unfold qval
  have hden : (1 : ℚ) ≤ (sndN m : ℚ) + 1 := by
    have : (0 : ℚ) ≤ sndN m := Nat.cast_nonneg _
    linarith
  have hnumZ : |qnumZ (fstN m)| ≤ (fstN m : ℤ) := by
    unfold qnumZ
    split_ifs with h
    · rw [abs_of_nonneg (by positivity)]; omega
    · rw [abs_neg, abs_of_nonneg (by positivity)]; omega
  have hnum : |((qnumZ (fstN m) : ℤ) : ℚ)| ≤ (fstN m : ℚ) := by exact_mod_cast hnumZ
  have hf : (fstN m : ℚ) ≤ m := by
    have : fstN m ≤ m := Nat.sub_le _ _
    exact_mod_cast this
  rw [abs_div, abs_of_pos (by linarith : (0:ℚ) < (sndN m : ℚ) + 1)]
  calc |((qnumZ (fstN m) : ℤ) : ℚ)| / ((sndN m : ℚ) + 1)
      ≤ |((qnumZ (fstN m) : ℤ) : ℚ)| / 1 :=
        div_le_div_of_nonneg_left (abs_nonneg _) one_pos hden
    _ = |((qnumZ (fstN m) : ℤ) : ℚ)| := div_one _
    _ ≤ (fstN m : ℚ) := hnum
    _ ≤ m := hf

/-- The `cauchyfy` state invariant: the flag is `0` or `1`, and while it is `0` the value is
`g n` on the nose. -/
theorem cauchyStateN_inv (g : ℕ → ℕ) : ∀ n : ℕ,
    (sndN (cauchyStateN g n) = 0 ∧ fstN (cauchyStateN g n) = g n) ∨
      sndN (cauchyStateN g n) = 1
  | 0 => Or.inl ⟨by simp [cauchyStateN], by simp [cauchyStateN]⟩
  | n + 1 => by
      rcases cauchyStateN_inv g n with ⟨hf, _⟩ | hf
      · rw [cauchyStateN_succ]
        by_cases hc : checkN g n = 0
        · left
          simp [cstep, hf, iteN, sgBarN, hc]
        · right
          have hs : sgBarN (checkN g n) = 0 := by unfold sgBarN; omega
          simp [cstep, hf, iteN, hs]
      · right
        rw [cauchyStateN_succ]
        simp [cstep, hf, iteN]

/-- One `cauchyfy` step moves the value by less than `2^{-(n+1)}`, for **any** `g`: either the
check passed and the value moved to `g (n+1)` (with the check's own bound), or it did not and
the value froze. -/
theorem cauchyfyN_step (g : ℕ → ℕ) (n : ℕ) :
    |qval (cauchyfyN g (n + 1)) - qval (cauchyfyN g n)| < 1 / 2 ^ (n + 1) := by
  unfold cauchyfyN
  rcases cauchyStateN_inv g n with ⟨hf, hv⟩ | hf
  · rw [cauchyStateN_succ]
    by_cases hc : checkN g n = 0
    · have hlt := (checkN_eq_zero_iff g n).mp hc
      simp only [cstep, hf, iteN, sgBarN, hc]
      simp only [Nat.sub_zero, Nat.sub_self, one_mul, zero_mul, add_zero, zero_add,
        fstN_pairN, hv]
      rw [abs_sub_comm]
      exact hlt
    · have hs : sgBarN (checkN g n) = 0 := by unfold sgBarN; omega
      simp only [cstep, hf, iteN, hs]
      simp only [Nat.sub_zero, one_mul, zero_mul, zero_add, fstN_pairN, sub_self, abs_zero]
      positivity
  · rw [cauchyStateN_succ]
    simp only [cstep, hf, iteN]
    simp only [Nat.sub_self, one_mul, zero_mul, add_zero, sub_self, abs_zero]
    positivity

/-- Telescoped: the value never drifts more than `1 − 2^{-n}` from `g 0`. -/
theorem cauchyfyN_drift (g : ℕ → ℕ) : ∀ n : ℕ,
    |qval (cauchyfyN g n) - qval (g 0)| ≤ 1 - 1 / 2 ^ n
  | 0 => by simp [cauchyfyN, cauchyStateN]
  | n + 1 => by
      have ih := cauchyfyN_drift g n
      have hs := cauchyfyN_step g n
      have hhalf : (1 : ℚ) / 2 ^ n = 2 * (1 / 2 ^ (n + 1)) := by
        rw [pow_succ]; field_simp
      calc |qval (cauchyfyN g (n + 1)) - qval (g 0)|
          = |(qval (cauchyfyN g (n + 1)) - qval (cauchyfyN g n))
              + (qval (cauchyfyN g n) - qval (g 0))| := by ring_nf
        _ ≤ |qval (cauchyfyN g (n + 1)) - qval (cauchyfyN g n)|
              + |qval (cauchyfyN g n) - qval (g 0)| := abs_add_le _ _
        _ ≤ 1 / 2 ^ (n + 1) + (1 - 1 / 2 ^ n) := add_le_add (le_of_lt hs) ih
        _ = 1 - 1 / 2 ^ (n + 1) := by rw [hhalf]; ring

/-- **The magnitude bound**: `|f̂(n)| ≤ f(0) + 1`, the semantic `cauchyfy_mag_le`. -/
theorem abs_qval_cauchyfyN_le (g : ℕ → ℕ) (n : ℕ) :
    |qval (cauchyfyN g n)| ≤ (g 0 : ℚ) + 1 := by
  have h1 := cauchyfyN_drift g n
  have h2 := abs_qval_le_self (g 0)
  have h3 : (0 : ℚ) ≤ 1 / 2 ^ n := by positivity
  calc |qval (cauchyfyN g n)|
      = |(qval (cauchyfyN g n) - qval (g 0)) + qval (g 0)| := by ring_nf
    _ ≤ |qval (cauchyfyN g n) - qval (g 0)| + |qval (g 0)| := abs_add_le _ _
    _ ≤ (1 - 1 / 2 ^ n) + (g 0 : ℚ) := add_le_add h1 h2
    _ ≤ (g 0 : ℚ) + 1 := by linarith

-- Convergence, and the bound on the limit

/-- The cauchyfied value sequence converges to `codeReal g` — for every `g`. -/
theorem codeReal_tendsto (g : ℕ → ℕ) :
    Filter.Tendsto (fun n => ((qval (cauchyfyN g n) : ℚ) : ℝ)) Filter.atTop
      (nhds (codeReal g)) := by
  apply tendsto_nhds_limUnder
  refine cauchySeq_tendsto_of_complete ?_
  refine cauchySeq_of_le_geometric_two (C := 1) ?_
  intro n
  rw [Real.dist_eq]
  have h := cauchyfyN_step g n
  have hq : |qval (cauchyfyN g n) - qval (cauchyfyN g (n + 1))| ≤ 1 / 2 ^ (n + 1) := by
    rw [abs_sub_comm]; exact le_of_lt h
  have hr : |((qval (cauchyfyN g n) : ℚ) : ℝ) - ((qval (cauchyfyN g (n + 1)) : ℚ) : ℝ)|
      ≤ ((1 / 2 ^ (n + 1) : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast hq
  calc |((qval (cauchyfyN g n) : ℚ) : ℝ) - ((qval (cauchyfyN g (n + 1)) : ℚ) : ℝ)|
      ≤ ((1 / 2 ^ (n + 1) : ℚ) : ℝ) := hr
    _ = 1 / 2 / 2 ^ n := by push_cast; rw [pow_succ]; ring

/-- **`|codeReal g| ≤ g(0) + 1`** — the bound a majorant for a real-argument constant uses. -/
theorem abs_codeReal_le (g : ℕ → ℕ) : |codeReal g| ≤ (g 0 : ℝ) + 1 := by
  have ht := (continuous_abs.tendsto (codeReal g)).comp (codeReal_tendsto g)
  refine le_of_tendsto' ht ?_
  intro n
  have h := abs_qval_cauchyfyN_le g n
  have h' : |((qval (cauchyfyN g n) : ℚ) : ℝ)| ≤ (((g 0 : ℚ) + 1 : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast h
  simpa using h'

-- Axiom hygiene

#print axioms abs_codeReal_le
#print axioms codeReal_tendsto

end Metatheorems
