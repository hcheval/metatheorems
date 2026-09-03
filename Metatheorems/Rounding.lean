/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics

namespace Metatheorems

/-!
# The rounding operator `(·)◦`, and Kohlenbach's Lemma 17.8

**`(·)◦` is a SEMANTIC operator.** Kohlenbach, Definition 17.7: for `x ∈ [0,∞)`,

    (x)◦(n) := j(2k₀, 2^{n+1} − 1),   k₀ := max {k : k / 2^{n+1} ≤ x}

He flags the domain himself — *"[0,∞) refers to the 'real' space of all positive reals, i.e.
not to the sets of representatives"*. Leuştean (§4, eq. 4.4) says it in so many words: *"we
need a semantic operator which for any real number `x ∈ [0,∞)` selects out of all the
representatives `f : ℕ → ℕ` of `x` a unique representative `(x)◦`"*.

So this file lives on the Lean side of the interpretation and uses Mathlib's `ℝ`. There is
deliberately **no** `Term F Γ (realTy ι →ₜ Ty.nat)`; that would be the wrong type and the
wrong side. Contrast `Term.round_nat` in `RealNumbers.lean`, which is `(·)◦` *restricted to
ℕ* (Kohlenbach p. 430: `(x⁰)◦(n) = j(x·2^{n+2}, 2^{n+1} − 1)`) and is therefore an
object-level term, correctly.

Why this matters for scoping: because the domain is Mathlib's `ℝ`, the parts of Lemma 17.8
that the majorants consume are provable **without** any of `RealNumbers.lean`'s open
ordered-field goals. See `METRIC_PLAN.md` §2 and §2.5.

## What is proved here

Lemma 17.8, parts (ii), (iii), (iv), (v), (vi) — everything that is a statement about `(x)◦`
as a `ℕ → ℕ` function under the pointwise order `≤₁`. These need only monotonicity of the
Cantor pairing and of `Nat.floor`.

Part (i) is **not** here, on purpose; see the note at the bottom of the file.
-/

namespace Rounding

-- ============================================================================
-- The Cantor pairing, semantically
-- ============================================================================

/-- Triangular numbers, matching `Term.triag`: `triag 0 = 0`, `triag (n+1) = triag n + (n+1)`. -/
def triagN : ℕ → ℕ
  | 0     => 0
  | n + 1 => triagN n + (n + 1)

/-- Cantor pairing, matching `Term.pair`: `pair a b = triag (a + b) + a`. -/
def pairN (a b : ℕ) : ℕ := triagN (a + b) + a

theorem triagN_le_succ (n : ℕ) : triagN n ≤ triagN (n + 1) := by
  simp only [triagN]; omega

theorem triagN_mono : Monotone triagN := monotone_nat_of_le_succ triagN_le_succ

/-- `pairN` is monotone in its first argument. -/
theorem pairN_mono_left {a a' b : ℕ} (h : a ≤ a') : pairN a b ≤ pairN a' b := by
  unfold pairN
  exact Nat.add_le_add (triagN_mono (by omega)) h

/-- `pairN` is monotone in its second argument. -/
theorem pairN_mono_right {a b b' : ℕ} (h : b ≤ b') : pairN a b ≤ pairN a b' := by
  unfold pairN
  exact Nat.add_le_add_right (triagN_mono (by omega)) a

/-- `pairN` is monotone in both arguments at once. -/
theorem pairN_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    pairN a b ≤ pairN a' b' :=
  Nat.le_trans (pairN_mono_left ha) (pairN_mono_right hb)

-- ============================================================================
-- Definition 17.7
-- ============================================================================

/-- `k₀` of Definition 17.7: the largest `k` with `k / 2^{n+1} ≤ x`, i.e. `⌊x · 2^{n+1}⌋`. -/
noncomputable def k0 (x : ℝ) (n : ℕ) : ℕ := ⌊x * 2 ^ (n + 1)⌋₊

/-- **Definition 17.7(1)**, `(x)◦ : ℕ → ℕ`. The code `j(2k₀, 2^{n+1} − 1)` is the rational
`2k₀ / 2^{n+2}` — i.e. `k₀ / 2^{n+1}` — in the project's `ℚ` encoding, where the second
component is the denominator minus one and an even first component is a non-negative
numerator. -/
noncomputable def roundR (x : ℝ) (n : ℕ) : ℕ :=
  pairN (2 * k0 x n) (2 ^ (n + 1) - 1)

/-- **Definition 17.7(2)**: `M(b) := λn. j(b·2^{n+2}, 2^{n+1} − 1)`, the uniform majorant for
reals bounded by the natural `b`. -/
def Mmaj (b : ℕ) (n : ℕ) : ℕ := pairN (b * 2 ^ (n + 2)) (2 ^ (n + 1) - 1)

/-- Pointwise order on `ℕ → ℕ`, Kohlenbach's `≤₁`. -/
def le₁ (f g : ℕ → ℕ) : Prop := ∀ n, f n ≤ g n

@[inherit_doc] scoped infix:50 " ≤₁ " => le₁

-- ============================================================================
-- Lemma 17.8 — the parts that are pure `ℕ → ℕ` statements
-- ============================================================================

theorem k0_mono {x y : ℝ} (h : x ≤ y) (n : ℕ) : k0 x n ≤ k0 y n :=
  Nat.floor_mono (mul_le_mul_of_nonneg_right h (by positivity))

/-- **Lemma 17.8(2)**: `x ≤ y → (x)◦ ≤₁ (y)◦`. -/
theorem roundR_le₁_of_le {x y : ℝ} (h : x ≤ y) : roundR x ≤₁ roundR y := by
  intro n
  exact pairN_mono_left (Nat.mul_le_mul_left 2 (k0_mono h n))

/-- `k₀` grows with the precision index: `k₀ x n ≤ k₀ x (n+1)` — in fact doubling. -/
theorem k0_succ_ge {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : k0 x n ≤ k0 x (n + 1) := by
  unfold k0
  apply Nat.floor_mono
  have h2 : (0:ℝ) < 2 := by norm_num
  have : x * 2 ^ (n + 1) ≤ x * 2 ^ (n + 2) := by
    apply mul_le_mul_of_nonneg_left _ hx
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact this

/-- **Lemma 17.8(3)**: `(x)◦` is monotone in the precision index. -/
theorem roundR_mono {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : roundR x n ≤ roundR x (n + 1) := by
  unfold roundR
  refine pairN_mono (Nat.mul_le_mul_left 2 (k0_succ_ge hx n)) ?_
  have : (2:ℕ) ^ (n + 1) ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Lemma 17.8(5)**: a real in `[0, b]` is dominated pointwise by `M(b)`. -/
theorem roundR_le₁_Mmaj {x : ℝ} {b : ℕ} (_hx : 0 ≤ x) (hb : x ≤ (b : ℝ)) :
    roundR x ≤₁ Mmaj b := by
  intro n
  refine pairN_mono_left ?_
  have hfloor : k0 x n ≤ b * 2 ^ (n + 1) := by
    unfold k0
    have : x * 2 ^ (n + 1) ≤ ((b * 2 ^ (n + 1) : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    exact Nat.floor_le_of_le this |>.trans (by simp)
  calc 2 * k0 x n ≤ 2 * (b * 2 ^ (n + 1)) := Nat.mul_le_mul_left 2 hfloor
    _ = b * 2 ^ (n + 2) := by ring

/-- **Lemma 17.8(6)**: `M(b)` is monotone in the precision index. -/
theorem Mmaj_mono (b : ℕ) (n : ℕ) : Mmaj b n ≤ Mmaj b (n + 1) := by
  unfold Mmaj
  refine pairN_mono ?_ ?_
  · exact Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have : (2:ℕ) ^ (n + 1) ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Lemma 17.8(4)**: `x ≤ y → (y)◦ s-maj₁ (x)◦`, stated as the two monotonicity facts about
`(·)◦` that both `bezemMaj` and `hatMaj` need at type `1 = nat →ₜ nat`. Stated once because
at that type the two relations unfold to *the same* pair: `bezemMaj` at `.nat` and `hatMaj`
at `.nat` are both `≥`. Consumed by `MetricModel.dist_maj` in `MetricSpaces.lean`. -/
theorem roundR_maj_pair {a b : ℝ} (hb : 0 ≤ b) (hab : a ≤ b) :
    (∀ p q : ℕ, p ≥ q → roundR b p ≥ roundR a q) ∧
    (∀ p q : ℕ, p ≥ q → roundR b p ≥ roundR b q) := by
  have hmono : Monotone (roundR b) :=
    monotone_nat_of_le_succ (roundR_mono hb)
  exact ⟨fun p q h => Nat.le_trans (roundR_le₁_of_le hab q) (hmono h),
         fun p q h => hmono h⟩

/-! ## What is deliberately not here

**Part (1)** — "`(x)◦` is a representative of `x`", i.e. `(x)◦` satisfies the Cauchy condition
(4.2) and `((x)◦)^b =₁ (x)◦`. The **first half is now proved, in `QVal.lean`**: that file
defines `qval : ℕ → ℚ`, the missing Lean-level "meaning of a rational code", and proves
`roundR_cauchy` (`|(x)◦(n) − (x)◦(n+1)| < 2^{-(n+1)}`) together with
`qval_roundR_dist_le` and `roundR_tendsto`. It is stated at the level of actual rationals;
relating it to the *object-level* decision term `Term.lt_Q_dec` under `Term.interpret` is
still open, as is the `((x)◦)^b =₁ (x)◦` half, which needs `cauchyfy`.

**Part (4)** used to be excluded too, blocked on the `bezemMaj` question in `METRIC_PLAN.md`
§2.5 (the one-clause `bezemMaj` lacked the self-majorization conjunct, which at type
`1 = ℕ → ℕ` is exactly what distinguishes `s-maj₁` from `≤₁`). The two-clause widening on
2026-09-02 removed the blocker; it is `roundR_maj_pair` above. -/

end Rounding

end Metatheorems
