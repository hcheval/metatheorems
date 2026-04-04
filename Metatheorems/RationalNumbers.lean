/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Arithmetic

namespace Metatheorems

/-!
# Rational Numbers in WE-HA^{ω}

Rational numbers are encoded as natural numbers via Cantor pairing of
(sign-adjusted numerator, denominator - 1). This module provides:

1. **Auxiliary arithmetic**: `max`, `sg`, `isEven`, `triag`, `exp2`
2. **Cantor pairing**: `pair`, `inv_triag`, `fst_pair`, `snd_pair`
3. **Division by 2**: `div2` (via state-pair recursion using pairing)
4. **Rational encoding**: `rat_num`, `rat_den`, `rat_sign`, `rat_encode`
5. **Rational arithmetic**: `neg_Q`, `add_Q`, `sub_Q`, `mul_Q`, `abs_Q`
6. **Rational comparison**: `le_Q_dec`, `lt_Q_dec` (decision terms, 0 = true)
7. **Rational constants**: `encode_nat_Q`, `pow2neg_Q`, `zero_Q`, `one_Q`
-/

open Formula

/-- The type of real numbers: type level 1 = ℕ → ℕ.
    A real `x : ℝₜ` is a function where `x(n)` encodes a rational
    approximation of the real value to within 2^{-n}. -/
abbrev realTy (ι : Type) : Ty ι := Ty.nat →ₜ Ty.nat

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Section 1: Auxiliary Arithmetic Terms
-- ============================================================================

namespace Term

/-- Maximum: max(x, y) = x + (y ∸ x). -/
def max {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.add (.var (.vs .vz))
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))))

/-- Minimum: min(x, y) = x ∸ (x ∸ y). -/
def min {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.monus (.var (.vs .vz))
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))))

/-- Sign: sg(0) = 0, sg(Sn) = 1. -/
def sg {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                        -- sg(0) = 0
      (Term.lam (Term.lam                          -- λr k. 1
        (.app .succ .zero)))
      (.var .vz))

/-- Is-even: isEven(0) = 1, isEven(Sn) = sg_bar(isEven(n)).
    Returns 1 for even, 0 for odd. -/
def isEven {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      (.app .succ .zero)                           -- isEven(0) = 1
      (Term.lam (Term.lam                          -- λr k. sg_bar(r)
        (.app Term.sg_bar (.var (.vs .vz)))))
      (.var .vz))

/-- Is-odd: isOdd(n) = 1 ∸ isEven(n). -/
def isOdd {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app2 Term.monus (.app .succ .zero)
      (.app Term.isEven (.var .vz)))

/-- Triangular number: triag(0) = 0, triag(Sn) = triag(n) + S(n).
    Computes n·(n+1)/2. -/
def triag {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                        -- triag(0) = 0
      (Term.lam (Term.lam                          -- λr k. add r (S k)
        (Term.app2 Term.add
          (.var (.vs .vz))                         -- r
          (.app .succ (.var .vz)))))               -- S k
      (.var .vz))

/-- Power of 2: exp2(0) = 1, exp2(Sn) = 2 · exp2(n). -/
def exp2 {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      (.app .succ .zero)                           -- exp2(0) = 1
      (Term.lam (Term.lam                          -- λr k. r + r = 2r
        (Term.app2 Term.add
          (.var (.vs .vz))
          (.var (.vs .vz)))))
      (.var .vz))

/-- Conditional: ite(b, x, y) = b·x + (1-b)·y for b ∈ {0,1}.
    When b = 1: returns x. When b = 0: returns y. -/
def ite_nat {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam (Term.lam
    -- b = var (vs (vs vz)), x = var (vs vz), y = var vz
    (Term.app2 Term.add
      (Term.app2 Term.mul (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (Term.app2 Term.mul
        (Term.app2 Term.monus (.app .succ .zero) (.var (.vs (.vs .vz))))
        (.var .vz)))))

/-- geq(a, b) = 1 if a ≥ b, 0 if a < b.
    Computed as sg_bar(b ∸ a). -/
def geq {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (.app Term.sg_bar
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))))

-- ============================================================================
-- Section 2: Cantor Pairing
-- ============================================================================

/-- Cantor pairing: pair(a, b) = triag(a + b) + a. -/
def pair {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.add
      (.app Term.triag (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
      (.var (.vs .vz))))

/-- Inverse triangular number: the largest w with triag(w) ≤ n.
    inv_triag(0) = 0
    inv_triag(Sk) = inv_triag(k) + sg_bar(monus(triag(S(inv_triag(k))))(Sk))

    The step increments w when triag(w+1) ≤ n. -/
def inv_triag {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                        -- inv_triag(0) = 0
      (Term.lam (Term.lam                          -- λr k. r + sg_bar(monus(triag(Sr))(Sk))
        (Term.app2 Term.add
          (.var (.vs .vz))                         -- r
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag                     -- triag(S r)
                (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))         -- S k
      (.var .vz))

/-- First Cantor projection: fst_pair(n) = n - triag(inv_triag(n)). -/
def fst_pair {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app2 Term.monus
      (.var .vz)
      (.app Term.triag (.app Term.inv_triag (.var .vz))))

/-- Second Cantor projection: snd_pair(n) = inv_triag(n) - fst_pair(n). -/
def snd_pair {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app2 Term.monus
      (.app Term.inv_triag (.var .vz))
      (.app Term.fst_pair (.var .vz)))

-- ============================================================================
-- Section 3: Division by 2
-- ============================================================================

/-- Division by 2 via state-pair recursion.
    Tracks state pair(div2(k), isEven(k)) as a single natural number.
    state(0) = pair(0, 1)
    state(Sk) = pair(fst(state(k)) + snd(state(k)), sg_bar(snd(state(k))))
    div2(n) = fst_pair(state(n)). -/
def div2 {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (.app Term.fst_pair
      (Term.app3 (.prec Ty.nat)
        (Term.app2 Term.pair .zero (.app .succ .zero))  -- pair(0, 1)
        (Term.lam (Term.lam                              -- λr k.
          (Term.app2 Term.pair
            (Term.app2 Term.add                          --   fst(r) + snd(r)
              (.app Term.fst_pair (.var (.vs .vz)))
              (.app Term.snd_pair (.var (.vs .vz))))
            (.app Term.sg_bar                            --   sg_bar(snd(r))
              (.app Term.snd_pair (.var (.vs .vz)))))))
        (.var .vz)))

-- ============================================================================
-- Section 4: Rational Number Encoding
-- ============================================================================

-- A natural number n encodes the rational:
--   j₁(n) even:  +(j₁(n)/2)     / (j₂(n) + 1)
--   j₁(n) odd:   -((j₁(n)+1)/2) / (j₂(n) + 1)
--
-- We extract: sign, unsigned numerator, denominator.

/-- Unsigned numerator of the rational encoded by n.
    = div2(j₁(n) + isOdd(j₁(n))). -/
def rat_num {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (.app Term.div2
      (Term.app2 Term.add
        (.app Term.fst_pair (.var .vz))
        (.app Term.isOdd (.app Term.fst_pair (.var .vz)))))

/-- Denominator of the rational encoded by n: j₂(n) + 1. -/
def rat_den {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam (.app .succ (.app Term.snd_pair (.var .vz)))

/-- Sign of the rational encoded by n: 1 if positive (j₁(n) even), 0 if negative. -/
def rat_sign {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam (.app Term.isEven (.app Term.fst_pair (.var .vz)))

/-- Encode a rational from (sign, unsigned_num, denom_minus_1) → ℕ.
    sign = 1 → j₁ = 2·num (even)
    sign = 0 → j₁ = 2·num - 1 (odd, only makes sense when num > 0)
    For num = 0, the sign doesn't matter (both encode 0). -/
def rat_encode {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam (Term.lam
    -- sign = var (vs (vs vz)), num = var (vs vz), den_m1 = var vz
    (Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))  -- 2·num
        (.app Term.isOdd (.var (.vs (.vs .vz)))))              -- - isOdd(sign)
      (.var .vz))))                                            -- den_m1

-- ============================================================================
-- Section 5: Rational Arithmetic
-- ============================================================================

-- All rational operations take natural-number encodings and return encodings.

/-- Negation of a rational: flip the sign.
    neg_Q(n) = encode(1 - sign(n), num(n), j₂(n)). -/
def neg_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 Term.rat_encode
      (Term.app2 Term.monus (.app .succ .zero)      -- 1 - sign(n)
        (.app Term.rat_sign (.var .vz)))
      (.app Term.rat_num (.var .vz))                 -- num(n)
      (.app Term.snd_pair (.var .vz)))               -- j₂(n) = den - 1

/-- Rational addition: add_Q(n₁, n₂).
    Extracts signs, numerators, denominators, cross-multiplies,
    handles same/different sign cases. -/
def add_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    -- n₁ = var (vs vz), n₂ = var vz
    -- Let s₁ = rat_sign(n₁), p₁ = rat_num(n₁), d₁ = rat_den(n₁)
    -- Let s₂ = rat_sign(n₂), p₂ = rat_num(n₂), d₂ = rat_den(n₂)
    -- Let a = p₁ · d₂, b = p₂ · d₁  (cross products)
    -- same_sign = sg_bar(|s₁ - s₂|)
    -- result_num = ite(same, a + b, |a - b|)
    -- result_sign = ite(same, s₁, ite(geq(a,b), s₁, s₂))
    -- result_den_m1 = d₁ · d₂ - 1
    (let n₁ := Term.var (.vs .vz)
     let n₂ := Term.var .vz
     let s₁ := Term.app Term.rat_sign n₁
     let p₁ := Term.app Term.rat_num n₁
     let d₁ := Term.app Term.rat_den n₁
     let s₂ := Term.app Term.rat_sign n₂
     let p₂ := Term.app Term.rat_num n₂
     let d₂ := Term.app Term.rat_den n₂
     let a  := Term.app2 Term.mul p₁ d₂
     let b  := Term.app2 Term.mul p₂ d₁
     let same := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
     let result_num := Term.app3 Term.ite_nat same
       (Term.app2 Term.add a b)
       (Term.app2 Term.abs_diff a b)
     let result_sign := Term.app3 Term.ite_nat same s₁
       (Term.app3 Term.ite_nat (Term.app2 Term.geq a b) s₁ s₂)
     let result_den_m1 := Term.app Term.pd (Term.app2 Term.mul d₁ d₂)
     Term.app3 Term.rat_encode result_sign result_num result_den_m1))

/-- Rational subtraction: sub_Q(n₁, n₂) = add_Q(n₁, neg_Q(n₂)). -/
def sub_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.add_Q
      (.var (.vs .vz))
      (.app Term.neg_Q (.var .vz))))

/-- Rational multiplication: mul_Q(n₁, n₂).
    num = num₁ · num₂
    den = den₁ · den₂
    sign = same_sign(sign₁, sign₂) -/
def mul_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (let n₁ := Term.var (.vs .vz)
     let n₂ := Term.var .vz
     let s₁ := Term.app Term.rat_sign n₁
     let s₂ := Term.app Term.rat_sign n₂
     -- same sign = positive result
     let result_sign := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
     let result_num := Term.app2 Term.mul
       (Term.app Term.rat_num n₁) (Term.app Term.rat_num n₂)
     let result_den_m1 := Term.app Term.pd (Term.app2 Term.mul
       (Term.app Term.rat_den n₁) (Term.app Term.rat_den n₂))
     Term.app3 Term.rat_encode result_sign result_num result_den_m1))

/-- Absolute value of a rational: set sign to positive.
    abs_Q(n) = encode(1, num(n), j₂(n)). -/
def abs_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 Term.rat_encode
      (.app .succ .zero)                             -- sign = 1 (positive)
      (.app Term.rat_num (.var .vz))                 -- num(n)
      (.app Term.snd_pair (.var .vz)))               -- j₂(n) = den - 1

-- ============================================================================
-- Section 6: Rational Comparison (Decision Terms)
-- ============================================================================

-- Convention: decision terms return 0 when the predicate holds (matching qf_term).

/-- Less-than for rationals (decision term): returns 0 iff n₁ <_ℚ n₂.
    n₁ < n₂ ⟺ n₂ - n₁ is strictly positive
    ⟺ sign(sub(n₂, n₁)) = 1 ∧ num(sub(n₂, n₁)) > 0.
    Returns: |sign(d) - 1| + sg_bar(num(d)) where d = sub_Q(n₂, n₁). -/
def lt_Q_dec {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (let diff := Term.app2 Term.sub_Q (.var .vz) (.var (.vs .vz))
     Term.app2 Term.add
       (Term.app2 Term.abs_diff (.app Term.rat_sign diff) (.app .succ .zero))
       (.app Term.sg_bar (.app Term.rat_num diff))))

/-- Less-than-or-equal for rationals (decision term): returns 0 iff n₁ ≤_ℚ n₂.
    n₁ ≤ n₂ ⟺ n₂ - n₁ is non-negative
    ⟺ sign(sub(n₂, n₁)) = 1 ∨ num(sub(n₂, n₁)) = 0.
    Returns: |sign(d) - 1| · num(d) where d = sub_Q(n₂, n₁). -/
def le_Q_dec {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (let diff := Term.app2 Term.sub_Q (.var .vz) (.var (.vs .vz))
     Term.app2 Term.mul
       (Term.app2 Term.abs_diff (.app Term.rat_sign diff) (.app .succ .zero))
       (.app Term.rat_num diff)))

-- ============================================================================
-- Section 7: Rational Constants
-- ============================================================================

/-- Encode the natural number n as a (non-negative) rational: n/1.
    encode_nat_Q(n) = pair(2·n, 0). -/
def encode_nat_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app2 Term.pair
      (Term.app2 Term.mul (Term.ofNat 2) (.var .vz))
      .zero)

/-- Encode the rational 2^{-n} as a natural number.
    2^{-n} = 1 / 2^n, encoded as pair(2·1, 2^n - 1) = pair(2, exp2(n) - 1). -/
def pow2neg_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app2 Term.pair
      (Term.ofNat 2)                                 -- 2·1 = 2 (positive, numerator = 1)
      (.app Term.pd (.app Term.exp2 (.var .vz))))    -- exp2(n) - 1

/-- The rational zero: 0/1 = pair(0, 0). -/
def zero_Q {Γ : Ctx ι} : Term F Γ Ty.nat :=
  Term.app2 Term.pair .zero .zero

/-- The rational one: 1/1 = pair(2, 0). -/
def one_Q {Γ : Ctx ι} : Term F Γ Ty.nat :=
  Term.app2 Term.pair (Term.ofNat 2) .zero

-- ============================================================================
-- Section 8: Rational Equality (Decision Term and Formula)
-- ============================================================================

/-- Decision term for rational equality: returns 0 iff a =_ℚ b.
    eq_Q_dec(a, b) = |num(a)·den(b) - num(b)·den(a)| + |sign(a) - sign(b)| · sg(num(a) + num(b))

    This returns 0 exactly when:
    1. Cross products agree: num(a)·den(b) = num(b)·den(a), AND
    2. Either signs agree, or both numerators are 0 (encoding ±0). -/
def eq_Q_dec {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    -- a = var (vs vz), b = var vz
    (let a := Term.var (.vs .vz)
     let b := Term.var .vz
     let na := Term.app Term.rat_num a
     let nb := Term.app Term.rat_num b
     let da := Term.app Term.rat_den a
     let db := Term.app Term.rat_den b
     let sa := Term.app Term.rat_sign a
     let sb := Term.app Term.rat_sign b
     -- |na·db - nb·da| + |sa - sb| · sg(na + nb)
     Term.app2 Term.add
       (Term.app2 Term.abs_diff
         (Term.app2 Term.mul na db)
         (Term.app2 Term.mul nb da))
       (Term.app2 Term.mul
         (Term.app2 Term.abs_diff sa sb)
         (Term.app Term.sg (Term.app2 Term.add na nb)))))

end Term

/-- Rational equality as a QF formula: a =_ℚ b ≡ eq_Q_dec(a, b) =₀ 0. -/
def eq_Q {Γ : Ctx ι} (a b : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (Term.app2 Term.eq_Q_dec a b) Term.zero

/-- `eq_Q` is quantifier-free. -/
theorem eq_Q_isQF (a b : Term F Γ Ty.nat) : (eq_Q a b).isQF = true := by rfl

-- ============================================================================
-- Closed term substitution lemmas
-- ============================================================================

-- With primitive `lam`, all closed terms satisfy `subst σ t = t` by rfl.
-- We prove them individually to avoid deep defeq chains that time out.

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

-- Basic arithmetic closed_subst lemmas (terms from Arithmetic.lean)
@[simp] theorem add_closed_subst :
    (Term.add : Term F Γ _).subst σ = Term.add := by rfl
@[simp] theorem mul_closed_subst :
    (Term.mul : Term F Γ _).subst σ = Term.mul := by rfl
@[simp] theorem monus_closed_subst :
    (Term.monus : Term F Γ _).subst σ = Term.monus := by rfl
@[simp] theorem abs_diff_closed_subst :
    (Term.abs_diff : Term F Γ _).subst σ = Term.abs_diff := by rfl
@[simp] theorem pd_closed_subst :
    (Term.pd : Term F Γ _).subst σ = Term.pd := by rfl

@[simp] theorem sg_bar_closed_subst :
    (Term.sg_bar : Term F Γ _).subst σ = Term.sg_bar := by rfl
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
@[simp] theorem div2_closed_subst :
    (Term.div2 : Term F Γ _).subst σ = Term.div2 := by rfl
@[simp] theorem rat_num_closed_subst :
    (Term.rat_num : Term F Γ _).subst σ = Term.rat_num := by rfl
@[simp] theorem rat_den_closed_subst :
    (Term.rat_den : Term F Γ _).subst σ = Term.rat_den := by rfl
@[simp] theorem rat_sign_closed_subst :
    (Term.rat_sign : Term F Γ _).subst σ = Term.rat_sign := by rfl
@[simp] theorem rat_encode_closed_subst :
    (Term.rat_encode : Term F Γ _).subst σ = Term.rat_encode := by rfl
@[simp] theorem neg_Q_closed_subst :
    (Term.neg_Q : Term F Γ _).subst σ = Term.neg_Q := by rfl
@[simp] theorem add_Q_closed_subst :
    (Term.add_Q : Term F Γ _).subst σ = Term.add_Q := by rfl
@[simp] theorem sub_Q_closed_subst :
    (Term.sub_Q : Term F Γ _).subst σ = Term.sub_Q := by rfl
@[simp] theorem mul_Q_closed_subst :
    (Term.mul_Q : Term F Γ _).subst σ = Term.mul_Q := by rfl
@[simp] theorem abs_Q_closed_subst :
    (Term.abs_Q : Term F Γ _).subst σ = Term.abs_Q := by rfl
@[simp] theorem lt_Q_dec_closed_subst :
    (Term.lt_Q_dec : Term F Γ _).subst σ = Term.lt_Q_dec := by rfl
@[simp] theorem le_Q_dec_closed_subst :
    (Term.le_Q_dec : Term F Γ _).subst σ = Term.le_Q_dec := by rfl
@[simp] theorem eq_Q_dec_closed_subst :
    (Term.eq_Q_dec : Term F Γ _).subst σ = Term.eq_Q_dec := by rfl
@[simp] theorem encode_nat_Q_closed_subst :
    (Term.encode_nat_Q : Term F Γ _).subst σ = Term.encode_nat_Q := by rfl
@[simp] theorem pow2neg_Q_closed_subst :
    (Term.pow2neg_Q : Term F Γ _).subst σ = Term.pow2neg_Q := by rfl
@[simp] theorem zero_Q_closed_subst :
    (Term.zero_Q : Term F Γ _).subst σ = Term.zero_Q := by rfl
@[simp] theorem one_Q_closed_subst :
    (Term.one_Q : Term F Γ _).subst σ = Term.one_Q := by rfl

end ClosedSubst

-- ============================================================================
-- Section 9: Rational Ordered Field Axioms (as Derivable terms)
-- ============================================================================

-- These are number-theoretic facts provable in WE-HA^ω from the primitive
-- arithmetic operations (rec, succ, etc.) and the rational encoding.

variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) →
    Term F Γ (Ty.base i) → Formula F Γ}
  {al : Allowed} {Premises : PremiseSet F}
  (adm : AdmissibleEqX EqX)

-- ── Congruence helpers (outside section to avoid Γ capture) ──────────────

/-- s =₀ t → add(s, u) =₀ add(t, u) -/
private def add_congr_l {Γ : Ctx ι}
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (Formula.eq0 s t))
    (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add s u) (Term.app2 Term.add t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u s))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u t))

/-- s =₀ t → add(u, s) =₀ add(u, t) -/
private def add_congr_r {Γ : Ctx ι} (u : Term F Γ Ty.nat)
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add u s) (Term.app2 Term.add u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
        exact congrArg (Term.app · s) (congrArg (Term.app Term.add ·) (Term.weaken_subst0 u s)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
        exact congrArg (Term.app · t) (congrArg (Term.app Term.add ·) (Term.weaken_subst0 u t)))

/-- s =₀ t → mul(s, u) =₀ mul(t, u) -/
private def mul_congr_l {Γ : Ctx ι}
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (Formula.eq0 s t))
    (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul s u) (Term.app2 Term.mul t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.mul (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u s))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u t))

/-- s =₀ t → mul(u, s) =₀ mul(u, t) -/
private def mul_congr_r {Γ : Ctx ι} (u : Term F Γ Ty.nat)
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul u s) (Term.app2 Term.mul u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.mul u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
        exact congrArg (Term.app · s) (congrArg (Term.app Term.mul ·) (Term.weaken_subst0 u s)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
        exact congrArg (Term.app · t) (congrArg (Term.app Term.mul ·) (Term.weaken_subst0 u t)))

/-- s =₀ t → sg(s) =₀ sg(t) -/
private def sg_congr {Γ : Ctx ι} {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app Term.sg s) (Term.app Term.sg t)) :=
  qfer_no_premise_nat_nf h (r := Term.app Term.sg (.var .vz)) rfl rfl

section RationalOrderedField

variable {Γ : Ctx ι}

-- ── Helpers ────────────────────────────────────────────────────────────────

/-- Weaken introduction: from ⊢ A, derive ⊢ B → A. -/
private def weaken_intro {Γ : Ctx ι} {A B : Formula F Γ}
    (h : Derivable F EqX al Premises A) : Derivable F EqX al Premises (B →ᶠ A) :=
  .mp h (.exportation .and_weak)

/-- abs_diff(x, x) =₀ 0 for any x. From backward abs_diff_eq_zero_iff + refl0. -/
private def abs_diff_self (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.abs_diff x x) Term.zero) :=
  .mp .refl0 (.mp (abs_diff_eq_zero_iff adm x x) (.syllogism .and_perm .and_weak))

-- ── Equality is an equivalence relation ────────────────────────────────────

/-- ⊢ ∀a. eq_Q(a, a) -/
def eq_Q_refl :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (eq_Q (.var .vz) (.var .vz))) :=
  -- In context nat :: Γ, prove eq_Q_dec(a,a) =₀ 0
  let a : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let p := Term.app2 Term.mul (Term.app Term.rat_num a) (Term.app Term.rat_den a)
  let s := Term.app Term.rat_sign a
  let n := Term.app Term.rat_num a
  let Y := Term.app Term.sg (Term.app2 Term.add n n)
  -- Body of eq_Q_dec (in context nat :: nat :: nat :: Γ)
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have body_nf : (body.subst0 (a.weaken)).subst0 a =
      Term.app2 Term.add (Term.app2 Term.abs_diff p p)
        (Term.app2 Term.mul (Term.app2 Term.abs_diff s s) Y) := by
    simp only [body, p, s, n, Y, a, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  have body_eq : (Term.eq_Q_dec : Term F (Ty.nat :: Γ) _) = Term.lam (Term.lam body) := by rfl
  -- Unfold: eq_Q_dec(a,a) =₀ add(abs_diff(p,p), mul(abs_diff(s,s), Y))
  let unfold := body_eq ▸ lam2_correct_nf adm body a a body_nf
  -- abs_diff(p,p) =₀ 0 and abs_diff(s,s) =₀ 0
  let h1 := abs_diff_self adm p
  let h2 := abs_diff_self adm s
  -- mul(abs_diff(s,s), Y) =₀ 0: from h2 via or_weak + mul_eq_zero backward
  let h3 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.abs_diff s s) Y) Term.zero) :=
    .mp (.mp h2 .or_weak) (.mp (mul_eq_zero_iff adm _ Y) (.syllogism .and_perm .and_weak))
  -- add(abs_diff(p,p), mul(...)) =₀ 0: from h1, h3 via add_eq_zero backward
  let h4 : Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add (Term.app2 Term.abs_diff p p)
        (Term.app2 Term.mul (Term.app2 Term.abs_diff s s) Y)) Term.zero) :=
    .mp (.mp h3 (.mp h1 and_intro))
      (.mp (add_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  -- Chain unfold + h4: eq_Q_dec(a,a) =₀ 0
  let core : Derivable F EqX al Premises (eq_Q a a) :=
    .mp (.mp h4 (.mp unfold and_intro)) .trans0
  -- Universalize via forall_rule
  let step := Derivable.forall_rule (weaken_intro core (B := ⊥ᶠ →ᶠ ⊥ᶠ))
  let taut : Derivable F EqX al Premises (Γ := Γ) (⊥ᶠ →ᶠ ⊥ᶠ) :=
    .syllogism .and_contract .and_weak
  .mp taut step

/-- ⊢ ∀a,b. eq_Q(a, b) → eq_Q(b, a) -/
def eq_Q_sym :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs .vz)) (.var .vz) →ᶠ
         eq_Q (.var .vz) (.var (.vs .vz))))) :=
  let a : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let b : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let na := Term.app Term.rat_num a
  let nb := Term.app Term.rat_num b
  let da := Term.app Term.rat_den a
  let db := Term.app Term.rat_den b
  let sa := Term.app Term.rat_sign a
  let sb := Term.app Term.rat_sign b
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have body_eq : (Term.eq_Q_dec : Term F (Ty.nat :: Ty.nat :: Γ) _) = Term.lam (Term.lam body) := by rfl
  -- Normal forms for eq_Q_dec(a,b) and eq_Q_dec(b,a)
  have body_nf_ab : (body.subst0 (b.weaken)).subst0 a =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff (Term.app2 Term.mul na db) (Term.app2 Term.mul nb da))
        (Term.app2 Term.mul (Term.app2 Term.abs_diff sa sb)
          (Term.app Term.sg (Term.app2 Term.add na nb))) := by
    simp only [body, a, b, na, nb, da, db, sa, sb,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  have body_nf_ba : (body.subst0 (a.weaken)).subst0 b =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff (Term.app2 Term.mul nb da) (Term.app2 Term.mul na db))
        (Term.app2 Term.mul (Term.app2 Term.abs_diff sb sa)
          (Term.app Term.sg (Term.app2 Term.add nb na))) := by
    simp only [body, a, b, na, nb, da, db, sa, sb,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  let unfold_ab := body_eq ▸ lam2_correct_nf adm body a b body_nf_ab
  let unfold_ba := body_eq ▸ lam2_correct_nf adm body b a body_nf_ba
  -- NF_ab =₀ NF_ba via abs_diff_comm and add_comm
  let p1 := abs_diff_comm adm (Term.app2 Term.mul na db) (Term.app2 Term.mul nb da)
  let ml := mul_congr_l (abs_diff_comm adm sa sb) (Term.app Term.sg (Term.app2 Term.add na nb))
  let mr := mul_congr_r (Term.app2 Term.abs_diff sb sa) (sg_congr (add_comm adm na nb))
  let p2 := .mp (.mp mr (.mp ml and_intro)) .trans0
  let al' := add_congr_l p1 _
  let ar := add_congr_r _ p2
  let eq_nf := .mp (.mp ar (.mp al' and_intro)) .trans0
  -- eq_Q_dec(a,b) =₀ eq_Q_dec(b,a) via unfold + eq_nf + sym(unfold)
  let c1 := .mp (.mp eq_nf (.mp unfold_ab and_intro)) .trans0
  let h_eq := .mp (.mp (.mp unfold_ba .sym0) (.mp c1 and_intro)) .trans0
  -- eq_Q(a,b) → eq_Q(b,a)
  let core : Derivable F EqX al Premises (eq_Q a b →ᶠ eq_Q b a) :=
    .syllogism (pair_h (weaken_intro (.mp h_eq .sym0)) I_comb) .trans0
  univ_gen (univ_gen core)

/-- ⊢ ∀a,b,c. eq_Q(a, b) ∧ eq_Q(b, c) → eq_Q(a, c) -/
def eq_Q_trans :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q (.var (.vs (.vs .vz))) (.var .vz))))) :=
  sorry

-- ── Additive group ─────────────────────────────────────────────────────────

/-- ⊢ ∀a,b. eq_Q(add_Q(a, b), add_Q(b, a)) -/
def add_Q_comm :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_Q (.var .vz) (.var (.vs .vz)))))) :=
  sorry

/-- ⊢ ∀a,b,c. eq_Q(add_Q(add_Q(a,b), c), add_Q(a, add_Q(b,c))) -/
def add_Q_assoc :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q
          (Term.app2 Term.add_Q
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.add_Q (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀a. eq_Q(add_Q(a, zero_Q), a) -/
def add_Q_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var .vz) Term.zero_Q) (.var .vz))) :=
  sorry

/-- ⊢ ∀a. eq_Q(add_Q(a, neg_Q(a)), zero_Q) -/
def add_Q_neg :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var .vz)
                (Term.app Term.neg_Q (.var .vz)))
              Term.zero_Q)) :=
  sorry

-- ── Multiplicative monoid ──────────────────────────────────────────────────

/-- ⊢ ∀a,b. eq_Q(mul_Q(a, b), mul_Q(b, a)) -/
def mul_Q_comm :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.mul_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.mul_Q (.var .vz) (.var (.vs .vz)))))) :=
  sorry

/-- ⊢ ∀a,b,c. eq_Q(mul_Q(mul_Q(a,b), c), mul_Q(a, mul_Q(b,c))) -/
def mul_Q_assoc :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q
          (Term.app2 Term.mul_Q
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.mul_Q (.var (.vs (.vs .vz)))
            (Term.app2 Term.mul_Q (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀a. eq_Q(mul_Q(a, one_Q), a) -/
def mul_Q_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.mul_Q (.var .vz) Term.one_Q) (.var .vz))) :=
  sorry

-- ── Distributivity ─────────────────────────────────────────────────────────

/-- ⊢ ∀a,b,c. eq_Q(mul_Q(a, add_Q(b,c)), add_Q(mul_Q(a,b), mul_Q(a,c))) -/
def distrib_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q
          (Term.app2 Term.mul_Q (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz)))
          (Term.app2 Term.add_Q
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  sorry

-- ── Order properties ───────────────────────────────────────────────────────

/-- Rational less-than as a QF formula: a <_ℚ b ≡ lt_Q_dec(a, b) =₀ 0. -/
def lt_Q {Γ : Ctx ι} (a b : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (Term.app2 Term.lt_Q_dec a b) Term.zero

/-- Rational less-or-equal as a QF formula: a ≤_ℚ b ≡ le_Q_dec(a, b) =₀ 0. -/
def le_Q {Γ : Ctx ι} (a b : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (Term.app2 Term.le_Q_dec a b) Term.zero

/-- ⊢ ∀a. ¬(lt_Q(a, a))  (irreflexivity) -/
def lt_Q_irrefl :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (¬ᶠ lt_Q (.var .vz) (.var .vz))) :=
  sorry

/-- ⊢ ∀a,b,c. lt_Q(a, b) ∧ lt_Q(b, c) → lt_Q(a, c)  (transitivity) -/
def lt_Q_trans :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ lt_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ lt_Q (.var (.vs (.vs .vz))) (.var .vz))))) :=
  sorry

/-- ⊢ ∀a,b. lt_Q(a, b) ∨ eq_Q(a, b) ∨ lt_Q(b, a)  (trichotomy) -/
def lt_Q_trichotomy :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (.var (.vs .vz)) (.var .vz)
          ∨ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          ∨ᶠ lt_Q (.var .vz) (.var (.vs .vz))))) :=
  sorry

/-- ⊢ ∀a,b,c. lt_Q(a, b) → lt_Q(add_Q(a, c), add_Q(b, c))
    (order compatible with addition) -/
def lt_Q_add :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (.var (.vs (.vs .vz))) (.var (.vs .vz))
          →ᶠ lt_Q
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var .vz))
            (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz)))))) :=
  sorry

/-- ⊢ ∀a,b. lt_Q(zero_Q, a) ∧ lt_Q(zero_Q, b) → lt_Q(zero_Q, mul_Q(a, b))
    (positive times positive is positive) -/
def lt_Q_mul_pos :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q Term.zero_Q (.var (.vs .vz))
          ∧ᶠ lt_Q Term.zero_Q (.var .vz)
          →ᶠ lt_Q Term.zero_Q
            (Term.app2 Term.mul_Q (.var (.vs .vz)) (.var .vz))))) :=
  sorry

/-- ⊢ lt_Q(zero_Q, one_Q) -/
def zero_lt_one_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (lt_Q Term.zero_Q Term.one_Q) :=
  sorry

-- ── Congruence (eq_Q respects operations) ──────────────────────────────────

/-- ⊢ ∀a,b,c,d. eq_Q(a,b) ∧ eq_Q(c,d) → eq_Q(add_Q(a,c), add_Q(b,d)) -/
def add_Q_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.add_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀a,b,c,d. eq_Q(a,b) ∧ eq_Q(c,d) → eq_Q(mul_Q(a,c), mul_Q(b,d)) -/
def mul_Q_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.mul_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  sorry

end RationalOrderedField

end Metatheorems
