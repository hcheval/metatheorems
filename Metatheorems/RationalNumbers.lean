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
        (.app Term.isEven (.var (.vs (.vs .vz)))))             -- - isEven(sign)
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

private def sg_bar_congr {Γ : Ctx ι} {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app Term.sg_bar s) (Term.app Term.sg_bar t)) :=
  qfer_no_premise_nat_nf h (r := Term.app Term.sg_bar (.var .vz)) rfl rfl

private def pd_congr {Γ : Ctx ι} {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app Term.pd s) (Term.app Term.pd t)) :=
  qfer_no_premise_nat_nf h (r := Term.app Term.pd (.var .vz)) rfl rfl

/-- Variant of `Term.weaken_subst0` matching the eta-expanded form left by `simp`. -/
private theorem weaken_subst0_eta (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (fun {_τ} => Term.subst0_map s) (Term.weaken t) = t :=
  Term.weaken_subst0 t s

/-- Congruence for a closed ternary operation: from three pairwise equalities. -/
private def app3_congr_closed {Γ : Ctx ι}
    (f : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat →ₜ Ty.nat))
    {a a' b b' c c' : Term F Γ Ty.nat}
    (ha : Derivable F EqX al Premises (Formula.eq0 a a'))
    (hb : Derivable F EqX al Premises (Formula.eq0 b b'))
    (hc : Derivable F EqX al Premises (Formula.eq0 c c')) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app3 f a b c) (Term.app3 f a' b' c')) :=
  have mk_nf (x y z : Term F Γ Ty.nat) :
      (Term.app3 f.weaken x.weaken y.weaken (.var .vz) : Term F (Ty.nat :: Γ) _).subst0 z =
      Term.app3 f x y z := by
    simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
      weaken_subst0_eta]
  have mk_nf2 (x z : Term F Γ Ty.nat) (y : Term F Γ Ty.nat) :
      (Term.app3 f.weaken x.weaken (.var .vz) z.weaken : Term F (Ty.nat :: Γ) _).subst0 y =
      Term.app3 f x y z := by
    simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
      weaken_subst0_eta]
  have mk_nf3 (y z : Term F Γ Ty.nat) (x : Term F Γ Ty.nat) :
      (Term.app3 f.weaken (.var .vz) y.weaken z.weaken : Term F (Ty.nat :: Γ) _).subst0 x =
      Term.app3 f x y z := by
    simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
      weaken_subst0_eta]
  let s1 := qfer_no_premise_nat_nf hc (mk_nf a b c) (mk_nf a b c')
  let s2 := qfer_no_premise_nat_nf hb (mk_nf2 a c' b) (mk_nf2 a c' b')
  let s3 := qfer_no_premise_nat_nf ha (mk_nf3 b' c' a) (mk_nf3 b' c' a')
  .mp (.mp s3 (.mp (.mp (.mp s2 (.mp s1 and_intro)) .trans0) and_intro)) .trans0

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

-- ── sg evaluation ─────────────────────────────────────────────────────────

private theorem sg_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.app .succ .zero)))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.app .succ .zero))) s := by rfl

/-- sg(0) = 0. -/
private def sg_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app Term.sg Term.zero) Term.zero) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.app .succ .zero))) (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- sg(Sn) = 1. -/
private def sg_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.sg (.app .succ n)) (.app .succ .zero)) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.app .succ .zero))) (.var .vz)
  let z := Term.lam (Term.lam ((.app .succ .zero) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat))
  let h1 := lam_correct_nf body (.app .succ n) (sg_body_nf _)
  let h2 := lam2_correct_nf adm ((.app .succ .zero) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    (Term.app3 (.prec Ty.nat) .zero z n) n
    (by simp only [Term.subst0, Term.subst])
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)

-- ── ite_nat evaluation ────────────────────────────────────────────────────

private theorem ite_nat_body_nf {Γ : Ctx ι} (b x y : Term F Γ Ty.nat) :
    (((Term.app2 Term.add
      (Term.app2 Term.mul (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (Term.app2 Term.mul
        (Term.app2 Term.monus (.app .succ .zero) (.var (.vs (.vs .vz))))
        (.var .vz))
      : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0
        y.weaken.weaken).subst0 x.weaken).subst0 b =
    Term.app2 Term.add
      (Term.app2 Term.mul b x)
      (Term.app2 Term.mul (Term.app2 Term.monus (.app .succ .zero) b) y) := by
  simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
    add_closed_subst, mul_closed_subst, monus_closed_subst, weaken_subst0_eta]

/-- Beta-reduction of ite_nat:
    ite_nat(b, x, y) =₀ add(mul(b, x), mul(monus(1, b), y)). -/
private def ite_nat_unfold (b x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (eqAtType EqX Ty.nat
      (Term.app3 Term.ite_nat b x y)
      (Term.app2 Term.add (Term.app2 Term.mul b x)
        (Term.app2 Term.mul (Term.app2 Term.monus (.app .succ .zero) b) y))) :=
  lam3_correct_nf adm _ b x y (ite_nat_body_nf b x y)

/-- ite_nat(0, x, y) =₀ y. -/
private def ite_nat_zero (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app3 Term.ite_nat Term.zero x y) y) :=
  let h1 := ite_nat_unfold adm Term.zero x y
  let h2 := mul_zero_l adm x
  let h3 := add_zero_l adm (Term.app2 Term.mul (Term.app2 Term.monus (.app .succ .zero) Term.zero) y)
  let h4 := monus_zero adm (.app .succ .zero)
  let h5 := mul_one_l adm y
  let h6 := mul_congr_l h4 y
  let c1 := add_congr_l h2 (Term.app2 Term.mul (Term.app2 Term.monus (.app .succ .zero) Term.zero) y)
  let c2 := .mp (.mp h3 (.mp c1 and_intro)) .trans0
  let c3 := .mp (.mp h6 (.mp c2 and_intro)) .trans0
  let c4 := .mp (.mp h5 (.mp c3 and_intro)) .trans0
  .mp (.mp c4 (.mp h1 and_intro)) .trans0

/-- ite_nat(S0, x, y) =₀ x. -/
private def ite_nat_one (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app3 Term.ite_nat (.app .succ .zero) x y) x) :=
  let h1 := ite_nat_unfold adm (.app .succ .zero) x y
  let h2 := mul_one_l adm x
  let h3 := monus_succ_l adm .zero .zero
  let h4 := monus_zero adm .zero
  let h5 := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  let h6 := mul_zero_l adm y
  let h7 := .mp (.mp h6 (.mp (mul_congr_l h5 y) and_intro)) .trans0
  let h8 := add_zero_r adm x
  let c1 := add_congr_l h2 (Term.app2 Term.mul (Term.app2 Term.monus (.app .succ .zero) (.app .succ .zero)) y)
  let c2 := add_congr_r x h7
  let c3 := .mp (.mp c2 (.mp c1 and_intro)) .trans0
  let c4 := .mp (.mp h8 (.mp c3 and_intro)) .trans0
  .mp (.mp c4 (.mp h1 and_intro)) .trans0

-- ── Congruence for closed unary functions ─────────────────────────────────

private def triag_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.triag s) (.app Term.triag t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.triag (.var .vz)) rfl rfl

private def inv_triag_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.inv_triag s) (.app Term.inv_triag t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.inv_triag (.var .vz)) rfl rfl

private def fst_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.fst_pair s) (.app Term.fst_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.fst_pair (.var .vz)) rfl rfl

private def snd_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.snd_pair s) (.app Term.snd_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.snd_pair (.var .vz)) rfl rfl

private def isEven_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.isEven s) (.app Term.isEven t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.isEven (.var .vz)) rfl rfl

private def isOdd_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.isOdd s) (.app Term.isOdd t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.isOdd (.var .vz)) rfl rfl

private def div2_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.div2 s) (.app Term.div2 t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.div2 (.var .vz)) rfl rfl

private def rat_num_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.rat_num s) (.app Term.rat_num t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_num (.var .vz)) rfl rfl

private def rat_den_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.rat_den s) (.app Term.rat_den t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_den (.var .vz)) rfl rfl

private def rat_sign_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app Term.rat_sign s) (.app Term.rat_sign t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_sign (.var .vz)) rfl rfl

private def monus_congr_l {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus s u) (Term.app2 Term.monus t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.monus (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u s))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u t))

private def monus_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus u s) (Term.app2 Term.monus u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.monus u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg (Term.app · s) (congrArg (Term.app Term.monus ·) (Term.weaken_subst0 u s)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg (Term.app · t) (congrArg (Term.app Term.monus ·) (Term.weaken_subst0 u t)))

-- ── triag evaluation ──────────────────────────────────────────────────────

private theorem triag_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat) .zero
      (Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz)))))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat) .zero
      (Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz))))) s := by rfl

/-- triag(0) =₀ 0. -/
private def triag_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.triag Term.zero) Term.zero) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero
      (Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz))))) (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- triag(Sn) =₀ add(triag(n), Sn). -/
private def triag_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.triag (.app .succ n))
        (Term.app2 Term.add (.app Term.triag n) (.app .succ n))) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero
      (Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz))))) (.var .vz)
  let step_fn : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
    Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz))))
  let rec_n : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) .zero step_fn n
  let h1 := lam_correct_nf body (.app .succ n) (triag_body_nf _)
  let h2 := lam2_correct_nf adm
    (Term.app2 Term.add (.var (.vs .vz)) (.app .succ (.var .vz))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    rec_n n
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          add_closed_subst, weaken_subst0_eta]
        rfl)
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  -- Convert rec_n to triag(n): triag(n) =₀ rec_n by lam_correct
  let h3 := lam_correct_nf body n (triag_body_nf _)
  let h4 := add_congr_l (.mp h3 .sym0) (.app .succ n)
  .mp (.mp h4 (.mp c2 and_intro)) .trans0

-- ── pair evaluation ───────────────────────────────────────────────────────

private theorem pair_body_nf {Γ : Ctx ι} (x y : Term F Γ Ty.nat) :
    ((Term.app2 Term.add
      (.app Term.triag (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
      (.var (.vs .vz))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 y.weaken).subst0 x =
    Term.app2 Term.add
      (.app Term.triag (Term.app2 Term.add x y)) x := by
  simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
    add_closed_subst, triag_closed_subst, weaken_subst0_eta]

/-- pair(x, y) =₀ add(triag(add(x, y)), x). -/
private def pair_unfold (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.pair x y)
        (Term.app2 Term.add (.app Term.triag (Term.app2 Term.add x y)) x)) :=
  lam2_correct_nf adm _ x y (pair_body_nf x y)

/-- pair(0, 0) =₀ 0. -/
private def pair_zero_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.pair Term.zero Term.zero) Term.zero) :=
  -- pair(0,0) =₀ add(triag(add(0,0)), 0)
  let h1 := pair_unfold adm Term.zero Term.zero
  -- add(0,0) =₀ 0
  let h2 := add_zero_r adm Term.zero
  -- triag(add(0,0)) =₀ triag(0)
  let h3 := triag_congr h2
  -- triag(0) =₀ 0
  let h4 := triag_zero
  -- triag(add(0,0)) =₀ 0
  let h5 := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  -- add(triag(add(0,0)), 0) =₀ add(0, 0)
  let h6 := add_congr_l h5 Term.zero
  -- add(0, 0) =₀ 0
  let h7 := add_zero_r adm Term.zero
  -- Chain
  let h8 := .mp (.mp h7 (.mp h6 and_intro)) .trans0
  .mp (.mp h8 (.mp h1 and_intro)) .trans0

-- ── inv_triag and fst_pair evaluation at 0 ────────────────────────────────

private theorem inv_triag_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat)
      .zero
      (Term.lam (Term.lam
        (Term.app2 Term.add (.var (.vs .vz))
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat)
      .zero
      (Term.lam (Term.lam
        (Term.app2 Term.add (.var (.vs .vz))
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))
      s := by rfl

/-- inv_triag(0) =₀ 0. -/
private def inv_triag_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.inv_triag Term.zero) Term.zero) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat)
      .zero
      (Term.lam (Term.lam
        (Term.app2 Term.add (.var (.vs .vz))
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))
      (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

private theorem fst_pair_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app2 Term.monus (.var .vz) (.app Term.triag (.app Term.inv_triag (.var .vz)))
      : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app2 Term.monus s (.app Term.triag (.app Term.inv_triag s)) := by rfl

/-- fst_pair(n) =₀ monus(n, triag(inv_triag(n))). -/
private def fst_pair_unfold (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair n)
        (Term.app2 Term.monus n (.app Term.triag (.app Term.inv_triag n)))) :=
  lam_correct_nf _ n (fst_pair_body_nf n)

/-- fst_pair(0) =₀ 0. -/
private def fst_pair_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.fst_pair Term.zero) Term.zero) :=
  -- fst_pair(0) =₀ monus(0, triag(inv_triag(0)))
  let h1 := fst_pair_unfold Term.zero
  -- inv_triag(0) =₀ 0
  let h2 := inv_triag_zero
  -- triag(inv_triag(0)) =₀ triag(0)
  let h3 := triag_congr h2
  -- triag(0) =₀ 0
  let h4 := triag_zero
  -- triag(inv_triag(0)) =₀ 0
  let h5 := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  -- monus(0, triag(inv_triag(0))) =₀ monus(0, 0)
  let h6 := monus_congr_r Term.zero h5
  -- monus(0, 0) =₀ 0
  let h7 := monus_zero adm Term.zero
  -- Chain
  let h8 := .mp (.mp h7 (.mp h6 and_intro)) .trans0
  .mp (.mp h8 (.mp h1 and_intro)) .trans0

private theorem snd_pair_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app2 Term.monus (.app Term.inv_triag (.var .vz)) (.app Term.fst_pair (.var .vz))
      : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app2 Term.monus (.app Term.inv_triag s) (.app Term.fst_pair s) := by rfl

/-- snd_pair(0) =₀ 0. -/
private def snd_pair_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.snd_pair Term.zero) Term.zero) :=
  let h1 := lam_correct_nf _ (Term.zero : Term F Γ _) (snd_pair_body_nf _)
  -- inv_triag(0) =₀ 0 and fst_pair(0) =₀ 0
  let h2 := monus_congr_l inv_triag_zero (Term.app Term.fst_pair Term.zero)
  let h3 := monus_congr_r Term.zero (fst_pair_zero adm)
  let h4 := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  let h5 := monus_zero adm Term.zero
  let h6 := .mp (.mp h5 (.mp h4 and_intro)) .trans0
  .mp (.mp h6 (.mp h1 and_intro)) .trans0

-- ── isEven evaluation ─────────────────────────────────────────────────────

private theorem isEven_body_nf {Γ : Ctx ι} (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat) (.app .succ .zero)
      (Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz)))))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat) (.app .succ .zero)
      (Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))) s := by rfl

/-- isEven(0) =₀ 1. -/
private def isEven_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isEven Term.zero) (.app .succ .zero)) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.app .succ .zero)
      (Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))) (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- isOdd(n) =₀ monus(1, isEven(n)). (Definitional unfold) -/
private def isOdd_unfold (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isOdd n) (Term.app2 Term.monus (.app .succ .zero) (.app Term.isEven n))) :=
  lam_correct_nf
    (Term.app2 Term.monus (.app .succ .zero) (.app Term.isEven (.var .vz))
      : Term F (Ty.nat :: Γ) Ty.nat) n (by rfl)

/-- isOdd(0) =₀ 0. -/
private def isOdd_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isOdd Term.zero) Term.zero) :=
  let h1 := isOdd_unfold Term.zero
  let h2 := monus_congr_r (.app .succ .zero) isEven_zero
  let h3 := monus_succ_l adm .zero .zero
  let h4 := monus_zero adm .zero
  let h5 := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  let h6 := .mp (.mp h5 (.mp h2 and_intro)) .trans0
  .mp (.mp h6 (.mp h1 and_intro)) .trans0

-- ── succ_congr (needed locally since Arithmetic.lean's is private) ─────────

private def succ_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) rfl rfl

-- ── rat_sign/rat_num/rat_den of zero_Q ────────────────────────────────────

/-- rat_sign(zero_Q) =₀ 1. -/
private def rat_sign_zero_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_sign Term.zero_Q) (.app .succ .zero)) :=
  -- rat_sign(n) = isEven(fst_pair(n)); zero_Q = pair(0,0)
  -- rat_sign(pair(0,0)) =₀ rat_sign(0) by rat_sign_congr(pair_zero_zero)
  let h1 := rat_sign_congr (pair_zero_zero adm)
  -- rat_sign(0) = isEven(fst_pair(0))
  -- Need: rat_sign(0) =₀ isEven(fst_pair(0))
  let h2 := Term.lam_correct
    (.app Term.isEven (.app Term.fst_pair (.var .vz)) : Term F (Ty.nat :: Γ) _) Term.zero
  -- isEven(fst_pair(0)) =₀ isEven(0)
  let h3 := isEven_congr (fst_pair_zero adm)
  -- isEven(0) =₀ 1
  let h4 := isEven_zero
  -- Chain: rat_sign(pair(0,0)) =₀ rat_sign(0) =₀ isEven(fst_pair(0)) =₀ isEven(0) =₀ 1
  let c1 := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  let c2 := .mp (.mp h4 (.mp c1 and_intro)) .trans0
  .mp (.mp c2 (.mp h1 and_intro)) .trans0

/-- rat_den(zero_Q) =₀ S0. -/
private def rat_den_zero_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_den Term.zero_Q) (.app .succ .zero)) :=
  -- rat_den(pair(0,0)) =₀ rat_den(0) by congr
  let h1 := rat_den_congr (pair_zero_zero adm)
  -- rat_den(0) = S(snd_pair(0))
  let h2 := Term.lam_correct
    (.app .succ (.app Term.snd_pair (.var .vz)) : Term F (Ty.nat :: Γ) _) Term.zero
  -- S(snd_pair(0)) =₀ S(0)
  let h3 := succ_congr (snd_pair_zero adm)
  -- Chain
  let c1 := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  .mp (.mp c1 (.mp h1 and_intro)) .trans0

-- ── Small-value evaluation: triag(1) =₀ 1, pair(0,1) =₀ 1 ───────────────

/-- triag(1) =₀ 1. -/
private def triag_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.triag (.app .succ .zero)) (.app .succ .zero)) :=
  let h1 := triag_succ adm Term.zero
  let h2 := add_congr_l triag_zero (.app .succ .zero)
  let h3 := add_zero_l adm (.app .succ .zero)
  let c := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

/-- pair(0, S0) =₀ S0. -/
private def pair_zero_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.pair Term.zero (.app .succ .zero)) (.app .succ .zero)) :=
  let h1 := pair_unfold adm Term.zero (.app .succ .zero)
  let h2 := add_zero_l adm (.app .succ .zero)
  let h3 := .mp (.mp (triag_one adm) (.mp (triag_congr h2) and_intro)) .trans0
  let h4 := add_congr_l h3 Term.zero
  let h5 := add_zero_r adm (.app .succ .zero)
  let c := .mp (.mp h5 (.mp h4 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

-- ── inv_triag(S0) =₀ S0, fst_pair(S0) =₀ 0 ──────────────────────────────

-- The rec_succ unfold produces the literal rec subterm `rec(0, step, 0)`.
-- This is syntactically the SAME term as `body[0]` from `inv_triag = lam(body)`,
-- so we work directly with the rec term rather than `inv_triag(0)`.

/-- inv_triag(S0) =₀ S0. -/
private def inv_triag_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.inv_triag (.app .succ .zero)) (.app .succ .zero)) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat)
      .zero
      (Term.lam (Term.lam
        (Term.app2 Term.add (.var (.vs .vz))
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))
      (.var .vz)
  let step_fn := Term.lam (Term.lam
    (Term.app2 Term.add (.var (.vs .vz))
      (.app Term.sg_bar
        (Term.app2 Term.monus
          (.app Term.triag (.app .succ (.var (.vs .vz))))
          (.app .succ (.var .vz))))))
  -- Abbreviation for rec(0, step, 0) — the literal rec term from body[0]
  let r0 : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) .zero step_fn .zero
  -- inv_triag(S0) =₀ body[S0] by lam_correct
  let h1 := lam_correct_nf body (.app .succ .zero) (inv_triag_body_nf _)
  -- body[S0] = rec(0, step, S0) =₀ step(rec(0,step,0), 0) by rec_succ
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  -- step(r0, 0) = add(r0, sg_bar(monus(triag(S(r0)), S0))) by lam2_correct
  let h2 := lam2_correct_nf adm
    (Term.app2 Term.add (.var (.vs .vz))
      (.app Term.sg_bar
        (Term.app2 Term.monus (.app Term.triag (.app .succ (.var (.vs .vz))))
          (.app .succ (.var .vz))))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    r0 .zero (by rfl)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  -- Now: inv_triag(S0) =₀ add(r0, sg_bar(monus(triag(S(r0)), S0)))
  -- r0 = rec(0, step, 0) =₀ 0 by rec_zero
  let r0_eq : Derivable F EqX al Premises (Formula.eq0 r0 Term.zero) :=
    .rec_zero (ρ := Ty.nat)
  -- triag(S(r0)) =₀ triag(S0) =₀ 1
  let h3 := .mp (.mp (triag_one adm) (.mp (triag_congr (succ_congr r0_eq)) and_intro)) .trans0
  -- monus(triag(S(r0)), S0) =₀ monus(1, 1) =₀ 0
  let h4 := monus_congr_l h3 (.app .succ .zero)
  let monus_11 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus (.app .succ .zero) (.app .succ .zero)) Term.zero) :=
    .mp (.mp (monus_zero adm .zero) (.mp (monus_succ_l adm .zero .zero) and_intro)) .trans0
  let h5 := .mp (.mp monus_11 (.mp h4 and_intro)) .trans0
  -- sg_bar(monus(...)) =₀ sg_bar(0) =₀ 1
  let h6 := .mp (.mp (sg_bar_zero (Premises := Premises)) (.mp (sg_bar_congr h5) and_intro)) .trans0
  -- add(r0, sg_bar(...)) =₀ add(0, 1) =₀ 1
  let h7 := add_congr_l r0_eq _
  let h8 := add_congr_r Term.zero h6
  let h9 := .mp (.mp h8 (.mp h7 and_intro)) .trans0
  let h10 := .mp (.mp (add_zero_l adm (.app .succ .zero)) (.mp h9 and_intro)) .trans0
  -- Chain
  .mp (.mp h10 (.mp c2 and_intro)) .trans0

-- ── fst_pair(S0) =₀ 0 and snd_pair(S0) =₀ 0 ────────────────────────────

/-- fst_pair(S0) =₀ 0. Since inv_triag(S0)=S0, triag(S0)=S0:
    fst_pair(S0) = monus(S0, triag(inv_triag(S0))) = monus(S0, triag(S0)) = monus(S0, S0) = 0. -/
private def fst_pair_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.fst_pair (.app .succ .zero)) Term.zero) :=
  let h1 := fst_pair_unfold (.app .succ .zero)
  -- triag(inv_triag(S0)) =₀ triag(S0)
  let h2 := triag_congr (inv_triag_one adm)
  -- triag(S0) =₀ S0
  let h3 := .mp (.mp (triag_one adm) (.mp h2 and_intro)) .trans0
  -- monus(S0, triag(inv_triag(S0))) =₀ monus(S0, S0)
  let h4 := monus_congr_r (.app .succ .zero) h3
  -- monus(S0, S0) =₀ 0
  let h5 := monus_self adm (.app .succ .zero)
  let c := .mp (.mp h5 (.mp h4 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

/-- snd_pair(S0) =₀ S0. Since inv_triag(S0)=S0, fst_pair(S0)=0:
    snd_pair(S0) = monus(S0, 0) = S0. -/
private def snd_pair_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.snd_pair (.app .succ .zero)) (.app .succ .zero)) :=
  -- snd_pair(S0) =₀ monus(inv_triag(S0), fst_pair(S0)) by lam_correct
  let h1 : Derivable F EqX al Premises (Formula.eq0
      (.app Term.snd_pair (.app .succ .zero))
      (Term.app2 Term.monus (.app Term.inv_triag (.app .succ .zero)) (.app Term.fst_pair (.app .succ .zero)))) :=
    lam_correct_nf _ ((.app .succ .zero) : Term F Γ _) (snd_pair_body_nf _)
  -- inv_triag(S0) =₀ S0
  let h2 := monus_congr_l (inv_triag_one adm) (.app Term.fst_pair (.app .succ .zero))
  -- fst_pair(S0) =₀ 0
  let h3 := monus_congr_r (.app .succ .zero) (fst_pair_one adm)
  let h4 := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  -- monus(S0, 0) =₀ S0
  let h5 := monus_zero adm (.app .succ .zero)
  let h6 := .mp (.mp h5 (.mp h4 and_intro)) .trans0
  .mp (.mp h6 (.mp h1 and_intro)) .trans0

-- ── div2(0) =₀ 0 ─────────────────────────────────────────────────────────

/-- div2(0) =₀ 0. State(0) = pair(0, S0). div2(0) = fst_pair(pair(0, S0)). -/
private def div2_zero :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.div2 Term.zero) Term.zero) :=
  -- div2(0) = fst_pair(rec(pair(0,1), step, 0)) by lam_correct
  -- rec(..., 0) =₀ pair(0,1) by rec_zero
  -- fst_pair(pair(0,1)) =₀ fst_pair(S0) by fst_pair_congr(pair_zero_one)
  -- fst_pair(S0) =₀ 0 by fst_pair_one
  let div2_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.fst_pair
      (Term.app3 (.prec Ty.nat)
        (Term.app2 Term.pair .zero (.app .succ .zero))
        (Term.lam (Term.lam
          (Term.app2 Term.pair
            (Term.app2 Term.add
              (.app Term.fst_pair (.var (.vs .vz)))
              (.app Term.snd_pair (.var (.vs .vz))))
            (.app Term.sg_bar
              (.app Term.snd_pair (.var (.vs .vz)))))))
        (.var .vz))
  let h1 := lam_correct_nf div2_body Term.zero (by rfl)
  -- fst_pair(rec(pair(0,1), step, 0)) =₀ fst_pair(pair(0,1)) by rec_zero + congr
  let h2 := fst_pair_congr (.rec_zero (ρ := Ty.nat) : Derivable F EqX al Premises _)
  -- fst_pair(pair(0,1)) =₀ fst_pair(S0) by congr(pair_zero_one)
  let h3 := fst_pair_congr (pair_zero_one adm)
  -- fst_pair(S0) =₀ 0
  let h4 := fst_pair_one adm
  -- Chain
  let c1 := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  let c2 := .mp (.mp h4 (.mp c1 and_intro)) .trans0
  .mp (.mp c2 (.mp h1 and_intro)) .trans0

-- ── rat_num(zero_Q) =₀ 0 ─────────────────────────────────────────────────

/-- rat_num(zero_Q) =₀ 0.
    rat_num(n) = div2(fst_pair(n) + isOdd(fst_pair(n)))
    For zero_Q = pair(0,0): fst_pair(0) = 0, isOdd(0) = 0, so div2(0+0) = div2(0) = 0. -/
private def rat_num_zero_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_num Term.zero_Q) Term.zero) :=
  -- rat_num(pair(0,0)) =₀ rat_num(0)
  let h1 := rat_num_congr (pair_zero_zero adm)
  -- rat_num(0) =₀ div2(add(fst_pair(0), isOdd(fst_pair(0))))
  let rat_num_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.div2
      (Term.app2 Term.add
        (.app Term.fst_pair (.var .vz))
        (.app Term.isOdd (.app Term.fst_pair (.var .vz))))
  let h2 := lam_correct_nf rat_num_body Term.zero (by rfl)
  -- fst_pair(0) =₀ 0
  -- isOdd(fst_pair(0)) =₀ isOdd(0) =₀ 0
  let h3 := .mp (.mp (isOdd_zero adm) (.mp (isOdd_congr (fst_pair_zero adm)) and_intro)) .trans0
  -- add(fst_pair(0), isOdd(fst_pair(0))) =₀ add(0, 0) =₀ 0
  let h4 := add_congr_l (fst_pair_zero adm) _
  let h5 := add_congr_r Term.zero h3
  let h6 := .mp (.mp h5 (.mp h4 and_intro)) .trans0
  let h7 := .mp (.mp (add_zero_r adm Term.zero) (.mp h6 and_intro)) .trans0
  -- div2(add(...)) =₀ div2(0)
  let h8 := div2_congr h7
  -- div2(0) =₀ 0
  let h9 := div2_zero adm
  -- Chain
  let c1 := .mp (.mp h8 (.mp h2 and_intro)) .trans0
  let c2 := .mp (.mp h9 (.mp c1 and_intro)) .trans0
  .mp (.mp c2 (.mp h1 and_intro)) .trans0

-- ── Equality is an equivalence relation ────────────────────────────────────

-- ── Additional arithmetic helpers ─────────────────────────────────────────

/-- |n - 0| =₀ n. abs_diff(n, 0) = add(monus(n,0), monus(0,n)) = add(n, 0) = n. -/
private def abs_diff_zero_r (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.abs_diff n Term.zero) n) :=
  let h1 := lam2_correct_nf adm
    (Term.app2 Term.add
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    n Term.zero (by rfl)
  -- add(monus(n,0), monus(0,n)) =₀ add(n, monus(0,n))
  let h2 := add_congr_l (monus_zero adm n) _
  -- monus(0,n) =₀ 0
  let h3 := add_congr_r n (monus_zero_l adm n)
  -- add(n, 0) =₀ n
  let h4 := add_zero_r adm n
  let c := .mp (.mp h4 (.mp (.mp (.mp h3 (.mp h2 and_intro)) .trans0) and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

/-- |0 - n| =₀ n. -/
private def abs_diff_zero_l (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.abs_diff Term.zero n) n) :=
  .mp (.mp (abs_diff_zero_r adm n) (.mp (abs_diff_comm adm Term.zero n) and_intro)) .trans0


/-- geq(n, 0) =₀ S0 for all n. geq(n,0) = sg_bar(monus(0,n)) = sg_bar(0) = 1. -/
private def geq_zero_r (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.geq n Term.zero) (.app .succ .zero)) :=
  let h1 := lam2_correct_nf adm
    (.app Term.sg_bar (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    n Term.zero (by rfl)
  let h2 := sg_bar_congr (monus_zero_l adm n)
  let h3 := sg_bar_zero (Premises := Premises)
  let c := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

-- ── Case analysis infrastructure ──────────────────────────────────────────

/-- For any n: sg_bar(n) =₀ S0 ∨ sg_bar(n) =₀ 0.
    Case n=0: sg_bar(0) = S0. Case n≠0: n = S(pd n), sg_bar(S(pd n)) = 0. -/
private def sg_bar_cases (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.sg_bar n) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (Term.app Term.sg_bar n) Term.zero) :=
  -- Case n = 0: n=0 → sg_bar(n) =₀ sg_bar(0) (by qfer) → =₀ S0
  let qf_sg0 : Derivable F EqX al Premises
      (Formula.eq0 n Term.zero →ᶠ
       Formula.eq0 (Term.app Term.sg_bar n) (Term.app Term.sg_bar Term.zero)) :=
    .qfer (r := .app Term.sg_bar (.var .vz)) (by rfl) (by rfl) I_comb
  let case_z := .syllogism (pair_h qf_sg0 (weaken_intro sg_bar_zero))
    (.syllogism .trans0 .or_weak)
  -- Case n ≠ 0: n=S(pd n) → sg_bar(n) =₀ sg_bar(S(pd n)) (by qfer) → =₀ 0
  let qf_sgn : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 n Term.zero →ᶠ
       Formula.eq0 (Term.app Term.sg_bar n) (Term.app Term.sg_bar (.app .succ (.app Term.pd n)))) :=
    .qfer (r := .app Term.sg_bar (.var .vz)) (by rfl) (by rfl) (ne_zero_eq_succ_pd adm n)
  let case_nz := .syllogism (pair_h qf_sgn (weaken_intro (sg_bar_succ adm (.app Term.pd n))))
    (.syllogism .trans0 or_inr)
  .mp (.mp eq0_decidable' (.forall_ax n)) (or_elim_rule case_z case_nz)

/-- Congruence for ite_nat in the boolean argument:
    b =₀ b' → ite(b, x, y) =₀ ite(b', x, y). -/
private def ite_nat_congr_b {b b' x y : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 b b')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat b x y) (Term.app3 Term.ite_nat b' x y)) :=
  app3_congr_closed Term.ite_nat h .refl0 .refl0

/-- Congruence for ite_nat in the first value argument:
    x =₀ x' → ite(b, x, y) =₀ ite(b, x', y). -/
private def ite_nat_congr_x {b x x' y : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 x x')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat b x y) (Term.app3 Term.ite_nat b x' y)) :=
  app3_congr_closed Term.ite_nat .refl0 h .refl0

/-- Congruence for ite_nat in the second value argument:
    y =₀ y' → ite(b, x, y) =₀ ite(b, x, y'). -/
private def ite_nat_congr_y {b x y y' : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 y y')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat b x y) (Term.app3 Term.ite_nat b x y')) :=
  app3_congr_closed Term.ite_nat .refl0 .refl0 h

/-- ite(sg_bar(n), x, x) =₀ x for any n.
    By case analysis: sg_bar(n) = 1 → ite(1,x,x) = x; sg_bar(n) = 0 → ite(0,x,x) = x. -/
private def ite_nat_sg_bar_same (n x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat (Term.app Term.sg_bar n) x x) x) :=
  let b := Term.app Term.sg_bar n
  -- Case sg_bar(n) = S0: ite(b, x, x) =₀ ite(S0, x, x) =₀ x
  let qf_ite1 : Derivable F EqX al Premises
      (Formula.eq0 b (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat b x x)
                   (Term.app3 Term.ite_nat (.app .succ .zero) x x)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app3 Term.ite_nat (.var .vz) x.weaken x.weaken)
      (by simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
            ite_nat_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
            ite_nat_closed_subst, weaken_subst0_eta])
  let case1 := .syllogism (pair_h qf_ite1 (weaken_intro (ite_nat_one adm x x))) .trans0
  -- Case sg_bar(n) = 0: ite(b, x, x) =₀ ite(0, x, x) =₀ x
  let qf_ite0 : Derivable F EqX al Premises
      (Formula.eq0 b Term.zero →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat b x x)
                   (Term.app3 Term.ite_nat Term.zero x x)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app3 Term.ite_nat (.var .vz) x.weaken x.weaken)
      (by simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
            ite_nat_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.app3, Term.subst, Term.subst0_map,
            ite_nat_closed_subst, weaken_subst0_eta])
  let case0 := .syllogism (pair_h qf_ite0 (weaken_intro (ite_nat_zero adm x x))) .trans0
  .mp (sg_bar_cases adm n) (or_elim_rule case1 case0)

-- geq(n, 0) =₀ S0 for all n (already proved, but alias for clarity).
-- (geq_zero_r is already defined above)

/-- Congruence for geq in the first argument:
    s =₀ t → geq(s, u) =₀ geq(t, u). -/
private def geq_congr_l {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.geq s u) (Term.app2 Term.geq t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.geq (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, geq_closed_subst,
          weaken_subst0_eta])
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, geq_closed_subst,
          weaken_subst0_eta])

/-- Congruence for geq in the second argument. -/
private def geq_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.geq u s) (Term.app2 Term.geq u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.geq u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, geq_closed_subst,
          weaken_subst0_eta])
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, geq_closed_subst,
          weaken_subst0_eta])

/-- Congruence for rat_encode in all three arguments. -/
private def rat_encode_congr {s s' n n' d d' : Term F Γ Ty.nat}
    (hs : Derivable F EqX al Premises (Formula.eq0 s s'))
    (hn : Derivable F EqX al Premises (Formula.eq0 n n'))
    (hd : Derivable F EqX al Premises (Formula.eq0 d d')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.rat_encode s n d) (Term.app3 Term.rat_encode s' n' d')) :=
  app3_congr_closed Term.rat_encode hs hn hd

-- ============================================================================
-- Cantor pair projection lemmas
-- ============================================================================

/-- `x ≤ x + y`, i.e., `monus x (add x y) =₀ 0`.
    By induction on `y`. Base: `monus x (x+0) =₀ monus x x =₀ 0`.
    Step: `monus x (x + Sy) =₀ monus x (S(x+y)) =₀ pd(monus x (x+y)) =₀ pd(0) =₀ 0`. -/
private def le_add_right (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus x (Term.app2 Term.add x y)) Term.zero) :=
  let xw := x.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus xw (Term.app2 Term.add xw (.var .vz))) Term.zero
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  -- Base: monus x (add x 0) = 0. monus x (add x 0) = monus x x (add_zero_r) = 0 (monus_self).
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus x (Term.app2 Term.add x Term.zero)) Term.zero := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst, add_closed_subst, xw_subst0]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    let h1 := add_zero_r adm x  -- add x 0 =₀ x
    let h2 := monus_congr_r x h1  -- monus x (add x 0) =₀ monus x x
    let h3 := monus_self adm x  -- monus x x =₀ 0
    .mp (.mp h3 (.mp h2 and_intro)) .trans0
  -- Step: A(y) → A(Sy).
  -- A(y): monus xw (add xw y) =₀ 0
  -- A(Sy): monus xw (add xw (Sy)) =₀ 0
  -- add xw (Sy) = S(add xw y) [add_succ]
  -- monus xw (S(add xw y)) = pd(monus xw (add xw y)) [monus_succ]
  -- pd(monus xw (add xw y)) = pd 0 [IH via pd congruence, i.e. qfer]
  -- pd 0 = 0 [pd_zero]
  have xw_substVar0 : x.weaken.subst
      (Term.substVar0_map (.app .succ (.var .vz : Term F (Ty.nat :: Γ) Ty.nat))) = x.weaken := by
    simp only [Term.weaken]
    rw [Term.rename_subst, Term.rename_eq_subst]; rfl
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus xw
        (Term.app2 Term.add xw (.app .succ (.var .vz)))) Term.zero := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, monus_closed_subst, add_closed_subst, xw_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let yv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- add_succ xw yv : add xw (Syv) =₀ S(add xw yv)
    let as_eq := add_succ adm xw yv
    -- monus_eq1 : monus xw (add xw Syv) =₀ monus xw (S(add xw yv))  [congr on 2nd arg]
    let monus_eq1 := monus_congr_r xw as_eq
    -- monus_eq2 : monus xw (S(add xw yv)) =₀ pd(monus xw (add xw yv))  [monus_succ]
    let monus_eq2 := monus_succ adm xw (Term.app2 Term.add xw yv)
    -- combined : monus xw (add xw Syv) =₀ pd(monus xw (add xw yv))
    let combined := .mp (.mp monus_eq2 (.mp monus_eq1 and_intro)) .trans0
    -- pd_ih : A → pd(monus xw (add xw yv)) =₀ pd 0  [pd congruence]
    let pd_ih : Derivable F EqX al Premises (A →ᶠ
        Formula.eq0 (.app Term.pd (Term.app2 Term.monus xw (Term.app2 Term.add xw yv)))
          (.app Term.pd Term.zero)) :=
      .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) I_comb
    -- chain1 : A → monus xw (add xw Syv) =₀ pd 0
    let chain1 : Derivable F EqX al Premises (A →ᶠ
        Formula.eq0 (Term.app2 Term.monus xw (Term.app2 Term.add xw (.app .succ yv)))
          (.app Term.pd Term.zero)) :=
      .syllogism (pair_h (weaken_intro combined) pd_ih) .trans0
    -- pd_zero: pd 0 =₀ 0
    let pz : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
        (Formula.eq0 (.app Term.pd Term.zero) Term.zero) := pd_zero
    -- final: A → monus xw (add xw Syv) =₀ 0
    .syllogism (pair_h chain1 (weaken_intro pz)) .trans0
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.monus x (Term.app2 Term.add x y)) Term.zero := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst, add_closed_subst, xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- Commuted `monus_cancel`: `(a + b) ∸ a =₀ b`.
    From `monus_cancel b a : (b + a) ∸ a =₀ b` via `add_comm`. -/
private def monus_add_cancel_l (a b : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add a b) a) b) :=
  let h1 := add_comm adm a b  -- add a b =₀ add b a
  let h2 := monus_congr_l h1 a  -- (add a b) ∸ a =₀ (add b a) ∸ a
  let h3 := monus_cancel (Premises := Premises) adm b a  -- (add b a) ∸ a =₀ b
  .mp (.mp h3 (.mp h2 and_intro)) .trans0

/-- Step equation for `inv_triag`:
    `inv_triag(Sn) =₀ inv_triag(n) + sg_bar(triag(S(inv_triag(n))) ∸ Sn)`.

    Follows directly from the definition of `inv_triag` via `rec_succ`. Generalizes
    the unfold pattern used in `inv_triag_one`. -/
private def inv_triag_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (.app .succ n))
        (Term.app2 Term.add (.app Term.inv_triag n)
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.app Term.inv_triag n)))
              (.app .succ n))))) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat)
      .zero
      (Term.lam (Term.lam
        (Term.app2 Term.add (.var (.vs .vz))
          (.app Term.sg_bar
            (Term.app2 Term.monus
              (.app Term.triag (.app .succ (.var (.vs .vz))))
              (.app .succ (.var .vz)))))))
      (.var .vz)
  let step_fn : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
    Term.lam (Term.lam
      (Term.app2 Term.add (.var (.vs .vz))
        (.app Term.sg_bar
          (Term.app2 Term.monus
            (.app Term.triag (.app .succ (.var (.vs .vz))))
            (.app .succ (.var .vz))))))
  -- r0 := rec(0, step, n) — the literal rec term equal to inv_triag(n)
  let r0 : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) .zero step_fn n
  -- Step 1: inv_triag(Sn) =₀ body[Sn] by lam_correct
  let h1 := lam_correct_nf body (.app .succ n) (inv_triag_body_nf _)
  -- Step 2: body[Sn] = rec(0, step, Sn) =₀ step(rec(0,step,n), n) by rec_succ
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  -- Step 3: step(r0, n) = add(r0, sg_bar(monus(triag(S r0), Sn))) by lam2_correct
  let h2 := lam2_correct_nf adm
    (Term.app2 Term.add (.var (.vs .vz))
      (.app Term.sg_bar
        (Term.app2 Term.monus (.app Term.triag (.app .succ (.var (.vs .vz))))
          (.app .succ (.var .vz))))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    r0 n
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          add_closed_subst, sg_bar_closed_subst, monus_closed_subst, triag_closed_subst,
          weaken_subst0_eta]; rfl)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  -- Now: inv_triag(Sn) =₀ add(r0, sg_bar(monus(triag(S r0), Sn)))
  -- Need to convert r0 to inv_triag(n).
  let r0_eq : Derivable F EqX al Premises (Formula.eq0 r0 (.app Term.inv_triag n)) :=
    .mp (.mp (lam_correct_nf body n (inv_triag_body_nf _)) .sym0) I_comb
  -- Replace r0 with inv_triag(n) everywhere on the RHS via congruence
  let h_add_l := add_congr_l r0_eq
    (.app Term.sg_bar
      (Term.app2 Term.monus (.app Term.triag (.app .succ r0)) (.app .succ n)))
  let h_tr_cong := triag_congr (succ_congr r0_eq)
  let h_monus_cong := monus_congr_l h_tr_cong (.app .succ n)
  let h_sg_cong := sg_bar_congr h_monus_cong
  let h_add_r := add_congr_r (.app Term.inv_triag n) h_sg_cong
  let h_final_rhs := .mp (.mp h_add_r (.mp h_add_l and_intro)) .trans0
  .mp (.mp h_final_rhs (.mp c2 and_intro)) .trans0

/-!
### The `inv_triag_triag_add` invariant

Key fact: `inv_triag(triag(w) + r) =₀ w` when `r ≤ w`.

This powers `fst_pair_pair` and `snd_pair_pair`. The full proof uses *nested*
Peano induction (outer on `w`, inner on `r` for the step case) because the
two-variable bound `r ≤ w` cannot be reduced to a single induction variable.

We split the proof into four pieces:

* `inv_triag_triag_self_succ` (L1) — closes the `r = 0` branch of the inner
  induction at `w ↦ Sw`: given the outer IH specialised at `r := w`, derive
  `inv_triag(triag(Sw)) =₀ Sw`.

* `inv_triag_triag_add_inner_step` (L2) — the `r → Sr` branch of the inner
  induction. Given `inv_triag(triag(Sw) + r) =₀ Sw` with `Sr ≤ Sw`, derive
  `inv_triag(triag(Sw) + Sr) =₀ Sw`. Uses `inv_triag_succ` and the fact that
  `triag(S(Sw)) ∸ S(triag(Sw) + r) ≥ 1` (so the `sg_bar` correction vanishes).

* `inv_triag_triag_add_step` (L3) — the outer induction step `B(w) →ᶠ B(Sw)`,
  where `B(w) := ∀r. monus r w =₀ 0 → inv_triag(triag w + r) =₀ w`. Combines
  L1 (at `r = 0`) with an inner `Derivable.induction` driven by L2.

* `inv_triag_triag_add` — outer induction on `w` with base case (trivial:
  `r ≤ 0` forces `r = 0`, then `inv_triag(0) = 0`) and step L3.
-/

/-- **L1.** Closes the `r = 0` case in the step of the outer induction.

    Given the outer IH specialised to `r := w` (i.e. `inv_triag(triag w + w) =₀ w`),
    derive `inv_triag(triag(Sw)) =₀ Sw`.

    Proof: `triag(Sw) = S(triag w + w)` via `triag_succ` + `add_succ`.
    Apply `inv_triag_succ`:
    `inv_triag(S(triag w + w)) = inv_triag(triag w + w) + sg_bar(triag(S(inv_triag(triag w + w))) ∸ S(triag w + w))`.
    Rewrite the inner `inv_triag(triag w + w)` to `w` via the hypothesis.
    The `sg_bar` argument becomes `triag(Sw) ∸ S(triag w + w) = 0`, so `sg_bar = 1`.
    Result: `w + 1 = Sw`. -/
private def inv_triag_triag_self_succ (w : Term F Γ Ty.nat)
    (ih : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag w) w)) w)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (.app Term.triag (.app .succ w)))
        (.app .succ w)) :=
  -- Step 1: triag(Sw) =₀ triag w + Sw
  let h_ts := triag_succ adm w
  -- Step 2: triag w + Sw =₀ S(triag w + w)
  let h_as := add_succ adm (.app Term.triag w) w
  -- Combine: triag(Sw) =₀ S(triag w + w)
  let h_triagSw : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.triag (.app .succ w))
        (.app .succ (Term.app2 Term.add (.app Term.triag w) w))) :=
    .mp (.mp h_as (.mp h_ts and_intro)) .trans0
  -- Step 3: inv_triag(triag(Sw)) =₀ inv_triag(S(triag w + w))
  let h_itSw := inv_triag_congr h_triagSw
  -- Step 4: Unfold inv_triag(S(triag w + w)) via inv_triag_succ
  let h_unfold := inv_triag_succ adm (Term.app2 Term.add (.app Term.triag w) w)
  -- Step 5: Using ih, rewrite inv_triag(triag w + w) to w in the add_l position.
  let h_add_l := add_congr_l ih
    (.app Term.sg_bar
      (Term.app2 Term.monus
        (.app Term.triag (.app .succ
          (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
        (.app .succ (Term.app2 Term.add (.app Term.triag w) w))))
  -- Step 6: triag(S(inv_triag(triag w + w))) =₀ triag(Sw)  (via succ_congr ih)
  let h_tr_inner := triag_congr (succ_congr ih)
  -- Step 7: monus(triag(S(...)), S(triag w + w)) =₀ monus(triag(Sw), S(triag w + w))
  let h_monus_step1 := monus_congr_l h_tr_inner
    (.app .succ (Term.app2 Term.add (.app Term.triag w) w))
  -- Step 8: monus(triag(Sw), S(triag w + w)) =₀ monus(S(triag w + w), S(triag w + w))
  let h_monus_step2 := monus_congr_l h_triagSw
    (.app .succ (Term.app2 Term.add (.app Term.triag w) w))
  -- Chain Steps 7-8
  let h_monus_chain :=
    .mp (.mp h_monus_step2 (.mp h_monus_step1 and_intro)) .trans0
  -- Step 9: monus(S(triag w + w), S(triag w + w)) =₀ 0
  let h_monus_self :=
    monus_self adm (.app .succ (Term.app2 Term.add (.app Term.triag w) w))
  -- Chain to 0
  let h_monus_0 := .mp (.mp h_monus_self (.mp h_monus_chain and_intro)) .trans0
  -- Step 10: sg_bar(that) =₀ sg_bar(0) =₀ S0
  let h_sg_eq_0 := sg_bar_congr h_monus_0
  let h_sg_1 :=
    .mp (.mp (sg_bar_zero (Premises := Premises)) (.mp h_sg_eq_0 and_intro)) .trans0
  -- Step 11: add(w, sg_bar(...)) =₀ add(w, S0)
  let h_add_r := add_congr_r w h_sg_1
  -- Step 12: add(w, S0) =₀ S(add(w, 0))  via add_succ
  let h_add_w_succ := add_succ adm w Term.zero
  -- Step 13: S(add(w, 0)) =₀ Sw  via succ_congr (add_zero_r w)
  let h_S_add0 := succ_congr (add_zero_r adm w)
  -- add(w, S0) =₀ Sw
  let h_add_w_S0 :=
    .mp (.mp h_S_add0 (.mp h_add_w_succ and_intro)) .trans0
  -- add(w, sg_bar(...)) =₀ Sw
  let h_add_final := .mp (.mp h_add_w_S0 (.mp h_add_r and_intro)) .trans0
  -- add(inv_triag(triag w + w), sg_bar(X)) =₀ Sw
  let h_rhs_eq_Sw := .mp (.mp h_add_final (.mp h_add_l and_intro)) .trans0
  -- inv_triag(S(triag w + w)) =₀ Sw
  let h_itS_eq_Sw := .mp (.mp h_rhs_eq_Sw (.mp h_unfold and_intro)) .trans0
  -- inv_triag(triag(Sw)) =₀ Sw
  .mp (.mp h_itS_eq_Sw (.mp h_itSw and_intro)) .trans0

/-- **L2.** Inner induction step on `r`.

    Given `inv_triag(triag(Sw) + r) =₀ Sw` and `monus (Sr) (Sw) =₀ 0` (i.e. `Sr ≤ Sw`),
    derive `inv_triag(triag(Sw) + Sr) =₀ Sw`.

    Proof sketch: `triag(Sw) + Sr = S(triag(Sw) + r)`. Apply `inv_triag_succ`:
    `inv_triag(S(triag(Sw) + r)) = inv_triag(triag(Sw) + r) + sg_bar(triag(S(inv_triag(triag(Sw) + r))) ∸ S(triag(Sw) + r))`.
    Rewrite inner `inv_triag(triag(Sw) + r)` to `Sw` via the hypothesis.
    The `sg_bar` argument: `triag(S(Sw)) ∸ S(triag(Sw) + r) = (Sw ∸ r)`.
    From `Sr ≤ Sw` we get `r < Sw` hence `Sw ∸ r ≥ 1`, so `sg_bar = 0`.
    Result: `Sw + 0 = Sw`. -/
private def inv_triag_triag_add_inner_step (w r : Term F Γ Ty.nat)
    (_ih : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) r)) (.app .succ w)))
    (_hle : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) (.app .succ w)) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) (.app .succ r)))
        (.app .succ w)) :=
  sorry

/-- **L3.** Outer induction step: `B(w) →ᶠ B(Sw)`, where
    `B(w) := ∀r. monus r w =₀ 0 →ᶠ inv_triag(triag w + r) =₀ w`.

    Proof sketch: open the outer IH at `r := w` (since `monus w w =₀ 0` by
    `monus_self`) to obtain the specialized fact needed by L1. Then perform an
    inner `Derivable.induction` on `r` inside `B(Sw)`:

    * Inner base `r = 0`: `monus 0 (Sw) =₀ 0` holds; use L1 to conclude
      `inv_triag(triag(Sw) + 0) =₀ inv_triag(triag(Sw)) =₀ Sw`.

    * Inner step `r → Sr`: the inner IH provides
      `inv_triag(triag(Sw) + r) =₀ Sw` (under hypothesis `monus r (Sw) =₀ 0`).
      Combine with `monus (Sr) (Sw) =₀ 0` via L2 to get the step conclusion.

    The nested induction is assembled with `forall_inst_succ` + `forall_map`
    or a direct `Derivable.induction` on the bundled `∀r` formula `B`. -/
private def inv_triag_triag_add_step {Γ : Ctx ι} :
    let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
      Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.var (.vs .vz))) (.var .vz)))
        (.var (.vs .vz))
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
    Derivable F EqX al Premises (B →ᶠ Formula.substVar0 B (.app .succ (.var .vz))) :=
  sorry

/-- **Main theorem.** Key invariant: `inv_triag(triag(w) + r) =₀ w` when `r ≤ w`.

    This is the core arithmetic fact behind the Cantor pairing projections.
    The side condition `r ≤ w` ensures `triag(w) + r < triag(w+1)`, so the
    `inv_triag` recursion correctly identifies `w` as the triangle index.

    Proved by outer induction on `w` using `B(w) := ∀r. monus r w =₀ 0 → ...`.
    Base case: `r ≤ 0` forces `r = 0`, then `inv_triag(triag 0 + 0) = inv_triag(0) = 0`.
    Step case: delegated to `inv_triag_triag_add_step` (L3). -/
private def inv_triag_triag_add (w r : Term F Γ Ty.nat)
    (_h : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus r w) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag w) r)) w) :=
  sorry

/-- **Cantor projection 1**: `fst_pair(pair(x, y)) =₀ x`.

    Proof: `pair(x,y) = triag(x+y) + x` (by `pair_unfold`), so
    `fst_pair(pair(x,y)) = (triag(x+y) + x) ∸ triag(inv_triag(triag(x+y) + x))`
    `= (triag(x+y) + x) ∸ triag(x+y)` (by `inv_triag_triag_add`)
    `= x` (by `monus_add_cancel_l`). -/
private def fst_pair_pair (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair (Term.app2 Term.pair x y)) x) :=
  -- tpxy := triag(x+y) + x (the unfolded form of pair(x,y))
  let tpxy : Term F Γ Ty.nat :=
    Term.app2 Term.add (.app Term.triag (Term.app2 Term.add x y)) x
  -- h_pair : pair(x,y) =₀ tpxy
  let h_pair := pair_unfold adm x y
  -- h_cong1 : fst_pair(pair(x,y)) =₀ fst_pair(tpxy)
  let h_cong1 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair (Term.app2 Term.pair x y))
        (.app Term.fst_pair tpxy)) :=
    qfer_no_premise_nat_nf h_pair (r := .app Term.fst_pair (.var .vz)) rfl rfl
  -- h_unfold : fst_pair(tpxy) =₀ tpxy ∸ triag(inv_triag(tpxy))
  let h_unfold := fst_pair_unfold tpxy
  -- h_le : monus x (x + y) =₀ 0  (i.e., x ≤ x + y)
  let h_le := le_add_right adm x y
  -- h_inv : inv_triag(tpxy) =₀ x+y
  let h_inv : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag tpxy) (Term.app2 Term.add x y)) :=
    inv_triag_triag_add (Term.app2 Term.add x y) x h_le
  -- h_mcong : tpxy ∸ triag(inv_triag(tpxy)) =₀ tpxy ∸ triag(x+y)
  let h_mcong : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus tpxy (.app Term.triag (.app Term.inv_triag tpxy)))
        (Term.app2 Term.monus tpxy (.app Term.triag (Term.app2 Term.add x y)))) :=
    monus_congr_r tpxy (triag_congr h_inv)
  -- h_cancel : tpxy ∸ triag(x+y) =₀ x, i.e., (triag(x+y) + x) ∸ triag(x+y) =₀ x
  let h_cancel := monus_add_cancel_l adm (.app Term.triag (Term.app2 Term.add x y)) x
  -- Chain: fst_pair(pair(x,y)) =₀ fst_pair(tpxy) =₀ tpxy ∸ triag(inv_triag tpxy)
  --                           =₀ tpxy ∸ triag(x+y) =₀ x
  let step_a := .mp (.mp h_unfold (.mp h_cong1 and_intro)) .trans0
  let step_b := .mp (.mp h_mcong (.mp step_a and_intro)) .trans0
  .mp (.mp h_cancel (.mp step_b and_intro)) .trans0

/-- **Cantor projection 2**: `snd_pair(pair(x, y)) =₀ y`.

    Proof: `snd_pair(n) = inv_triag(n) ∸ fst_pair(n)`. For `n = pair(x,y)`:
    `inv_triag(pair(x,y)) =₀ x+y` (via `pair_unfold` + `inv_triag_triag_add`),
    `fst_pair(pair(x,y)) =₀ x` (by `fst_pair_pair`).
    So `snd_pair(pair(x,y)) =₀ (x+y) ∸ x =₀ y` (by `monus_add_cancel_l`). -/
private def snd_pair_pair (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.app2 Term.pair x y)) y) :=
  let pxy := Term.app2 Term.pair x y
  -- h_unfold : snd_pair(pxy) =₀ inv_triag(pxy) ∸ fst_pair(pxy)
  let h_unfold : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair pxy)
        (Term.app2 Term.monus (.app Term.inv_triag pxy) (.app Term.fst_pair pxy))) :=
    lam_correct_nf _ pxy (snd_pair_body_nf _)
  -- Step 1: inv_triag(pxy) =₀ x+y
  --   pxy =₀ triag(x+y) + x (pair_unfold), then congr on inv_triag, then inv_triag_triag_add
  let h_pair := pair_unfold adm x y  -- pxy =₀ triag(x+y) + x
  let h_inv_cong : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag pxy)
        (.app Term.inv_triag
          (Term.app2 Term.add (.app Term.triag (Term.app2 Term.add x y)) x))) :=
    qfer_no_premise_nat_nf h_pair (r := .app Term.inv_triag (.var .vz)) rfl rfl
  let h_le := le_add_right adm x y
  let h_inv_triag_add :=
    inv_triag_triag_add (Term.app2 Term.add x y) x h_le
  let h_inv : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag pxy) (Term.app2 Term.add x y)) :=
    .mp (.mp h_inv_triag_add (.mp h_inv_cong and_intro)) .trans0
  -- Step 2: fst_pair(pxy) =₀ x
  let h_fst := fst_pair_pair adm x y
  -- Step 3: monus(inv_triag(pxy), fst_pair(pxy)) =₀ monus(x+y, x)
  let h_m1 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.inv_triag pxy) (.app Term.fst_pair pxy))
        (Term.app2 Term.monus (Term.app2 Term.add x y) (.app Term.fst_pair pxy))) :=
    monus_congr_l h_inv (.app Term.fst_pair pxy)
  let h_m2 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add x y) (.app Term.fst_pair pxy))
        (Term.app2 Term.monus (Term.app2 Term.add x y) x)) :=
    monus_congr_r (Term.app2 Term.add x y) h_fst
  let h_m := .mp (.mp h_m2 (.mp h_m1 and_intro)) .trans0
  -- Step 4: monus(x+y, x) =₀ y by monus_add_cancel_l
  let h_cancel := monus_add_cancel_l adm x y
  -- Chain everything
  let step_a := .mp (.mp h_m (.mp h_unfold and_intro)) .trans0
  .mp (.mp h_cancel (.mp step_a and_intro)) .trans0

-- ============================================================================
-- rat_encode roundtrip lemmas
-- ============================================================================

/-- `rat_den(rat_encode(s, n, d)) =₀ succ(d)`.

    Unfolds: `rat_encode(s,n,d) = pair(2n ∸ isEven(s), d)`,
    so `rat_den(...) = succ(snd_pair(pair(2n ∸ isEven(s), d))) = succ(d)`
    via `snd_pair_pair`. -/
private def rat_den_rat_encode (s n d : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den (Term.app3 Term.rat_encode s n d))
        (.app .succ d)) :=
  -- body of rat_encode in context (s,n,d :: Γ)
  let encoded_pair : Term F Γ Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) n)
        (.app Term.isEven s))
      d
  -- Step 1: rat_encode(s,n,d) =₀ pair(2n ∸ isEven(s), d)
  -- Directly: apply lam3_correct with the rat_encode body NF.
  let body_e : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)
  have body_e_nf : ((body_e.subst0 (d.weaken.weaken)).subst0 (n.weaken)).subst0 s =
      encoded_pair := by
    simp only [body_e, encoded_pair, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      Term.ofNat, pair_closed_subst, mul_closed_subst, monus_closed_subst,
      isEven_closed_subst, weaken_subst0_eta]
  let h_encode : Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.rat_encode s n d) encoded_pair) :=
    lam3_correct_nf adm body_e s n d body_e_nf
  -- Step 2: rat_den(rat_encode(s,n,d)) =₀ rat_den(encoded_pair) via congr
  let h_den_cong : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den (Term.app3 Term.rat_encode s n d))
        (.app Term.rat_den encoded_pair)) :=
    qfer_no_premise_nat_nf h_encode (r := .app Term.rat_den (.var .vz)) rfl rfl
  -- Step 3: rat_den(encoded_pair) =₀ S(snd_pair(encoded_pair)) by lam_correct
  let rat_den_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app .succ (.app Term.snd_pair (.var .vz))
  have rat_den_body_nf : rat_den_body.subst0 encoded_pair =
      .app .succ (.app Term.snd_pair encoded_pair) := by
    simp only [rat_den_body, encoded_pair, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      snd_pair_closed_subst, pair_closed_subst, mul_closed_subst, monus_closed_subst,
      isEven_closed_subst]
  let h_unfold : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den encoded_pair)
        (.app .succ (.app Term.snd_pair encoded_pair))) :=
    lam_correct_nf rat_den_body encoded_pair rat_den_body_nf
  -- Step 4: snd_pair(encoded_pair) =₀ d by snd_pair_pair
  let h_snd := snd_pair_pair adm
    (Term.app2 Term.monus (Term.app2 Term.mul (Term.ofNat 2) n) (.app Term.isEven s)) d
  -- Step 5: succ(snd_pair(encoded_pair)) =₀ succ(d) by succ_congr
  let h_succ := succ_congr h_snd
  -- Chain
  let chain1 := .mp (.mp h_unfold (.mp h_den_cong and_intro)) .trans0
  .mp (.mp h_succ (.mp chain1 and_intro)) .trans0

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

/-- From s =₀ t (nat equality), derive eq_Q(s, t). -/
private def eq_Q_from_nat_eq {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (eq_Q s t) :=
  let refl_s := Derivable.mp (eq_Q_refl (adm := adm)) (.forall_ax s)
  let congr := qfer_no_premise_nat_nf h
    (r := Term.app2 Term.eq_Q_dec s.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, eq_Q_dec_closed_subst]
        exact congrArg (Term.app · s) (congrArg (Term.app Term.eq_Q_dec ·) (Term.weaken_subst0 s s)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, eq_Q_dec_closed_subst]
        exact congrArg (Term.app · t) (congrArg (Term.app Term.eq_Q_dec ·) (Term.weaken_subst0 s t)))
  .mp (.mp refl_s (.mp (.mp congr .sym0) and_intro)) .trans0

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
  let a : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let b : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let sb := Term.app Term.rat_sign b
  let na := Term.app Term.rat_num a
  let nb := Term.app Term.rat_num b
  let da := Term.app Term.rat_den a
  let db := Term.app Term.rat_den b
  -- Body of mul_Q in extended context
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 Term.rat_encode
      (Term.app Term.sg_bar (Term.app2 Term.abs_diff
        (Term.app Term.rat_sign (.var (.vs .vz)))
        (Term.app Term.rat_sign (.var .vz))))
      (Term.app2 Term.mul
        (Term.app Term.rat_num (.var (.vs .vz)))
        (Term.app Term.rat_num (.var .vz)))
      (Term.app Term.pd (Term.app2 Term.mul
        (Term.app Term.rat_den (.var (.vs .vz)))
        (Term.app Term.rat_den (.var .vz))))
  have body_eq : (Term.mul_Q : Term F (Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  -- NF for mul_Q(a,b)
  have nf_ab : (body.subst0 (b.weaken)).subst0 a =
      Term.app3 Term.rat_encode
        (Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sb))
        (Term.app2 Term.mul na nb)
        (Term.app Term.pd (Term.app2 Term.mul da db)) := by
    simp only [body, a, b, sa, sb, na, nb, da, db,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
      mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      rat_sign_closed_subst, pd_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  -- NF for mul_Q(b,a)
  have nf_ba : (body.subst0 (a.weaken)).subst0 b =
      Term.app3 Term.rat_encode
        (Term.app Term.sg_bar (Term.app2 Term.abs_diff sb sa))
        (Term.app2 Term.mul nb na)
        (Term.app Term.pd (Term.app2 Term.mul db da)) := by
    simp only [body, a, b, sa, sb, na, nb, da, db,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
      mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      rat_sign_closed_subst, pd_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  -- Unfold mul_Q(a,b) and mul_Q(b,a) to their NFs
  let unfold_ab := body_eq ▸ lam2_correct_nf adm body a b nf_ab
  let unfold_ba := body_eq ▸ lam2_correct_nf adm body b a nf_ba
  -- NF_ab =₀ NF_ba via commutativity of components
  let h1 := sg_bar_congr (abs_diff_comm adm sa sb)
  let h2 := mul_comm adm na nb
  let h3 := pd_congr (mul_comm adm da db)
  let eq_nf := app3_congr_closed Term.rat_encode h1 h2 h3
  -- Chain: mul_Q(a,b) =₀ NF_ab =₀ NF_ba =₀ mul_Q(b,a)
  let c1 : Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul_Q a b)
      (Term.app3 Term.rat_encode
        (Term.app Term.sg_bar (Term.app2 Term.abs_diff sb sa))
        (Term.app2 Term.mul nb na)
        (Term.app Term.pd (Term.app2 Term.mul db da)))) :=
    Derivable.mp (Derivable.mp eq_nf (Derivable.mp unfold_ab and_intro)) .trans0
  let h_eq := Derivable.mp (Derivable.mp (Derivable.mp unfold_ba .sym0) (Derivable.mp c1 and_intro)) .trans0
  -- Lift to eq_Q and universalize
  univ_gen (univ_gen (@eq_Q_from_nat_eq _ _ _ _ _ adm _ _ _ h_eq))

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
