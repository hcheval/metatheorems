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

-- Basic arithmetic closed_subst lemmas (terms from Arithmetic.lean).
-- `add_closed_subst` lives in `Arithmetic.lean`; it is only marked `@[simp]` here.
attribute [simp] add_closed_subst

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

-- `mul_congr_l` / `mul_congr_r` now live in `Arithmetic.lean` (non-private); the local
-- duplicates that used to sit here were removed to avoid the name clash.

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

private def abs_diff_congr_l {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff s u) (Term.app2 Term.abs_diff t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.abs_diff (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, abs_diff_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u s))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, abs_diff_closed_subst]
        exact congrArg _ (Term.weaken_subst0 u t))

private def abs_diff_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff u s) (Term.app2 Term.abs_diff u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.abs_diff u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, abs_diff_closed_subst]
        exact congrArg (Term.app · s)
          (congrArg (Term.app Term.abs_diff ·) (Term.weaken_subst0 u s)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, abs_diff_closed_subst]
        exact congrArg (Term.app · t)
          (congrArg (Term.app Term.abs_diff ·) (Term.weaken_subst0 u t)))

private def abs_diff_congr {a a' b b' : Term F Γ Ty.nat}
    (ha : Derivable F EqX al Premises (Formula.eq0 a a'))
    (hb : Derivable F EqX al Premises (Formula.eq0 b b')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff a b) (Term.app2 Term.abs_diff a' b')) :=
  .mp (.mp (abs_diff_congr_r a' hb) (.mp (abs_diff_congr_l ha b) and_intro)) .trans0

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

-- ── isEven/isOdd successor evaluation ─────────────────────────────────────

/-- isEven(Sn) =₀ sg_bar(isEven(n)). -/
private def isEven_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isEven (.app .succ n))
        (.app Term.sg_bar (.app Term.isEven n))) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.app .succ .zero)
      (Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))) (.var .vz)
  let step := Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))
  let base : Term F Γ Ty.nat := .app .succ .zero
  let rec_n : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) base step n
  let h1 := lam_correct_nf body (.app .succ n) (by rfl)
  let c1 := .mp (.mp (.rec_succ (ρ := Ty.nat)) (.mp h1 and_intro)) (eqAtType_trans adm)
  let h2 := lam2_correct_nf adm
    (.app Term.sg_bar (.var (.vs .vz)) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    rec_n n (by rfl)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  let h3 : Derivable F EqX al Premises (Formula.eq0 rec_n (.app Term.isEven n)) :=
    .mp (lam_correct_nf body n (by rfl)) .sym0
  let h4 := sg_bar_congr h3
  .mp (.mp h4 (.mp c2 and_intro)) .trans0

/-- isEven(S0) =₀ 0. -/
private def isEven_one :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isEven (.app .succ .zero)) Term.zero) :=
  let h1 := isEven_succ adm Term.zero
  let h2 := sg_bar_congr isEven_zero
  let h3 := sg_bar_succ adm .zero
  let c := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

/-- isEven(SS0) =₀ S0. -/
private def isEven_two :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isEven (Term.ofNat 2)) (.app .succ .zero)) :=
  let h1 := isEven_succ adm (.app .succ .zero)
  let h2 := sg_bar_congr (isEven_one adm)
  let h3 := sg_bar_zero (Premises := Premises)
  let c := .mp (.mp h3 (.mp h2 and_intro)) .trans0
  .mp (.mp c (.mp h1 and_intro)) .trans0

/-- isOdd(SS0) =₀ 0. -/
private def isOdd_two :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isOdd (Term.ofNat 2)) Term.zero) :=
  let h1 := isOdd_unfold (Term.ofNat 2)
  let h2 := monus_congr_r (.app .succ .zero) (isEven_two adm)
  let h3 := monus_succ_l adm .zero .zero
  let h4 := monus_zero adm .zero
  let h5 := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  let h6 := .mp (.mp h5 (.mp h2 and_intro)) .trans0
  .mp (.mp h6 (.mp h1 and_intro)) .trans0

-- ── Double-step parity and division ──────────────────────────────────────

/-- isEven(n + n) =₀ S0 for all n.

    Base: isEven(0 + 0) = isEven(0) = S0.
    Step: isEven(S(n) + S(n)) = isEven(SS(n+n)) = sg_bar(sg_bar(isEven(n+n)))
          = sg_bar(sg_bar(S0)) = sg_bar(0) = S0. -/
private def isEven_double (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isEven (Term.app2 Term.add n n)) (.app .succ .zero)) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (.app Term.isEven (Term.app2 Term.add (.var .vz) (.var .vz))) (.app .succ .zero)
  -- Base: A[0] = isEven(add(0, 0)) =₀ S0
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (.app Term.isEven (Term.app2 Term.add Term.zero Term.zero)) (.app .succ .zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, isEven_closed_subst]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    base_nf ▸
    let h1 := isEven_congr (add_zero_r adm Term.zero)
    .mp (.mp isEven_zero (.mp h1 and_intro)) .trans0
  -- Step: A(k) → A(Sk), i.e., isEven(k+k) =₀ S0 → isEven(Sk+Sk) =₀ S0
  let k : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let kk := Term.app2 Term.add k k
  have step_nf : Formula.substVar0 A (.app .succ k) =
      Formula.eq0 (.app Term.isEven (Term.app2 Term.add (.app .succ k) (.app .succ k)))
        (.app .succ .zero) := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      add_closed_subst, isEven_closed_subst]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ k)) :=
    step_nf ▸
    -- add(Sk, Sk) =₀ S(add(k, Sk)) =₀ SS(add(k, k))
    let h_add1 := add_succ_l adm k (.app .succ k)
    let h_add2 := succ_congr (add_succ adm k k)
    let h_add := .mp (.mp h_add2 (.mp h_add1 and_intro)) .trans0
    -- isEven(add(Sk, Sk)) =₀ isEven(SS(kk))
    let h_ie_cong := isEven_congr h_add
    -- isEven(SS(kk)) =₀ sg_bar(isEven(S(kk))) by isEven_succ
    let h_ie_ss1 := isEven_succ adm (.app .succ kk)
    -- isEven(S(kk)) =₀ sg_bar(isEven(kk)) by isEven_succ
    let h_ie_ss2 := isEven_succ adm kk
    -- isEven(SS(kk)) =₀ sg_bar(sg_bar(isEven(kk)))
    let h_chain1 := .mp (.mp (sg_bar_congr h_ie_ss2) (.mp h_ie_ss1 and_intro)) .trans0
    -- isEven(add(Sk,Sk)) =₀ sg_bar(sg_bar(isEven(kk)))
    let h_chain2 := .mp (.mp h_chain1 (.mp h_ie_cong and_intro)) .trans0
    -- From IH: isEven(kk) =₀ S0 → sg_bar(sg_bar(isEven(kk))) =₀ sg_bar(sg_bar(S0))
    let congr_ih : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (.app Term.sg_bar (.app Term.sg_bar (.app Term.isEven kk)))
                          (.app Term.sg_bar (.app Term.sg_bar (.app .succ .zero)))) :=
      qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := .app Term.sg_bar (.app Term.sg_bar (.var .vz)))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst])
    -- sg_bar(sg_bar(S0)) =₀ sg_bar(0) =₀ S0
    let h_sgsg := .mp (.mp sg_bar_zero (.mp (sg_bar_congr (sg_bar_succ adm .zero)) and_intro)) .trans0
    -- IH → sg_bar(sg_bar(isEven(kk))) =₀ S0
    let h_ih_to_target := .syllogism (pair_h congr_ih (weaken_intro h_sgsg)) .trans0
    -- IH → isEven(add(Sk,Sk)) =₀ S0
    .syllogism (pair_h (weaken_intro h_chain2) h_ih_to_target) .trans0
  -- Instantiate
  have inst_nf : A.subst0 n =
      Formula.eq0 (.app Term.isEven (Term.app2 Term.add n n)) (.app .succ .zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, isEven_closed_subst]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax n)

/-- isOdd(n + n) =₀ 0 for all n.
    From isEven_double: isEven(n+n) = S0, isOdd(n+n) = 1 - isEven(n+n) = 1 - 1 = 0. -/
private def isOdd_double (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isOdd (Term.app2 Term.add n n)) Term.zero) :=
  let h1 := isOdd_unfold (Term.app2 Term.add n n)
  let h2 := monus_congr_r (.app .succ .zero) (isEven_double adm n)
  let h3 := monus_succ_l adm .zero .zero
  let h4 := monus_zero adm .zero
  let c := .mp (.mp h4 (.mp h3 and_intro)) .trans0
  let c2 := .mp (.mp c (.mp h2 and_intro)) .trans0
  .mp (.mp c2 (.mp h1 and_intro)) .trans0


/-- For any n: isEven(n) =₀ S0 ∨ isEven(n) =₀ 0.
    Base: isEven(0) =₀ S0 → left disjunct.
    Step: case left (isEven(k) =₀ S0): sg_bar(S0) =₀ 0, so isEven(Sk) =₀ 0 → right.
          case right (isEven(k) =₀ 0): sg_bar(0) =₀ S0, so isEven(Sk) =₀ S0 → left. -/
private def isEven_cases (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isEven n) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (.app Term.isEven n) Term.zero) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (.app Term.isEven (.var .vz)) (.app .succ .zero) ∨ᶠ
    Formula.eq0 (.app Term.isEven (.var .vz)) Term.zero
  -- Base: A[0] = isEven(0) =₀ S0 ∨ isEven(0) =₀ 0
  have base_nf : A.subst0 Term.zero =
      (Formula.eq0 (.app Term.isEven Term.zero) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (.app Term.isEven Term.zero) Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      isEven_closed_subst]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    base_nf ▸ .mp isEven_zero .or_weak
  -- Step: A(k) → A(Sk)
  let k : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  have step_nf : Formula.substVar0 A (.app .succ k) =
      (Formula.eq0 (.app Term.isEven (.app .succ k)) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (.app Term.isEven (.app .succ k)) Term.zero) := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      isEven_closed_subst]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ k)) :=
    step_nf ▸
    -- isEven_succ: isEven(Sk) =₀ sg_bar(isEven(k))
    let h_succ := isEven_succ adm k
    -- Case left: isEven(k) =₀ S0 → isEven(Sk) =₀ S0 ∨ isEven(Sk) =₀ 0
    -- sg_bar(isEven(k)) =₀ sg_bar(S0) conditional on isEven(k) =₀ S0
    let cong_l : Derivable F EqX al Premises
        (Formula.eq0 (.app Term.isEven k) (.app .succ .zero) →ᶠ
         Formula.eq0 (.app Term.sg_bar (.app Term.isEven k))
                     (.app Term.sg_bar (.app .succ .zero))) :=
      qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := .app Term.sg_bar (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst])
    -- sg_bar(S0) =₀ 0
    let h_sg_s0 := sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    -- isEven(k) =₀ S0 → sg_bar(isEven(k)) =₀ 0
    let h_l_sg0 := .syllogism (pair_h cong_l (weaken_intro h_sg_s0)) .trans0
    -- isEven(k) =₀ S0 → isEven(Sk) =₀ 0
    let h_l_ie0 := .syllogism (pair_h (weaken_intro h_succ) h_l_sg0) .trans0
    -- isEven(k) =₀ S0 → (isEven(Sk) =₀ S0 ∨ isEven(Sk) =₀ 0)
    let case_left := .syllogism h_l_ie0 or_inr
    -- Case right: isEven(k) =₀ 0 → isEven(Sk) =₀ S0 ∨ isEven(Sk) =₀ 0
    -- sg_bar(isEven(k)) =₀ sg_bar(0) conditional on isEven(k) =₀ 0
    let cong_r : Derivable F EqX al Premises
        (Formula.eq0 (.app Term.isEven k) Term.zero →ᶠ
         Formula.eq0 (.app Term.sg_bar (.app Term.isEven k))
                     (.app Term.sg_bar Term.zero)) :=
      qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := .app Term.sg_bar (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst])
    -- sg_bar(0) =₀ S0
    let h_sg_0 := sg_bar_zero (Premises := Premises) (Γ := Ty.nat :: Γ)
    -- isEven(k) =₀ 0 → sg_bar(isEven(k)) =₀ S0
    let h_r_sgs1 := .syllogism (pair_h cong_r (weaken_intro h_sg_0)) .trans0
    -- isEven(k) =₀ 0 → isEven(Sk) =₀ S0
    let h_r_ies1 := .syllogism (pair_h (weaken_intro h_succ) h_r_sgs1) .trans0
    -- isEven(k) =₀ 0 → (isEven(Sk) =₀ S0 ∨ isEven(Sk) =₀ 0)
    let case_right := .syllogism h_r_ies1 .or_weak
    -- Combine: A(k) → A(Sk)
    or_elim_rule case_left case_right
  -- Instantiate with n
  have inst_nf : A.subst0 n =
      (Formula.eq0 (.app Term.isEven n) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (.app Term.isEven n) Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      isEven_closed_subst]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax n)

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

/-- `(x + y) ∸ (x + z) =₀ y ∸ z`. By induction on `x`.

    Base `x=0`: `(0+y) ∸ (0+z) =₀ y ∸ z` via `add_zero_l` on both sides.
    Step `x → Sx`: `(Sx+y) ∸ (Sx+z) =₀ S(x+y) ∸ S(x+z) =₀ (x+y) ∸ (x+z) =₀ y ∸ z`
    via `add_succ_l` twice, `monus_succ_l`, then the IH. -/
private def add_monus_cancel_l (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.monus (Term.app2 Term.add x y) (Term.app2 Term.add x z))
        (Term.app2 Term.monus y z)) :=
  let yw := y.weaken (σ := Ty.nat)
  let zw := z.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus
        (Term.app2 Term.add (.var .vz) yw) (Term.app2 Term.add (.var .vz) zw))
      (Term.app2 Term.monus yw zw)
  have yw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) y.weaken = y := Term.weaken_subst0 y
  have zw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) z.weaken = z := Term.weaken_subst0 z
  -- Base: (0+y) ∸ (0+z) =₀ y ∸ z.
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus
        (Term.app2 Term.add Term.zero y) (Term.app2 Term.add Term.zero z))
        (Term.app2 Term.monus y z) := by
    simp only [A, yw, zw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst, add_closed_subst, yw_subst0, zw_subst0]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    let az1 := add_zero_l adm y  -- 0+y =₀ y
    let az2 := add_zero_l adm z  -- 0+z =₀ z
    let c1 := monus_congr_l az1 (Term.app2 Term.add Term.zero z)
    -- c1 : (0+y) ∸ (0+z) =₀ y ∸ (0+z)
    let c2 := monus_congr_r y az2
    -- c2 : y ∸ (0+z) =₀ y ∸ z
    .mp (.mp c2 (.mp c1 and_intro)) .trans0
  -- Step: A(x) → A(Sx).
  have yw_substVar0 : y.weaken.subst
      (Term.substVar0_map (.app .succ (.var .vz : Term F (Ty.nat :: Γ) Ty.nat))) = y.weaken := by
    simp only [Term.weaken]
    rw [Term.rename_subst, Term.rename_eq_subst]; rfl
  have zw_substVar0 : z.weaken.subst
      (Term.substVar0_map (.app .succ (.var .vz : Term F (Ty.nat :: Γ) Ty.nat))) = z.weaken := by
    simp only [Term.weaken]
    rw [Term.rename_subst, Term.rename_eq_subst]; rfl
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus
        (Term.app2 Term.add (.app .succ (.var .vz)) yw)
        (Term.app2 Term.add (.app .succ (.var .vz)) zw))
        (Term.app2 Term.monus yw zw) := by
    simp only [A, yw, zw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, monus_closed_subst, add_closed_subst, yw_substVar0, zw_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let xv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- as_y : (Sx + y) =₀ S(x + y)
    let as_y := add_succ_l adm xv yw
    -- as_z : (Sx + z) =₀ S(x + z)
    let as_z := add_succ_l adm xv zw
    -- m1 : (Sx+y) ∸ (Sx+z) =₀ S(x+y) ∸ (Sx+z)
    let m1 := monus_congr_l as_y (Term.app2 Term.add (.app .succ xv) zw)
    -- m2 : S(x+y) ∸ (Sx+z) =₀ S(x+y) ∸ S(x+z)
    let m2 := monus_congr_r (.app .succ (Term.app2 Term.add xv yw)) as_z
    -- m3 : S(x+y) ∸ S(x+z) =₀ (x+y) ∸ (x+z)
    let m3 := monus_succ_l adm (Term.app2 Term.add xv yw) (Term.app2 Term.add xv zw)
    -- Chain m1;m2;m3: (Sx+y) ∸ (Sx+z) =₀ (x+y) ∸ (x+z)  (unconditional)
    let c12 := .mp (.mp m2 (.mp m1 and_intro)) .trans0
    let c123 := .mp (.mp m3 (.mp c12 and_intro)) .trans0
    -- A is exactly: (x+y) ∸ (x+z) =₀ y ∸ z (with x = .var .vz = xv).
    -- So (A →ᶠ A) via I_comb gives us the IH step.
    .syllogism (pair_h (weaken_intro c123) (@I_comb _ _ EqX al Premises _ A)) .trans0
  have inst_nf : A.subst0 x =
      Formula.eq0 (Term.app2 Term.monus
        (Term.app2 Term.add x y) (Term.app2 Term.add x z))
        (Term.app2 Term.monus y z) := by
    simp only [A, yw, zw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst, add_closed_subst, yw_subst0, zw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax x)

/-- `Sr ∸ w =₀ 0 → r ∸ w =₀ 0` (monotonicity of `≤` under predecessor on the left).
    By induction on `w`; step does not use IH.

    Base `w=0`: `Sr ∸ 0 =₀ Sr`, so hypothesis forces `Sr =₀ 0`, contradiction via
    `succ_ne_zero`, then `.exfalso`.
    Step `w → Sw`: use `monus_succ_l` (LHS), `monus_succ` (RHS), `pd_zero`. -/
private def le_pred (r w : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) w) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus r w) Term.zero) :=
  let rw := r.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.app .succ rw) (.var .vz)) Term.zero →ᶠ
    Formula.eq0 (Term.app2 Term.monus rw (.var .vz)) Term.zero
  have rw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) r.weaken = r := Term.weaken_subst0 r
  have rw_substVar0 : r.weaken.subst
      (Term.substVar0_map (.app .succ (.var .vz : Term F (Ty.nat :: Γ) Ty.nat))) = r.weaken := by
    simp only [Term.weaken]
    rw [Term.rename_subst, Term.rename_eq_subst]; rfl
  -- Base w=0
  have base_nf : A.subst0 Term.zero =
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) Term.zero) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus r Term.zero) Term.zero) := by
    simp only [A, rw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst, rw_subst0]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    let mz_Sr := monus_zero adm (.app .succ r)  -- Sr ∸ 0 =₀ Sr
    -- qf: (Sr ∸ 0 =₀ 0) → (Sr =₀ 0) via sym(mz_Sr) + trans
    let qf : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus (.app .succ r) Term.zero) Term.zero →ᶠ
         Formula.eq0 (.app .succ r) Term.zero) :=
      .syllogism (pair_h (weaken_intro (.mp mz_Sr .sym0)) I_comb) .trans0
    let succ_ne : Derivable F EqX al Premises (Formula.eq0 (.app .succ r) Term.zero →ᶠ ⊥ᶠ) :=
      .mp (@Derivable.succ_ne_zero _ _ EqX al Premises Γ) (.forall_ax r)
    let to_bot := .syllogism qf succ_ne
    .syllogism to_bot .exfalso
  -- Step w → Sw
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      (Formula.eq0 (Term.app2 Term.monus (.app .succ rw) (.app .succ (.var .vz))) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus rw (.app .succ (.var .vz))) Term.zero) := by
    simp only [A, rw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, monus_closed_subst, rw_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let wv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let ms_l := monus_succ_l adm rw wv  -- S(rw) ∸ S(wv) =₀ rw ∸ wv
    let ms := monus_succ adm rw wv       -- rw ∸ S(wv) =₀ pd(rw ∸ wv)
    -- hyp_to_rw_monus_wv : (S(rw) ∸ S(wv) =₀ 0) → (rw ∸ wv =₀ 0)
    let hyp_to_rw_monus_wv : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus (.app .succ rw) (.app .succ wv)) Term.zero →ᶠ
         Formula.eq0 (Term.app2 Term.monus rw wv) Term.zero) :=
      .syllogism (pair_h (weaken_intro (.mp ms_l .sym0)) I_comb) .trans0
    -- pd_cong : (rw ∸ wv =₀ 0) → (pd(rw ∸ wv) =₀ pd 0)
    let pd_cong : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus rw wv) Term.zero →ᶠ
         Formula.eq0 (.app Term.pd (Term.app2 Term.monus rw wv)) (.app Term.pd Term.zero)) :=
      .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) I_comb
    -- chain1 : (rw ∸ wv =₀ 0) → (pd(rw ∸ wv) =₀ 0)
    let chain1 : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus rw wv) Term.zero →ᶠ
         Formula.eq0 (.app Term.pd (Term.app2 Term.monus rw wv)) Term.zero) :=
      .syllogism (pair_h pd_cong (weaken_intro (pd_zero (Γ := Ty.nat :: Γ)))) .trans0
    -- chain2 : (rw ∸ wv =₀ 0) → (rw ∸ S wv =₀ 0)
    let chain2 : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus rw wv) Term.zero →ᶠ
         Formula.eq0 (Term.app2 Term.monus rw (.app .succ wv)) Term.zero) :=
      .syllogism (pair_h (weaken_intro ms) chain1) .trans0
    -- Final (no IH used): A → ((Sr ∸ Sv = 0) → (r ∸ Sv = 0))  via weaken_intro
    weaken_intro (.syllogism hyp_to_rw_monus_wv chain2)
  have inst_nf : A.subst0 w =
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) w) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus r w) Term.zero) := by
    simp only [A, rw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst, rw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax w)

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

/-- Commute a universal and an implication when the hypothesis doesn't
    contain the bound variable: from `⊢ ∀r. (B.weakenBy ρ →ᶠ P)`, derive
    `⊢ B →ᶠ ∀r. P`. Built from `.forall_rule I_comb` and `forall_lift`. -/
private def forall_imp_swap {Γ' : Ctx ι} {ρ : Ty ι}
    {B : Formula F Γ'} {P : Formula F (ρ :: Γ')}
    (h : Derivable F EqX al Premises
      (Formula.all ρ (Formula.weakenBy ρ B →ᶠ P))) :
    Derivable F EqX al Premises (B →ᶠ Formula.all ρ P) :=
  -- B →ᶠ ∀r. B.weakenBy ρ via .forall_rule on I_comb
  let intro_weaken : Derivable F EqX al Premises
      (B →ᶠ Formula.all ρ (Formula.weakenBy ρ B)) :=
    .forall_rule I_comb
  .syllogism intro_weaken (forall_lift h)

/-- **L1-imp.** Implication form of `inv_triag_triag_self_succ`.

    Given `P →ᶠ (inv_triag(triag w + w) =₀ w)`, derive
    `P →ᶠ (inv_triag(triag(Sw)) =₀ Sw)`.

    Each step of `inv_triag_triag_self_succ` that uses `ih` is threaded with `P`. -/
private def inv_triag_triag_self_succ_imp
    {P : Formula F Γ} (w : Term F Γ Ty.nat)
    (ih_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag w) w)) w)) :
    Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (.app Term.inv_triag (.app Term.triag (.app .succ w)))
        (.app .succ w)) :=
  -- Unconditional steps (not using ih)
  let h_ts := triag_succ adm w
  let h_as := add_succ adm (.app Term.triag w) w
  let h_triagSw : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.triag (.app .succ w))
        (.app .succ (Term.app2 Term.add (.app Term.triag w) w))) :=
    .mp (.mp h_as (.mp h_ts and_intro)) .trans0
  let h_itSw := inv_triag_congr h_triagSw
  let h_unfold := inv_triag_succ adm (Term.app2 Term.add (.app Term.triag w) w)
  -- Step using ih: h_add_l_imp : P → add(invTri(triag w+w), X) = add(w, X)
  -- Use qfer_nat_nf with r := add (.var .vz) X.weaken, and premise ih_imp.
  let X : Term F Γ Ty.nat :=
    .app Term.sg_bar
      (Term.app2 Term.monus
        (.app Term.triag (.app .succ
          (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
        (.app .succ (Term.app2 Term.add (.app Term.triag w) w)))
  -- We can't use qfer with P as premise (P is not necessarily QF). Instead:
  -- First build the congruence as a bare implication (using I_comb on eq0), then syllogism.
  let cong_add_l : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)) w →ᶠ
       Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)) X)
         (Term.app2 Term.add w X)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.add (.var .vz) X.weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg _ (Term.weaken_subst0 X
            (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg _ (Term.weaken_subst0 X w))
  let h_add_l_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)) X)
         (Term.app2 Term.add w X)) :=
    .syllogism ih_imp cong_add_l
  -- Step using ih: h_tr_inner_imp : P → triag(S(invTri(triag w + w))) = triag(Sw)
  -- Via triag ∘ succ congruence on ih.
  let cong_triag_succ : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)) w →ᶠ
       Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
         (.app Term.triag (.app .succ w))) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app Term.triag (.app .succ (.var .vz)))
      rfl rfl
  let h_tr_inner_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
         (.app Term.triag (.app .succ w))) :=
    .syllogism ih_imp cong_triag_succ
  -- Step 7 (imp): monus(triag(S(invTri..)), S(triag w + w)) =₀ monus(triag(Sw), S(triag w + w))
  -- This is a monus_congr_l applied to h_tr_inner_imp. Build as imp version:
  let Y : Term F Γ Ty.nat := .app .succ (Term.app2 Term.add (.app Term.triag w) w)
  let cong_monus_l_tr : Derivable F EqX al Premises
      (Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))))
         (.app Term.triag (.app .succ w)) →ᶠ
       Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)
         (Term.app2 Term.monus (.app Term.triag (.app .succ w)) Y)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.monus (.var .vz) Y.weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 Y _))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 Y _))
  let h_monus_step1_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)
         (Term.app2 Term.monus (.app Term.triag (.app .succ w)) Y)) :=
    .syllogism h_tr_inner_imp cong_monus_l_tr
  -- Unconditional: monus(triag(Sw), S(triag w + w)) =₀ monus(S(triag w + w), S(triag w + w))
  let h_monus_step2 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.triag (.app .succ w)) Y)
        (Term.app2 Term.monus (.app .succ (Term.app2 Term.add (.app Term.triag w) w)) Y)) :=
    monus_congr_l h_triagSw Y
  -- h_monus_chain_imp: P → monus(triag(S(invTri..)), Y) = monus(S(triag w + w), Y)
  let h_monus_chain_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)
         (Term.app2 Term.monus (.app .succ (Term.app2 Term.add (.app Term.triag w) w)) Y)) :=
    .syllogism (pair_h h_monus_step1_imp (weaken_intro h_monus_step2)) .trans0
  -- Step 9: unconditional: monus(S(triag w + w), S(triag w + w)) = 0
  let h_monus_self := monus_self adm (.app .succ (Term.app2 Term.add (.app Term.triag w) w))
  -- chain to 0 under P
  let h_monus_0_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)
         Term.zero) :=
    .syllogism (pair_h h_monus_chain_imp (weaken_intro h_monus_self)) .trans0
  -- sg_bar congr (imp form): P → sg_bar(monus(...)) = sg_bar(0)
  let cong_sg_bar : Derivable F EqX al Premises
      (Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)
         Term.zero →ᶠ
       Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y))
         (.app Term.sg_bar Term.zero)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app Term.sg_bar (.var .vz)) rfl rfl
  let h_sg_eq_0_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y))
         (.app Term.sg_bar Term.zero)) :=
    .syllogism h_monus_0_imp cong_sg_bar
  -- sg_bar(0) = S0 unconditionally
  let h_sg_1_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y))
         (.app .succ Term.zero)) :=
    .syllogism (pair_h h_sg_eq_0_imp (weaken_intro (sg_bar_zero (Premises := Premises)))) .trans0
  -- add_congr_r: add(w, sg_bar(...)) = add(w, S0) (imp form)
  let cong_add_r : Derivable F EqX al Premises
      (Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y))
         (.app .succ Term.zero) →ᶠ
       Formula.eq0 (Term.app2 Term.add w
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)))
         (Term.app2 Term.add w (.app .succ Term.zero))) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.add w.weaken (.var .vz))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg (Term.app · _) (congrArg (Term.app Term.add ·) (Term.weaken_subst0 w _)))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg (Term.app · _) (congrArg (Term.app Term.add ·) (Term.weaken_subst0 w _)))
  let h_add_r_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add w
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)))
         (Term.app2 Term.add w (.app .succ Term.zero))) :=
    .syllogism h_sg_1_imp cong_add_r
  -- Unconditional: add(w, S0) = Sw (via add_succ + add_zero_r + succ_congr)
  let h_add_w_succ := add_succ adm w Term.zero
  let h_S_add0 := succ_congr (add_zero_r adm w)
  let h_add_w_S0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add w (.app .succ Term.zero)) (.app .succ w)) :=
    .mp (.mp h_S_add0 (.mp h_add_w_succ and_intro)) .trans0
  -- h_add_final_imp: P → add(w, sg_bar(...)) = Sw
  let h_add_final_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add w
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)))
         (.app .succ w)) :=
    .syllogism (pair_h h_add_r_imp (weaken_intro h_add_w_S0)) .trans0
  -- h_rhs_eq_Sw_imp: P → add(invTri(triag w + w), sg_bar(...)) = Sw
  --   Chain: P → (add(invTri(..), sg_bar(..)) = add(w, sg_bar(..))) [h_add_l_imp] → Sw [h_add_final_imp]
  let h_rhs_eq_Sw_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w))
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add (.app Term.triag w) w)))) Y)))
         (.app .succ w)) :=
    .syllogism (pair_h h_add_l_imp h_add_final_imp) .trans0
  -- h_itS_eq_Sw_imp: P → invTri(S(triag w + w)) = Sw  (chain with h_unfold)
  let h_itS_eq_Sw_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.inv_triag (.app .succ (Term.app2 Term.add (.app Term.triag w) w)))
         (.app .succ w)) :=
    .syllogism (pair_h (weaken_intro h_unfold) h_rhs_eq_Sw_imp) .trans0
  -- Final: P → invTri(triag(Sw)) = Sw  (chain with h_itSw)
  .syllogism (pair_h (weaken_intro h_itSw) h_itS_eq_Sw_imp) .trans0

/-- `Sw ∸ w =₀ S0`. Proof by induction on `w`:
    base `w=0` uses `monus_zero`; step uses `monus_succ_l` + IH. -/
private def succ_monus_self (w : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (.app .succ Term.zero)) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.app .succ (.var .vz)) (.var .vz))
      (.app .succ Term.zero)
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus (.app .succ Term.zero) Term.zero)
        (.app .succ Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    monus_zero adm (.app .succ Term.zero)
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ (.var .vz)))
        (.app .succ (.var .vz))) (.app .succ Term.zero) := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      monus_closed_subst]
  have step_body : Derivable F EqX al Premises
      (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let wv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- S(Sw) ∸ S w =₀ S w ∸ w
    let msl := monus_succ_l adm (.app .succ wv) wv
    -- Chain with IH (A): S(Sw) ∸ Sw =₀ Sw ∸ w =₀ S0
    .syllogism (pair_h (weaken_intro msl) I_comb) .trans0
  have inst_nf : A.subst0 w =
      Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (.app .succ Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax w)

/-- `r ∸ w =₀ 0 → r ∸ Sw =₀ 0`. No induction: uses `monus_succ` + `pd_zero`. -/
private def le_extend (r w : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus r w) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus r (.app .succ w)) Term.zero) :=
  -- ms : r ∸ Sw =₀ pd(r ∸ w)
  let ms := monus_succ adm r w
  -- pd_cong : (r ∸ w =₀ 0) → (pd(r ∸ w) =₀ pd 0)
  let pd_cong : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus r w) Term.zero →ᶠ
       Formula.eq0 (.app Term.pd (Term.app2 Term.monus r w)) (.app Term.pd Term.zero)) :=
    .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) I_comb
  -- chain1 : (r ∸ w =₀ 0) → (pd(r ∸ w) =₀ 0) using pd_zero
  let chain1 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus r w) Term.zero →ᶠ
       Formula.eq0 (.app Term.pd (Term.app2 Term.monus r w)) Term.zero) :=
    .syllogism (pair_h pd_cong (weaken_intro (pd_zero (Γ := Γ)))) .trans0
  -- chain2 : (r ∸ w =₀ 0) → (r ∸ Sw =₀ 0) using ms (rewrite LHS)
  .syllogism (pair_h (weaken_intro ms) chain1) .trans0

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
    (ih : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) r)) (.app .succ w)))
    (hle : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) (.app .succ w)) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) (.app .succ r)))
        (.app .succ w)) :=
  -- Abbreviations
  let tSw : Term F Γ Ty.nat := .app Term.triag (.app .succ w)  -- triag(Sw)
  -- Step 1: triag(Sw) + Sr =₀ S(triag(Sw) + r)  (via add_succ)
  let h_as := add_succ adm tSw r
  -- Step 2: inv_triag(triag(Sw) + Sr) =₀ inv_triag(S(triag(Sw) + r))  (inv_triag congr)
  let h_it_cong := inv_triag_congr h_as
  -- Step 3: inv_triag(S(triag(Sw) + r)) unfolds via inv_triag_succ
  let h_unfold := inv_triag_succ adm (Term.app2 Term.add tSw r)
  -- Step 4: rewrite inner inv_triag(triag(Sw)+r) to Sw on the LHS of the add.
  let h_add_l := add_congr_l ih
    (.app Term.sg_bar
      (Term.app2 Term.monus
        (.app Term.triag (.app .succ
          (.app Term.inv_triag (Term.app2 Term.add tSw r))))
        (.app .succ (Term.app2 Term.add tSw r))))
  -- Step 5: rewrite inner inv_triag inside triag(S(.)) via ih + triag/succ congr
  let h_tr_inner := triag_congr (succ_congr ih)
  -- Step 6: monus(triag(S(inv_triag(..))), S(triag(Sw)+r)) =₀ monus(triag(S(Sw)), S(triag(Sw)+r))
  let h_monus1 := monus_congr_l h_tr_inner (.app .succ (Term.app2 Term.add tSw r))
  -- Step 7: triag(S(Sw)) =₀ triag(Sw) + S(Sw)  (triag_succ)
  let h_triag_SSw := triag_succ adm (.app .succ w)
  -- Step 8: monus(triag(S(Sw)), S(triag(Sw)+r)) =₀ monus(triag(Sw) + S(Sw), S(triag(Sw)+r))
  let h_monus2 := monus_congr_l h_triag_SSw (.app .succ (Term.app2 Term.add tSw r))
  -- Step 9: S(triag(Sw)+r) =₀ triag(Sw) + Sr  (sym of add_succ)
  let h_Sadd_sym : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app2 Term.add tSw r))
        (Term.app2 Term.add tSw (.app .succ r))) :=
    .mp h_as .sym0
  -- Step 10: monus(triag(Sw) + S(Sw), S(triag(Sw)+r)) =₀ monus(triag(Sw) + S(Sw), triag(Sw) + Sr)
  let h_monus3 := monus_congr_r (Term.app2 Term.add tSw (.app .succ (.app .succ w))) h_Sadd_sym
  -- Step 11: (triag(Sw)+S(Sw)) ∸ (triag(Sw)+Sr) =₀ S(Sw) ∸ Sr  (add_monus_cancel_l)
  let h_add_cancel := add_monus_cancel_l adm tSw (.app .succ (.app .succ w)) (.app .succ r)
  -- Step 12: S(Sw) ∸ Sr =₀ Sw ∸ r  (monus_succ_l)
  let h_monus_sl := monus_succ_l adm (.app .succ w) r
  -- Chain monus1..monus3, add_cancel, monus_sl:
  -- monus(triag(S(inv_triag(..))), S(..)) =₀ Sw ∸ r
  let h_chain_m1 := .mp (.mp h_monus2 (.mp h_monus1 and_intro)) .trans0
  let h_chain_m2 := .mp (.mp h_monus3 (.mp h_chain_m1 and_intro)) .trans0
  let h_chain_m3 := .mp (.mp h_add_cancel (.mp h_chain_m2 and_intro)) .trans0
  let h_sg_arg_eq := .mp (.mp h_monus_sl (.mp h_chain_m3 and_intro)) .trans0
  -- Step 13: sg_bar(monus(...)) =₀ sg_bar(Sw ∸ r)  (sg_bar congruence)
  let h_sg_cong := sg_bar_congr h_sg_arg_eq
  -- Step 14: sg_bar(Sw ∸ r) =₀ 0.
  -- From hle: Sr ∸ Sw = 0 and monus_succ_l, we get r ∸ w = 0.
  -- Then Sw ∸ r ≠ 0 (otherwise monus_eq_zero_antisym gives r = Sw, forcing
  -- Sw ∸ w = r ∸ w = 0, but succ_monus_self says Sw ∸ w = S0, contradiction).
  -- From Sw ∸ r ≠ 0, sg_bar_eq_zero_iff gives sg_bar(Sw ∸ r) = 0.
  let h_rw_eq_0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus r w) Term.zero) :=
    -- monus_succ_l : S r ∸ S w =₀ r ∸ w; sym + trans with hle
    .mp (.mp hle (.mp (.mp (monus_succ_l adm r w) .sym0) and_intro)) .trans0
  -- r ∸ Sw = 0 from le_extend
  let h_rSw_eq_0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus r (.app .succ w)) Term.zero) :=
    .mp h_rw_eq_0 (le_extend adm r w)
  -- (Sw ∸ r = 0) →ᶠ ⊥ (the "not equal to zero" fact)
  let h_Swmr_ne_0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ ⊥ᶠ) :=
    -- Step A: (Sw∸r = 0) → (r∸Sw = 0) ∧ (Sw∸r = 0)
    let pair_both : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
         (Formula.eq0 (Term.app2 Term.monus r (.app .succ w)) Term.zero ∧ᶠ
          Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero)) :=
      .mp h_rSw_eq_0 and_intro
    -- Step B: and → (r = Sw)
    let antisym := monus_eq_zero_antisym (Premises := Premises) adm r (.app .succ w)
    let to_r_eq_Sw : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
         Formula.eq0 r (.app .succ w)) :=
      .syllogism pair_both antisym
    -- Step C: (r = Sw) → (r ∸ w = Sw ∸ w)
    let cong_monus : Derivable F EqX al Premises
        (Formula.eq0 r (.app .succ w) →ᶠ
         Formula.eq0 (Term.app2 Term.monus r w) (Term.app2 Term.monus (.app .succ w) w)) :=
      qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.monus (.var .vz) w.weaken)
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
            exact congrArg _ (Term.weaken_subst0 w r))
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
            exact congrArg _ (Term.weaken_subst0 w (.app .succ w)))
    -- Step D: (r = Sw) → (Sw ∸ w = r ∸ w) via sym
    let cong_monus_sym : Derivable F EqX al Premises
        (Formula.eq0 r (.app .succ w) →ᶠ
         Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (Term.app2 Term.monus r w)) :=
      .syllogism cong_monus .sym0
    -- Step E: (r = Sw) → (Sw ∸ w = 0) by chaining with h_rw_eq_0
    let to_Swmw_eq_0 : Derivable F EqX al Premises
        (Formula.eq0 r (.app .succ w) →ᶠ
         Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) Term.zero) :=
      .syllogism (pair_h cong_monus_sym (weaken_intro h_rw_eq_0)) .trans0
    -- Step F: Sw ∸ w = S0 (unconditional) from succ_monus_self
    let h_Swmw_eq_S0 := succ_monus_self adm w
    -- Step G: (r = Sw) → (S0 = 0) via sym of h_Swmw_eq_S0 + to_Swmw_eq_0
    let to_S0_eq_0 : Derivable F EqX al Premises
        (Formula.eq0 r (.app .succ w) →ᶠ
         Formula.eq0 (.app .succ Term.zero) Term.zero) :=
      .syllogism (pair_h (weaken_intro (.mp h_Swmw_eq_S0 .sym0)) to_Swmw_eq_0) .trans0
    -- Step H: (S0 = 0) → ⊥ via succ_ne_zero
    let h_succ_ne : Derivable F EqX al Premises
        (Formula.eq0 (.app .succ Term.zero) Term.zero →ᶠ ⊥ᶠ) :=
      .mp (@Derivable.succ_ne_zero _ _ EqX al Premises Γ) (.forall_ax Term.zero)
    -- Step I: chain to_r_eq_Sw, to_S0_eq_0, h_succ_ne
    .syllogism to_r_eq_Sw (.syllogism to_S0_eq_0 h_succ_ne)
  -- Extract: sg_bar(Sw ∸ r) = 0 from sg_bar_eq_zero_iff (backward direction)
  let h_sg_zero : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus (.app .succ w) r)) Term.zero) :=
    let iff_res := sg_bar_eq_zero_iff (Premises := Premises) adm
      (Term.app2 Term.monus (.app .succ w) r)
    .mp h_Swmr_ne_0 (.mp iff_res (.syllogism .and_perm .and_weak))
  -- Chain sg_cong + sg_zero: sg_bar(monus(...)) =₀ 0
  let h_sg_final := .mp (.mp h_sg_zero (.mp h_sg_cong and_intro)) .trans0
  -- Step 15: add(Sw, sg_bar(...)) =₀ add(Sw, 0)  (add_congr_r on sg_final)
  let h_add_r := add_congr_r (.app .succ w) h_sg_final
  -- Step 16: add(Sw, 0) =₀ Sw  (add_zero_r)
  let h_add_0 := add_zero_r adm (.app .succ w)
  -- Chain: add(Sw, sg_bar(...)) =₀ Sw
  let h_add_sw := .mp (.mp h_add_0 (.mp h_add_r and_intro)) .trans0
  -- Chain with h_add_l: add(inv_triag(triag(Sw)+r), sg_bar(...)) =₀ Sw
  let h_rhs_eq_Sw := .mp (.mp h_add_sw (.mp h_add_l and_intro)) .trans0
  -- Chain with h_unfold: inv_triag(S(triag(Sw)+r)) =₀ Sw
  let h_itS_eq_Sw := .mp (.mp h_rhs_eq_Sw (.mp h_unfold and_intro)) .trans0
  -- Chain with h_it_cong: inv_triag(triag(Sw) + Sr) =₀ Sw
  .mp (.mp h_itS_eq_Sw (.mp h_it_cong and_intro)) .trans0

/-- **L2-imp.** Implication form of `inv_triag_triag_add_inner_step`.

    Mirrors `inv_triag_triag_add_inner_step` line-by-line, threading each derivation
    through the hypothesis `P`. Unconditional facts are lifted via `weaken_intro`;
    each `.mp x lemma` becomes `eval_h (weaken_intro lemma) x_imp`. -/
private def inv_triag_triag_add_inner_step_imp
    {P : Formula F Γ} (w r : Term F Γ Ty.nat)
    (ih_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) r)) (.app .succ w)))
    (hle_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ r) (.app .succ w)) Term.zero)) :
    Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w)) (.app .succ r)))
        (.app .succ w)) :=
  let tSw : Term F Γ Ty.nat := .app Term.triag (.app .succ w)
  -- Unconditional Step 1-3 (wrapped with weaken_intro at usage)
  let h_as := add_succ adm tSw r
  let h_it_cong := inv_triag_congr h_as
  let h_unfold := inv_triag_succ adm (Term.app2 Term.add tSw r)
  -- X = sg_bar argument
  let X : Term F Γ Ty.nat :=
    .app Term.sg_bar
      (Term.app2 Term.monus
        (.app Term.triag (.app .succ
          (.app Term.inv_triag (Term.app2 Term.add tSw r))))
        (.app .succ (Term.app2 Term.add tSw r)))
  -- Step 4 (imp): rewrite inner inv_triag(triag(Sw)+r) to Sw on the LHS of add.
  -- Build bare congruence via qfer_nat_nf, then syllogism with ih_imp.
  let cong_add_l : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add tSw r)) (.app .succ w) →ᶠ
       Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add tSw r)) X)
         (Term.app2 Term.add (.app .succ w) X)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.add (.var .vz) X.weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg _ (Term.weaken_subst0 X _))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg _ (Term.weaken_subst0 X _))
  let h_add_l_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add tSw r)) X)
         (Term.app2 Term.add (.app .succ w) X)) :=
    .syllogism ih_imp cong_add_l
  -- Step 5 (imp): triag(S(inv_triag(triag(Sw)+r))) =₀ triag(S(Sw))
  let cong_tr_inner : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add tSw r)) (.app .succ w) →ᶠ
       Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add tSw r))))
         (.app Term.triag (.app .succ (.app .succ w)))) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app Term.triag (.app .succ (.var .vz)))
      rfl rfl
  let h_tr_inner_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add tSw r))))
         (.app Term.triag (.app .succ (.app .succ w)))) :=
    .syllogism ih_imp cong_tr_inner
  -- Step 6 (imp): monus(triag(S(inv_triag(..))), S(triag(Sw)+r)) =₀ monus(triag(S(Sw)), S(triag(Sw)+r))
  let Y : Term F Γ Ty.nat := .app .succ (Term.app2 Term.add tSw r)
  let cong_monus1 : Derivable F EqX al Premises
      (Formula.eq0
         (.app Term.triag (.app .succ
           (.app Term.inv_triag (Term.app2 Term.add tSw r))))
         (.app Term.triag (.app .succ (.app .succ w))) →ᶠ
       Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)
         (Term.app2 Term.monus (.app Term.triag (.app .succ (.app .succ w))) Y)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.monus (.var .vz) Y.weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 Y _))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 Y _))
  let h_monus1_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)
         (Term.app2 Term.monus (.app Term.triag (.app .succ (.app .succ w))) Y)) :=
    .syllogism h_tr_inner_imp cong_monus1
  -- Unconditional Step 7-12
  let h_triag_SSw := triag_succ adm (.app .succ w)
  let h_monus2 := monus_congr_l h_triag_SSw (.app .succ (Term.app2 Term.add tSw r))
  let h_Sadd_sym : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app2 Term.add tSw r))
        (Term.app2 Term.add tSw (.app .succ r))) :=
    .mp h_as .sym0
  let h_monus3 := monus_congr_r (Term.app2 Term.add tSw (.app .succ (.app .succ w))) h_Sadd_sym
  let h_add_cancel := add_monus_cancel_l adm tSw (.app .succ (.app .succ w)) (.app .succ r)
  let h_monus_sl := monus_succ_l adm (.app .succ w) r
  -- Chain m1..m3, add_cancel, monus_sl threaded through P
  let h_chain_m1_imp := .syllogism (pair_h h_monus1_imp (weaken_intro h_monus2)) .trans0
  let h_chain_m2_imp := .syllogism (pair_h h_chain_m1_imp (weaken_intro h_monus3)) .trans0
  let h_chain_m3_imp := .syllogism (pair_h h_chain_m2_imp (weaken_intro h_add_cancel)) .trans0
  let h_sg_arg_eq_imp := .syllogism (pair_h h_chain_m3_imp (weaken_intro h_monus_sl)) .trans0
  -- Step 13 (imp): sg_bar(monus(...)) =₀ sg_bar(Sw ∸ r)
  let cong_sg_bar : Derivable F EqX al Premises
      (Formula.eq0
         (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)
         (Term.app2 Term.monus (.app .succ w) r) →ᶠ
       Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y))
         (.app Term.sg_bar (Term.app2 Term.monus (.app .succ w) r))) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app Term.sg_bar (.var .vz)) rfl rfl
  let h_sg_cong_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y))
         (.app Term.sg_bar (Term.app2 Term.monus (.app .succ w) r))) :=
    .syllogism h_sg_arg_eq_imp cong_sg_bar
  -- Step 14 (imp): sg_bar(Sw ∸ r) =₀ 0.
  -- First derive the threaded forms of h_rw_eq_0 and h_rSw_eq_0.
  let cong_monus_sl_sym : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ r) (.app .succ w)) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus r w) Term.zero) :=
    .syllogism (pair_h (weaken_intro (.mp (monus_succ_l adm r w) .sym0)) I_comb) .trans0
  let h_rw_eq_0_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.monus r w) Term.zero) :=
    .syllogism hle_imp cong_monus_sl_sym
  let h_rSw_eq_0_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.monus r (.app .succ w)) Term.zero) :=
    .syllogism h_rw_eq_0_imp (le_extend adm r w)
  -- Build h_Swmr_ne_0_imp : P →ᶠ ((Sw ∸ r = 0) →ᶠ ⊥).
  -- We construct a bare lemma `ne_bare : (r∸w=0) ∧ (r∸Sw=0) →ᶠ ((Sw∸r=0) →ᶠ ⊥)`,
  -- then apply it to the pair (h_rw_eq_0_imp, h_rSw_eq_0_imp).
  -- ne_bare is the original h_Swmr_ne_0 with the two facts exposed as explicit
  -- antecedents in a conjoined form.
  let antisym := monus_eq_zero_antisym (Premises := Premises) adm r (.app .succ w)
  let cong_monus_rSw : Derivable F EqX al Premises
      (Formula.eq0 r (.app .succ w) →ᶠ
       Formula.eq0 (Term.app2 Term.monus r w) (Term.app2 Term.monus (.app .succ w) w)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.monus (.var .vz) w.weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 w r))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
          exact congrArg _ (Term.weaken_subst0 w (.app .succ w)))
  let cong_monus_sym : Derivable F EqX al Premises
      (Formula.eq0 r (.app .succ w) →ᶠ
       Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (Term.app2 Term.monus r w)) :=
    .syllogism cong_monus_rSw .sym0
  let h_Swmw_eq_S0 := succ_monus_self adm w
  let h_succ_ne : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ Term.zero) Term.zero →ᶠ ⊥ᶠ) :=
    .mp (@Derivable.succ_ne_zero _ _ EqX al Premises Γ) (.forall_ax Term.zero)
  -- Now, using `pair_h`/`eval_h` style where the "H" is P, we derive:
  -- h_Swmr_ne_0_imp : P → ((Sw∸r=0) → ⊥)
  -- by chaining through:
  --   P → (r∸Sw=0)                         [h_rSw_eq_0_imp]
  --   P → ((Sw∸r=0) → (r∸Sw=0 ∧ Sw∸r=0))  [via and_intro]
  --   P → ((Sw∸r=0) → (r = Sw))            [via antisym]
  --   P → ((Sw∸r=0) → (Sw∸w = r∸w))        [via cong_monus_sym]
  --   P → ((Sw∸r=0) → (Sw∸w = 0))          [chain with h_rw_eq_0_imp]
  --   P → ((Sw∸r=0) → (S0 = 0))            [chain with h_Swmw_eq_S0 sym]
  --   P → ((Sw∸r=0) → ⊥)                   [chain with h_succ_ne]
  -- Use `eval_h` and `pair_h` uniformly with H = P.
  let pair_both_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
       (Formula.eq0 (Term.app2 Term.monus r (.app .succ w)) Term.zero ∧ᶠ
        Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero))) :=
    eval_h (weaken_intro and_intro) h_rSw_eq_0_imp
  let to_r_eq_Sw_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
       Formula.eq0 r (.app .succ w))) :=
    -- Chain pair_both_imp with antisym (bare) via eval_h under P:
    -- pair_both_imp : P → (C → A∧B),  antisym : (A∧B) → (r=Sw)
    -- want: P → (C → (r=Sw))
    -- This is: P → (C → (A∧B))  followed by weakened bare (C → ((A∧B) → (r=Sw)))
    -- i.e., use a "syllogism under imp": given (P → C → X) and (X → Y), get (P → C → Y).
    -- Build via: λP. λC. antisym (pair_both P C)
    -- Concretely: `.syllogism pair_both_imp (imp_compose antisym)` where
    -- `imp_compose : (X → Y) → ((C → X) → (C → Y))` is `B_comb` or similar.
    -- Use `.exportation (.importation ...)` tricks.
    -- Simpler: use the lemma (C → X) → (X → Y) → (C → Y) = syllogism, then lift through P.
    -- Namely: from P → (C → X), get (P → C → Y) by applying eval_h twice.
    let step1 : Derivable F EqX al Premises (P →ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ Formula.eq0 r (.app .succ w)) :=
      -- We want from pair_both_imp : P → (C → (A∧B)) and antisym : (A∧B) → X,
      -- derive P → (C → X).
      -- Use .exportation/importation: the bare rule `(C → Y) → (Y → X) → (C → X)` is syllogism.
      -- Lifted: (P → C → Y) → ((Y → X) bare) → (P → C → X). We can do this via importation.
      -- Form .importation pair_both_imp : P ∧ C → (A∧B)
      -- .syllogism with antisym : P ∧ C → (r=Sw)
      -- .exportation : P → C → (r=Sw)
      .exportation (.syllogism (.importation pair_both_imp) antisym)
    step1
  -- to_Swmw_eq_r_minus_w_imp : P → ((Sw∸r=0) → (Sw∸w = r∸w))
  let to_Swmw_eq_r_minus_w_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (Term.app2 Term.monus r w))) :=
    .exportation (.syllogism (.importation to_r_eq_Sw_imp) cong_monus_sym)
  -- to_Swmw_eq_0_imp : P → ((Sw∸r=0) → (Sw∸w = 0))
  -- Chain: (Sw∸w = r∸w) ∧ (r∸w = 0) → (Sw∸w = 0) via trans0
  let to_Swmw_eq_0_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) Term.zero)) :=
    -- Need (P → (C → (Sw∸w=0)))
    -- Have to_Swmw_eq_r_minus_w_imp : P → (C → (Sw∸w = r∸w))
    -- Have h_rw_eq_0_imp : P → (r∸w = 0)
    -- Under (P ∧ C), we need: (Sw∸w = r∸w) ∧ (r∸w = 0) → (Sw∸w = 0) [trans0]
    -- .importation to_Swmw_eq_r_minus_w_imp : (P ∧ C) → (Sw∸w = r∸w)
    -- We also need h_rw_eq_0_imp lifted to (P ∧ C) → (r∸w = 0) via syllogism with .and_weak
    let imp1 : Derivable F EqX al Premises
        ((P ∧ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero) →ᶠ
         Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) (Term.app2 Term.monus r w)) :=
      .importation to_Swmw_eq_r_minus_w_imp
    let imp2 : Derivable F EqX al Premises
        ((P ∧ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero) →ᶠ
         Formula.eq0 (Term.app2 Term.monus r w) Term.zero) :=
      .syllogism .and_weak h_rw_eq_0_imp
    .exportation (.syllogism (pair_h imp1 imp2) .trans0)
  -- to_S0_eq_0_imp : P → ((Sw∸r=0) → (S0 = 0))
  let to_S0_eq_0_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ
       Formula.eq0 (.app .succ Term.zero) Term.zero)) :=
    -- (Sw∸w = 0) combined with (Sw∸w = S0).sym0 = (S0 = Sw∸w) gives (S0 = 0) via trans0
    let s0_eq_swmw := .mp h_Swmw_eq_S0 .sym0  -- S0 = Sw∸w
    -- Under (P ∧ C): (S0 = Sw∸w) ∧ (Sw∸w = 0) → (S0 = 0)
    let imp1 : Derivable F EqX al Premises
        ((P ∧ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero) →ᶠ
         Formula.eq0 (.app .succ Term.zero) (Term.app2 Term.monus (.app .succ w) w)) :=
      weaken_intro s0_eq_swmw
    let imp2 : Derivable F EqX al Premises
        ((P ∧ᶠ Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero) →ᶠ
         Formula.eq0 (Term.app2 Term.monus (.app .succ w) w) Term.zero) :=
      .importation to_Swmw_eq_0_imp
    .exportation (.syllogism (pair_h imp1 imp2) .trans0)
  -- h_Swmr_ne_0_imp : P → ((Sw∸r=0) → ⊥)  via h_succ_ne
  let h_Swmr_ne_0_imp : Derivable F EqX al Premises
      (P →ᶠ (Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ ⊥ᶠ)) :=
    .exportation (.syllogism (.importation to_S0_eq_0_imp) h_succ_ne)
  -- Extract: P → (sg_bar(Sw ∸ r) = 0) from sg_bar_eq_zero_iff (backward direction)
  let h_sg_zero_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus (.app .succ w) r)) Term.zero) :=
    let iff_res := sg_bar_eq_zero_iff (Premises := Premises) adm
      (Term.app2 Term.monus (.app .succ w) r)
    -- iff_res : (sg_bar(x) = 0 ↔ (x = 0 → ⊥))  in and-form.
    -- From the original L2: `.mp h_Swmr_ne_0 (.mp iff_res (.syllogism .and_perm .and_weak))`
    -- which extracts the backward direction `((x = 0 → ⊥) → sg_bar(x) = 0)` and applies it.
    let bwd_bare : Derivable F EqX al Premises
        ((Formula.eq0 (Term.app2 Term.monus (.app .succ w) r) Term.zero →ᶠ ⊥ᶠ) →ᶠ
         Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus (.app .succ w) r)) Term.zero) :=
      .mp iff_res (.syllogism .and_perm .and_weak)
    .syllogism h_Swmr_ne_0_imp bwd_bare
  -- Chain h_sg_cong_imp + h_sg_zero_imp: P → sg_bar(monus(...)) = 0
  let h_sg_final_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y))
         Term.zero) :=
    .syllogism (pair_h h_sg_cong_imp h_sg_zero_imp) .trans0
  -- Step 15 (imp): add(Sw, sg_bar(...)) = add(Sw, 0) via add_congr_r (bare congruence).
  let Sw : Term F Γ Ty.nat := .app .succ w
  let cong_add_r_Sw : Derivable F EqX al Premises
      (Formula.eq0
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y))
         Term.zero →ᶠ
       Formula.eq0 (Term.app2 Term.add Sw
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)))
         (Term.app2 Term.add Sw Term.zero)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.add Sw.weaken (.var .vz))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg (Term.app · _) (congrArg (Term.app Term.add ·)
            (Term.weaken_subst0 Sw _)))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst]
          exact congrArg (Term.app · _) (congrArg (Term.app Term.add ·)
            (Term.weaken_subst0 Sw _)))
  let h_add_r_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add (.app .succ w)
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)))
         (Term.app2 Term.add (.app .succ w) Term.zero)) :=
    .syllogism h_sg_final_imp cong_add_r_Sw
  -- Step 16: add(Sw, 0) = Sw unconditional
  let h_add_0 := add_zero_r adm (.app .succ w)
  -- Chain: add(Sw, sg_bar(...)) = Sw  (imp)
  let h_add_sw_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add (.app .succ w)
         (.app Term.sg_bar (Term.app2 Term.monus
           (.app Term.triag (.app .succ
             (.app Term.inv_triag (Term.app2 Term.add tSw r)))) Y)))
         (.app .succ w)) :=
    .syllogism (pair_h h_add_r_imp (weaken_intro h_add_0)) .trans0
  -- Chain with h_add_l_imp: add(inv_triag(triag(Sw)+r), sg_bar(...)) = Sw  (imp)
  let h_rhs_eq_Sw_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0 (Term.app2 Term.add
         (.app Term.inv_triag (Term.app2 Term.add tSw r)) X)
         (.app .succ w)) :=
    .syllogism (pair_h h_add_l_imp h_add_sw_imp) .trans0
  -- Chain with h_unfold: inv_triag(S(triag(Sw)+r)) = Sw  (imp)
  let h_itS_eq_Sw_imp : Derivable F EqX al Premises
      (P →ᶠ Formula.eq0
         (.app Term.inv_triag (.app .succ (Term.app2 Term.add tSw r)))
         (.app .succ w)) :=
    .syllogism (pair_h (weaken_intro h_unfold) h_rhs_eq_Sw_imp) .trans0
  -- Final: chain with h_it_cong
  .syllogism (pair_h (weaken_intro h_it_cong) h_itS_eq_Sw_imp) .trans0

/-- **L3.** Outer induction step: `B(w) →ᶠ B(Sw)`, where
    `B(w) := ∀r. monus r w =₀ 0 →ᶠ inv_triag(triag w + r) =₀ w`.

    Proof strategy: We work in context `Ty.nat :: Γ`, where "w" is `.var .vz`.
    We must produce a derivation of `B →ᶠ ∀r. C[Sw/w]`. Using `forall_imp_swap`
    we reduce to proving `∀r. (B.weakenBy Ty.nat →ᶠ C[Sw/w, r])`, which by
    `univ_gen` reduces to proving the body in context `Ty.nat :: Ty.nat :: Γ`.
    The body is then proved by inner induction on `r` via `Derivable.induction`
    on a formula `E(r)` in context `Ty.nat :: Ty.nat :: Γ`. The inner base uses
    the outer IH `B` instantiated at `r := w` (obtained from `B.weakenBy`) via
    `inv_triag_triag_self_succ_imp` (L1-imp). The inner step uses
    `inv_triag_triag_add_inner_step_imp` (L2-imp). -/
private def inv_triag_triag_add_step {Γ : Ctx ι} :
    let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
      Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.var (.vs .vz))) (.var .vz)))
        (.var (.vs .vz))
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
    Derivable F EqX al Premises (B →ᶠ Formula.substVar0 B (.app .succ (.var .vz))) := by
  intro C B
  -- Step 1: Normalize the RHS: `Formula.substVar0 B (S .vz) = Formula.all Ty.nat C'`
  -- where C' is the body with outer `w = .vs .vz` replaced by `S (.vs .vz)` and
  -- inner `r = .vz` unchanged.
  let C' : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.app .succ (.var (.vs .vz)))) Term.zero →ᶠ
    Formula.eq0 (.app Term.inv_triag
      (Term.app2 Term.add (.app Term.triag (.app .succ (.var (.vs .vz)))) (.var .vz)))
      (.app .succ (.var (.vs .vz)))
  have rhs_nf : Formula.substVar0 B (.app .succ (.var .vz)) = Formula.all Ty.nat C' := by
    simp only [B, C, C', Formula.substVar0, Formula.substF, Term.Subst.ext, Term.substVar0_map,
      Term.subst, Term.app2, Term.weaken, Term.rename, Term.Renaming.shift,
      monus_closed_subst, add_closed_subst, triag_closed_subst, inv_triag_closed_subst]
  rw [rhs_nf]
  -- Goal: B →ᶠ Formula.all Ty.nat C'
  -- Apply forall_imp_swap to reduce to: Formula.all Ty.nat (B.weakenBy Ty.nat →ᶠ C')
  refine forall_imp_swap ?_
  -- Apply `Derivable.induction` directly on the formula `A := B.weakenBy Ty.nat →ᶠ C'`
  -- with induction variable `.var .vz : Ty.nat` (the inner r).
  -- After induction, base is `A.subst0 Term.zero`, step is `Formula.all Ty.nat (A →ᶠ A[S.vz/.vz])`.
  -- We rely on the fact that `(B.weakenBy Ty.nat).subst0 Term.zero = B` and
  -- `(B.weakenBy Ty.nat).substVar0 (S .vz) = B.weakenBy Ty.nat`.
  -- We also need to compute C'.subst0 Term.zero and C'.substVar0 (S .vz).
  -- Define the base/step normal forms.
  let w_v : Term F (Ty.nat :: Γ) Ty.nat := .var .vz  -- outer "w"
  -- Base body: (0 ∸ S w_v = 0) → inv_triag(triag(S w_v) + 0) = S w_v
  let base_body : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus Term.zero (.app .succ w_v)) Term.zero →ᶠ
    Formula.eq0 (.app Term.inv_triag
      (Term.app2 Term.add (.app Term.triag (.app .succ w_v)) Term.zero))
      (.app .succ w_v)
  -- Helper: (B.weakenBy Ty.nat).subst0 t = B for any t, since weakening shifts all vars.
  have B_weaken_subst0 : ∀ t : Term F (Ty.nat :: Γ) Ty.nat,
      (B.weakenBy Ty.nat).subst0 t = B := by
    intro t
    exact substF_renameF_id Term.Renaming.shift (Term.subst0_map t) (fun {_} _ => rfl) B
  -- The full base: B →ᶠ base_body
  have C'_base_nf : C'.subst0 Term.zero = base_body := by
    simp only [C', base_body, w_v, Formula.subst0, Formula.substF, Term.subst, Term.app2,
      Term.subst0_map, monus_closed_subst, add_closed_subst,
      triag_closed_subst, inv_triag_closed_subst]
  have base_nf : (B.weakenBy Ty.nat →ᶠ C').subst0 Term.zero = (B →ᶠ base_body) := by
    show Formula.imp ((B.weakenBy Ty.nat).subst0 Term.zero) (C'.subst0 Term.zero) = _
    rw [B_weaken_subst0, C'_base_nf]
  -- Helper: C.subst0 w_v NF reduction (used to extract the outer IH from B).
  have C_subst0_wv_nf : C.subst0 w_v =
      (Formula.eq0 (Term.app2 Term.monus w_v w_v) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag
         (Term.app2 Term.add (.app Term.triag w_v) w_v)) w_v) := by
    simp only [C, w_v, Formula.subst0, Formula.substF, Term.subst, Term.app2,
      Term.subst0_map, monus_closed_subst, add_closed_subst, triag_closed_subst,
      inv_triag_closed_subst]
  -- Build the base derivation: B →ᶠ base_body.
  -- Strategy: use L1-imp with P := B. We need P →ᶠ (inv_triag(triag w_v + w_v) = w_v)
  -- from B. Instantiate B (which is ∀r. ...) at r := w_v via .forall_ax w_v, then
  -- feed `monus_self w_v` to the extracted implication.
  have base_deriv : Derivable F EqX al Premises (B →ᶠ base_body) :=
    let fa : Derivable F EqX al Premises (B →ᶠ C.subst0 w_v) :=
      @Derivable.forall_ax ι F EqX al Premises (Ty.nat :: Γ) Ty.nat C w_v
    let fa' : Derivable F EqX al Premises
        (B →ᶠ (Formula.eq0 (Term.app2 Term.monus w_v w_v) Term.zero →ᶠ
               Formula.eq0 (.app Term.inv_triag
                 (Term.app2 Term.add (.app Term.triag w_v) w_v)) w_v)) :=
      C_subst0_wv_nf ▸ fa
    -- Extract IH from fa' by feeding `monus_self w_v` (unconditional) into the inner implication.
    -- Use `eval_h` : from (P → (A → Q)) and (P → A), derive (P → Q).
    let ih_imp : Derivable F EqX al Premises
        (B →ᶠ Formula.eq0 (.app Term.inv_triag
          (Term.app2 Term.add (.app Term.triag w_v) w_v)) w_v) :=
      eval_h fa' (weaken_intro (monus_self adm w_v))
    -- Apply L1-imp with P := B:
    let l1 := inv_triag_triag_self_succ_imp (P := B) adm w_v ih_imp
    -- Convert l1 : B →ᶠ (inv_triag(triag(S w_v)) = S w_v) to base_body target by
    -- chaining with inv_triag(triag(S w_v) + 0) = inv_triag(triag(S w_v)):
    let add_zero : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.add (.app Term.triag (.app .succ w_v)) Term.zero)
          (.app Term.triag (.app .succ w_v))) :=
      add_zero_r adm (.app Term.triag (.app .succ w_v))
    let h_it_cong := inv_triag_congr add_zero
    let consequent_imp : Derivable F EqX al Premises
        (B →ᶠ Formula.eq0 (.app Term.inv_triag
          (Term.app2 Term.add (.app Term.triag (.app .succ w_v)) Term.zero))
          (.app .succ w_v)) :=
      .syllogism (pair_h (weaken_intro h_it_cong) l1) .trans0
    -- Introduce the (0 ∸ S w_v = 0) hypothesis (weaken_intro on the inner implication):
    -- Given B →ᶠ Q, we want B →ᶠ (H →ᶠ Q), obtained by syllogism with K_comb.
    .syllogism consequent_imp (.exportation .and_weak)
  -- ─── STEP CASE ───────────────────────────────────────────────────────────
  -- We work in context Ty.nat :: Ty.nat :: Γ with inner r at .vz, outer w at .vs .vz.
  -- Goal body: (B.weakenBy Ty.nat →ᶠ C') →ᶠ (B.weakenBy Ty.nat →ᶠ C'.substVar0 (S .vz))
  -- Simpler abbreviations: r_v = .var .vz (inner r), w2_v = .var (.vs .vz) (outer w in inner ctx).
  let r_v : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let w2_v : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  -- Normalize `C'.substVar0 (S .vz)` to a concrete formula.
  let C'_step : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.app .succ r_v) (.app .succ w2_v)) Term.zero →ᶠ
    Formula.eq0 (.app Term.inv_triag
      (Term.app2 Term.add (.app Term.triag (.app .succ w2_v)) (.app .succ r_v)))
      (.app .succ w2_v)
  have C'_step_nf : C'.substVar0 (.app .succ (.var .vz)) = C'_step := by
    simp only [C', C'_step, r_v, w2_v, Formula.substVar0, Formula.substF, Term.subst,
      Term.app2, Term.substVar0_map, monus_closed_subst, add_closed_subst,
      triag_closed_subst, inv_triag_closed_subst]
  -- B.weakenBy Ty.nat has no `.vz`; substVar0 at `.vz` is identity on the weakened formula.
  -- Prove via: substVar0 t = substF (substVar0_map t), weaken = renameF shift, and
  -- substVar0_map t ∘ shift = λv. .var (.vs v) which is exactly Term.var ∘ shift.
  -- We fuse via substF_renameF (inlined) to get substF (Term.var ∘ shift) B = B.weaken.
  -- Helper `rfl` lemmas for closed-constant renames (monus, add, triag, inv_triag).
  have monus_closed_rename : ∀ {Γa Δa : Ctx ι} (r : Renaming Γa Δa),
      Term.rename r (Term.monus : Term F Γa _) = Term.monus := fun _ => rfl
  have add_closed_rename : ∀ {Γa Δa : Ctx ι} (r : Renaming Γa Δa),
      Term.rename r (Term.add : Term F Γa _) = Term.add := fun _ => rfl
  have triag_closed_rename : ∀ {Γa Δa : Ctx ι} (r : Renaming Γa Δa),
      Term.rename r (Term.triag : Term F Γa _) = Term.triag := fun _ => rfl
  have inv_triag_closed_rename : ∀ {Γa Δa : Ctx ι} (r : Renaming Γa Δa),
      Term.rename r (Term.inv_triag : Term F Γa _) = Term.inv_triag := fun _ => rfl
  have B_weaken_substVar0 : (B.weakenBy Ty.nat).substVar0 (.app .succ (.var .vz)) =
      B.weakenBy Ty.nat := by
    show Formula.substF (Term.substVar0_map (.app .succ (.var .vz)))
      (Formula.renameF Term.Renaming.shift B) = Formula.renameF Term.Renaming.shift B
    simp only [B, C, Formula.renameF, Formula.substF, Term.rename, Term.subst,
      Term.Subst.ext, Term.Renaming.ext, Term.Renaming.shift, Term.substVar0_map,
      Term.app2, monus_closed_subst, add_closed_subst, triag_closed_subst,
      inv_triag_closed_subst, monus_closed_rename, add_closed_rename,
      triag_closed_rename, inv_triag_closed_rename, Term.weaken]
  have step_body_nf : ((B.weakenBy Ty.nat →ᶠ C') →ᶠ
      (B.weakenBy Ty.nat →ᶠ C').substVar0 (.app .succ (.var .vz))) =
      ((B.weakenBy Ty.nat →ᶠ C') →ᶠ (B.weakenBy Ty.nat →ᶠ C'_step)) := by
    show Formula.imp _ (Formula.imp (Formula.substF _ (Formula.weakenBy Ty.nat B))
      (Formula.substF _ C')) = _
    change _ = Formula.imp _ (Formula.imp (Formula.weakenBy Ty.nat B) C'_step)
    congr 1
  -- Use Derivable.induction on A := B.weakenBy Ty.nat →ᶠ C' to prove ∀r. A.
  -- base: A.subst0 0 = B →ᶠ base_body (proved above as base_deriv)
  -- step: ∀r. A →ᶠ A.substVar0 (Sr) which normalizes via step_body_nf
  --       to ∀r. (B.wk →ᶠ C') →ᶠ (B.wk →ᶠ C'_step)
  --
  -- Step body derivation:
  -- Need: (B.wk →ᶠ C') →ᶠ (B.wk →ᶠ C'_step)
  -- Where C' = (r ∸ Sw = 0) →ᶠ inv_triag(triag(Sw) + r) = Sw
  --       C'_step = (Sr ∸ Sw = 0) →ᶠ inv_triag(triag(Sw) + Sr) = Sw
  -- By triple importation:
  --   (B.wk →ᶠ C') ∧ᶠ B.wk ∧ᶠ (Sr ∸ Sw = 0) →ᶠ inv_triag(triag(Sw) + Sr) = Sw
  -- From the 3-conj:
  --   1. Extract C': .syllogism .and_weak (eval_h with .syllogism .and_perm .and_weak)
  --      Actually: eval_h .and_weak (.syllogism .and_perm .and_weak) gives
  --      ((B.wk→C') ∧ B.wk) → C'. But we have ((B.wk→C') ∧ B.wk ∧ _) so first drop third.
  --   2. Extract (Sr ∸ Sw = 0): .syllogism .and_perm .and_weak → .syllogism .and_perm .and_weak
  --   3. le_pred gives (Sr ∸ Sw = 0) → (r ∸ Sw = 0)
  --   4. Feed (r ∸ Sw = 0) into C' to get inv_triag(triag(Sw)+r) = Sw
  --   5. L2 plain gives the step conclusion.
  -- Let's assemble:
  -- P3 := (B.wk →ᶠ C') ∧ᶠ B.wk ∧ᶠ (Sr ∸ Sw = 0)
  -- Abbreviation for the le-hypothesis formula:
  -- Use L2-imp with P := (B.wk →ᶠ C') ∧ᶠ B.wk ∧ᶠ hle_fml.
  -- ∧ᶠ is right-associative: (B.wk →ᶠ C') ∧ᶠ (B.wk ∧ᶠ hle_fml).
  let hle_fml : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.app .succ r_v) (.app .succ w2_v)) Term.zero
  let P3 : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    (B.weakenBy Ty.nat →ᶠ C') ∧ᶠ B.weakenBy Ty.nat ∧ᶠ hle_fml
  -- P3 = ((B.wk →ᶠ C') ∧ᶠ B.wk) ∧ᶠ hle_fml  (∧ᶠ is infixl)
  -- Projections from P3:
  -- get_Q : P3 → (B.wk →ᶠ C')
  let get_Q : Derivable F EqX al Premises (P3 →ᶠ (B.weakenBy Ty.nat →ᶠ C')) :=
    .syllogism .and_weak .and_weak
  -- get_Bwk : P3 → B.wk
  let get_Bwk : Derivable F EqX al Premises (P3 →ᶠ B.weakenBy Ty.nat) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  -- get_C' : P3 → C'  (= (r ∸ Sw = 0) →ᶠ goal_r)
  let get_C' : Derivable F EqX al Premises (P3 →ᶠ C') :=
    eval_h get_Q get_Bwk
  -- get_hle : P3 → (Sr ∸ Sw = 0)
  let get_hle : Derivable F EqX al Premises (P3 →ᶠ hle_fml) :=
    .syllogism .and_perm .and_weak
  -- get_hle_r : P3 → (r ∸ Sw = 0) via le_pred
  let get_hle_r : Derivable F EqX al Premises
      (P3 →ᶠ Formula.eq0 (Term.app2 Term.monus r_v (.app .succ w2_v)) Term.zero) :=
    .syllogism get_hle (le_pred adm r_v (.app .succ w2_v))
  -- get_goal_r : P3 → inv_triag(triag(Sw) + r) = Sw
  let get_goal_r : Derivable F EqX al Premises
      (P3 →ᶠ Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w2_v)) r_v))
        (.app .succ w2_v)) :=
    eval_h get_C' get_hle_r
  -- Apply L2-imp: from (P3 → goal_r) and (P3 → hle), get (P3 → goal_Sr)
  let step_conj : Derivable F EqX al Premises
      (P3 →ᶠ Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag (.app .succ w2_v)) (.app .succ r_v)))
        (.app .succ w2_v)) :=
    inv_triag_triag_add_inner_step_imp adm w2_v r_v get_goal_r get_hle
  -- Triple exportation: P3 → goal_Sr becomes Q → B.wk → hle → goal_Sr = Q → B.wk → C'_step
  let step_deriv : Derivable F EqX al Premises
      ((B.weakenBy Ty.nat →ᶠ C') →ᶠ B.weakenBy Ty.nat →ᶠ C'_step) :=
    .exportation (.exportation step_conj)
  -- Assemble the induction.
  exact Derivable.induction (base_nf ▸ base_deriv) (step_body_nf ▸ univ_gen step_deriv)

/-- **Main theorem.** Key invariant: `inv_triag(triag(w) + r) =₀ w` when `r ≤ w`.

    This is the core arithmetic fact behind the Cantor pairing projections.
    The side condition `r ≤ w` ensures `triag(w) + r < triag(w+1)`, so the
    `inv_triag` recursion correctly identifies `w` as the triangle index.

    Proved by outer induction on `w` using `B(w) := ∀r. monus r w =₀ 0 → ...`.
    Base case: `r ≤ 0` forces `r = 0`, then `inv_triag(triag 0 + 0) = inv_triag(0) = 0`.
    Step case: delegated to `inv_triag_triag_add_step` (L3). -/
private def inv_triag_triag_add (w r : Term F Γ Ty.nat)
    (h : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus r w) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag w) r)) w) :=
  -- Outer induction on w with B(w) := ∀r. (r ∸ w = 0) →ᶠ inv_triag(triag w + r) = w
  let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
    Formula.eq0 (.app Term.inv_triag
      (Term.app2 Term.add (.app Term.triag (.var (.vs .vz))) (.var .vz)))
      (.var (.vs .vz))
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
  -- Base B(0): ∀r. (r ∸ 0 = 0) →ᶠ inv_triag(triag 0 + r) = 0
  have base_nf : B.subst0 Term.zero = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (.var .vz) Term.zero) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag
         (Term.app2 Term.add (.app Term.triag Term.zero) (.var .vz))) Term.zero) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst, add_closed_subst,
      triag_closed_subst, inv_triag_closed_subst, Term.weaken, Term.rename,
      Term.Renaming.shift]
  let rv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  -- r_eq_0 : (r ∸ 0 = 0) → (r = 0)
  let r_eq_0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus rv Term.zero) Term.zero →ᶠ
       Formula.eq0 rv Term.zero) :=
    .syllogism (pair_h (weaken_intro (.mp (monus_zero adm rv) .sym0)) I_comb) .trans0
  -- goal_chain : inv_triag(triag 0 + 0) = 0 (at context Ty.nat :: Γ)
  let h_az := add_zero_r adm (.app Term.triag (Term.zero : Term F (Ty.nat :: Γ) _))
  let h_tz := triag_zero (Γ := Ty.nat :: Γ)
  let h_chain1 := .mp (.mp h_tz (.mp h_az and_intro)) .trans0  -- triag 0 + 0 = 0
  let h_it_cong := inv_triag_congr h_chain1  -- inv_triag(triag 0 + 0) = inv_triag 0
  let h_itz := inv_triag_zero (Γ := Ty.nat :: Γ)
  let h_goal_0 := .mp (.mp h_itz (.mp h_it_cong and_intro)) .trans0
  -- From (r = 0) derive inv_triag(triag 0 + r) = inv_triag(triag 0 + 0) via .qfer
  let t0 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.triag Term.zero
  let it_cong_imp : Derivable F EqX al Premises
      (Formula.eq0 rv Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add t0 rv))
         (.app Term.inv_triag (Term.app2 Term.add t0 Term.zero))) :=
    .qfer (σ := Ty.nat)
      (r := .app Term.inv_triag
        (Term.app2 Term.add (.app Term.triag Term.zero) (.var .vz)))
      (by rfl) (by rfl) I_comb
  -- base_body : (r ∸ 0 = 0) → inv_triag(triag 0 + r) = 0
  let base_body : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus rv Term.zero) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag (Term.app2 Term.add t0 rv)) Term.zero) :=
    .syllogism r_eq_0 (.syllogism (pair_h it_cong_imp (weaken_intro h_goal_0)) .trans0)
  let base : Derivable F EqX al Premises (B.subst0 Term.zero) :=
    base_nf ▸ univ_gen base_body
  -- Step: inv_triag_triag_add_step
  let step := @inv_triag_triag_add_step _ _ _ _ Premises adm Γ
  -- Induction
  let ind := Derivable.induction base (univ_gen step)
  -- Instantiate: ind : ∀w. B(w), so at w: B(w) = ∀r. C(w,r)
  have B_inst_nf : B.subst0 w = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (.var .vz) w.weaken) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag
         (Term.app2 Term.add (.app Term.triag w.weaken) (.var .vz))) w.weaken) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst, add_closed_subst,
      triag_closed_subst, inv_triag_closed_subst]
  let at_w := .mp ind (.forall_ax w)  -- B(w)
  let at_w' := Eq.mp (congrArg (Derivable F EqX al Premises) B_inst_nf) at_w
  -- Instantiate inner ∀ at r
  have C_inst_nf :
      (Formula.eq0 (Term.app2 Term.monus (.var .vz) w.weaken) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag
         (Term.app2 Term.add (.app Term.triag w.weaken) (.var .vz))) w.weaken).subst0 r =
      (Formula.eq0 (Term.app2 Term.monus r w) Term.zero →ᶠ
       Formula.eq0 (.app Term.inv_triag
         (Term.app2 Term.add (.app Term.triag w) r)) w) := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst, add_closed_subst, triag_closed_subst,
      inv_triag_closed_subst]
    have hw := Term.weaken_subst0 w r; simp only [Term.subst0] at hw; rw [hw]
  let at_wr := .mp at_w' (.forall_ax r)
  let at_wr' := Eq.mp (congrArg (Derivable F EqX al Premises) C_inst_nf) at_wr
  -- at_wr' : (r ∸ w = 0) →ᶠ inv_triag(triag w + r) = w
  .mp h at_wr'

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
    inv_triag_triag_add adm (Term.app2 Term.add x y) x h_le
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
    inv_triag_triag_add adm (Term.app2 Term.add x y) x h_le
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

/-- Helper: `add(pd(add(n,n)), isOdd(pd(add(n,n)))) =₀ add(n,n)`. By induction on n. -/
private def pd_double_add_isOdd_pd_double (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.add
          (.app Term.pd (Term.app2 Term.add n n))
          (.app Term.isOdd (.app Term.pd (Term.app2 Term.add n n))))
        (Term.app2 Term.add n n)) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0
      (Term.app2 Term.add
        (.app Term.pd (Term.app2 Term.add (.var .vz) (.var .vz)))
        (.app Term.isOdd (.app Term.pd (Term.app2 Term.add (.var .vz) (.var .vz)))))
      (Term.app2 Term.add (.var .vz) (.var .vz))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0
        (Term.app2 Term.add
          (.app Term.pd (Term.app2 Term.add Term.zero Term.zero))
          (.app Term.isOdd (.app Term.pd (Term.app2 Term.add Term.zero Term.zero))))
        (Term.app2 Term.add Term.zero Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, pd_closed_subst, isOdd_closed_subst]
  have base_proof : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.add
          (.app Term.pd (Term.app2 Term.add Term.zero Term.zero))
          (.app Term.isOdd (.app Term.pd (Term.app2 Term.add Term.zero Term.zero))))
        (Term.app2 Term.add Term.zero Term.zero)) :=
    let zz := Term.app2 Term.add Term.zero Term.zero
    let h_zz := add_zero_r adm Term.zero
    let h_pd_zz := .mp (.mp pd_zero (.mp (pd_congr h_zz) and_intro)) .trans0
    let h_isOdd_pd_zz := .mp (.mp (isOdd_zero (adm := adm))
      (.mp (isOdd_congr h_pd_zz) and_intro)) .trans0
    let h1 := .mp (.mp (add_congr_r Term.zero h_isOdd_pd_zz)
      (.mp (add_congr_l h_pd_zz (.app Term.isOdd (.app Term.pd zz))) and_intro)) .trans0
    let h2 := add_zero_r adm Term.zero
    .mp (.mp (.mp h_zz .sym0) (.mp (.mp (.mp h2 (.mp h1 and_intro)) .trans0) and_intro)) .trans0
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸ base_proof
  let k : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let kk := Term.app2 Term.add k k
  let SkSk := Term.app2 Term.add (.app .succ k) (.app .succ k)
  have step_nf : Formula.substVar0 A (.app .succ k) =
      Formula.eq0
        (Term.app2 Term.add (.app Term.pd SkSk) (.app Term.isOdd (.app Term.pd SkSk)))
        SkSk := by
    simp only [A, SkSk, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, add_closed_subst, pd_closed_subst, isOdd_closed_subst]
  have step_proof : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.add (.app Term.pd SkSk) (.app Term.isOdd (.app Term.pd SkSk))) SkSk) :=
    let h_add1 := add_succ_l adm k (.app .succ k)
    let h_add2 := add_succ adm k k
    let h_SkSk_eq : Derivable F EqX al Premises
        (Formula.eq0 SkSk (.app .succ (.app .succ kk))) :=
      .mp (.mp (succ_congr h_add2) (.mp h_add1 and_intro)) .trans0
    let h_pd : Derivable F EqX al Premises
        (Formula.eq0 (.app Term.pd SkSk) (.app .succ kk)) :=
      .mp (.mp (pd_succ adm (.app .succ kk))
        (.mp (pd_congr h_SkSk_eq) and_intro)) .trans0
    let h_ie_skk : Derivable F EqX al Premises
        (Formula.eq0 (.app Term.isEven (.app .succ kk)) Term.zero) :=
      .mp (.mp (sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _))
        (.mp (.mp (.mp (sg_bar_congr (isEven_double adm k))
          (.mp (isEven_succ adm kk) and_intro)) .trans0) and_intro)) .trans0
    let h_isOdd_skk : Derivable F EqX al Premises
        (Formula.eq0 (.app Term.isOdd (.app .succ kk)) (.app .succ .zero)) :=
      .mp (.mp (monus_zero adm (.app .succ .zero))
        (.mp (.mp (.mp (monus_congr_r (.app .succ .zero) h_ie_skk)
          (.mp (isOdd_unfold (.app .succ kk)) and_intro)) .trans0) and_intro)) .trans0
    let h_isOdd_pd := .mp (.mp h_isOdd_skk (.mp (isOdd_congr h_pd) and_intro)) .trans0
    let h_lhs := .mp (.mp (add_congr_r (.app .succ kk) h_isOdd_pd)
      (.mp (add_congr_l h_pd (.app Term.isOdd (.app Term.pd SkSk))) and_intro)) .trans0
    let h_add_s0 : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.add (.app .succ kk) (.app .succ .zero))
          (.app .succ (.app .succ kk))) :=
      let s1 := add_succ_l adm kk (.app .succ .zero)
      let s2 := succ_congr (add_succ adm kk .zero)
      let s3 := succ_congr (succ_congr (add_zero_r adm kk))
      .mp (.mp s3 (.mp (.mp (.mp s2 (.mp s1 and_intro)) .trans0) and_intro)) .trans0
    let h_rhs := .mp (.mp (.mp h_SkSk_eq .sym0) (.mp h_add_s0 and_intro)) .trans0
    .mp (.mp h_rhs (.mp h_lhs and_intro)) .trans0
  have step : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ k)) :=
    step_nf ▸ weaken_intro step_proof
  have inst_nf : A.subst0 n =
      Formula.eq0
        (Term.app2 Term.add
          (.app Term.pd (Term.app2 Term.add n n))
          (.app Term.isOdd (.app Term.pd (Term.app2 Term.add n n))))
        (Term.app2 Term.add n n) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, pd_closed_subst, isOdd_closed_subst]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step)) (.forall_ax n)

-- ── pair congruence (both arguments) ──────────────────────────────────────

/-- pair(a, b) =₀ pair(a', b') from a =₀ a' and b =₀ b'. -/
private def pair_congr {a a' b b' : Term F Γ Ty.nat}
    (ha : Derivable F EqX al Premises (Formula.eq0 a a'))
    (hb : Derivable F EqX al Premises (Formula.eq0 b b')) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.pair a b) (Term.app2 Term.pair a' b')) :=
  have mk_nf1 (x y : Term F Γ Ty.nat) :
      (Term.app2 Term.pair x.weaken (.var .vz) : Term F (Ty.nat :: Γ) _).subst0 y =
      Term.app2 Term.pair x y := by
    simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, pair_closed_subst,
      weaken_subst0_eta]
  have mk_nf2 (x y : Term F Γ Ty.nat) :
      (Term.app2 Term.pair (.var .vz) x.weaken : Term F (Ty.nat :: Γ) _).subst0 y =
      Term.app2 Term.pair y x := by
    simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, pair_closed_subst,
      weaken_subst0_eta]
  let s1 := qfer_no_premise_nat_nf hb
    (r := Term.app2 Term.pair a.weaken (.var .vz))
    (mk_nf1 a b) (mk_nf1 a b')
  let s2 := qfer_no_premise_nat_nf ha
    (r := Term.app2 Term.pair (.var .vz) b'.weaken)
    (mk_nf2 b' a) (mk_nf2 b' a')
  .mp (.mp s2 (.mp s1 and_intro)) .trans0


/-- The step function body of div2's state-pair recursion (context-polymorphic).
    step(r, _) = pair(fst(r) + snd(r), sg_bar(snd(r))). -/
private def div2_step_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
  Term.app2 Term.pair
    (Term.app2 Term.add (.app Term.fst_pair (.var (.vs .vz))) (.app Term.snd_pair (.var (.vs .vz))))
    (.app Term.sg_bar (.app Term.snd_pair (.var (.vs .vz))))

/-- The step function of div2's state-pair recursion (context-polymorphic). -/
private def div2_step : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam (div2_step_body (F := F) (Γ := Γ)))

@[simp] private theorem div2_step_closed_subst :
    (div2_step : Term F Γ _).subst σ = div2_step := by rfl

@[simp] private theorem div2_step_closed_rename :
    (div2_step : Term F Γ _).rename r = div2_step := by rfl

/-- div2(n + n) =₀ n for all n.

    Uses the pair invariant: rec(pair(0,1), step, n+n) = pair(n, 1) where
    step(r, _) = pair(fst(r)+snd(r), sg_bar(snd(r))).
    Base: rec(..., 0) = pair(0, 1).
    Step: two rec_succ unfoldings, using IH to simplify. -/
private def div2_double (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.div2 (Term.app2 Term.add n n)) n) :=
  let k : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let kk := Term.app2 Term.add k k
  let base_val := Term.app2 Term.pair (.zero : Term F _ _) (.app .succ .zero)
  let step_fn := div2_step (F := F) (Γ := Ty.nat :: Γ)
  let rec_m := Term.app3 (.prec Ty.nat) base_val step_fn kk
  -- A(k) := rec(base, step, k+k) =₀ pair(k, S0)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 rec_m (Term.app2 Term.pair k (.app .succ .zero))
  -- ── Base: A[0] ──
  have base_nf : A.subst0 Term.zero =
      Formula.eq0
        (Term.app3 (.prec Ty.nat)
          (Term.app2 Term.pair .zero (.app .succ .zero))
          div2_step
          (Term.app2 Term.add Term.zero Term.zero))
        (Term.app2 Term.pair Term.zero (.app .succ .zero)) := by
    simp only [A, rec_m, base_val, step_fn, kk, k,
      Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2, Term.app3,
      add_closed_subst, pair_closed_subst, div2_step_closed_subst]
  have base_pf : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    base_nf ▸
    let h_add00 := add_zero_r adm (Term.zero : Term F Γ _)
    let h_rec_cong : Derivable F EqX al Premises
        (Formula.eq0
          (Term.app3 (.prec Ty.nat)
            (Term.app2 Term.pair (.zero : Term F Γ _) (.app .succ .zero))
            (div2_step : Term F Γ _)
            (Term.app2 Term.add Term.zero Term.zero))
          (Term.app3 (.prec Ty.nat)
            (Term.app2 Term.pair (.zero : Term F Γ _) (.app .succ .zero))
            (div2_step : Term F Γ _)
            Term.zero)) :=
      qfer_no_premise_nat_nf h_add00
        (r := Term.app3 (.prec Ty.nat)
          (Term.app2 Term.pair (.zero : Term F (Ty.nat :: Γ) _) (.app .succ .zero))
          (div2_step : Term F (Ty.nat :: Γ) _)
          (.var .vz))
        (by simp only [Term.subst0, Term.app3, Term.app2, Term.subst, Term.subst0_map,
              add_closed_subst, div2_step_closed_subst, pair_closed_subst])
        (by simp only [Term.subst0, Term.app3, Term.app2, Term.subst, Term.subst0_map,
              div2_step_closed_subst, pair_closed_subst])
    .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h_rec_cong and_intro)) .trans0
  -- ── Step: A(k) ��� A(Sk) ──
  have step_nf_eq : Formula.substVar0 A (.app .succ k) =
      Formula.eq0
        (Term.app3 (.prec Ty.nat) base_val step_fn (Term.app2 Term.add (.app .succ k) (.app .succ k)))
        (Term.app2 Term.pair (.app .succ k) (.app .succ .zero)) := by
    simp only [A, rec_m, base_val, step_fn, kk, k,
      Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2, Term.app3,
      add_closed_subst, pair_closed_subst, div2_step_closed_subst]
  let Sm := Term.app .succ kk
  let rec_Sm := Term.app3 (.prec Ty.nat) base_val step_fn Sm
  let rec_SSm := Term.app3 (.prec Ty.nat) base_val step_fn (.app .succ Sm)
  let step_body_inner := div2_step_body (F := F) (Γ := Ty.nat :: Γ)
  have step_body_fn : Derivable F EqX al Premises
      (A →ᶠ Formula.substVar0 A (.app .succ k)) :=
    step_nf_eq ▸
    -- add(Sk, Sk) =₀ SS(kk)
    let h_add_chain :=
      let h1 := add_succ_l adm k (.app .succ k)
      let h2 := succ_congr (add_succ adm k k)
      .mp (.mp h2 (.mp h1 and_intro)) .trans0
    -- rec(_, _, add(Sk,Sk)) =₀ rec(_, _, SS(kk)) by congruence
    let h_rec_chain := qfer_no_premise_nat_nf h_add_chain
      (r := Term.app3 (.prec Ty.nat)
        (Term.app2 Term.pair (.zero : Term F (Ty.nat :: Ty.nat :: Γ) _) (.app .succ .zero))
        (div2_step : Term F (Ty.nat :: Ty.nat :: Γ) _)
        (.var .vz))
      (by simp only [Term.subst0, Term.app3, Term.app2,
            Term.subst, Term.subst0_map, pair_closed_subst, add_closed_subst,
            div2_step_closed_subst]; rfl)
      (by simp only [Term.subst0, Term.app3, Term.app2,
            Term.subst, Term.subst0_map, pair_closed_subst,
            div2_step_closed_subst]; rfl)
    -- rec_succ unfoldings
    let h_rs2 : Derivable F EqX al Premises (Formula.eq0 rec_SSm
        (Term.app2 step_fn rec_Sm Sm)) := .rec_succ (ρ := Ty.nat)
    let h_rs1 : Derivable F EqX al Premises (Formula.eq0 rec_Sm
        (Term.app2 step_fn rec_m kk)) := .rec_succ (ρ := Ty.nat)
    -- step(rec_m, kk) unfold: pair(fst(rec_m)+snd(rec_m), sg_bar(snd(rec_m)))
    have step_nf1 : (step_body_inner.subst0 (kk.weaken)).subst0 rec_m =
        Term.app2 Term.pair
          (Term.app2 Term.add (.app Term.fst_pair rec_m) (.app Term.snd_pair rec_m))
          (.app Term.sg_bar (.app Term.snd_pair rec_m)) := by
      simp only [step_body_inner, div2_step_body, rec_m, kk, k, base_val, step_fn,
        Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.app3,
        pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
        snd_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst,
        Term.weaken, Term.rename]
    let h_step1_unfold := lam2_correct_nf adm step_body_inner rec_m kk step_nf1
    -- IH → fst(rec_m) =₀ k
    let h_fst_ih : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (.app Term.fst_pair rec_m) k) :=
      .syllogism
        (qfer_nat_nf (by rfl) (by rfl) I_comb
          (r := .app Term.fst_pair (.var .vz))
          (by simp only [rec_m, kk, k, base_val, step_fn, div2_step,
                Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
                fst_pair_closed_subst, pair_closed_subst, add_closed_subst,
                snd_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst])
          (by simp only [Term.subst0, Term.subst, Term.subst0_map,
                fst_pair_closed_subst, pair_closed_subst]))
        (.syllogism (pair_h I_comb (weaken_intro (fst_pair_pair adm k (.app .succ .zero)))) .trans0)
    -- IH → snd(rec_m) =₀ S0
    let h_snd_ih : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (.app Term.snd_pair rec_m) (.app .succ .zero)) :=
      .syllogism
        (qfer_nat_nf (by rfl) (by rfl) I_comb
          (r := .app Term.snd_pair (.var .vz))
          (by simp only [rec_m, kk, k, base_val, step_fn, div2_step,
                Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
                snd_pair_closed_subst, pair_closed_subst, add_closed_subst,
                fst_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst])
          (by simp only [Term.subst0, Term.subst, Term.subst0_map,
                snd_pair_closed_subst, pair_closed_subst]))
        (.syllogism (pair_h I_comb (weaken_intro (snd_pair_pair adm k (.app .succ .zero)))) .trans0)
    -- k + S0 =₀ Sk
    let h_add_kS0 :=
      let h1 := add_succ adm k (.zero : Term F (Ty.nat :: Γ) _)
      let h2 := succ_congr (add_zero_r adm k)
      .mp (.mp h2 (.mp h1 and_intro)) .trans0
    -- IH → fst(rec_m)+snd(rec_m) =₀ Sk
    let h_add_ih : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (Term.app2 Term.add (.app Term.fst_pair rec_m) (.app Term.snd_pair rec_m))
          (.app .succ k)) :=
      let cong_l := qfer_nat_nf (by rfl) (by rfl) h_fst_ih
        (r := Term.app2 Term.add (.var .vz) ((Term.app Term.snd_pair rec_m).weaken))
        (by simp only [rec_m, kk, k, base_val, step_fn, div2_step,
              Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.app3,
              add_closed_subst, fst_pair_closed_subst, snd_pair_closed_subst,
              pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst,
              Term.weaken, Term.rename]; rfl)
        (by simp only [rec_m, kk, k, base_val, step_fn, div2_step,
              Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.app3,
              add_closed_subst, snd_pair_closed_subst, pair_closed_subst,
              fst_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst,
              Term.weaken, Term.rename, Term.Renaming.shift]; rfl)
      let cong_r := qfer_nat_nf (by rfl) (by rfl) h_snd_ih
        (r := Term.app2 Term.add k.weaken (.var .vz))
        (by simp only [k, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
              add_closed_subst, snd_pair_closed_subst, Term.weaken, Term.rename,
              Term.Renaming.shift]; rfl)
        (by simp only [k, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
              add_closed_subst]; rfl)
      .syllogism (pair_h cong_l cong_r)
        (.syllogism .trans0 (.syllogism (pair_h I_comb (weaken_intro h_add_kS0)) .trans0))
    -- IH → sg_bar(snd(rec_m)) =₀ 0
    let h_sgb_ih : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (.app Term.sg_bar (.app Term.snd_pair rec_m)) Term.zero) :=
      .syllogism
        (qfer_nat_nf (by rfl) (by rfl) h_snd_ih
          (r := .app Term.sg_bar (.var .vz))
          (by simp only [rec_m, kk, k, base_val, step_fn, div2_step,
                Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
                sg_bar_closed_subst, snd_pair_closed_subst, pair_closed_subst,
                add_closed_subst, fst_pair_closed_subst, div2_step_closed_subst])
          (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_bar_closed_subst]))
        (.syllogism (pair_h I_comb (weaken_intro (sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)))) .trans0)
    -- IH → pair(fst+snd, sg_bar(snd)) =₀ pair(Sk, 0)
    let h_pair1 : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0
          (Term.app2 Term.pair
            (Term.app2 Term.add (.app Term.fst_pair rec_m) (.app Term.snd_pair rec_m))
            (.app Term.sg_bar (.app Term.snd_pair rec_m)))
          (Term.app2 Term.pair (.app .succ k) Term.zero)) :=
      let cong_l : Derivable F EqX al Premises
          (A →ᶠ Formula.eq0
            (Term.app2 Term.pair
              (Term.app2 Term.add (.app Term.fst_pair rec_m) (.app Term.snd_pair rec_m))
              (.app Term.sg_bar (.app Term.snd_pair rec_m)))
            (Term.app2 Term.pair (.app .succ k) (.app Term.sg_bar (.app Term.snd_pair rec_m)))) :=
        qfer_nat_nf (by rfl) (by rfl) h_add_ih
          (r := Term.app2 Term.pair (.var .vz)
            ((Term.app Term.sg_bar (Term.app Term.snd_pair rec_m)).weaken))
          (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
                pair_closed_subst, weaken_subst0_eta])
          (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
                pair_closed_subst, weaken_subst0_eta])
      let cong_r : Derivable F EqX al Premises
          (A →ᶠ Formula.eq0
            (Term.app2 Term.pair (.app .succ k) (.app Term.sg_bar (.app Term.snd_pair rec_m)))
            (Term.app2 Term.pair (.app .succ k) Term.zero)) :=
        qfer_nat_nf (by rfl) (by rfl) h_sgb_ih
          (r := Term.app2 Term.pair ((Term.app .succ k).weaken) (.var .vz))
          (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
                pair_closed_subst, weaken_subst0_eta])
          (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
                pair_closed_subst, weaken_subst0_eta])
      .syllogism (pair_h cong_l cong_r) .trans0
    -- IH → step(rec_m, kk) =₀ pair(Sk, 0)
    let h_step1_val : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (Term.app2 step_fn rec_m kk)
          (Term.app2 Term.pair (.app .succ k) Term.zero)) :=
      .syllogism (pair_h (weaken_intro h_step1_unfold) h_pair1) .trans0
    -- IH → rec_Sm =₀ pair(Sk, 0)
    let h_rec_Sm_val : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 rec_Sm (Term.app2 Term.pair (.app .succ k) Term.zero)) :=
      .syllogism (pair_h (weaken_intro h_rs1) h_step1_val) .trans0
    -- step(pair(Sk, 0), Sm) unfolding
    let Sk := Term.app .succ k
    let pair_Sk_0 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.pair Sk Term.zero
    have step_nf2 : (step_body_inner.subst0 (Sm.weaken)).subst0 pair_Sk_0 =
        Term.app2 Term.pair
          (Term.app2 Term.add (.app Term.fst_pair pair_Sk_0) (.app Term.snd_pair pair_Sk_0))
          (.app Term.sg_bar (.app Term.snd_pair pair_Sk_0)) := by
      simp only [step_body_inner, div2_step_body, pair_Sk_0, Sk, Sm, kk, k,
        Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
        snd_pair_closed_subst, sg_bar_closed_subst, Term.weaken, Term.rename]
    let h_step2_unfold := lam2_correct_nf adm step_body_inner pair_Sk_0 Sm step_nf2
    -- Simplify: fst(pair(Sk, 0)) =₀ Sk, snd(pair(Sk, 0)) =₀ 0
    let h_fst2 := fst_pair_pair adm Sk Term.zero
    let h_snd2 := snd_pair_pair adm Sk Term.zero
    let h_add2 := .mp (.mp (add_zero_r adm Sk)
        (.mp (.mp (.mp (add_congr_r Sk h_snd2)
            (.mp (add_congr_l h_fst2 (.app Term.snd_pair pair_Sk_0)) and_intro)) .trans0) and_intro)) .trans0
    let h_sgb2 := .mp (.mp (sg_bar_zero (Premises := Premises))
      (.mp (sg_bar_congr h_snd2) and_intro)) .trans0
    -- step(pair(Sk, 0), Sm) =₀ pair(Sk, S0)
    let h_step2_val : Derivable F EqX al Premises (Formula.eq0
        (Term.app2 step_fn pair_Sk_0 Sm)
        (Term.app2 Term.pair Sk (.app .succ .zero))) :=
      .mp (.mp (pair_congr h_add2 h_sgb2) (.mp h_step2_unfold and_intro)) .trans0
    -- IH → step(rec_Sm, Sm) =₀ step(pair(Sk, 0), Sm) via congruence
    let h_step2_cong : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (Term.app2 step_fn rec_Sm Sm) (Term.app2 step_fn pair_Sk_0 Sm)) :=
      qfer_nat_nf (by rfl) (by rfl) h_rec_Sm_val
        (r := Term.app2 (div2_step : Term F (Ty.nat :: Ty.nat :: Γ) _) (.var .vz) Sm.weaken)
        (by simp only [step_fn, div2_step, rec_Sm, Sm, kk, k, base_val, pair_Sk_0,
              Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.app3,
              pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
              snd_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst,
              Term.weaken, Term.rename, Term.Renaming.shift]; rfl)
        (by simp only [step_fn, div2_step, pair_Sk_0, Sm, kk, k,
              Term.subst0, Term.subst, Term.subst0_map, Term.app2,
              pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
              snd_pair_closed_subst, sg_bar_closed_subst, div2_step_closed_subst,
              Term.weaken, Term.rename, Term.Renaming.shift]; rfl)
    -- IH → step(rec_Sm, Sm) =₀ pair(Sk, S0)
    let h_step2_final : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 (Term.app2 step_fn rec_Sm Sm) (Term.app2 Term.pair Sk (.app .succ .zero))) :=
      .syllogism (pair_h h_step2_cong (weaken_intro h_step2_val)) .trans0
    -- IH → rec_SSm =₀ pair(Sk, S0) via rec_succ chain
    let h_rec_SSm : Derivable F EqX al Premises
        (A →ᶠ Formula.eq0 rec_SSm (Term.app2 Term.pair Sk (.app .succ .zero))) :=
      .syllogism (pair_h (weaken_intro h_rs2) h_step2_final) .trans0
    -- IH → rec(_, _, add(Sk, Sk)) =₀ pair(Sk, S0)
    .syllogism (pair_h (weaken_intro h_rec_chain) h_rec_SSm) .trans0
  -- ── Instantiate ──
  have inst_nf : A.subst0 n =
      Formula.eq0
        (Term.app3 (.prec Ty.nat)
          (Term.app2 Term.pair .zero (.app .succ .zero))
          div2_step
          (Term.app2 Term.add n n))
        (Term.app2 Term.pair n (.app .succ .zero)) := by
    simp only [A, rec_m, base_val, step_fn, kk, k,
      Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2, Term.app3,
      add_closed_subst, pair_closed_subst, div2_step_closed_subst]
  let h_all := Derivable.induction base_pf (univ_gen step_body_fn)
  let h_pair : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app3 (.prec Ty.nat)
          (Term.app2 Term.pair .zero (.app .succ .zero))
          div2_step
          (Term.app2 Term.add n n))
        (Term.app2 Term.pair n (.app .succ .zero))) :=
    inst_nf ▸ Derivable.mp h_all (.forall_ax n)
  -- div2(n+n) = fst(rec(base, step, n+n))
  let div2_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.fst_pair (Term.app3 (.prec Ty.nat)
      (Term.app2 Term.pair .zero (.app .succ .zero))
      div2_step
      (.var .vz))
  let h_div2_unfold := lam_correct_nf div2_body (Term.app2 Term.add n n) (by rfl)
  let h_fst_final := fst_pair_pair adm n (.app .succ .zero)
  let h_fst_cong := fst_pair_congr h_pair
  let c1 := .mp (.mp h_fst_cong (.mp h_div2_unfold and_intro)) .trans0
  .mp (.mp h_fst_final (.mp c1 and_intro)) .trans0
-- ── pair congruence (both arguments) ──────────────────────────────────────

/-- `rat_num(rat_encode(s, n, d)) =₀ n` when `isEven(s) ∈ {S0, 0}`.

    Unfolds: `rat_encode(s,n,d) = pair(2n ∸ isEven(s), d)`,
    so `rat_num(rat_encode(s,n,d)) = div2(fst_pair(pair(2n ∸ isEven(s), d))
        + isOdd(fst_pair(pair(2n ∸ isEven(s), d))))`.
    By `fst_pair_pair` this simplifies to `div2((2n ∸ isEven(s)) + isOdd(2n ∸ isEven(s)))`.
    Case `isEven(s) = 0`: `2n ∸ 0 = 2n`, `isOdd(2n) = 0`, `div2(2n + 0) = div2(2n) = n`.
    Case `isEven(s) = S0`: `2n ∸ S0 = pd(2n)`, use `pd_double_add_isOdd_pd_double`. -/
private def rat_num_rat_encode (s n d : Term F Γ Ty.nat)
    (hs : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.isEven s) (.app .succ .zero) ∨ᶠ
       Formula.eq0 (.app Term.isEven s) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_num (Term.app3 Term.rat_encode s n d)) n) :=
  -- Abbreviations
  let ie_s := Term.app Term.isEven s
  let nn := Term.app2 Term.add n n
  let two_n := Term.app2 Term.mul (Term.ofNat 2) n
  let encoded_pair : Term F Γ Ty.nat :=
    Term.app2 Term.pair (Term.app2 Term.monus two_n ie_s) d
  -- Step 1: rat_encode(s,n,d) =₀ pair(2n ∸ isEven(s), d)
  let body_e : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)
  have body_e_nf : ((body_e.subst0 (d.weaken.weaken)).subst0 (n.weaken)).subst0 s =
      encoded_pair := by
    simp only [body_e, encoded_pair, two_n, ie_s, Term.subst0, Term.subst, Term.subst0_map,
      Term.app2, Term.ofNat, pair_closed_subst, mul_closed_subst, monus_closed_subst,
      isEven_closed_subst, weaken_subst0_eta]
  let h_encode := lam3_correct_nf adm body_e s n d body_e_nf
  -- Step 2: rat_num(rat_encode(s,n,d)) =₀ rat_num(encoded_pair)
  let h_rn_cong := rat_num_congr h_encode
  -- Step 3: rat_num(encoded_pair) = div2(fst_pair(ep) + isOdd(fst_pair(ep)))
  let fp_ep := Term.app Term.fst_pair encoded_pair
  let rat_num_unfolded :=
    Term.app Term.div2 (Term.app2 Term.add fp_ep (.app Term.isOdd fp_ep))
  let rat_num_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.div2
      (Term.app2 Term.add
        (.app Term.fst_pair (.var .vz))
        (.app Term.isOdd (.app Term.fst_pair (.var .vz))))
  have rn_body_nf : rat_num_body.subst0 encoded_pair = rat_num_unfolded := by
    simp only [rat_num_body, rat_num_unfolded, fp_ep, encoded_pair, Term.subst0, Term.subst,
      Term.subst0_map, Term.app2, div2_closed_subst, add_closed_subst, fst_pair_closed_subst,
      isOdd_closed_subst, pair_closed_subst, monus_closed_subst, mul_closed_subst,
      isEven_closed_subst]
  let h_rn_unfold := lam_correct_nf rat_num_body encoded_pair rn_body_nf
  -- Step 4: fst_pair(encoded_pair) =₀ 2n ∸ isEven(s)
  let f := Term.app2 Term.monus two_n ie_s
  let h_fst := fst_pair_pair adm f d
  -- Step 5: rat_num_unfolded =₀ div2(f + isOdd(f)) by congruence on fst_pair result
  -- First: fst_pair(ep) + isOdd(fst_pair(ep)) =₀ f + isOdd(f)
  let h_add_cong := .mp (.mp (add_congr_r f (isOdd_congr h_fst))
    (.mp (add_congr_l h_fst (.app Term.isOdd fp_ep)) and_intro)) .trans0
  -- Chain: rat_num(rat_encode(s,n,d)) =₀ div2(f + isOdd(f))
  let c1 := .mp (.mp h_rn_unfold (.mp h_rn_cong and_intro)) .trans0
  let chain1 := .mp (.mp (div2_congr h_add_cong) (.mp c1 and_intro)) .trans0
  -- Step 6: 2n =₀ n+n
  let h_two_n_eq_nn : Derivable F EqX al Premises (Formula.eq0 two_n nn) :=
    let h_ms := mul_succ_l adm (.app .succ .zero) n
    let h_m1 := .mp (.mp (mul_one_r adm n)
      (.mp (mul_comm adm (.app .succ .zero) n) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 n) (.mp h_ms and_intro)) .trans0
  -- f =₀ f'  where f' = (n+n) ∸ isEven(s)
  let f' := Term.app2 Term.monus nn ie_s
  let h_f_eq := monus_congr_l h_two_n_eq_nn ie_s
  -- div2(f + isOdd(f)) =₀ div2(f' + isOdd(f'))
  let h_add_f := .mp (.mp (add_congr_r f' (isOdd_congr h_f_eq))
    (.mp (add_congr_l h_f_eq (.app Term.isOdd f)) and_intro)) .trans0
  let chain2 := .mp (.mp (div2_congr h_add_f) (.mp chain1 and_intro)) .trans0
  -- chain2 : rat_num(rat_encode(s,n,d)) =₀ div2(f' + isOdd(f'))
  -- Conditional monus: isEven(s)=e → f'=₀(n+n)∸e
  let mk_monus_cond (e : Term F Γ Ty.nat) :
      Derivable F EqX al Premises
        (Formula.eq0 ie_s e →ᶠ Formula.eq0 f' (Term.app2 Term.monus nn e)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.monus nn.weaken (.var .vz))
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst,
            weaken_subst0_eta]; rfl)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst,
            weaken_subst0_eta])
  -- Conditional div2: H → f'=₀t gives H → div2(f'+isOdd(f'))=₀div2(t+isOdd(t))
  let mk_div2_cond (e t : Term F Γ Ty.nat)
      (h_f'_t : Derivable F EqX al Premises (Formula.eq0 ie_s e →ᶠ Formula.eq0 f' t)) :
      Derivable F EqX al Premises
        (Formula.eq0 ie_s e →ᶠ
         Formula.eq0
           (.app Term.div2 (Term.app2 Term.add f' (.app Term.isOdd f')))
           (.app Term.div2 (Term.app2 Term.add t (.app Term.isOdd t)))) :=
    qfer_nat_nf (by rfl) (by rfl) h_f'_t
      (r := .app Term.div2 (Term.app2 Term.add (.var .vz) (.app Term.isOdd (.var .vz))))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, div2_closed_subst,
            add_closed_subst, isOdd_closed_subst, monus_closed_subst]; rfl)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, div2_closed_subst,
            add_closed_subst, isOdd_closed_subst, monus_closed_subst, pd_closed_subst]; rfl)
  -- ── Case isEven(s) = 0 ──
  let case_zero : Derivable F EqX al Premises
      (Formula.eq0 ie_s Term.zero →ᶠ
       Formula.eq0 (.app Term.rat_num (Term.app3 Term.rat_encode s n d)) n) :=
    let h_f'_nn := .syllogism (mk_monus_cond Term.zero)
      (.syllogism (pair_h I_comb (weaken_intro (monus_zero adm nn))) .trans0)
    let h_d := mk_div2_cond Term.zero nn h_f'_nn
    let h_tail :=
      let h1 := div2_congr (add_congr_r nn (isOdd_double adm n))
      let h2 := div2_congr (add_zero_r adm nn)
      let h3 := div2_double adm n
      .mp (.mp h3 (.mp (.mp (.mp h2 (.mp h1 and_intro)) .trans0) and_intro)) .trans0
    .syllogism (pair_h (weaken_intro chain2)
      (.syllogism h_d (.syllogism (pair_h I_comb (weaken_intro h_tail)) .trans0))) .trans0
  -- ── Case isEven(s) = S0 ──
  let case_one : Derivable F EqX al Premises
      (Formula.eq0 ie_s (.app .succ .zero) →ᶠ
       Formula.eq0 (.app Term.rat_num (Term.app3 Term.rat_encode s n d)) n) :=
    let h_monus_s0 : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus nn (.app .succ .zero)) (.app Term.pd nn)) :=
      .mp (.mp (pd_congr (monus_zero adm nn))
        (.mp (monus_succ adm nn .zero) and_intro)) .trans0
    let h_f'_pd := .syllogism (mk_monus_cond (.app .succ .zero))
      (.syllogism (pair_h I_comb (weaken_intro h_monus_s0)) .trans0)
    let h_d := mk_div2_cond (.app .succ .zero) (.app Term.pd nn) h_f'_pd
    let h_tail :=
      .mp (.mp (div2_double adm n)
        (.mp (div2_congr (pd_double_add_isOdd_pd_double adm n)) and_intro)) .trans0
    .syllogism (pair_h (weaken_intro chain2)
      (.syllogism h_d (.syllogism (pair_h I_comb (weaken_intro h_tail)) .trans0))) .trans0
  .mp hs (or_elim_rule case_one case_zero)

-- ── rat_sign roundtrip ───────────────────────────────────────────────────

/-- The common chain: rat_sign(rat_encode(s,n,d)) =₀ isEven(2n ∸ isEven(s)). -/
private def rat_sign_rat_encode_unfold (s n d : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode s n d))
        (.app Term.isEven (Term.app2 Term.monus
          (Term.app2 Term.mul (Term.ofNat 2) n) (.app Term.isEven s)))) :=
  let two_n := Term.app2 Term.mul (Term.ofNat 2) n
  let ie_s := Term.app Term.isEven s
  let encoded_pair : Term F Γ Ty.nat :=
    Term.app2 Term.pair (Term.app2 Term.monus two_n ie_s) d
  let body_e : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)
  have body_e_nf : ((body_e.subst0 (d.weaken.weaken)).subst0 (n.weaken)).subst0 s =
      encoded_pair := by
    simp only [body_e, encoded_pair, two_n, ie_s, Term.subst0, Term.subst, Term.subst0_map,
      Term.app2, Term.ofNat, pair_closed_subst, mul_closed_subst, monus_closed_subst,
      isEven_closed_subst, weaken_subst0_eta]
  let h_encode := lam3_correct_nf adm body_e s n d body_e_nf
  let h_rs_cong := rat_sign_congr h_encode
  let rat_sign_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.isEven (.app Term.fst_pair (.var .vz))
  let h_unfold := lam_correct_nf rat_sign_body encoded_pair (by rfl)
  let h_fst := fst_pair_pair adm (Term.app2 Term.monus two_n ie_s) d
  let h_ie := isEven_congr h_fst
  let c := .mp (.mp h_unfold (.mp h_rs_cong and_intro)) .trans0
  .mp (.mp h_ie (.mp c and_intro)) .trans0

/-- rat_sign(rat_encode(s,n,d)) =₀ S0 when isEven(s) =₀ 0 (s is odd, positive sign). -/
private def rat_sign_rat_encode_pos (s n d : Term F Γ Ty.nat)
    (hs : Derivable F EqX al Premises (Formula.eq0 (.app Term.isEven s) Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode s n d))
        (.app .succ .zero)) :=
  let two_n := Term.app2 Term.mul (Term.ofNat 2) n
  let h1 := rat_sign_rat_encode_unfold adm s n d
  let h_monus := monus_congr_r two_n hs
  let h_monus0 := .mp (.mp (monus_zero adm two_n) (.mp h_monus and_intro)) .trans0
  let h_ie := isEven_congr h_monus0
  let h_two_n_eq_nn := let h_ms := mul_succ_l adm (.app .succ .zero) n
    let h_m1 := .mp (.mp (mul_one_r adm n)
      (.mp (mul_comm adm (.app .succ .zero) n) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 n) (.mp h_ms and_intro)) .trans0
  let h_ie2 := isEven_congr h_two_n_eq_nn
  let h_double := isEven_double adm n
  let c1 := .mp (.mp h_ie2 (.mp h_ie and_intro)) .trans0
  let c2 := .mp (.mp h_double (.mp c1 and_intro)) .trans0
  .mp (.mp c2 (.mp h1 and_intro)) .trans0

/-- rat_sign(rat_encode(s,n,d)) =₀ 0 when isEven(s) =₀ S0 and n ≠ 0 (negative sign with
    nonzero numerator). -/
private def rat_sign_rat_encode_neg (s n d : Term F Γ Ty.nat)
    (hs : Derivable F EqX al Premises (Formula.eq0 (.app Term.isEven s) (.app .succ .zero)))
    (hn : Derivable F EqX al Premises (¬ᶠFormula.eq0 n Term.zero)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode s n d)) Term.zero) :=
  let two_n := Term.app2 Term.mul (Term.ofNat 2) n
  let nn := Term.app2 Term.add n n
  let h1 := rat_sign_rat_encode_unfold adm s n d
  let h_monus := monus_congr_r two_n hs
  let h_two_n_eq_nn := let h_ms := mul_succ_l adm (.app .succ .zero) n
    let h_m1 := .mp (.mp (mul_one_r adm n)
      (.mp (mul_comm adm (.app .succ .zero) n) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 n) (.mp h_ms and_intro)) .trans0
  let h_monus_s0 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus two_n (.app .succ .zero))
        (.app Term.pd nn)) :=
    let hm1 := monus_congr_l h_two_n_eq_nn (.app .succ .zero)
    let hm2 := monus_succ adm nn .zero
    let hm3 := pd_congr (monus_zero adm nn)
    .mp (.mp hm3 (.mp (.mp (.mp hm2 (.mp hm1 and_intro)) .trans0) and_intro)) .trans0
  let h_tgt := .mp (.mp h_monus_s0 (.mp h_monus and_intro)) .trans0
  let h_ie_tgt := isEven_congr h_tgt
  let h_ie_chain := .mp (.mp h_ie_tgt (.mp h1 and_intro)) .trans0
  -- Now need: isEven(pd(n+n)) =₀ 0.
  -- From n ≠ 0: n = S(pd(n)), so n+n = S(pd n) + S(pd n) which is > 0.
  -- n+n ≠ 0 and isEven(n+n) = S0, so by isEven_succ: isEven(S(pd(n+n))) = sg_bar(isEven(pd(n+n)))
  -- We have n+n = S(pd(n+n)), so isEven(n+n) = isEven(S(pd(n+n))) = sg_bar(isEven(pd(n+n)))
  -- Since isEven(n+n) = S0, sg_bar(isEven(pd(n+n))) = S0, so isEven(pd(n+n)) = 0.
  -- Proof: n≠0 → n+n≠0 → n+n=S(pd(n+n)) → isEven(n+n)=isEven(S(pd(nn)))=sg_bar(isEven(pd(nn)))
  --        isEven(nn)=S0 → sg_bar(isEven(pd(nn)))=S0 → isEven(pd(nn))=0
  let h_nn_ne : Derivable F EqX al Premises (¬ᶠFormula.eq0 nn Term.zero) :=
    -- add_eq_zero_iff forward: nn=0 → n=0 ∧ n=0; then and_weak: n=0 ∧ n=0 → n=0
    let h_fwd := .mp (add_eq_zero_iff adm n n) .and_weak
    -- nn=0 → n=0 (compose forward with and_weak)
    let h_nn_imp_n := .syllogism h_fwd .and_weak
    -- ¬(n=0) → ¬(nn=0) (contrapositive)
    .syllogism h_nn_imp_n hn
  let h_nn_eq_succ : Derivable F EqX al Premises
      (Formula.eq0 nn (.app .succ (.app Term.pd nn))) :=
    .mp h_nn_ne (ne_zero_eq_succ_pd adm nn)
  let h_ie_nn_eq := isEven_congr h_nn_eq_succ
  let h_ie_succ := isEven_succ adm (.app Term.pd nn)
  -- isEven(nn) =₀ sg_bar(isEven(pd(nn)))
  let h_ie_nn_sgb := .mp (.mp h_ie_succ (.mp h_ie_nn_eq and_intro)) .trans0
  -- sg_bar(isEven(pd(nn))) =₀ isEven(nn)
  let h_sgb_to_nn := Derivable.mp h_ie_nn_sgb .sym0
  let h_ie_double := isEven_double adm n
  -- sg_bar(isEven(pd(nn))) =₀ S0
  let h_sgb_eq := .mp (.mp h_ie_double (.mp h_sgb_to_nn and_intro)) .trans0
  -- From sg_bar(x) = S0 we need x = 0.
  -- sg_bar(isEven(pd(nn))) =₀ S0. We do a case split on isEven(pd(nn)):
  -- If isEven(pd(nn)) = S0: sg_bar(S0) =₀ 0 ≠ S0 — contradiction
  -- If isEven(pd(nn)) = 0: done
  let ie_pd_nn := Term.app Term.isEven (.app Term.pd nn)
  let h_cases := isEven_cases adm (.app Term.pd nn)
  -- Case isEven(pd(nn)) = S0: derive contradiction
  let case_s0 : Derivable F EqX al Premises
      (Formula.eq0 ie_pd_nn (.app .succ .zero) →ᶠ
       Formula.eq0 ie_pd_nn Term.zero) :=
    -- H: ie_pd_nn =₀ S0 → sg_bar(ie_pd_nn) =₀ sg_bar(S0)
    let h_sgb_cond : Derivable F EqX al Premises
        (Formula.eq0 ie_pd_nn (.app .succ .zero) →ᶠ
         Formula.eq0 (.app Term.sg_bar ie_pd_nn) (.app Term.sg_bar (.app .succ .zero))) :=
      qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := .app Term.sg_bar (.var .vz)) rfl rfl
    -- sg_bar(S0) =₀ 0
    let h_sgb_s0 := sg_bar_succ adm (.zero : Term F Γ _)
    -- H → sg_bar(ie_pd_nn) =₀ 0
    let h_cond_zero := .syllogism (pair_h h_sgb_cond (weaken_intro h_sgb_s0)) .trans0
    -- H → S0 =₀ 0 (chain h_sgb_eq sym + cond_zero)
    let h_to_bad := .syllogism (pair_h
        (weaken_intro (Derivable.mp h_sgb_eq .sym0))
        h_cond_zero) .trans0
    -- S0 =₀ 0 → ⊥ (from succ_ne_zero instantiated at 0)
    let h_sne : Derivable F EqX al Premises
        (Formula.eq0 (.app .succ .zero) Term.zero →ᶠ ⊥ᶠ) :=
      .mp .succ_ne_zero (.forall_ax .zero)
    -- H → ⊥ → ie_pd_nn =₀ 0
    .syllogism (.syllogism h_to_bad h_sne) .exfalso
  -- Case isEven(pd(nn)) = 0: trivially have the goal
  let case_z : Derivable F EqX al Premises
      (Formula.eq0 ie_pd_nn Term.zero →ᶠ Formula.eq0 ie_pd_nn Term.zero) := I_comb
  let h_ie_pd := .mp h_cases (or_elim_rule case_s0 case_z)
  -- h_ie_pd : isEven(pd(nn)) =₀ 0. Chain with h_ie_chain.
  .mp (.mp h_ie_pd (.mp h_ie_chain and_intro)) .trans0

-- ── div2(2) =₀ 1 ─────────────────────────────────────────────────────────

/-- div2(SS0) =₀ S0.  Computed via two rec_succ steps on the state machine. -/
private def div2_two :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.div2 (Term.ofNat 2)) (.app .succ .zero)) :=
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
  let step := Term.lam (Term.lam
    (Term.app2 Term.pair
      (Term.app2 Term.add
        (.app Term.fst_pair (.var (.vs .vz)))
        (.app Term.snd_pair (.var (.vs .vz))))
      (.app Term.sg_bar
        (.app Term.snd_pair (.var (.vs .vz))))))
  let base : Term F Γ Ty.nat := Term.app2 Term.pair .zero (.app .succ .zero)
  let step_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.add
        (.app Term.fst_pair (.var (.vs .vz)))
        (.app Term.snd_pair (.var (.vs .vz))))
      (.app Term.sg_bar
        (.app Term.snd_pair (.var (.vs .vz))))
  let rec1 : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) base step (.app .succ .zero)
  -- div2(SS0) =₀ fst_pair(rec(base, step, SS0))
  let h_unfold := lam_correct_nf div2_body (Term.ofNat 2) (by rfl)
  -- rec(base, step, SS0) =₀ step(rec1, S0)
  let h_rec2 : Derivable F EqX al Premises (Formula.eq0
      (Term.app3 (.prec Ty.nat) base step (Term.ofNat 2))
      (Term.app2 step rec1 (.app .succ .zero))) := .rec_succ (ρ := Ty.nat)
  -- step(rec1, S0) =₀ pair(add(fst_pair(rec1), snd_pair(rec1)), sg_bar(snd_pair(rec1)))
  have step_nf2 : (step_body.subst0 ((.app .succ .zero : Term F Γ _).weaken)).subst0 rec1 =
      Term.app2 Term.pair
        (Term.app2 Term.add (.app Term.fst_pair rec1) (.app Term.snd_pair rec1))
        (.app Term.sg_bar (.app Term.snd_pair rec1)) := by
    simp only [step_body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
      snd_pair_closed_subst, sg_bar_closed_subst,
      Term.weaken, Term.rename]
  let h_step2 := lam2_correct_nf adm step_body rec1 (.app .succ .zero) step_nf2
  -- rec0 = prec(base, step, 0)
  let rec0 : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) base step .zero
  -- rec_succ: rec1 =₀ step(rec0, 0)
  let h_rec_succ : Derivable F EqX al Premises
      (Formula.eq0 rec1 (Term.app2 step rec0 .zero)) := .rec_succ (ρ := Ty.nat)
  -- rec_zero: rec0 =₀ base
  let h_rec_zero : Derivable F EqX al Premises (Formula.eq0 rec0 base) :=
    .rec_zero (ρ := Ty.nat)
  -- step(rec0, 0) =₀ pair(add(fst(rec0), snd(rec0)), sg_bar(snd(rec0)))
  have step_nf0 : (step_body.subst0 ((.zero : Term F Γ _).weaken)).subst0 rec0 =
      Term.app2 Term.pair
        (Term.app2 Term.add (.app Term.fst_pair rec0) (.app Term.snd_pair rec0))
        (.app Term.sg_bar (.app Term.snd_pair rec0)) := by
    simp only [step_body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      pair_closed_subst, add_closed_subst, fst_pair_closed_subst,
      snd_pair_closed_subst, sg_bar_closed_subst,
      Term.weaken, Term.rename]
  let h_step0 := lam2_correct_nf adm step_body rec0 .zero step_nf0
  -- fst_pair(rec0) =₀ 0, snd_pair(rec0) =₀ S0 (via rec_zero + fst/snd_pair_pair)
  let h_fst_rec0 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair rec0) Term.zero) :=
    .mp (.mp (fst_pair_pair adm Term.zero (.app .succ .zero))
      (.mp (fst_pair_congr h_rec_zero) and_intro)) .trans0
  let h_snd_rec0 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair rec0) (.app .succ .zero)) :=
    .mp (.mp (snd_pair_pair adm Term.zero (.app .succ .zero))
      (.mp (snd_pair_congr h_rec_zero) and_intro)) .trans0
  -- add(fst(rec0), snd(rec0)) =₀ S0
  let h_add_0 := .mp (.mp (add_zero_l adm (.app .succ .zero))
    (.mp (.mp (.mp (add_congr_l h_fst_rec0 (.app .succ .zero))
        (.mp (add_congr_r (.app Term.fst_pair rec0) h_snd_rec0) and_intro)) .trans0) and_intro)) .trans0
  -- sg_bar(snd(rec0)) =₀ 0
  let h_sgb_0 := .mp (.mp (sg_bar_succ adm .zero) (.mp (sg_bar_congr h_snd_rec0) and_intro)) .trans0
  -- step(rec0, 0) =₀ pair(S0, 0)
  let h_val0 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 step rec0 .zero)
      (Term.app2 Term.pair (.app .succ .zero) Term.zero)) :=
    .mp (.mp (pair_congr h_add_0 h_sgb_0) (.mp h_step0 and_intro)) .trans0
  -- rec1 =₀ pair(S0, 0)
  let h_rec1_val := .mp (.mp h_val0 (.mp h_rec_succ and_intro)) .trans0
  -- fst_pair(rec1) =₀ S0, snd_pair(rec1) =₀ 0
  let h_fst_r1 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair rec1) (.app .succ .zero)) :=
    .mp (.mp (fst_pair_pair adm (.app .succ .zero) Term.zero)
      (.mp (fst_pair_congr h_rec1_val) and_intro)) .trans0
  let h_snd_r1 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair rec1) Term.zero) :=
    .mp (.mp (snd_pair_pair adm (.app .succ .zero) Term.zero)
      (.mp (snd_pair_congr h_rec1_val) and_intro)) .trans0
  -- NF of step(rec1, S0) = pair(add(fst(rec1), snd(rec1)), sg_bar(snd(rec1)))
  -- Simplify: add(S0, 0) =₀ S0, sg_bar(0) =₀ S0
  let h_add_r1 := .mp (.mp (add_zero_r adm (.app .succ .zero))
    (.mp (.mp (.mp (add_congr_l h_fst_r1 Term.zero)
        (.mp (add_congr_r (.app Term.fst_pair rec1) h_snd_r1) and_intro)) .trans0) and_intro)) .trans0
  let h_sgb_r1 := .mp (.mp (sg_bar_zero (Premises := Premises))
    (.mp (sg_bar_congr h_snd_r1) and_intro)) .trans0
  -- step(rec1, S0) =₀ NF =₀ pair(S0, S0)
  let h_val2 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 step rec1 (.app .succ .zero))
      (Term.app2 Term.pair (.app .succ .zero) (.app .succ .zero))) :=
    .mp (.mp (pair_congr h_add_r1 h_sgb_r1) (.mp h_step2 and_intro)) .trans0
  -- rec(base, step, SS0) =₀ pair(S0, S0)
  let h_rec2_val := .mp (.mp h_val2 (.mp h_rec2 and_intro)) .trans0
  -- fst_pair(rec(base, step, SS0)) =₀ S0
  let h_fst_final := .mp (.mp (fst_pair_pair adm (.app .succ .zero) (.app .succ .zero))
    (.mp (fst_pair_congr h_rec2_val) and_intro)) .trans0
  -- div2(SS0) =₀ S0
  .mp (.mp h_fst_final (.mp h_unfold and_intro)) .trans0

-- ── one_Q component lemmas ────────────────────────────────────────────────

/-- rat_sign(one_Q) =₀ S0. -/
private def rat_sign_one_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_sign Term.one_Q) (.app .succ .zero)) :=
  let h1 := lam_correct_nf
    (.app Term.isEven (.app Term.fst_pair (.var .vz)) : Term F (Ty.nat :: Γ) _) Term.one_Q (by rfl)
  let h_fst := fst_pair_pair adm (Term.ofNat 2) Term.zero
  let h2 := isEven_congr h_fst
  let h3 := isEven_two adm
  let c := .mp (.mp h2 (.mp h1 and_intro)) .trans0
  .mp (.mp h3 (.mp c and_intro)) .trans0

/-- rat_den(one_Q) =₀ S0. -/
private def rat_den_one_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_den Term.one_Q) (.app .succ .zero)) :=
  let h1 := lam_correct_nf
    (.app .succ (.app Term.snd_pair (.var .vz)) : Term F (Ty.nat :: Γ) _) Term.one_Q (by rfl)
  let h_snd := snd_pair_pair adm (Term.ofNat 2) Term.zero
  let h2 := succ_congr h_snd
  .mp (.mp h2 (.mp h1 and_intro)) .trans0

/-- rat_num(one_Q) =₀ S0. -/
private def rat_num_one_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_num Term.one_Q) (.app .succ .zero)) :=
  let rat_num_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app Term.div2
      (Term.app2 Term.add
        (.app Term.fst_pair (.var .vz))
        (.app Term.isOdd (.app Term.fst_pair (.var .vz))))
  let h1 := lam_correct_nf rat_num_body Term.one_Q (by rfl)
  let h_fst := fst_pair_pair adm (Term.ofNat 2) Term.zero
  let h_isOdd := .mp (.mp (isOdd_two adm) (.mp (isOdd_congr h_fst) and_intro)) .trans0
  let h_add1 := add_congr_l h_fst (.app Term.isOdd (.app Term.fst_pair Term.one_Q))
  let h_add2 := add_congr_r (Term.ofNat 2) h_isOdd
  let h_add3 := .mp (.mp h_add2 (.mp h_add1 and_intro)) .trans0
  let h_add4 := .mp (.mp (add_zero_r adm (Term.ofNat 2)) (.mp h_add3 and_intro)) .trans0
  let h_div2_cong := div2_congr h_add4
  let c := .mp (.mp h_div2_cong (.mp h1 and_intro)) .trans0
  .mp (.mp (div2_two adm) (.mp c and_intro)) .trans0

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

/-- Derive eq_Q(a, b) from proofs that the cross-product and sign·sg parts of eq_Q_dec
    are both zero.  Handles the eq_Q_dec unfolding internally. -/
private def eq_Q_from_components {a b : Term F Γ Ty.nat}
    (h_cross : Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num a) (Term.app Term.rat_den b))
        (Term.app2 Term.mul (Term.app Term.rat_num b) (Term.app Term.rat_den a)))
      Term.zero))
    (h_sign : Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign a) (Term.app Term.rat_sign b))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num a) (Term.app Term.rat_num b))))
      Term.zero)) :
    Derivable F EqX al Premises (eq_Q a b) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have body_eq : (Term.eq_Q_dec : Term F Γ _) = Term.lam (Term.lam body) := by rfl
  have body_nf : (body.subst0 (b.weaken)).subst0 a =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff
          (Term.app2 Term.mul (Term.app Term.rat_num a) (Term.app Term.rat_den b))
          (Term.app2 Term.mul (Term.app Term.rat_num b) (Term.app Term.rat_den a)))
        (Term.app2 Term.mul
          (Term.app2 Term.abs_diff (Term.app Term.rat_sign a) (Term.app Term.rat_sign b))
          (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num a) (Term.app Term.rat_num b)))) := by
    simp only [body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      weaken_subst0_eta]
  let unfold := body_eq ▸ lam2_correct_nf adm body a b body_nf
  let h_sum := .mp (.mp h_sign (.mp h_cross and_intro))
    (.mp (add_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  .mp (.mp h_sum (.mp unfold and_intro)) .trans0

-- Distributivity of ∧ over ∨ (`and_or_dist`) now lives in `PropositionalLemmas`.

/-- From `sg_bar(x) =₀ S0`, derive `x =₀ 0`. -/
private def sg_bar_eq_S0_implies_zero (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar x) (.app .succ .zero) →ᶠ Formula.eq0 x .zero) :=
  let backward : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 x .zero →ᶠ Formula.eq0 (.app Term.sg_bar x) .zero) :=
    .mp (sg_bar_eq_zero_iff adm x) (.syllogism .and_perm .and_weak)
  let h_contra : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar x) (.app .succ .zero) ∧ᶠ ¬ᶠFormula.eq0 x .zero →ᶠ ⊥ᶠ) :=
    .syllogism
      (.syllogism (pair_h (.syllogism .and_weak .sym0) (.syllogism and_proj2 backward)) .trans0)
      (.mp .succ_ne_zero (.forall_ax (.zero : Term F Γ _)))
  let h_disj := .mp eq0_decidable' (.forall_ax x)
  .syllogism (pair_h I_comb (weaken_intro h_disj)) (
    .syllogism and_or_dist
      (or_elim_rule and_proj2 (.syllogism h_contra .exfalso)))

/-- x+z =₀ y+z → x =₀ y (right additive cancellation). -/
private def add_cancel_r {Γ : Ctx ι} (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add x z) (Term.app2 Term.add y z) →ᶠ
       Formula.eq0 x y) :=
  let m1 := monus_cancel adm x z
  let m2 := monus_cancel adm y z
  let cond_mon := qfer_nat_nf (by rfl) (by rfl) I_comb
    (r := Term.app2 Term.monus (.var .vz) z.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg _ (Term.weaken_subst0 z (Term.app2 Term.add x z)))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst]
        exact congrArg _ (Term.weaken_subst0 z (Term.app2 Term.add y z)))
  .syllogism (pair_h (.syllogism (pair_h (weaken_intro_h (.mp m1 .sym0)) cond_mon) .trans0)
    (weaken_intro_h m2)) .trans0

-- Helpers for doubly-weakened terms under substitution
private theorem dw_subst0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat) (s : Term F Γ Ty.nat) :
    Term.subst (Term.Subst.ext (σ := Ty.nat) (Term.subst0_map s))
      (t.weaken (σ := Ty.nat)).weaken = t.weaken := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_subst, Term.rename_eq_subst]; rfl

private theorem dw_substVar0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat)
    (u : Term F (Ty.nat :: Γ) Ty.nat) :
    Term.subst (Term.Subst.ext (σ := Ty.nat) (Term.substVar0_map u))
      (t.weaken (σ := Ty.nat)).weaken = (t.weaken (σ := Ty.nat)).weaken := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_subst, Term.rename_rename, Term.rename_eq_subst]; rfl

private theorem tw_subst0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat)
    (s : Term F (Ty.nat :: Γ) Ty.nat) :
    Term.subst (Term.Subst.ext (σ := Ty.nat) (Term.subst0_map s))
      ((t.weaken (σ := Ty.nat)).weaken (σ := Ty.nat)).weaken = (t.weaken (σ := Ty.nat)).weaken := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_subst, Term.rename_subst,
    Term.rename_rename, Term.rename_eq_subst]; rfl

@[simp] private theorem mul_closed_rename {Γ Δ : Ctx ι} (r : Renaming Γ Δ) :
    (Term.mul : Term F Γ _).rename r = Term.mul := by rfl

private theorem ww_subst_ext_subst0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat)
    (s : Term F Γ Ty.nat) :
    Term.subst (Term.Subst.ext (σ := Ty.nat) (Term.subst0_map s))
      ((t.weaken (σ := Ty.nat)).weaken (σ := Ty.nat)) = t.weaken (σ := Ty.nat) := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_subst, Term.rename_eq_subst]; rfl

private theorem ww_subst_ext_substVar0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat)
    (u : Term F (Ty.nat :: Γ) Ty.nat) :
    Term.subst (Term.Subst.ext (σ := Ty.nat) (Term.substVar0_map u))
      ((t.weaken (σ := Ty.nat)).weaken (σ := Ty.nat)) =
      (t.weaken (σ := Ty.nat)).weaken (σ := Ty.nat) := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_subst, Term.rename_rename, Term.rename_eq_subst]; rfl

private theorem nww_rename_subst0 {Γ : Ctx ι} {F : ι → Ty ι} (t : Term F Γ Ty.nat)
    (s : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat) :
    Term.subst (Term.subst0_map s)
      (Term.rename (Term.Renaming.ext Term.Renaming.shift)
        (Term.rename Term.Renaming.shift (Term.rename Term.Renaming.shift t))) =
    Term.rename Term.Renaming.shift (Term.rename Term.Renaming.shift t) := by
  rw [Term.rename_subst, Term.rename_subst, Term.rename_subst,
      Term.rename_rename, Term.rename_eq_subst]; rfl

/-- Step body for mul_cancel_succ induction.
    In context Ty.nat :: Ty.nat :: Γ: var(vs vz) = x (induction var), var(vz) = y.
    IH (A.weakenBy) is ∀z. x*S(nww) = z*S(nww) → x = z.
    Goal: S(x)*S(nww) = y*S(nww) → S(x) = y. -/
private def mul_cancel_succ_step {Γ : Ctx ι} (n : Term F Γ Ty.nat) :
    let nww := (n.weaken (σ := Ty.nat)).weaken (σ := Ty.nat)
    let nwww := nww.weaken (σ := Ty.nat)
    let xv : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
    let yv : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
    let sxv := Term.app Term.succ xv
    let inner : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.mul (.var (.vs .vz)) (.app .succ nww))
                 (Term.app2 Term.mul (.var .vz) (.app .succ nww))
      →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)
    let A : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat inner
    Derivable F EqX al Premises (A.weakenBy Ty.nat →ᶠ
      (Formula.eq0 (Term.app2 Term.mul sxv (.app .succ nww))
                   (Term.app2 Term.mul yv (.app .succ nww))
       →ᶠ Formula.eq0 sxv yv)) :=
  let nww := (n.weaken (σ := Ty.nat)).weaken (σ := Ty.nat)
  let nwww := nww.weaken (σ := Ty.nat)
  let xv : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let sxv := Term.app Term.succ xv
  let snww := Term.app Term.succ nww
  let pdy := Term.app Term.pd yv
  let inner : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul (.var (.vs .vz)) snww)
               (Term.app2 Term.mul (.var .vz) snww)
    →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)
  let A : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat inner
  -- IH instantiated at pd(y): x*S(nww) = pd(y)*S(nww) → x = pd(y)
  have ih_nf : (inner.renameF (Renaming.ext Renaming.shift)).subst0 pdy =
      (Formula.eq0 (Term.app2 Term.mul xv snww)
                   (Term.app2 Term.mul pdy snww)
       →ᶠ Formula.eq0 xv pdy) := by
    simp only [inner, snww, nww, Formula.renameF, Formula.subst0, Formula.substF,
      Term.rename, Term.subst, Term.Renaming.ext,
      Term.subst0_map, Term.app2,
      mul_closed_subst, mul_closed_rename, Term.weaken,
      nww_rename_subst0]; rfl
  let ih_at_pdy := Eq.mp (congrArg (fun f => Derivable F EqX al Premises
    (A.weakenBy Ty.nat →ᶠ f)) ih_nf) (Derivable.forall_ax pdy)
  -- Case y = 0: S(x)*S(nww) = 0 contradicts succ_ne_zero
  let mul_zero_eq : Derivable F EqX al Premises
      (Formula.eq0 yv .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul yv snww) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.mul (.var .vz) snww.weaken)
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
            exact congrArg _ (Term.weaken_subst0 snww yv))
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
            exact congrArg _ (Term.weaken_subst0 snww .zero)))
      (weaken_intro_h (mul_zero_l adm snww))) .trans0
  let sxv_mul_ne_zero : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul sxv snww) .zero →ᶠ ⊥ᶠ) :=
    .syllogism (.mp (mul_eq_zero_iff adm sxv snww) .and_weak)
      (or_elim_rule
        (.mp .succ_ne_zero (.forall_ax xv))
        (.mp .succ_ne_zero (.forall_ax nww)))
  let case_y0 : Derivable F EqX al Premises
      (Formula.eq0 yv .zero →ᶠ
       (A.weakenBy Ty.nat →ᶠ
        (Formula.eq0 (Term.app2 Term.mul sxv snww)
                    (Term.app2 Term.mul yv snww) →ᶠ Formula.eq0 sxv yv))) :=
    .exportation (.exportation (.syllogism
      (pair_h and_proj2 (.syllogism (.syllogism .and_weak .and_weak) mul_zero_eq))
      (.syllogism .trans0 (.syllogism sxv_mul_ne_zero .exfalso))))
  -- Case y ≠ 0:
  -- mul_succ_l: S(x)*S(nww) = x*S(nww) + S(nww)
  let msl_sx := mul_succ_l adm xv snww
  -- y ≠ 0 → y = S(pd(y)), so y*S(nww) = S(pd(y))*S(nww) = pd(y)*S(nww) + S(nww)
  let ne_succ := ne_zero_eq_succ_pd adm yv
  let msl_pdy := mul_succ_l adm pdy snww
  let y_mul_eq : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul yv snww)
                   (Term.app2 Term.add (Term.app2 Term.mul pdy snww) snww)) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) ne_succ
        (r := Term.app2 Term.mul (.var .vz) snww.weaken)
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
            exact congrArg _ (Term.weaken_subst0 snww yv))
        (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst]
            exact congrArg _ (Term.weaken_subst0 snww (.app Term.succ pdy))))
      (weaken_intro_h msl_pdy)) .trans0
  -- Chain: S(x)*S(nww) = x*S(nww)+S(nww), y*S(nww) = pd(y)*S(nww)+S(nww)
  -- From hyp + chains: x*S(nww)+S(nww) = pd(y)*S(nww)+S(nww)
  -- By add_cancel_r: x*S(nww) = pd(y)*S(nww)
  -- By IH: x = pd(y)
  -- S(x) = S(pd(y)) = y
  let succ_congr : Derivable F EqX al Premises
      (Formula.eq0 xv pdy →ᶠ Formula.eq0 sxv (.app .succ pdy)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app .succ (.var .vz)) rfl rfl
  let case_yne0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero →ᶠ
       (A.weakenBy Ty.nat →ᶠ
        (Formula.eq0 (Term.app2 Term.mul sxv snww)
                    (Term.app2 Term.mul yv snww) →ᶠ Formula.eq0 sxv yv))) :=
    .exportation (.exportation (
    -- Hypothesis context (left-assoc): (¬(y=0) ∧ IH) ∧ hyp
    let get_hyp := @and_proj2 _ F EqX al Premises _
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat)
      (Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww))
    let get_ne : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         ¬ᶠFormula.eq0 yv .zero) :=
      .syllogism .and_weak .and_weak
    let chain1 : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         Formula.eq0 (Term.app2 Term.add (Term.app2 Term.mul xv snww) snww)
                     (Term.app2 Term.mul yv snww)) :=
      .syllogism (pair_h (weaken_intro_h (.mp msl_sx .sym0)) get_hyp) .trans0
    let chain2 : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         Formula.eq0 (Term.app2 Term.add (Term.app2 Term.mul xv snww) snww)
                     (Term.app2 Term.add (Term.app2 Term.mul pdy snww) snww)) :=
      .syllogism (pair_h chain1 (.syllogism get_ne y_mul_eq)) .trans0
    let chain3 : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         Formula.eq0 (Term.app2 Term.mul xv snww) (Term.app2 Term.mul pdy snww)) :=
      .syllogism chain2 (add_cancel_r adm _ _ snww)
    let get_ih : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         A.weakenBy Ty.nat) :=
      .syllogism .and_weak and_proj2
    let chain4 : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         Formula.eq0 xv pdy) :=
      .syllogism (pair_h get_ih chain3) (.importation ih_at_pdy)
    let chain5 : Derivable F EqX al Premises
        (¬ᶠFormula.eq0 yv .zero ∧ᶠ A.weakenBy Ty.nat ∧ᶠ
         Formula.eq0 (Term.app2 Term.mul sxv snww) (Term.app2 Term.mul yv snww) →ᶠ
         Formula.eq0 sxv yv) :=
      .syllogism (pair_h (.syllogism chain4 succ_congr)
        (.syllogism get_ne (.syllogism ne_succ .sym0))) .trans0
    chain5))
  -- Combine via case analysis
  let dec := .mp eq0_decidable' (.forall_ax yv)
  .mp dec (or_elim_rule case_y0 case_yne0)

/-- x*S(n) =₀ y*S(n) → x =₀ y (multiplicative cancellation for successor). -/
private def mul_cancel_succ {Γ : Ctx ι} (x y n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul x (.app .succ n))
                   (Term.app2 Term.mul y (.app .succ n)) →ᶠ
       Formula.eq0 x y) :=
  let nw := n.weaken (σ := Ty.nat)
  let nww := nw.weaken (σ := Ty.nat)
  let inner : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul (.var (.vs .vz)) (.app .succ nww))
               (Term.app2 Term.mul (.var .vz) (.app .succ nww))
    →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)
  let A : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat inner
  -- Base: ∀y. mul(0, S(n)) = mul(y, S(n)) → 0 = y
  have base_nf : A.subst0 Term.zero =
      Formula.all Ty.nat (
        Formula.eq0 (Term.app2 Term.mul Term.zero (.app .succ nw))
                   (Term.app2 Term.mul (.var .vz) (.app .succ nw))
        →ᶠ Formula.eq0 Term.zero (.var .vz)) := by
    simp only [A, inner, nww, nw, Formula.subst0, Formula.substF, Term.subst,
      Term.subst0_map, Term.Subst.ext, Term.app2, mul_closed_subst,
      ww_subst_ext_subst0]; rfl
  have base_body : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul Term.zero (.app .succ nw))
                   (Term.app2 Term.mul (.var .vz) (.app .succ nw))
       →ᶠ Formula.eq0 Term.zero (.var .vz)) :=
    let snw := Term.app Term.succ nw
    let yv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let mzl := mul_zero_l adm snw
    let y_mul_ne : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.mul yv snw) .zero →ᶠ
         Formula.eq0 yv .zero ∨ᶠ Formula.eq0 snw .zero) :=
      .mp (mul_eq_zero_iff adm yv snw) .and_weak
    let snw_ne : Derivable F EqX al Premises
        (Formula.eq0 snw .zero →ᶠ ⊥ᶠ) :=
      .mp .succ_ne_zero (.forall_ax nw)
    .syllogism
      (pair_h (.syllogism (weaken_intro_h (.mp mzl .sym0)) I_comb) I_comb)
      (.syllogism .trans0
        (.syllogism (.syllogism .sym0 y_mul_ne)
          (or_elim_rule (.syllogism .sym0 I_comb) (.syllogism snw_ne .exfalso))))
  have base := base_nf ▸ univ_gen base_body
  -- Step: A(x) → A(S(x)) via mul_cancel_succ_step
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.all Ty.nat (
        Formula.eq0 (Term.app2 Term.mul (.app .succ (.var (.vs .vz))) (.app .succ nww))
                   (Term.app2 Term.mul (.var .vz) (.app .succ nww))
        →ᶠ Formula.eq0 (.app .succ (.var (.vs .vz))) (.var .vz)) := by
    simp only [A, inner, nww, nw, Formula.substVar0, Formula.substF, Term.subst,
      Term.substVar0_map, Term.Subst.ext, Term.app2, mul_closed_subst,
      ww_subst_ext_substVar0]; rfl
  have step_body : Derivable F EqX al Premises
      (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸ Derivable.forall_rule (mul_cancel_succ_step adm n)
  -- Induction + double instantiation
  have inst_nf : (inner.substF (Term.Subst.ext (Term.subst0_map x))).subst0 y =
      (Formula.eq0 (Term.app2 Term.mul x (.app .succ n))
                   (Term.app2 Term.mul y (.app .succ n)) →ᶠ Formula.eq0 x y) := by
    simp only [inner, nww, nw, Formula.subst0, Formula.substF, Term.subst,
      Term.subst0_map, Term.Subst.ext, Term.app2, mul_closed_subst,
      ww_subst_ext_subst0, weaken_subst0_eta]
  inst_nf ▸
    .mp (.mp (Derivable.induction base (univ_gen step_body)) (.forall_ax x)) (.forall_ax y)

/-- abs_diff(x,y) = 0 ∧ P → x = y -/
private def abs_diff_zero_fwd {Γ : Ctx ι} (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff x y) .zero →ᶠ Formula.eq0 x y) :=
  .mp (abs_diff_eq_zero_iff adm x y) .and_weak

/-- rat_den(x) =₀ S(snd_pair(x)). -/
private def rat_den_unfold_eq (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den x) (.app .succ (.app Term.snd_pair x))) :=
  let rat_den_body : Term F (Ty.nat :: Γ) Ty.nat :=
    .app .succ (.app Term.snd_pair (.var .vz))
  lam_correct_nf rat_den_body x (by
    simp only [rat_den_body, Term.subst0, Term.subst, Term.subst0_map,
      snd_pair_closed_subst])

/-- From x*S(k) =₀ 0, derive x =₀ 0 (using succ_ne_zero). -/
private def mul_succ_eq_zero_imp (x k : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul x (.app .succ k)) .zero →ᶠ
       Formula.eq0 x .zero) :=
  let fwd := .mp (mul_eq_zero_iff adm x (.app .succ k)) .and_weak
  let ne := .mp .succ_ne_zero (.forall_ax k)
  .syllogism fwd (or_elim_rule I_comb (.syllogism ne .exfalso))

/-- sg(n) =₀ 0 → n =₀ 0. -/
private def sg_zero_fwd (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg n) .zero →ᶠ Formula.eq0 n .zero) :=
  let dec := .mp eq0_decidable' (.forall_ax n)
  let pd_n := Term.app Term.pd n
  let n_eq_spd := ne_zero_eq_succ_pd adm n
  let sg_step : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 n .zero →ᶠ
       Formula.eq0 (.app Term.sg n) (.app Term.sg (.app .succ pd_n))) :=
    qfer_nat_nf (by rfl) (by rfl) n_eq_spd
      (r := .app Term.sg (.var .vz))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst])
      (by simp only [pd_n, Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst])
  let sg_is_one : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 n .zero →ᶠ
       Formula.eq0 (.app Term.sg n) (.app .succ .zero)) :=
    .syllogism sg_step
      (.syllogism (pair_h I_comb (weaken_intro_h (sg_succ adm pd_n))) .trans0)
  let case1 : Derivable F EqX al Premises
      (Formula.eq0 n .zero →ᶠ
       (Formula.eq0 (.app Term.sg n) .zero →ᶠ Formula.eq0 n .zero)) :=
    .exportation .and_weak
  let case2 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 n .zero →ᶠ
       (Formula.eq0 (.app Term.sg n) .zero →ᶠ Formula.eq0 n .zero)) :=
    .exportation (.syllogism
      (pair_h (.syllogism .and_weak sg_is_one) and_proj2)
      (.syllogism
        (.syllogism (pair_h (.syllogism .and_weak .sym0) and_proj2)
          (.syllogism .trans0 (.mp .succ_ne_zero (.forall_ax (.zero : Term F Γ _)))))
        .exfalso))
  .mp dec (or_elim_rule case1 case2)

/-- s =₀ t →ᶠ s·u =₀ t·u (formula-level left multiplication congr). -/
private def mul_congr_l_imp {s t : Term F Γ Ty.nat} (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 s t →ᶠ
       Formula.eq0 (Term.app2 Term.mul s u) (Term.app2 Term.mul t u)) :=
  qfer_nat_nf (by rfl) (by rfl) I_comb
    (r := Term.app2 Term.mul (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        mul_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        mul_closed_subst, weaken_subst0_eta])

/-- s =₀ t →ᶠ u·s =₀ u·t (formula-level right multiplication congr). -/
private def mul_congr_r_imp {s t : Term F Γ Ty.nat} (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 s t →ᶠ
       Formula.eq0 (Term.app2 Term.mul u s) (Term.app2 Term.mul u t)) :=
  qfer_nat_nf (by rfl) (by rfl) I_comb
    (r := Term.app2 Term.mul u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        mul_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        mul_closed_subst, weaken_subst0_eta])

/-- ⊢ ∀a,b,c. eq_Q(a, b) ∧ eq_Q(b, c) → eq_Q(a, c) -/
def eq_Q_trans :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q (.var (.vs (.vs .vz))) (.var .vz))))) :=
  let a : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs (.vs .vz))
  let b : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let c : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let na := Term.app Term.rat_num a
  let nb := Term.app Term.rat_num b
  let nc := Term.app Term.rat_num c
  let da := Term.app Term.rat_den a
  let db := Term.app Term.rat_den b
  let dc := Term.app Term.rat_den c
  let sa := Term.app Term.rat_sign a
  let sb := Term.app Term.rat_sign b
  let sc := Term.app Term.rat_sign c
  -- eq_Q_dec body (in context with two variables)
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz)))
          (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz))
          (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz)))
          (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz)))
          (Term.app Term.rat_num (.var .vz)))))
  have body_eq : (Term.eq_Q_dec : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  -- Normal form for eq_Q_dec(a,b)
  have body_nf_ab : (body.subst0 (b.weaken)).subst0 a =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff (Term.app2 Term.mul na db)
          (Term.app2 Term.mul nb da))
        (Term.app2 Term.mul (Term.app2 Term.abs_diff sa sb)
          (Term.app Term.sg (Term.app2 Term.add na nb))) := by
    simp only [body, a, b, na, nb, da, db, sa, sb,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  -- Normal form for eq_Q_dec(b,c)
  have body_nf_bc : (body.subst0 (c.weaken)).subst0 b =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff (Term.app2 Term.mul nb dc)
          (Term.app2 Term.mul nc db))
        (Term.app2 Term.mul (Term.app2 Term.abs_diff sb sc)
          (Term.app Term.sg (Term.app2 Term.add nb nc))) := by
    simp only [body, b, c, nb, nc, db, dc, sb, sc,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  let unfold_ab := body_eq ▸ lam2_correct_nf adm body a b body_nf_ab
  let unfold_bc := body_eq ▸ lam2_correct_nf adm body b c body_nf_bc
  -- Abbreviations for the cross and sign NF terms
  let cross_ab := Term.app2 Term.abs_diff (Term.app2 Term.mul na db) (Term.app2 Term.mul nb da)
  let sign_ab := Term.app2 Term.mul (Term.app2 Term.abs_diff sa sb)
      (Term.app Term.sg (Term.app2 Term.add na nb))
  let cross_bc := Term.app2 Term.abs_diff (Term.app2 Term.mul nb dc) (Term.app2 Term.mul nc db)
  let sign_bc := Term.app2 Term.mul (Term.app2 Term.abs_diff sb sc)
      (Term.app Term.sg (Term.app2 Term.add nb nc))
  -- H = eq_Q(a,b) ∧ eq_Q(b,c)
  -- Extract: H → NF_ab = 0 and H → NF_bc = 0
  let H_to_nf_ab : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.add cross_ab sign_ab) .zero) :=
    .syllogism .and_weak
      (.syllogism (pair_h (weaken_intro_h (.mp unfold_ab .sym0)) I_comb) .trans0)
  let H_to_nf_bc : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.add cross_bc sign_bc) .zero) :=
    .syllogism and_proj2
      (.syllogism (pair_h (weaken_intro_h (.mp unfold_bc .sym0)) I_comb) .trans0)
  -- Extract cross and sign from each
  let aez_ab := add_eq_zero_iff adm cross_ab sign_ab
  let H_to_cross_ab0 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ Formula.eq0 cross_ab .zero) :=
    .syllogism H_to_nf_ab (.syllogism (.mp aez_ab .and_weak) .and_weak)
  let H_to_sign_ab0 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ Formula.eq0 sign_ab .zero) :=
    .syllogism H_to_nf_ab (.syllogism (.mp aez_ab .and_weak) and_proj2)
  let aez_bc := add_eq_zero_iff adm cross_bc sign_bc
  let H_to_cross_bc0 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ Formula.eq0 cross_bc .zero) :=
    .syllogism H_to_nf_bc (.syllogism (.mp aez_bc .and_weak) .and_weak)
  let H_to_sign_bc0 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ Formula.eq0 sign_bc .zero) :=
    .syllogism H_to_nf_bc (.syllogism (.mp aez_bc .and_weak) and_proj2)
  -- H → na·db = nb·da and H → nb·dc = nc·db
  let H_to_eq_ab : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul na db) (Term.app2 Term.mul nb da)) :=
    .syllogism H_to_cross_ab0 (abs_diff_zero_fwd adm _ _)
  let H_to_eq_bc : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul nb dc) (Term.app2 Term.mul nc db)) :=
    .syllogism H_to_cross_bc0 (abs_diff_zero_fwd adm _ _)
  -- ══════════════════════════════════════════════════════════════════════
  -- CROSS PART: H → na·dc = nc·da
  -- Strategy: (na·dc)·db = (nc·da)·db, then cancel db = S(snd_pair(b))
  -- ══════════════════════════════════════════════════════════════════════
  -- Chain: (na·db)·dc = (nb·da)·dc
  let H_to_step1 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.mul na db) dc)
                   (Term.app2 Term.mul (Term.app2 Term.mul nb da) dc)) :=
    .syllogism H_to_eq_ab (mul_congr_l_imp dc)
  let assoc1 := mul_assoc adm na db dc
  let assoc2 := mul_assoc adm nb da dc
  -- H → na·(db·dc) = nb·(da·dc)
  let H_to_step2 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul na (Term.app2 Term.mul db dc))
                   (Term.app2 Term.mul nb (Term.app2 Term.mul da dc))) :=
    .syllogism (pair_h (weaken_intro_h (.mp assoc1 .sym0)) H_to_step1) .trans0
    |> fun h => .syllogism (pair_h h (weaken_intro_h assoc2)) .trans0
  -- Chain: (nb·dc)·da = (nc·db)·da
  let H_to_step3 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.mul nb dc) da)
                   (Term.app2 Term.mul (Term.app2 Term.mul nc db) da)) :=
    .syllogism H_to_eq_bc (mul_congr_l_imp da)
  let assoc3 := mul_assoc adm nb dc da
  let assoc4 := mul_assoc adm nc db da
  -- H → nb·(dc·da) = nc·(db·da)
  let H_to_step4 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul nb (Term.app2 Term.mul dc da))
                   (Term.app2 Term.mul nc (Term.app2 Term.mul db da))) :=
    .syllogism (pair_h (weaken_intro_h (.mp assoc3 .sym0)) H_to_step3) .trans0
    |> fun h => .syllogism (pair_h h (weaken_intro_h assoc4)) .trans0
  -- nb·(da·dc) = nb·(dc·da) via comm
  let cong1 := mul_congr_r nb (mul_comm adm da dc)
  -- H → na·(db·dc) = nc·(db·da)
  let H_to_step5 : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul na (Term.app2 Term.mul db dc))
                   (Term.app2 Term.mul nc (Term.app2 Term.mul db da))) :=
    .syllogism (pair_h H_to_step2 (weaken_intro_h cong1)) .trans0
    |> fun h => .syllogism (pair_h h H_to_step4) .trans0
  -- Rearrange LHS: (na·dc)·db = na·(dc·db) = na·(db·dc) (standalone)
  let assoc5 := mul_assoc adm na dc db
  let cong2 := mul_congr_r na (mul_comm adm dc db)
  let lhs_eq : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.mul na dc) db)
                   (Term.app2 Term.mul na (Term.app2 Term.mul db dc))) :=
    .mp (.mp cong2 (.mp assoc5 and_intro)) .trans0
  -- Rearrange RHS: nc·(db·da) = nc·(da·db) = (nc·da)·db (standalone)
  let cong3 := mul_congr_r nc (mul_comm adm db da)
  let assoc6 := mul_assoc adm nc da db
  let rhs_eq : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul nc (Term.app2 Term.mul db da))
                   (Term.app2 Term.mul (Term.app2 Term.mul nc da) db)) :=
    .mp (.mp (.mp assoc6 .sym0) (.mp cong3 and_intro)) .trans0
  -- H → (na·dc)·db = (nc·da)·db
  let H_to_prod_eq : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.mul na dc) db)
                   (Term.app2 Term.mul (Term.app2 Term.mul nc da) db)) :=
    .syllogism (pair_h (weaken_intro_h lhs_eq) H_to_step5) .trans0
    |> fun h => .syllogism (pair_h h (weaken_intro_h rhs_eq)) .trans0
  -- db = S(snd_pair(b)), so cancel
  let db_eq := rat_den_unfold_eq b
  let spb := Term.app Term.snd_pair b
  -- H → (na·dc)·S(spb) = (nc·da)·S(spb)
  let cong_db_l := mul_congr_r (Term.app2 Term.mul na dc) db_eq
  let cong_db_r := mul_congr_r (Term.app2 Term.mul nc da) db_eq
  let H_to_prod_eq' : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.mul na dc) (.app .succ spb))
                   (Term.app2 Term.mul (Term.app2 Term.mul nc da) (.app .succ spb))) :=
    .syllogism (pair_h (weaken_intro_h (.mp cong_db_l .sym0)) H_to_prod_eq) .trans0
    |> fun h => .syllogism (pair_h h (weaken_intro_h cong_db_r)) .trans0
  -- Cancel: H → na·dc = nc·da
  let H_to_cross_eq : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul na dc) (Term.app2 Term.mul nc da)) :=
    .syllogism H_to_prod_eq' (mul_cancel_succ adm _ _ spb)
  -- H → |na·dc - nc·da| = 0
  let H_to_cross_ac : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff (Term.app2 Term.mul na dc)
         (Term.app2 Term.mul nc da)) .zero) :=
    .syllogism H_to_cross_eq
      (.mp (abs_diff_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  -- ══════════════════════════════════════════════════════════════════════
  -- SIGN PART: H → |sa - sc| · sg(na + nc) = 0
  -- ══════════════════════════════════════════════════════════════════════
  -- Helper: x·db=0 → x=0 (since db = S(spb))
  let mul_db_zero (x : Term F _ Ty.nat) : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul x db) .zero →ᶠ Formula.eq0 x .zero) :=
    .syllogism
      (pair_h (weaken_intro_h (.mp (mul_congr_r x db_eq) .sym0)) I_comb)
      (.syllogism .trans0 (mul_succ_eq_zero_imp adm x spb))
  -- Helper: na+nc=0 → sg(na+nc)=0
  let add_nc_to_sg : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add na nc) .zero →ᶠ
       Formula.eq0 (.app Term.sg (Term.app2 Term.add na nc)) .zero) :=
    .syllogism
      (qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app Term.sg (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst]))
      (.syllogism (pair_h I_comb (weaken_intro_h (sg_zero (Premises := Premises)))) .trans0)
  -- Helper: x=0 → x·y=0
  let zero_mul (x y : Term F _ Ty.nat) : Derivable F EqX al Premises
      (Formula.eq0 x .zero →ᶠ Formula.eq0 (Term.app2 Term.mul x y) .zero) :=
    .syllogism (mul_congr_l_imp (s := x) (t := .zero) y)
      (.syllogism (pair_h I_comb (weaken_intro_h (mul_zero_l adm y))) .trans0)
  -- Helper: sg(x+y)=0 → x=0 ∧ y=0
  let sg_add_parts (x y : Term F _ Ty.nat) : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg (Term.app2 Term.add x y)) .zero →ᶠ
       Formula.eq0 x .zero ∧ᶠ Formula.eq0 y .zero) :=
    .syllogism (sg_zero_fwd adm _) (Derivable.mp (add_eq_zero_iff adm x y) .and_weak)
  -- Abbreviation for target disjunction
  let sign_disj := Formula.eq0 (Term.app2 Term.abs_diff sa sc) .zero
      ∨ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add na nc)) .zero
  -- H disjunctions
  let mez_ab_fwd : Derivable F EqX al Premises
      (Formula.eq0 sign_ab .zero →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff sa sb) .zero
       ∨ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add na nb)) .zero) :=
    Derivable.mp (mul_eq_zero_iff adm _ _) Derivable.and_weak
  let mez_bc_fwd : Derivable F EqX al Premises
      (Formula.eq0 sign_bc .zero →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff sb sc) .zero
       ∨ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add nb nc)) .zero) :=
    Derivable.mp (mul_eq_zero_iff adm _ _) Derivable.and_weak
  let H_to_disj_ab : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff sa sb) .zero
       ∨ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add na nb)) .zero) :=
    .syllogism H_to_sign_ab0 mez_ab_fwd
  let H_to_disj_bc : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff sb sc) .zero
       ∨ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add nb nc)) .zero) :=
    .syllogism H_to_sign_bc0 mez_bc_fwd
  -- CASE A: H ∧ sg(na+nb)=0 → sign_disj
  let case_A : Derivable F EqX al Premises
      ((eq_Q a b ∧ᶠ eq_Q b c)
       ∧ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add na nb)) .zero →ᶠ sign_disj) :=
    let parts := .syllogism and_proj2 (sg_add_parts na nb)
    let get_na := .syllogism parts .and_weak
    let get_nb := .syllogism parts and_proj2
    let nb_dc_0 := .syllogism get_nb (zero_mul nb dc)
    let cross_bc := .syllogism .and_weak H_to_eq_bc
    let nc_db_0 := .syllogism (pair_h (.syllogism nb_dc_0 .sym0) cross_bc)
      (.syllogism .trans0 .sym0)
    let get_nc := .syllogism nc_db_0 (mul_db_zero nc)
    .syllogism (pair_h get_na get_nc)
      (.syllogism (Derivable.mp (add_eq_zero_iff adm na nc) (.syllogism .and_perm .and_weak))
        (.syllogism add_nc_to_sg or_inr))
  -- CASE B: H ∧ sg(nb+nc)=0 → sign_disj
  let case_B : Derivable F EqX al Premises
      ((eq_Q a b ∧ᶠ eq_Q b c)
       ∧ᶠ Formula.eq0 (.app Term.sg (Term.app2 Term.add nb nc)) .zero →ᶠ sign_disj) :=
    let parts := .syllogism and_proj2 (sg_add_parts nb nc)
    let get_nb := .syllogism parts .and_weak
    let get_nc := .syllogism parts and_proj2
    let nb_da_0 := .syllogism get_nb (zero_mul nb da)
    let cross_ab := .syllogism .and_weak H_to_eq_ab
    let na_db_0 := .syllogism (pair_h cross_ab nb_da_0) .trans0
    let get_na := .syllogism na_db_0 (mul_db_zero na)
    .syllogism (pair_h get_na get_nc)
      (.syllogism (Derivable.mp (add_eq_zero_iff adm na nc) (.syllogism .and_perm .and_weak))
        (.syllogism add_nc_to_sg or_inr))
  -- CASE C: |sa-sb|=0 ∧ |sb-sc|=0 → sign_disj
  let case_C : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff sa sb) .zero
       ∧ᶠ Formula.eq0 (Term.app2 Term.abs_diff sb sc) .zero →ᶠ sign_disj) :=
    .syllogism
      (.syllogism (pair_h (.syllogism .and_weak (abs_diff_zero_fwd adm sa sb))
                         (.syllogism and_proj2 (abs_diff_zero_fwd adm sb sc)))
        (.syllogism .trans0
          (Derivable.mp (abs_diff_eq_zero_iff adm sa sc) (.syllogism .and_perm .and_weak))))
      .or_weak
  -- Combine: H → sign_disj
  -- First distribute: H ∧ (A∨B) → (H∧A) ∨ (H∧B) using and_or_dist
  -- Outer case split on sign_ab disjunction
  let H_to_sign_disj : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ sign_disj) :=
    .syllogism (pair_h I_comb H_to_disj_ab)
      (.syllogism and_or_dist (or_elim_rule
        -- H ∧ |sa-sb|=0: inner case split on sign_bc disjunction
        -- Keep (H ∧ |sa-sb|=0) paired with the bc disjunction
        (.syllogism (pair_h I_comb (.syllogism .and_weak H_to_disj_bc))
          (.syllogism and_or_dist (or_elim_rule
            -- (H ∧ |sa-sb|=0) ∧ |sb-sc|=0 → case_C
            (.syllogism (pair_h (.syllogism .and_weak and_proj2) and_proj2) case_C)
            -- (H ∧ |sa-sb|=0) ∧ sg(nb+nc)=0 → case_B
            (.syllogism (pair_h (.syllogism .and_weak .and_weak) and_proj2) case_B))))
        -- H ∧ sg(na+nb)=0
        case_A))
  let H_to_sign_ac : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.mul
         (Term.app2 Term.abs_diff sa sc)
         (Term.app Term.sg (Term.app2 Term.add na nc))) .zero) :=
    .syllogism H_to_sign_disj
      (Derivable.mp (mul_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  -- ══════════════════════════════════════════════════════════════════════
  -- COMBINE: H → eq_Q(a, c)
  -- ══════════════════════════════════════════════════════════════════════
  let unfold_ac := body_eq ▸ lam2_correct_nf adm body a c (by
    simp only [body, a, c, na, nc, da, dc, sa, sc,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, rat_sign_closed_subst, sg_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift])
  let H_to_nf_ac_zero : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ
       Formula.eq0 (Term.app2 Term.add
         (Term.app2 Term.abs_diff (Term.app2 Term.mul na dc) (Term.app2 Term.mul nc da))
         (Term.app2 Term.mul (Term.app2 Term.abs_diff sa sc)
           (Term.app Term.sg (Term.app2 Term.add na nc)))) .zero) :=
    .syllogism (pair_h H_to_cross_ac H_to_sign_ac)
      (.mp (add_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  let core : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q b c →ᶠ eq_Q a c) :=
    .syllogism (pair_h (weaken_intro_h unfold_ac) H_to_nf_ac_zero) .trans0
  univ_gen (univ_gen (univ_gen core))


/-- `Term.weaken_subst0` with `subst0` unfolded, so it still fires after `Formula.subst0`
has been simped through to bare `Term.subst`. -/
theorem subst_subst0_map_weaken {Γ : Ctx ι} {τ ρ : Ty ι}
    (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (Term.subst0_map s) (Term.weaken t) = t :=
  Term.weaken_subst0 t s

/-- Normalize `Formula.subst0` / `Term.subst` through the closed rational-arithmetic terms.

Instantiating a ∀-lemma whose body mentions `eq_Q` leaves `Formula.subst0 … t` in the type.
Forcing that against a hand-written formula by `isDefEq` means traversing `eq_Q_dec` — a large
closed term — once per quantifier, which exhausts the heartbeat budget. `q_norm` does the same
reduction by rewriting with the `_closed_subst` lemmas instead, which is cheap and total.

Use as `by have h := …; simpa only [q_norm_lemmas] using h`, or via `q_norm using h`. -/
syntax "q_norm" "using" term : tactic

macro_rules
  | `(tactic| q_norm using $h:term) =>
    `(tactic| simpa only [eq_Q, Formula.subst0, Formula.substF, Term.subst0, Term.subst,
        Term.subst0_map, Term.Subst.ext, Term.app2, Term.weaken_subst_ext,
        Term.weaken_subst0, subst_subst0_map_weaken,
        add_closed_subst, mul_closed_subst, monus_closed_subst, abs_diff_closed_subst,
        pd_closed_subst, sg_bar_closed_subst, sg_closed_subst, isEven_closed_subst,
        isOdd_closed_subst, triag_closed_subst, exp2_closed_subst, ite_nat_closed_subst,
        geq_closed_subst, max_closed_subst, min_closed_subst, pair_closed_subst,
        inv_triag_closed_subst, fst_pair_closed_subst, snd_pair_closed_subst,
        div2_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
        rat_sign_closed_subst, rat_encode_closed_subst, neg_Q_closed_subst,
        add_Q_closed_subst, sub_Q_closed_subst, mul_Q_closed_subst, abs_Q_closed_subst,
        lt_Q_dec_closed_subst, le_Q_dec_closed_subst, eq_Q_dec_closed_subst,
        encode_nat_Q_closed_subst, pow2neg_Q_closed_subst, zero_Q_closed_subst,
        one_Q_closed_subst] using $h)

/-- `eq_Q_trans` instantiated at three explicit terms.

Stating the resulting formula once, here, is what keeps the three nested `forall_ax`
substitutions from being `whnf`'d blindly through `eq_Q_dec` at every use site — which is
what exhausts the heartbeat budget. Use this rather than chaining `.forall_ax` inline. -/
def eq_Q_trans_inst (adm : AdmissibleEqX EqX) (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (eq_Q x y ∧ᶠ eq_Q y z →ᶠ eq_Q x z) := by
  have h := Derivable.mp (Derivable.mp (Derivable.mp
    (eq_Q_trans (adm := adm) (al := al) (Premises := Premises) (Γ := Γ))
    (.forall_ax x)) (.forall_ax y)) (.forall_ax z)
  q_norm using h


-- ── Additive group ─────────────────────────────────────────────────────────

/-- geq(x, y) =₀ sg_bar(y ∸ x). -/
private def geq_unfold (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.geq x y) (.app Term.sg_bar (Term.app2 Term.monus y x))) :=
  lam2_correct_nf adm
    (.app Term.sg_bar (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))))
    x y (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        sg_bar_closed_subst, monus_closed_subst, weaken_subst0_eta])

/-- ⊢ ∀a,b. eq_Q(add_Q(a, b), add_Q(b, a)) -/
def add_Q_comm :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_Q (.var .vz) (.var (.vs .vz)))))) :=
  let a : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let b : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let sb := Term.app Term.rat_sign b
  let pa := Term.app Term.rat_num a
  let pb := Term.app Term.rat_num b
  let da := Term.app Term.rat_den a
  let db := Term.app Term.rat_den b
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let n₁ := Term.var (.vs .vz)
    let n₂ := Term.var .vz
    let s₁ := Term.app Term.rat_sign n₁
    let s₂ := Term.app Term.rat_sign n₂
    let p₁ := Term.app Term.rat_num n₁
    let p₂ := Term.app Term.rat_num n₂
    let d₁ := Term.app Term.rat_den n₁
    let d₂ := Term.app Term.rat_den n₂
    let ac := Term.app2 Term.mul p₁ d₂
    let bc := Term.app2 Term.mul p₂ d₁
    let same := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
    Term.app3 Term.rat_encode
      (Term.app3 Term.ite_nat same s₁
        (Term.app3 Term.ite_nat (Term.app2 Term.geq ac bc) s₁ s₂))
      (Term.app3 Term.ite_nat same (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))
      (Term.app Term.pd (Term.app2 Term.mul d₁ d₂))
  have body_eq : (Term.add_Q : Term F (Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  let ac_ab := Term.app2 Term.mul pa db
  let bc_ab := Term.app2 Term.mul pb da
  let same_ab := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sb)
  let sign_ab := Term.app3 Term.ite_nat same_ab sa
    (Term.app3 Term.ite_nat (Term.app2 Term.geq ac_ab bc_ab) sa sb)
  let num_ab := Term.app3 Term.ite_nat same_ab
    (Term.app2 Term.add ac_ab bc_ab)
    (Term.app2 Term.abs_diff ac_ab bc_ab)
  let den_ab := Term.app Term.pd (Term.app2 Term.mul da db)
  let same_ba := Term.app Term.sg_bar (Term.app2 Term.abs_diff sb sa)
  let sign_ba := Term.app3 Term.ite_nat same_ba sb
    (Term.app3 Term.ite_nat (Term.app2 Term.geq bc_ab ac_ab) sb sa)
  let num_ba := Term.app3 Term.ite_nat same_ba
    (Term.app2 Term.add bc_ab ac_ab)
    (Term.app2 Term.abs_diff bc_ab ac_ab)
  let den_ba := Term.app Term.pd (Term.app2 Term.mul db da)
  have nf_ab : (body.subst0 (b.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_ab num_ab den_ab := by
    simp only [body, a, b, sign_ab, num_ab, den_ab, same_ab, ac_ab, bc_ab,
      sa, sb, pa, pb, da, db,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, rat_sign_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst,
      abs_diff_closed_subst, add_closed_subst, mul_closed_subst,
      geq_closed_subst, pd_closed_subst, weaken_subst0_eta]
  have nf_ba : (body.subst0 (a.weaken)).subst0 b =
      Term.app3 Term.rat_encode sign_ba num_ba den_ba := by
    simp only [body, a, b, sign_ba, num_ba, den_ba, same_ba,
      sa, sb, pa, pb, da, db, ac_ab, bc_ab,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, rat_sign_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst,
      abs_diff_closed_subst, add_closed_subst, mul_closed_subst,
      geq_closed_subst, pd_closed_subst, weaken_subst0_eta]
  let unfold_ab := body_eq ▸ lam2_correct_nf adm body a b nf_ab
  let unfold_ba := body_eq ▸ lam2_correct_nf adm body b a nf_ba
  let h_same := sg_bar_congr (abs_diff_comm adm sa sb)
  let h_num : Derivable F EqX al Premises (Formula.eq0 num_ab num_ba) :=
    let h_sum := add_comm adm ac_ab bc_ab
    let h_diff := abs_diff_comm adm ac_ab bc_ab
    let h_x := ite_nat_congr_x (b := same_ab) (y := Term.app2 Term.abs_diff ac_ab bc_ab) h_sum
    let h_y := ite_nat_congr_y (b := same_ab) (x := Term.app2 Term.add bc_ab ac_ab) h_diff
    let h_xy := Derivable.mp (Derivable.mp h_y (Derivable.mp h_x and_intro)) .trans0
    Derivable.mp (Derivable.mp (ite_nat_congr_b (x := Term.app2 Term.add bc_ab ac_ab)
      (y := Term.app2 Term.abs_diff bc_ab ac_ab) h_same) (Derivable.mp h_xy and_intro)) .trans0
  let h_den : Derivable F EqX al Premises (Formula.eq0 den_ab den_ba) :=
    pd_congr (mul_comm adm da db)
  let result_ab := Term.app2 Term.add_Q a b
  let result_ba := Term.app2 Term.add_Q b a
  let rn_ab := Term.app Term.rat_num result_ab
  let rd_ab := Term.app Term.rat_den result_ab
  let rs_ab := Term.app Term.rat_sign result_ab
  let rn_ba := Term.app Term.rat_num result_ba
  let rd_ba := Term.app Term.rat_den result_ba
  let rs_ba := Term.app Term.rat_sign result_ba
  let h_rn_ab : Derivable F EqX al Premises (Formula.eq0 rn_ab num_ab) :=
    .mp (.mp (rat_num_rat_encode adm sign_ab num_ab den_ab
      (isEven_cases adm sign_ab)) (.mp (rat_num_congr unfold_ab) and_intro)) .trans0
  let h_rn_ba : Derivable F EqX al Premises (Formula.eq0 rn_ba num_ba) :=
    .mp (.mp (rat_num_rat_encode adm sign_ba num_ba den_ba
      (isEven_cases adm sign_ba)) (.mp (rat_num_congr unfold_ba) and_intro)) .trans0
  let h_rd_ab_nf : Derivable F EqX al Premises
      (Formula.eq0 rd_ab (.app .succ den_ab)) :=
    .mp (.mp (rat_den_rat_encode adm sign_ab num_ab den_ab)
      (.mp (rat_den_congr unfold_ab) and_intro)) .trans0
  let h_rd_ba_nf : Derivable F EqX al Premises
      (Formula.eq0 rd_ba (.app .succ den_ba)) :=
    .mp (.mp (rat_den_rat_encode adm sign_ba num_ba den_ba)
      (.mp (rat_den_congr unfold_ba) and_intro)) .trans0
  let h_sden_eq : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ den_ab) (.app .succ den_ba)) :=
    qfer_no_premise_nat_nf h_den (r := .app .succ (.var .vz))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, pd_closed_subst, mul_closed_subst,
          rat_den_closed_subst])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, pd_closed_subst, mul_closed_subst,
          rat_den_closed_subst])
  let h_rd_eq : Derivable F EqX al Premises (Formula.eq0 rd_ab rd_ba) :=
    .mp (.mp (.mp h_rd_ba_nf .sym0) (.mp (.mp (.mp h_sden_eq (.mp h_rd_ab_nf and_intro)) .trans0) and_intro)) .trans0
  let h_rn_eq : Derivable F EqX al Premises (Formula.eq0 rn_ab rn_ba) :=
    .mp (.mp (.mp h_rn_ba .sym0)
      (.mp (.mp (.mp h_num (.mp h_rn_ab and_intro)) .trans0) and_intro)) .trans0
  let h_lhs := mul_congr_l h_rn_eq rd_ba
  let h_rhs := mul_congr_r rn_ba h_rd_eq
  let h_prod_eq : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul rn_ab rd_ba)
        (Term.app2 Term.mul rn_ba rd_ab)) :=
    Derivable.mp (Derivable.mp (Derivable.mp h_rhs .sym0) (Derivable.mp h_lhs and_intro)) .trans0
  let h_cross : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn_ab rd_ba) (Term.app2 Term.mul rn_ba rd_ab)) .zero) :=
    Derivable.mp h_prod_eq
      (Derivable.mp (abs_diff_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
  let sg_nn := Term.app Term.sg (Term.app2 Term.add num_ab num_ab)
  let abs_rs := Term.app2 Term.abs_diff rs_ab rs_ba
  let h_sign_mul_red : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs
        (Term.app Term.sg (Term.app2 Term.add rn_ab rn_ba)))
        (Term.app2 Term.mul abs_rs sg_nn)) :=
    let h_rn_ba_num_ab : Derivable F EqX al Premises (Formula.eq0 rn_ba num_ab) :=
      Derivable.mp (Derivable.mp (Derivable.mp h_num .sym0)
        (Derivable.mp h_rn_ba and_intro)) .trans0
    mul_congr_r abs_rs (sg_congr
      (Derivable.mp (Derivable.mp (add_congr_r num_ab h_rn_ba_num_ab)
        (Derivable.mp (add_congr_l h_rn_ab rn_ba) and_intro)) .trans0))
  let h_num_disj : Derivable F EqX al Premises
      (Formula.eq0 num_ab .zero ∨ᶠ ¬ᶠFormula.eq0 num_ab .zero) :=
    eq0_decidable'.mp (.forall_ax num_ab)
  let b1_pp_zero : Derivable F EqX al Premises
      (Formula.eq0 num_ab .zero →ᶠ
       Formula.eq0 (Term.app2 Term.add num_ab num_ab) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.add (.var .vz) (.var .vz))
        (rs := Term.app2 Term.add num_ab num_ab) (rt := Term.app2 Term.add .zero .zero)
        (by rfl) (by rfl) I_comb
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, add_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, add_closed_subst]))
      (weaken_intro (add_zero_r adm .zero))) .trans0
  let b1_sg_zero : Derivable F EqX al Premises
      (Formula.eq0 num_ab .zero →ᶠ Formula.eq0 sg_nn .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app Term.sg (.var .vz))
        (rs := Term.app Term.sg (Term.app2 Term.add num_ab num_ab)) (rt := Term.app Term.sg .zero)
        (by rfl) (by rfl) b1_pp_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst, Term.app2])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst]))
      (weaken_intro sg_zero)) .trans0
  let case_b1 : Derivable F EqX al Premises
      (Formula.eq0 num_ab .zero →ᶠ Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.mul abs_rs.weaken (.var .vz))
        (rs := Term.app2 Term.mul abs_rs sg_nn) (rt := Term.app2 Term.mul abs_rs .zero)
        (by rfl) (by rfl) b1_sg_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero adm _))) .trans0
  -- ═══════ Chain: sign_ab = sign_ba → mul(abs_rs, sg_nn) = 0 ═══════
  let enc_ab := Term.app3 Term.rat_encode sign_ab num_ab den_ab
  let enc_ba := Term.app3 Term.rat_encode sign_ba num_ba den_ba
  let sign_to_enc : Derivable F EqX al Premises
      (Formula.eq0 sign_ab sign_ba →ᶠ Formula.eq0 enc_ab enc_ba) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.rat_encode (.var .vz) (Term.weaken num_ab) (Term.weaken den_ab))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            rat_encode_closed_subst, weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            rat_encode_closed_subst, weaken_subst0_eta]))
      (weaken_intro (rat_encode_congr .refl0 h_num h_den)))
    .trans0
  let h1_enc := .syllogism (pair_h (weaken_intro unfold_ab) I_comb) .trans0
  let enc_to_result : Derivable F EqX al Premises
      (Formula.eq0 enc_ab enc_ba →ᶠ Formula.eq0 result_ab result_ba) :=
    .syllogism (pair_h h1_enc (weaken_intro (.mp unfold_ba .sym0))) .trans0
  let result_to_rs : Derivable F EqX al Premises
      (Formula.eq0 result_ab result_ba →ᶠ Formula.eq0 rs_ab rs_ba) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app Term.rat_sign (.var .vz))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, rat_sign_closed_subst]; rfl)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, rat_sign_closed_subst]; rfl)
  let rs_to_abs : Derivable F EqX al Premises
      (Formula.eq0 rs_ab rs_ba →ᶠ Formula.eq0 abs_rs .zero) :=
    .mp (abs_diff_eq_zero_iff adm rs_ab rs_ba) (.syllogism .and_perm .and_weak)
  let abs_to_mul : Derivable F EqX al Premises
      (Formula.eq0 abs_rs .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.mul (.var .vz) (Term.weaken sg_nn))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero_l adm sg_nn)))
    .trans0
  let sign_to_mul : Derivable F EqX al Premises
      (Formula.eq0 sign_ab sign_ba →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism sign_to_enc (.syllogism enc_to_result
      (.syllogism result_to_rs (.syllogism rs_to_abs abs_to_mul)))
  -- ═══════ Case A: same_ab = S0 → sign_ab = sign_ba ═══════
  let inner_ab := Term.app3 Term.ite_nat (Term.app2 Term.geq ac_ab bc_ab) sa sb
  let inner_ba := Term.app3 Term.ite_nat (Term.app2 Term.geq bc_ab ac_ab) sb sa
  let h_sign_ab_sa : Derivable F EqX al Premises
      (Formula.eq0 same_ab (.app .succ .zero) →ᶠ Formula.eq0 sign_ab sa) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sa) (Term.weaken inner_ab))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_one (adm := adm) sa inner_ab)))
    .trans0
  let h_same_ba_S0 : Derivable F EqX al Premises
      (Formula.eq0 same_ab (.app .succ .zero) →ᶠ Formula.eq0 same_ba (.app .succ .zero)) :=
    .syllogism (pair_h (weaken_intro (.mp h_same .sym0)) I_comb) .trans0
  let h_sign_ba_sb : Derivable F EqX al Premises
      (Formula.eq0 same_ba (.app .succ .zero) →ᶠ Formula.eq0 sign_ba sb) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sb) (Term.weaken inner_ba))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_one (adm := adm) sb inner_ba)))
    .trans0
  let h_sa_eq_sb : Derivable F EqX al Premises
      (Formula.eq0 same_ab (.app .succ .zero) →ᶠ Formula.eq0 sa sb) :=
    .syllogism (sg_bar_eq_S0_implies_zero (adm := adm) _)
      (.mp (abs_diff_eq_zero_iff adm sa sb) .and_weak)
  let caseA : Derivable F EqX al Premises
      (Formula.eq0 same_ab (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    let h_ab_sb := .syllogism (pair_h h_sign_ab_sa h_sa_eq_sb) .trans0
    let h_ba_sb := .syllogism h_same_ba_S0 h_sign_ba_sb
    .syllogism (.syllogism (pair_h h_ab_sb (.syllogism h_ba_sb .sym0)) .trans0) sign_to_mul
  -- ═══════ Case B: same_ab = 0 → mul(abs_rs, sg_nn) = 0 ═══════
  -- When same_ab = 0: sign = inner (geq branch), num = abs_diff(ac,bc)
  let h_sign_ab_inner : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero →ᶠ Formula.eq0 sign_ab inner_ab) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sa) (Term.weaken inner_ab))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_zero (adm := adm) sa inner_ab))) .trans0
  let h_same_ba_zero : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero →ᶠ Formula.eq0 same_ba .zero) :=
    .syllogism (pair_h (weaken_intro (.mp h_same .sym0)) I_comb) .trans0
  let h_sign_ba_inner : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero →ᶠ Formula.eq0 sign_ba inner_ba) :=
    .syllogism h_same_ba_zero
      (.syllogism (pair_h
        (qfer_nat_nf (by rfl) (by rfl) I_comb
          (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sb) (Term.weaken inner_ba))
          (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
              ite_nat_closed_subst, weaken_subst0_eta]; rfl)
          (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
              ite_nat_closed_subst, weaken_subst0_eta]))
        (weaken_intro (ite_nat_zero (adm := adm) sb inner_ba))) .trans0)
  let h_num_ab_diff : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero →ᶠ
       Formula.eq0 num_ab (Term.app2 Term.abs_diff ac_ab bc_ab)) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz)
          (Term.weaken (Term.app2 Term.add ac_ab bc_ab))
          (Term.weaken (Term.app2 Term.abs_diff ac_ab bc_ab)))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, add_closed_subst, abs_diff_closed_subst,
            mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
            weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, add_closed_subst, abs_diff_closed_subst,
            mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
            weaken_subst0_eta]))
      (weaken_intro (ite_nat_zero (adm := adm)
        (Term.app2 Term.add ac_ab bc_ab) (Term.app2 Term.abs_diff ac_ab bc_ab)))) .trans0
  -- Relate inner values to sg_bar via geq_unfold
  let inner_ab_eq : Derivable F EqX al Premises
      (Formula.eq0 inner_ab (Term.app3 Term.ite_nat
        (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) sa sb)) :=
    ite_nat_congr_b (x := sa) (y := sb) (geq_unfold adm ac_ab bc_ab)
  let inner_ba_eq : Derivable F EqX al Premises
      (Formula.eq0 inner_ba (Term.app3 Term.ite_nat
        (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) sb sa)) :=
    ite_nat_congr_b (x := sb) (y := sa) (geq_unfold adm bc_ab ac_ab)
  -- From monus=0, derive sg_bar=S0
  let monus_to_sgbar_S0 (x y : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat) :
      Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.monus x y) .zero →ᶠ
         Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus x y)) (.app .succ .zero)) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := .app Term.sg_bar (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst]))
      (weaken_intro sg_bar_zero)) .trans0
  -- ite evaluations from sg_bar values
  -- sg_bar(bc∸ac)=0 → ite(sg_bar(bc∸ac), sa, sb) = sb
  let h_ite_ab_zero : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) .zero →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat
         (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) sa sb) sb) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sa) (Term.weaken sb))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_zero (adm := adm) sa sb))) .trans0
  -- sg_bar(bc∸ac)=S0 → ite(sg_bar(bc∸ac), sa, sb) = sa
  let h_ite_ab_S0 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat
         (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) sa sb) sa) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sa) (Term.weaken sb))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_one (adm := adm) sa sb))) .trans0
  -- sg_bar(ac∸bc)=S0 → ite(sg_bar(ac∸bc), sb, sa) = sb
  let h_ite_ba_S0 : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat
         (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) sb sa) sb) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sb) (Term.weaken sa))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_one (adm := adm) sb sa))) .trans0
  -- sg_bar(ac∸bc)=0 → ite(sg_bar(ac∸bc), sb, sa) = sa
  let h_ite_ba_zero : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) .zero →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat
         (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) sb sa) sa) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app3 Term.ite_nat (.var .vz) (Term.weaken sb) (Term.weaken sa))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3,
            ite_nat_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_zero (adm := adm) sb sa))) .trans0
  -- Derived: conditional inner value evaluations
  -- sg_bar(bc∸ac)=0 → inner_ab = sb
  let h_inner_ab_sb : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) .zero →ᶠ
       Formula.eq0 inner_ab sb) :=
    .syllogism (pair_h (weaken_intro inner_ab_eq) h_ite_ab_zero) .trans0
  -- bc∸ac=0 → sg_bar(bc∸ac)=S0 → inner_ab = sa
  let h_inner_ab_sa_from_mon_ba : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus bc_ab ac_ab) .zero →ᶠ
       Formula.eq0 inner_ab sa) :=
    .syllogism (pair_h (weaken_intro inner_ab_eq) (.syllogism (monus_to_sgbar_S0 bc_ab ac_ab) h_ite_ab_S0)) .trans0
  -- ac∸bc=0 → sg_bar(ac∸bc)=S0 → inner_ba = sb
  let h_inner_ba_sb_from_mon_ab : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus ac_ab bc_ab) .zero →ᶠ
       Formula.eq0 inner_ba sb) :=
    .syllogism (pair_h (weaken_intro inner_ba_eq) (.syllogism (monus_to_sgbar_S0 ac_ab bc_ab) h_ite_ba_S0)) .trans0
  -- sg_bar(ac∸bc)=0 → inner_ba = sa
  let h_inner_ba_sa : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) .zero →ᶠ
       Formula.eq0 inner_ba sa) :=
    .syllogism (pair_h (weaken_intro inner_ba_eq) h_ite_ba_zero) .trans0
  -- ── Sub-case B1: same_ab=0 ∧ ac∸bc=0 ──
  -- B1a: ... ∧ sg_bar(bc∸ac)=S0 → both monus 0 → ac=bc → num=0
  let caseB1a : Derivable F EqX al Premises
      ((Formula.eq0 same_ab .zero ∧ᶠ
        Formula.eq0 (Term.app2 Term.monus ac_ab bc_ab) .zero) ∧ᶠ
       Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    let get_same := Derivable.syllogism .and_weak .and_weak
    let get_mon_ab := Derivable.syllogism .and_weak and_proj2
    let get_sgbar := and_proj2
    let h_mon_ba := .syllogism get_sgbar (sg_bar_eq_S0_implies_zero (adm := adm) _)
    let h_ac_eq := .syllogism (pair_h get_mon_ab h_mon_ba) (monus_eq_zero_antisym adm ac_ab bc_ab)
    let h_diff := .syllogism h_ac_eq
      (.mp (abs_diff_eq_zero_iff adm ac_ab bc_ab) (.syllogism .and_perm .and_weak))
    let h_num := .syllogism (pair_h (.syllogism get_same h_num_ab_diff) h_diff) .trans0
    .syllogism h_num case_b1
  -- B1b: ... ∧ sg_bar(bc∸ac)=0 → sign_ab=sb=sign_ba → sign_to_mul
  let caseB1b : Derivable F EqX al Premises
      ((Formula.eq0 same_ab .zero ∧ᶠ
        Formula.eq0 (Term.app2 Term.monus ac_ab bc_ab) .zero) ∧ᶠ
       Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab)) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    let get_same := Derivable.syllogism .and_weak .and_weak
    let get_mon_ab := Derivable.syllogism .and_weak and_proj2
    let get_sgbar := and_proj2
    let h_sab := .syllogism
      (pair_h (.syllogism get_same h_sign_ab_inner) (.syllogism get_sgbar h_inner_ab_sb)) .trans0
    let h_sba := .syllogism
      (pair_h (.syllogism get_same h_sign_ba_inner) (.syllogism get_mon_ab h_inner_ba_sb_from_mon_ab)) .trans0
    .syllogism (.syllogism (pair_h h_sab (.syllogism h_sba .sym0)) .trans0) sign_to_mul
  let caseB1 : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus ac_ab bc_ab) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism
      (pair_h I_comb (weaken_intro (sg_bar_cases adm (Term.app2 Term.monus bc_ab ac_ab))))
      (.syllogism and_or_dist (or_elim_rule caseB1a caseB1b))
  -- ── Sub-case B2: same_ab=0 ∧ bc∸ac=0 ──
  -- B2a: ... ∧ sg_bar(ac∸bc)=S0 → both monus 0 → ac=bc → num=0
  let caseB2a : Derivable F EqX al Premises
      ((Formula.eq0 same_ab .zero ∧ᶠ
        Formula.eq0 (Term.app2 Term.monus bc_ab ac_ab) .zero) ∧ᶠ
       Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    let get_same := Derivable.syllogism .and_weak .and_weak
    let get_mon_ba := Derivable.syllogism .and_weak and_proj2
    let get_sgbar := and_proj2
    let h_mon_ab := .syllogism get_sgbar (sg_bar_eq_S0_implies_zero (adm := adm) _)
    let h_ac_eq := .syllogism (pair_h h_mon_ab get_mon_ba) (monus_eq_zero_antisym adm ac_ab bc_ab)
    let h_diff := .syllogism h_ac_eq
      (.mp (abs_diff_eq_zero_iff adm ac_ab bc_ab) (.syllogism .and_perm .and_weak))
    let h_num := .syllogism (pair_h (.syllogism get_same h_num_ab_diff) h_diff) .trans0
    .syllogism h_num case_b1
  -- B2b: ... ∧ sg_bar(ac∸bc)=0 → sign_ab=sa=sign_ba → sign_to_mul
  let caseB2b : Derivable F EqX al Premises
      ((Formula.eq0 same_ab .zero ∧ᶠ
        Formula.eq0 (Term.app2 Term.monus bc_ab ac_ab) .zero) ∧ᶠ
       Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab)) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    let get_same := Derivable.syllogism .and_weak .and_weak
    let get_mon_ba := Derivable.syllogism .and_weak and_proj2
    let get_sgbar := and_proj2
    let h_sab := .syllogism
      (pair_h (.syllogism get_same h_sign_ab_inner) (.syllogism get_mon_ba h_inner_ab_sa_from_mon_ba)) .trans0
    let h_sba := .syllogism
      (pair_h (.syllogism get_same h_sign_ba_inner) (.syllogism get_sgbar h_inner_ba_sa)) .trans0
    .syllogism (.syllogism (pair_h h_sab (.syllogism h_sba .sym0)) .trans0) sign_to_mul
  let caseB2 : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus bc_ab ac_ab) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism
      (pair_h I_comb (weaken_intro (sg_bar_cases adm (Term.app2 Term.monus ac_ab bc_ab))))
      (.syllogism and_or_dist (or_elim_rule caseB2a caseB2b))
  -- Combine B1 + B2 via monus_disjunct
  let caseB : Derivable F EqX al Premises
      (Formula.eq0 same_ab .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .syllogism
      (pair_h I_comb (weaken_intro (monus_disjunct adm ac_ab bc_ab)))
      (.syllogism and_or_dist (or_elim_rule caseB1 caseB2))
  -- ═══════ Final assembly ═══════
  let h_cases : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) :=
    .mp (sg_bar_cases adm (Term.app2 Term.abs_diff sa sb))
      (or_elim_rule caseA caseB)
  let h_sign_zero : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs
        (Term.app Term.sg (Term.app2 Term.add rn_ab rn_ba))) .zero) :=
    .mp (.mp h_cases (.mp h_sign_mul_red and_intro)) .trans0
  univ_gen (univ_gen (eq_Q_from_components adm h_cross h_sign_zero))


/-- `add_Q_comm` instantiated at two explicit terms, with the resulting formula stated.
See `q_norm` for why the inline `.forall_ax` chain is not affordable. -/
def add_Q_comm_inst (adm : AdmissibleEqX EqX) (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (eq_Q (Term.app2 Term.add_Q x y) (Term.app2 Term.add_Q y x)) := by
  have h := Derivable.mp (Derivable.mp
    (add_Q_comm (adm := adm) (al := al) (Premises := Premises) (Γ := Γ)) (.forall_ax x))
    (.forall_ax y)
  q_norm using h

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
  let a : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let pa := Term.app Term.rat_num a
  let da := Term.app Term.rat_den a
  let zero := (Term.zero_Q : Term F (Ty.nat :: Γ) Ty.nat)
  let sz := Term.app Term.rat_sign zero
  let pz := Term.app Term.rat_num zero
  let dz := Term.app Term.rat_den zero
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let n₁ := Term.var (.vs .vz)
    let n₂ := Term.var .vz
    let s₁ := Term.app Term.rat_sign n₁
    let s₂ := Term.app Term.rat_sign n₂
    let p₁ := Term.app Term.rat_num n₁
    let p₂ := Term.app Term.rat_num n₂
    let d₁ := Term.app Term.rat_den n₁
    let d₂ := Term.app Term.rat_den n₂
    let ac := Term.app2 Term.mul p₁ d₂
    let bc := Term.app2 Term.mul p₂ d₁
    let same := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
    Term.app3 Term.rat_encode
      (Term.app3 Term.ite_nat same s₁
        (Term.app3 Term.ite_nat (Term.app2 Term.geq ac bc) s₁ s₂))
      (Term.app3 Term.ite_nat same (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))
      (Term.app Term.pd (Term.app2 Term.mul d₁ d₂))
  have body_eq : (Term.add_Q : Term F (Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  let same_nf := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sz)
  let a_cross := Term.app2 Term.mul pa dz
  let b_cross := Term.app2 Term.mul pz da
  let sign_nf := Term.app3 Term.ite_nat same_nf sa
    (Term.app3 Term.ite_nat (Term.app2 Term.geq a_cross b_cross) sa sz)
  let num_nf := Term.app3 Term.ite_nat same_nf
    (Term.app2 Term.add a_cross b_cross)
    (Term.app2 Term.abs_diff a_cross b_cross)
  let den_nf := Term.app Term.pd (Term.app2 Term.mul da dz)
  have nf : (body.subst0 (zero.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_nf num_nf den_nf := by
    simp only [body, a, zero, sign_nf, num_nf, den_nf, same_nf, a_cross, b_cross,
      sa, sz, pa, pz, da, dz,
      Term.zero_Q, Term.pair, Term.subst0, Term.subst, Term.subst0_map,
      Term.app3, Term.app2, Term.ofNat,
      rat_encode_closed_subst, rat_sign_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst,
      abs_diff_closed_subst, add_closed_subst, mul_closed_subst,
      geq_closed_subst, pd_closed_subst, weaken_subst0_eta]
  let h_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add_Q a zero)
        (Term.app3 Term.rat_encode sign_nf num_nf den_nf)) :=
    body_eq ▸ lam2_correct_nf adm body a zero nf
  -- zero_Q component values
  let hsz : Derivable F EqX al Premises
      (Formula.eq0 sz (.app .succ .zero)) :=
    rat_sign_zero_Q (adm := adm)
  let hpz : Derivable F EqX al Premises
      (Formula.eq0 pz .zero) :=
    rat_num_zero_Q (adm := adm)
  let hdz : Derivable F EqX al Premises
      (Formula.eq0 dz (.app .succ .zero)) :=
    rat_den_zero_Q (adm := adm)
  -- a_cross = pa * dz =₀ pa * S0 =₀ pa
  let h_ac : Derivable F EqX al Premises (Formula.eq0 a_cross pa) :=
    .mp (.mp (mul_one_r adm pa) (.mp (mul_congr_r pa hdz) and_intro)) .trans0
  -- b_cross = pz * da =₀ 0 * da =₀ 0
  let h_bc : Derivable F EqX al Premises (Formula.eq0 b_cross .zero) :=
    .mp (.mp (mul_zero_l adm da) (.mp (mul_congr_l hpz da) and_intro)) .trans0
  -- num_nf: ite(same, ac+bc, |ac-bc|) = ite(same, pa, pa) = pa
  let h_sum : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add a_cross b_cross) pa) :=
    .mp (.mp (add_zero_r adm pa)
      (.mp (.mp (.mp (add_congr_r pa h_bc) (.mp (add_congr_l h_ac b_cross) and_intro)) .trans0)
        and_intro)) .trans0
  let h_diff : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff a_cross b_cross) pa) :=
    .mp (.mp (abs_diff_zero_r adm pa)
      (.mp (.mp (.mp (abs_diff_congr_r pa h_bc)
        (.mp (abs_diff_congr_l h_ac b_cross) and_intro)) .trans0)
        and_intro)) .trans0
  let h_num : Derivable F EqX al Premises (Formula.eq0 num_nf pa) :=
    .mp (.mp (ite_nat_sg_bar_same adm _ pa)
      (.mp (.mp (.mp (ite_nat_congr_y (b := same_nf) (x := pa) h_diff)
        (.mp (ite_nat_congr_x (b := same_nf) (y := Term.app2 Term.abs_diff a_cross b_cross) h_sum) and_intro)) .trans0)
        and_intro)) .trans0
  -- sign_nf: ite(same, sa, ite(geq(ac,bc), sa, sz)) = ite(same, sa, sa) = sa
  let h_geq : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.geq a_cross b_cross) (.app .succ .zero)) :=
    .mp (.mp (geq_zero_r adm pa)
      (.mp (.mp (.mp (geq_congr_r pa h_bc) (.mp (geq_congr_l h_ac b_cross) and_intro)) .trans0)
        and_intro)) .trans0
  let h_inner : Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat (Term.app2 Term.geq a_cross b_cross) sa sz) sa) :=
    .mp (.mp (ite_nat_one adm sa sz) (.mp (ite_nat_congr_b (x := sa) (y := sz) h_geq) and_intro)) .trans0
  let h_sign_nf : Derivable F EqX al Premises (Formula.eq0 sign_nf sa) :=
    .mp (.mp (ite_nat_sg_bar_same adm _ sa) (.mp (ite_nat_congr_y (b := same_nf) (x := sa) h_inner) and_intro)) .trans0
  -- den_nf = pd(da * dz) =₀ pd(da * S0) =₀ pd(da)
  let h_den : Derivable F EqX al Premises (Formula.eq0 den_nf (Term.app Term.pd da)) :=
    pd_congr (.mp (.mp (mul_one_r adm da) (.mp (mul_congr_r da hdz) and_intro)) .trans0)
  -- S(den_nf) =₀ da
  let rat_den_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    .app .succ (.app Term.snd_pair (.var .vz))
  let h_da_unfold : Derivable F EqX al Premises
      (Formula.eq0 da (.app .succ (.app Term.snd_pair a))) :=
    lam_correct_nf rat_den_body a (by
      simp only [rat_den_body, a, Term.subst0, Term.subst, Term.subst0_map,
        snd_pair_closed_subst])
  let h_pd_da : Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.pd da) (.app Term.snd_pair a)) :=
    .mp (.mp (pd_succ adm (.app Term.snd_pair a))
      (.mp (pd_congr h_da_unfold) and_intro)) .trans0
  let h_s_pd_da : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app Term.pd da)) (.app .succ (.app Term.snd_pair a))) :=
    qfer_no_premise_nat_nf h_pd_da
      (r := .app .succ (.var .vz))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map])
  let h_s_pd_da_eq_da : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app Term.pd da)) da) :=
    .mp (.mp (.mp h_da_unfold .sym0) (.mp h_s_pd_da and_intro)) .trans0
  let h_s_den_nf : Derivable F EqX al Premises (Formula.eq0 (.app .succ den_nf) da) :=
    .mp (.mp h_s_pd_da_eq_da
      (.mp (qfer_no_premise_nat_nf h_den (r := .app .succ (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, pd_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, pd_closed_subst]))
        and_intro)) .trans0
  -- Result components
  let result := Term.app2 Term.add_Q a zero
  let rn := Term.app Term.rat_num result
  let rd := Term.app Term.rat_den result
  let rs := Term.app Term.rat_sign result
  -- rn =₀ pa
  let h_rn : Derivable F EqX al Premises (Formula.eq0 rn pa) :=
    .mp (.mp h_num (.mp (.mp (.mp (rat_num_rat_encode adm sign_nf num_nf den_nf
      (isEven_cases adm sign_nf)) (.mp (rat_num_congr h_unfold) and_intro)) .trans0)
      and_intro)) .trans0
  -- rd =₀ da
  let h_rd : Derivable F EqX al Premises (Formula.eq0 rd da) :=
    .mp (.mp h_s_den_nf (.mp (.mp (.mp (rat_den_rat_encode adm sign_nf num_nf den_nf)
      (.mp (rat_den_congr h_unfold) and_intro)) .trans0) and_intro)) .trans0
  -- Cross-product: |rn*da - pa*rd| =₀ 0
  let h_cross : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn da) (Term.app2 Term.mul pa rd)) .zero) :=
    .mp (.mp (abs_diff_self adm _) (.mp (.mp (.mp (abs_diff_congr_r _ (mul_congr_r pa h_rd))
      (.mp (abs_diff_congr_l (mul_congr_l h_rn da) _) and_intro)) .trans0) and_intro)) .trans0
  -- Sign condition: |rs - sa| * sg(rn + pa) =₀ 0
  let h_mul_red := mul_congr_r _ (sg_congr (add_congr_l h_rn pa))
  let sg_pp := Term.app Term.sg (Term.app2 Term.add pa pa)
  let abs_rs_sa := Term.app2 Term.abs_diff rs sa
  -- Case B1: pa=0 → sg(pa+pa)=0 → product=0
  let h_pa_disj := .mp eq0_decidable' (.forall_ax pa)
  let b1_pp_zero :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.add (.var .vz) (.var .vz))
        (rs := Term.app2 Term.add pa pa) (rt := Term.app2 Term.add .zero .zero)
        (by rfl) (by rfl) I_comb
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, add_closed_subst]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, add_closed_subst]))
      (weaken_intro (add_zero_r adm .zero))) .trans0
  let b1_sg_zero :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app Term.sg (.var .vz))
        (rs := Term.app Term.sg (Term.app2 Term.add pa pa)) (rt := Term.app Term.sg .zero)
        (by rfl) (by rfl) b1_pp_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst, add_closed_subst, Term.app2]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, sg_closed_subst]))
      (weaken_intro sg_zero)) .trans0
  let case_b1 :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.mul abs_rs_sa.weaken (.var .vz))
        (rs := Term.app2 Term.mul abs_rs_sa sg_pp) (rt := Term.app2 Term.mul abs_rs_sa .zero)
        (by rfl) (by rfl) b1_sg_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            add_Q_closed_subst, sg_closed_subst, add_closed_subst,
            rat_num_closed_subst, weaken_subst0_eta]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            add_Q_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero adm _))) .trans0
  -- Case B2: ¬(pa=0) → need |rs - sa| = 0
  let S0 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ .zero
  let ie_fpa := Term.app Term.isEven (Term.app Term.fst_pair a)
  let h_sa_unfold : Derivable F EqX al Premises (Formula.eq0 sa ie_fpa) :=
    lam_correct_nf (Term.app Term.isEven (Term.app Term.fst_pair (.var .vz)) :
      Term F (Ty.nat :: Ty.nat :: Γ) _) a (by
      simp only [Term.subst0, Term.subst, Term.subst0_map,
        isEven_closed_subst, fst_pair_closed_subst]; rfl)
  let h_ie := isEven_cases adm (Term.app Term.fst_pair a)
  let h_sa_cases : Derivable F EqX al Premises
      (Formula.eq0 sa S0 ∨ᶠ Formula.eq0 sa .zero) :=
    let lift_case (v : Term F (Ty.nat :: Γ) Ty.nat) :
        Derivable F EqX al Premises (Formula.eq0 ie_fpa v →ᶠ Formula.eq0 sa v) :=
      .syllogism (pair_h (weaken_intro h_sa_unfold) I_comb) .trans0
    .mp h_ie (or_elim_rule (.syllogism (lift_case _) .or_weak) (.syllogism (lift_case _) or_inr))
  -- h_rs_enc = rat_sign(rat_encode(sign_nf, num_nf, den_nf))
  let h_rs_enc := rat_sign_congr h_unfold
  -- lift: sa =₀ X → sign_nf =₀ X
  let lift_sign (X : Term F (Ty.nat :: Γ) Ty.nat) :
      Derivable F EqX al Premises (Formula.eq0 sa X →ᶠ Formula.eq0 sign_nf X) :=
    .syllogism (pair_h (weaken_intro h_sign_nf) I_comb) .trans0
  -- Sub-case sa =₀ S0:
  let h_isE_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.isEven S0) .zero) :=
    let step1 := isEven_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    let step2 := sg_bar_congr (isEven_zero (Γ := Ty.nat :: Γ))
    let step3 := sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    .mp (.mp step3 (.mp (.mp (.mp step2 (.mp step1 and_intro)) .trans0) and_intro)) .trans0
  let h_pos := rat_sign_rat_encode_pos adm S0 num_nf den_nf h_isE_S0
  let h_rs_cond_S0 := qfer_nat_nf (by rfl) (by rfl) (lift_sign S0)
    (r := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) num_nf.weaken den_nf.weaken))
    (rs := Term.app Term.rat_sign (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
    (rt := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.app .succ .zero) num_nf den_nf))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta]; rfl)
  let h_rs_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ Formula.eq0 rs S0) :=
    .syllogism (pair_h (weaken_intro h_rs_enc)
      (.syllogism (pair_h h_rs_cond_S0 (weaken_intro h_pos)) .trans0)) .trans0
  let h_abs_S0_S0 := abs_diff_self adm S0
  let h_abs_step1_S0 := qfer_nat_nf (by rfl) (by rfl) I_comb
    (r := Term.app2 Term.abs_diff rs.weaken (.var .vz))
    (rs := Term.app2 Term.abs_diff rs sa) (rt := Term.app2 Term.abs_diff rs S0)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, add_Q_closed_subst,
        weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, add_Q_closed_subst,
        weaken_subst0_eta])
  let h_abs_step2_S0 := qfer_nat_nf (by rfl) (by rfl) h_rs_S0
    (r := Term.app2 Term.abs_diff (.var .vz) S0.weaken)
    (rs := Term.app2 Term.abs_diff rs S0) (rt := Term.app2 Term.abs_diff S0 S0)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, add_Q_closed_subst,
        weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, weaken_subst0_eta])
  let h_abs_zero_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ Formula.eq0 abs_rs_sa .zero) :=
    .syllogism (pair_h h_abs_step1_S0 (.syllogism (pair_h h_abs_step2_S0
      (weaken_intro h_abs_S0_S0)) .trans0)) .trans0
  let h_product_from_abs : Derivable F EqX al Premises
      (Formula.eq0 abs_rs_sa .zero →ᶠ Formula.eq0 (Term.app2 Term.mul abs_rs_sa sg_pp) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.mul (.var .vz) sg_pp.weaken)
        (rs := Term.app2 Term.mul abs_rs_sa sg_pp) (rt := Term.app2 Term.mul .zero sg_pp)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, sg_closed_subst, add_closed_subst,
            rat_sign_closed_subst, add_Q_closed_subst, rat_num_closed_subst,
            weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, sg_closed_subst, add_closed_subst,
            rat_num_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero_l adm sg_pp))) .trans0
  let case_b2_sub1 := .syllogism h_abs_zero_S0 h_product_from_abs
  -- Sub-case sa =₀ 0 (under ¬(pa=0)):
  let h_ne_0_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (¬ᶠFormula.eq0 (Term.app2 Term.abs_diff .zero S0) .zero) :=
    let h_fwd := .mp (abs_diff_eq_zero_iff adm (.zero : Term F (Ty.nat :: Γ) _) S0) .and_weak
    .syllogism (.syllogism h_fwd .sym0)
      (.mp .succ_ne_zero (.forall_ax (.zero : Term F (Ty.nat :: Γ) _)))
  let h_sgb_abs_0_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.abs_diff .zero S0)) .zero) :=
    .mp h_ne_0_S0 (.mp (sg_bar_eq_zero_iff adm (Term.app2 Term.abs_diff .zero S0))
      (.syllogism .and_perm .and_weak))
  let h_sgnf_when_0 : Derivable F EqX al Premises
      (Formula.eq0 sa .zero →ᶠ Formula.eq0 sign_nf .zero) := lift_sign .zero
  let two_nnf := Term.app2 Term.mul (Term.ofNat 2) num_nf
  let nnf := Term.app2 Term.add num_nf num_nf
  let h_rs_unfold_0 := rat_sign_rat_encode_unfold adm (.zero : Term F (Ty.nat :: Γ) _) num_nf den_nf
  let h_monus_ie0 := monus_congr_r two_nnf (isEven_zero (Γ := Ty.nat :: Γ))
  let h_two_nnf_eq_nnf :=
    let h_ms := mul_succ_l adm (.app .succ .zero : Term F (Ty.nat :: Γ) _) num_nf
    let h_m1 := .mp (.mp (mul_one_r adm num_nf)
      (.mp (mul_comm adm (.app .succ .zero) num_nf) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 num_nf) (.mp h_ms and_intro)) .trans0
  let h_monus_s0_0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.app2 Term.monus two_nnf (.app .succ .zero)) (.app Term.pd nnf)) :=
    let hm1 := monus_congr_l h_two_nnf_eq_nnf (.app .succ .zero)
    let hm2 := monus_succ adm nnf .zero
    let hm3 := pd_congr (monus_zero adm nnf)
    .mp (.mp hm3 (.mp (.mp (.mp hm2 (.mp hm1 and_intro)) .trans0) and_intro)) .trans0
  let h_ie_chain_0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf))
        (.app Term.isEven (.app Term.pd nnf))) :=
    .mp (.mp (isEven_congr (.mp (.mp h_monus_s0_0 (.mp h_monus_ie0 and_intro)) .trans0))
      (.mp h_rs_unfold_0 and_intro)) .trans0
  -- ¬(pa=0) → isEven(pd(nnf)) = 0
  let h_num_fwd : Derivable F EqX al Premises
      (Formula.eq0 num_nf .zero →ᶠ Formula.eq0 pa .zero) :=
    .syllogism (pair_h (weaken_intro (.mp h_num .sym0)) I_comb) .trans0
  let h_nnf_ne : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ ¬ᶠFormula.eq0 nnf .zero) :=
    .syllogism (contrapositive h_num_fwd)
      (contrapositive (.syllogism (.mp (add_eq_zero_iff adm num_nf num_nf) .and_weak) .and_weak))
  let h_nnf_succ : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 nnf (.app .succ (.app Term.pd nnf))) :=
    .syllogism h_nnf_ne (ne_zero_eq_succ_pd adm nnf)
  let h_ie_nnf_eq : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven nnf) (.app Term.isEven (.app .succ (.app Term.pd nnf)))) :=
    qfer_nat_nf (by rfl) (by rfl) h_nnf_succ
      (r := .app Term.isEven (.var .vz))
      (rs := .app Term.isEven nnf)
      (rt := .app Term.isEven (.app .succ (.app Term.pd nnf)))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, add_closed_subst, rat_num_closed_subst,
          add_Q_closed_subst, Term.app2])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, pd_closed_subst, add_closed_subst,
          rat_num_closed_subst, add_Q_closed_subst, Term.app2])
  let h_ie_nnf_sgb : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven nnf)
         (.app Term.sg_bar (.app Term.isEven (.app Term.pd nnf)))) :=
    .syllogism (pair_h h_ie_nnf_eq (weaken_intro (isEven_succ adm (.app Term.pd nnf)))) .trans0
  let h_ie_pd_zero : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven (.app Term.pd nnf)) .zero) :=
    .syllogism
      (.syllogism (pair_h (.syllogism h_ie_nnf_sgb .sym0) (weaken_intro (isEven_double adm num_nf))) .trans0)
      (sg_bar_eq_S0_implies_zero adm (.app Term.isEven (.app Term.pd nnf)))
  let h_neg_rs : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf)) .zero) :=
    .syllogism (pair_h (weaken_intro h_ie_chain_0) h_ie_pd_zero) .trans0
  let h_rs_cond_0 := qfer_nat_nf (by rfl) (by rfl) h_sgnf_when_0
    (r := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) num_nf.weaken den_nf.weaken))
    (rs := Term.app Term.rat_sign (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
    (rt := Term.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
  let h_rs_0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ Formula.eq0 rs .zero) :=
    .syllogism (pair_h
      (.syllogism (pair_h (.syllogism .and_weak (weaken_intro h_rs_enc))
        (.syllogism and_proj2 h_rs_cond_0)) .trans0)
      (.syllogism .and_weak h_neg_rs)) .trans0
  let h_abs_zero_0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ Formula.eq0 abs_rs_sa .zero) :=
    .syllogism (.syllogism (pair_h h_rs_0 (.syllogism and_proj2 .sym0)) .trans0)
      (.mp (abs_diff_eq_zero_iff adm rs sa) (.syllogism .and_perm .and_weak))
  let case_b2_sub2 := .syllogism h_abs_zero_0 h_product_from_abs
  -- Assemble case B2
  let case_b2 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 (Term.app2 Term.mul abs_rs_sa sg_pp) .zero) :=
    .syllogism (pair_h I_comb (weaken_intro h_sa_cases))
      (.syllogism and_or_dist (or_elim_rule (.syllogism and_proj2 case_b2_sub1) case_b2_sub2))
  -- Final assembly
  let h_reduced := .mp h_pa_disj (or_elim_rule case_b1 case_b2)
  let h_sign : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs_sa
        (Term.app Term.sg (Term.app2 Term.add rn pa))) .zero) :=
    .mp (.mp h_reduced (.mp h_mul_red and_intro)) .trans0
  univ_gen (eq_Q_from_components adm h_cross h_sign)

/-- ⊢ ∀a. eq_Q(add_Q(a, neg_Q(a)), zero_Q) -/
-- Helper: unfold neg_Q(a) and derive component equalities
private def add_Q_neg_core :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var .vz)
                (Term.app Term.neg_Q (.var .vz)))
              Term.zero_Q)) :=
  let a : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let pa := Term.app Term.rat_num a
  let da := Term.app Term.rat_den a
  let na := Term.app Term.neg_Q a
  let sn := Term.app Term.rat_sign na
  let pn := Term.app Term.rat_num na
  let dn := Term.app Term.rat_den na
  -- ── Unfold neg_Q(a) ──
  let neg_Q_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 Term.rat_encode
      (Term.app2 Term.monus (.app .succ .zero)
        (.app Term.rat_sign (.var .vz)))
      (.app Term.rat_num (.var .vz))
      (.app Term.snd_pair (.var .vz))
  have neg_Q_eq : (Term.neg_Q : Term F (Ty.nat :: Γ) _) = Term.lam neg_Q_body := by rfl
  let na_sign := Term.app2 Term.monus (.app .succ .zero : Term F (Ty.nat :: Γ) _) sa
  let na_den := Term.app Term.snd_pair a
  have neg_Q_nf : neg_Q_body.subst0 a =
      Term.app3 Term.rat_encode na_sign pa na_den := by
    simp only [neg_Q_body, a, na_sign, na_den, sa, pa,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, monus_closed_subst, rat_sign_closed_subst,
      rat_num_closed_subst, snd_pair_closed_subst]
  let h_neg_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.neg_Q a) (Term.app3 Term.rat_encode na_sign pa na_den)) :=
    neg_Q_eq ▸ lam_correct_nf neg_Q_body a neg_Q_nf
  -- ── Unfold add_Q(a, neg_Q(a)) ──
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let n₁ := Term.var (.vs .vz)
    let n₂ := Term.var .vz
    let s₁ := Term.app Term.rat_sign n₁
    let s₂ := Term.app Term.rat_sign n₂
    let p₁ := Term.app Term.rat_num n₁
    let p₂ := Term.app Term.rat_num n₂
    let d₁ := Term.app Term.rat_den n₁
    let d₂ := Term.app Term.rat_den n₂
    let ac := Term.app2 Term.mul p₁ d₂
    let bc := Term.app2 Term.mul p₂ d₁
    let same := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
    Term.app3 Term.rat_encode
      (Term.app3 Term.ite_nat same s₁
        (Term.app3 Term.ite_nat (Term.app2 Term.geq ac bc) s₁ s₂))
      (Term.app3 Term.ite_nat same (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))
      (Term.app Term.pd (Term.app2 Term.mul d₁ d₂))
  have body_eq : (Term.add_Q : Term F (Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  let same_nf := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sn)
  let ac := Term.app2 Term.mul pa dn
  let bc := Term.app2 Term.mul pn da
  let sign_nf := Term.app3 Term.ite_nat same_nf sa
    (Term.app3 Term.ite_nat (Term.app2 Term.geq ac bc) sa sn)
  let num_nf := Term.app3 Term.ite_nat same_nf
    (Term.app2 Term.add ac bc)
    (Term.app2 Term.abs_diff ac bc)
  let den_nf := Term.app Term.pd (Term.app2 Term.mul da dn)
  have nf : (body.subst0 (na.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_nf num_nf den_nf := by
    simp only [body, a, na, sign_nf, num_nf, den_nf, same_nf, ac, bc,
      sa, sn, pa, pn, da, dn,
      Term.neg_Q, Term.pair, Term.subst0, Term.subst, Term.subst0_map,
      Term.app3, Term.app2, Term.ofNat,
      rat_encode_closed_subst, rat_sign_closed_subst, rat_num_closed_subst,
      rat_den_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst,
      abs_diff_closed_subst, add_closed_subst, mul_closed_subst,
      geq_closed_subst, pd_closed_subst, neg_Q_closed_subst, weaken_subst0_eta]
  let h_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add_Q a na)
        (Term.app3 Term.rat_encode sign_nf num_nf den_nf)) :=
    body_eq ▸ lam2_correct_nf adm body a na nf
  -- ── neg_Q component equalities ──
  -- pn =₀ pa
  let h_pn : Derivable F EqX al Premises (Formula.eq0 pn pa) :=
    .mp (.mp (rat_num_rat_encode adm na_sign pa na_den (isEven_cases adm na_sign))
      (.mp (rat_num_congr h_neg_unfold) and_intro)) .trans0
  -- dn =₀ S(snd_pair(a))
  let h_dn1 : Derivable F EqX al Premises
      (Formula.eq0 dn (.app .succ na_den)) :=
    .mp (.mp (rat_den_rat_encode adm na_sign pa na_den)
      (.mp (rat_den_congr h_neg_unfold) and_intro)) .trans0
  -- da =₀ S(snd_pair(a))
  let h_da1 : Derivable F EqX al Premises
      (Formula.eq0 da (.app .succ (.app Term.snd_pair a))) :=
    lam_correct_nf (.app .succ (.app Term.snd_pair (.var .vz))
      : Term F (Ty.nat :: Ty.nat :: Γ) _) a (by
      simp only [Term.subst0, Term.subst, Term.subst0_map, snd_pair_closed_subst])
  -- dn =₀ da
  let h_dn : Derivable F EqX al Premises (Formula.eq0 dn da) :=
    .mp (.mp (.mp h_da1 .sym0) (.mp h_dn1 and_intro)) .trans0
  -- ── Cross products equal ──
  let h_ac : Derivable F EqX al Premises (Formula.eq0 ac (Term.app2 Term.mul pa da)) :=
    mul_congr_r pa h_dn
  let h_bc : Derivable F EqX al Premises (Formula.eq0 bc (Term.app2 Term.mul pa da)) :=
    mul_congr_l h_pn da
  -- |ac - bc| =₀ 0
  let h_diff : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff ac bc) .zero) :=
    .mp (.mp (abs_diff_self adm _) (.mp (.mp (.mp (abs_diff_congr_r _ h_bc)
      (.mp (abs_diff_congr_l h_ac _) and_intro)) .trans0) and_intro)) .trans0
  -- ── num_nf =₀ 0 ──
  -- Step: num_nf =₀ ite(same_nf, ac+bc, 0)
  let h_num_ite : Derivable F EqX al Premises (Formula.eq0 num_nf
      (Term.app3 Term.ite_nat same_nf (Term.app2 Term.add ac bc) .zero)) :=
    ite_nat_congr_y (b := same_nf) (x := Term.app2 Term.add ac bc) h_diff
  -- pa=0 → pa*da =₀ 0
  let h_pa_da_zero : Derivable F EqX al Premises
      (Formula.eq0 pa .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul pa da) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.mul (.var .vz) da.weaken)
        (rs := Term.app2 Term.mul pa da)
        (rt := Term.app2 Term.mul .zero da)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, rat_den_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, rat_den_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero_l adm da))) .trans0
  -- pa=0 → pa*da + pa*da =₀ 0+0
  let h_sum_pa_da : Derivable F EqX al Premises
      (Formula.eq0 pa .zero →ᶠ
       Formula.eq0 (Term.app2 Term.add (Term.app2 Term.mul pa da) (Term.app2 Term.mul pa da))
         (Term.app2 Term.add .zero .zero)) :=
    qfer_nat_nf (by rfl) (by rfl) h_pa_da_zero
      (r := Term.app2 Term.add (.var .vz) (.var .vz))
      (rs := Term.app2 Term.add (Term.app2 Term.mul pa da) (Term.app2 Term.mul pa da))
      (rt := Term.app2 Term.add .zero .zero)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          add_closed_subst, mul_closed_subst, rat_num_closed_subst,
          rat_den_closed_subst])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          add_closed_subst])
  -- ac+bc =₀ pa*da + pa*da (unconditional)
  let h_sum_eq : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add ac bc)
        (Term.app2 Term.add (Term.app2 Term.mul pa da) (Term.app2 Term.mul pa da))) :=
    .mp (.mp (add_congr_r _ h_bc) (.mp (add_congr_l h_ac bc) and_intro)) .trans0
  -- pa=0 → ac+bc =₀ 0
  let h_sum_zero : Derivable F EqX al Premises
      (Formula.eq0 pa .zero →ᶠ Formula.eq0 (Term.app2 Term.add ac bc) .zero) :=
    .syllogism (pair_h (weaken_intro h_sum_eq) h_sum_pa_da)
      (.syllogism .trans0 (.syllogism (pair_h I_comb (weaken_intro (add_zero_r adm .zero))) .trans0))
  -- pa=0 → ite(same_nf, ac+bc, 0) =₀ ite(same_nf, 0, 0)
  let h_ite_zero : Derivable F EqX al Premises
      (Formula.eq0 pa .zero →ᶠ
       Formula.eq0 (Term.app3 Term.ite_nat same_nf (Term.app2 Term.add ac bc) .zero)
         (Term.app3 Term.ite_nat same_nf .zero .zero)) :=
    qfer_nat_nf (by rfl) (by rfl) h_sum_zero
      (r := Term.app3 Term.ite_nat same_nf.weaken (.var .vz) (.zero : Term F (Ty.nat :: Ty.nat :: Γ) _))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          ite_nat_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
          rat_sign_closed_subst, neg_Q_closed_subst, add_closed_subst,
          mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
          weaken_subst0_eta])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          ite_nat_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
          rat_sign_closed_subst, neg_Q_closed_subst,
          weaken_subst0_eta])
  -- ite(same_nf, 0, 0) =₀ 0 (unconditional, by ite_nat_sg_bar_same)
  let h_ite_same : Derivable F EqX al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat same_nf .zero .zero) .zero) :=
    ite_nat_sg_bar_same adm _ .zero
  -- Case B1: pa=0 → num_nf =₀ 0
  let case_b1 : Derivable F EqX al Premises
      (Formula.eq0 pa .zero →ᶠ Formula.eq0 num_nf .zero) :=
    .syllogism (pair_h (weaken_intro h_num_ite)
      (.syllogism (pair_h h_ite_zero (weaken_intro h_ite_same)) .trans0)) .trans0
  -- ── Case B2: pa≠0 → same_nf =₀ 0, then num_nf =₀ 0 ──
  let S0 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ .zero
  let h_sn_enc := rat_sign_congr h_neg_unfold
  -- sa cases
  let h_sa_unfold : Derivable F EqX al Premises (Formula.eq0 sa
      (.app Term.isEven (.app Term.fst_pair a))) :=
    lam_correct_nf (Term.app Term.isEven (Term.app Term.fst_pair (.var .vz)) :
      Term F (Ty.nat :: Ty.nat :: Γ) _) a (by
      simp only [Term.subst0, Term.subst, Term.subst0_map,
        isEven_closed_subst, fst_pair_closed_subst])
  let h_sa_vals : Derivable F EqX al Premises
      (Formula.eq0 sa S0 ∨ᶠ Formula.eq0 sa .zero) :=
    let lift_sa (v : Term F (Ty.nat :: Γ) Ty.nat) :
        Derivable F EqX al Premises
          (Formula.eq0 (.app Term.isEven (.app Term.fst_pair a)) v →ᶠ Formula.eq0 sa v) :=
      .syllogism (pair_h (weaken_intro h_sa_unfold) I_comb) .trans0
    .mp (isEven_cases adm (Term.app Term.fst_pair a))
      (or_elim_rule (.syllogism (lift_sa _) .or_weak) (.syllogism (lift_sa _) or_inr))
  -- sa=X → na_sign =₀ monus(S0, X)
  let lift_na_sign (X : Term F (Ty.nat :: Γ) Ty.nat) :
      Derivable F EqX al Premises (Formula.eq0 sa X →ᶠ
        Formula.eq0 na_sign (Term.app2 Term.monus S0 X)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := Term.app2 Term.monus S0.weaken (.var .vz))
      (rs := Term.app2 Term.monus S0 sa) (rt := Term.app2 Term.monus S0 X)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          monus_closed_subst, rat_sign_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          monus_closed_subst, weaken_subst0_eta])
  -- sa=X → sn =₀ rat_sign(rat_encode(monus(S0,X), pa, na_den))
  let lift_sn (X : Term F (Ty.nat :: Γ) Ty.nat) :
      Derivable F EqX al Premises (Formula.eq0 sa X →ᶠ
        Formula.eq0 sn (.app Term.rat_sign
          (Term.app3 Term.rat_encode (Term.app2 Term.monus S0 X) pa na_den))) :=
    .syllogism (pair_h (weaken_intro h_sn_enc) (qfer_nat_nf (by rfl) (by rfl) (lift_na_sign X)
      (r := .app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) pa.weaken na_den.weaken))
      (rs := .app Term.rat_sign (Term.app3 Term.rat_encode na_sign pa na_den))
      (rt := .app Term.rat_sign (Term.app3 Term.rat_encode (Term.app2 Term.monus S0 X) pa na_den))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst, monus_closed_subst,
          snd_pair_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst, monus_closed_subst,
          weaken_subst0_eta]))) .trans0
  -- ── Sub-case sa=0: sn =₀ S0, |0-S0| = S0, sg_bar(S0) = 0 ──
  -- isEven(S0) =₀ 0
  let h_isE_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.isEven S0) .zero) :=
    let step1 := isEven_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    let step2 := sg_bar_congr (isEven_zero (Γ := Ty.nat :: Γ))
    let step3 := sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    .mp (.mp step3 (.mp (.mp (.mp step2 (.mp step1 and_intro)) .trans0) and_intro)) .trans0
  -- rat_sign(rat_encode(S0, pa, na_den)) =₀ S0 (unconditional, positive case)
  let h_pos := rat_sign_rat_encode_pos adm S0 pa na_den h_isE_S0
  -- monus(S0, 0) =₀ S0
  let h_monus_S0_0 := monus_zero adm S0
  -- rat_sign(rat_encode(monus(S0,0), pa, na_den)) =₀ S0
  let h_enc_monus_0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode (Term.app2 Term.monus S0 .zero) pa na_den)) S0) :=
    .mp (.mp h_pos (.mp (qfer_no_premise_nat_nf h_monus_S0_0
      (r := .app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) pa.weaken na_den.weaken))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst, monus_closed_subst,
          snd_pair_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst,
          snd_pair_closed_subst, weaken_subst0_eta])) and_intro)) .trans0
  -- sa=0 → sn =₀ S0
  let h_sn_when_0 : Derivable F EqX al Premises
      (Formula.eq0 sa .zero →ᶠ Formula.eq0 sn S0) :=
    .syllogism (pair_h (lift_sn .zero) (weaken_intro h_enc_monus_0)) .trans0
  -- sa=0 → |sa-sn| =₀ S0 (chain: sa=0, sn=S0, |0-S0|=S0)
  let h_abs_0 : Derivable F EqX al Premises
      (Formula.eq0 sa .zero →ᶠ Formula.eq0 (Term.app2 Term.abs_diff sa sn) S0) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) h_sn_when_0
        (r := Term.app2 Term.abs_diff (.zero : Term F (Ty.nat :: Ty.nat :: Γ) _) (.var .vz))
        (rs := Term.app2 Term.abs_diff .zero sn)
        (rt := Term.app2 Term.abs_diff .zero S0)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, rat_sign_closed_subst, neg_Q_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, weaken_subst0_eta]))
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.abs_diff (.var .vz) sn.weaken)
        (rs := Term.app2 Term.abs_diff sa sn)
        (rt := Term.app2 Term.abs_diff .zero sn)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, rat_sign_closed_subst, neg_Q_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, rat_sign_closed_subst, neg_Q_closed_subst, weaken_subst0_eta])))
      (.syllogism (.syllogism .and_perm .trans0) (.syllogism (pair_h I_comb (weaken_intro (abs_diff_zero_l adm S0))) .trans0))
  -- sa=0 → same_nf =₀ 0
  let h_same_0 : Derivable F EqX al Premises
      (Formula.eq0 sa .zero →ᶠ Formula.eq0 same_nf .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) h_abs_0
        (r := .app Term.sg_bar (.var .vz))
        (rs := .app Term.sg_bar (Term.app2 Term.abs_diff sa sn))
        (rt := .app Term.sg_bar S0)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            neg_Q_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst, weaken_subst0_eta]))
      (weaken_intro (sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)))) .trans0
  -- ── Sub-case sa=S0: need pa≠0 → sn =₀ 0 ──
  -- rat_sign(rat_encode(0, pa, na_den)) chain (reproducing rat_sign_rat_encode_neg logic)
  let h_rs_unfold_S0 := rat_sign_rat_encode_unfold adm (.zero : Term F (Ty.nat :: Γ) _) pa na_den
  let two_pa := Term.app2 Term.mul (Term.ofNat 2) pa
  let ppa := Term.app2 Term.add pa pa
  let h_monus_ie0 := monus_congr_r two_pa (isEven_zero (Γ := Ty.nat :: Γ))
  let h_two_pa_eq_ppa :=
    let h_ms := mul_succ_l adm (.app .succ .zero : Term F (Ty.nat :: Γ) _) pa
    let h_m1 := .mp (.mp (mul_one_r adm pa)
      (.mp (mul_comm adm (.app .succ .zero) pa) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 pa) (.mp h_ms and_intro)) .trans0
  let h_monus_s0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.app2 Term.monus two_pa S0) (.app Term.pd ppa)) :=
    let hm1 := monus_congr_l h_two_pa_eq_ppa S0
    let hm2 := monus_succ adm ppa .zero
    let hm3 := pd_congr (monus_zero adm ppa)
    .mp (.mp hm3 (.mp (.mp (.mp hm2 (.mp hm1 and_intro)) .trans0) and_intro)) .trans0
  -- rat_sign(rat_encode(0, pa, na_den)) =₀ isEven(pd(ppa))
  let h_ie_chain : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero pa na_den))
        (.app Term.isEven (.app Term.pd ppa))) :=
    .mp (.mp (isEven_congr (.mp (.mp h_monus_s0 (.mp h_monus_ie0 and_intro)) .trans0))
      (.mp h_rs_unfold_S0 and_intro)) .trans0
  -- ¬(pa=0) → isEven(pd(ppa)) =₀ 0
  let h_ppa_ne : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ ¬ᶠFormula.eq0 ppa .zero) :=
    contrapositive (.syllogism (.mp (add_eq_zero_iff adm pa pa) .and_weak) .and_weak)
  let h_ppa_succ : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 ppa (.app .succ (.app Term.pd ppa))) :=
    .syllogism h_ppa_ne (ne_zero_eq_succ_pd adm ppa)
  let h_ie_ppa_eq : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven ppa) (.app Term.isEven (.app .succ (.app Term.pd ppa)))) :=
    qfer_nat_nf (by rfl) (by rfl) h_ppa_succ
      (r := .app Term.isEven (.var .vz))
      (rs := .app Term.isEven ppa)
      (rt := .app Term.isEven (.app .succ (.app Term.pd ppa)))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, add_closed_subst, rat_num_closed_subst, Term.app2])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, pd_closed_subst, add_closed_subst,
          rat_num_closed_subst, Term.app2])
  let h_ie_ppa_sgb : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven ppa)
         (.app Term.sg_bar (.app Term.isEven (.app Term.pd ppa)))) :=
    .syllogism (pair_h h_ie_ppa_eq (weaken_intro (isEven_succ adm (.app Term.pd ppa)))) .trans0
  let h_ie_pd_zero : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.isEven (.app Term.pd ppa)) .zero) :=
    .syllogism
      (.syllogism (pair_h (.syllogism h_ie_ppa_sgb .sym0) (weaken_intro (isEven_double adm pa))) .trans0)
      (sg_bar_eq_S0_implies_zero adm (.app Term.isEven (.app Term.pd ppa)))
  -- ¬(pa=0) → rat_sign(rat_encode(0, pa, na_den)) =₀ 0
  let h_neg_rs : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ
       Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero pa na_den)) .zero) :=
    .syllogism (pair_h (weaken_intro h_ie_chain) h_ie_pd_zero) .trans0
  -- monus(S0, S0) =₀ 0
  let h_monus_S0_S0 := monus_self adm S0
  -- rat_sign(rat_encode(monus(S0,S0), pa, na_den)) =₀ rat_sign(rat_encode(0, pa, na_den))
  let h_enc_monus_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode (Term.app2 Term.monus S0 S0) pa na_den))
        (.app Term.rat_sign (Term.app3 Term.rat_encode .zero pa na_den))) :=
    qfer_no_premise_nat_nf h_monus_S0_S0
      (r := .app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) pa.weaken na_den.weaken))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst, monus_closed_subst,
          snd_pair_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
          rat_sign_closed_subst, rat_encode_closed_subst,
          snd_pair_closed_subst, weaken_subst0_eta])
  -- ¬(pa=0) ∧ sa=S0 → sn =₀ 0
  -- Chain: sa=S0 → sn =₀ rat_sign(rat_encode(monus(S0,S0), pa, na_den)) =₀ rat_sign(rat_encode(0, pa, na_den))
  --        ¬(pa=0) → rat_sign(rat_encode(0, pa, na_den)) =₀ 0
  let h_sn_cond_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ Formula.eq0 sn
        (.app Term.rat_sign (Term.app3 Term.rat_encode .zero pa na_den))) :=
    .syllogism (pair_h (lift_sn S0) (weaken_intro h_enc_monus_S0)) .trans0
  let h_sn_when_S0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero ∧ᶠ Formula.eq0 sa S0 →ᶠ Formula.eq0 sn .zero) :=
    .syllogism (pair_h (.syllogism and_proj2 h_sn_cond_S0) (.syllogism .and_weak h_neg_rs)) .trans0
  -- ¬(pa=0) ∧ sa=S0 → |sa-sn| =₀ |S0-0| =₀ S0
  let h_abs_S0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero ∧ᶠ Formula.eq0 sa S0 →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff sa sn) S0) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) h_sn_when_S0
        (r := Term.app2 Term.abs_diff sa.weaken (.var .vz))
        (rs := Term.app2 Term.abs_diff sa sn)
        (rt := Term.app2 Term.abs_diff sa .zero)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, rat_sign_closed_subst, neg_Q_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            abs_diff_closed_subst, rat_sign_closed_subst, weaken_subst0_eta]))
      (.syllogism and_proj2
        (qfer_nat_nf (by rfl) (by rfl) I_comb
          (r := Term.app2 Term.abs_diff (.var .vz) (.zero : Term F (Ty.nat :: Ty.nat :: Γ) _))
          (rs := Term.app2 Term.abs_diff sa .zero)
          (rt := Term.app2 Term.abs_diff S0 .zero)
          (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
              abs_diff_closed_subst, rat_sign_closed_subst, weaken_subst0_eta])
          (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
              abs_diff_closed_subst, weaken_subst0_eta]))))
      (.syllogism .trans0 (.syllogism (pair_h I_comb (weaken_intro (abs_diff_zero_r adm S0))) .trans0))
  -- ¬(pa=0) ∧ sa=S0 → same_nf =₀ 0
  let h_same_S0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero ∧ᶠ Formula.eq0 sa S0 →ᶠ Formula.eq0 same_nf .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) h_abs_S0
        (r := .app Term.sg_bar (.var .vz))
        (rs := .app Term.sg_bar (Term.app2 Term.abs_diff sa sn))
        (rt := .app Term.sg_bar S0)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            neg_Q_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst, weaken_subst0_eta]))
      (weaken_intro (sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)))) .trans0
  -- ¬(pa=0) → same_nf =₀ 0 (combine sub-cases via or_elim on sa)
  let h_same_zero : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 same_nf .zero) :=
    .syllogism (pair_h I_comb (weaken_intro h_sa_vals))
      (.syllogism and_or_dist (or_elim_rule
        (let swap := .syllogism .and_perm h_same_S0
         .syllogism (pair_h and_proj2 .and_weak) swap)
        (.syllogism and_proj2 h_same_0)))
  -- ¬(pa=0) → ite(same_nf, ac+bc, |ac-bc|) =₀ ite(0, ac+bc, |ac-bc|) =₀ |ac-bc| =₀ 0
  let h_ite_when_ne : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 num_nf .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) h_same_zero
        (r := Term.app3 Term.ite_nat (.var .vz)
          (Term.app2 Term.add ac bc).weaken
          (Term.app2 Term.abs_diff ac bc).weaken)
        (rs := num_nf)
        (rt := Term.app3 Term.ite_nat .zero (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))
        (by simp only [num_nf, Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
            ite_nat_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
            add_closed_subst, mul_closed_subst, rat_sign_closed_subst, neg_Q_closed_subst,
            rat_num_closed_subst, rat_den_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
            ite_nat_closed_subst, abs_diff_closed_subst, add_closed_subst,
            mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
            neg_Q_closed_subst, weaken_subst0_eta]))
      (weaken_intro (ite_nat_zero adm (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))))
      (.syllogism .trans0 (.syllogism (pair_h I_comb (weaken_intro h_diff)) .trans0))
  -- Case B2
  let case_b2 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 pa .zero →ᶠ Formula.eq0 num_nf .zero) := h_ite_when_ne
  -- ── Combine cases: num_nf =₀ 0 ──
  let h_pa_disj := .mp eq0_decidable' (.forall_ax pa)
  let h_num_zero : Derivable F EqX al Premises (Formula.eq0 num_nf .zero) :=
    .mp h_pa_disj (or_elim_rule case_b1 case_b2)
  -- ── Result components for eq_Q_from_components ──
  let result := Term.app2 Term.add_Q a na
  let rn := Term.app Term.rat_num result
  let rd := Term.app Term.rat_den result
  let rs := Term.app Term.rat_sign result
  let zero := (Term.zero_Q : Term F (Ty.nat :: Γ) Ty.nat)
  let sz := Term.app Term.rat_sign zero
  let nz := Term.app Term.rat_num zero
  let dz := Term.app Term.rat_den zero
  -- rn =₀ num_nf (via rat_num_rat_encode on the add_Q result)
  let h_rn : Derivable F EqX al Premises (Formula.eq0 rn .zero) :=
    .mp (.mp h_num_zero (.mp (.mp (.mp
      (rat_num_rat_encode adm sign_nf num_nf den_nf (isEven_cases adm sign_nf))
      (.mp (rat_num_congr h_unfold) and_intro)) .trans0) and_intro)) .trans0
  -- nz =₀ 0
  let h_nz : Derivable F EqX al Premises (Formula.eq0 nz .zero) :=
    rat_num_zero_Q (adm := adm)
  -- dz =₀ S0
  let h_dz : Derivable F EqX al Premises (Formula.eq0 dz S0) :=
    rat_den_zero_Q (adm := adm)
  -- Cross product: |rn*dz - nz*rd| =₀ |0*dz - 0*rd| =₀ |0-0| =₀ 0
  let h_rn_dz : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul rn dz) .zero) :=
    .mp (.mp (mul_zero_l adm dz) (.mp (mul_congr_l h_rn dz) and_intro)) .trans0
  let h_nz_rd : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul nz rd) .zero) :=
    .mp (.mp (mul_zero_l adm rd) (.mp (mul_congr_l h_nz rd) and_intro)) .trans0
  let h_cross : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn dz) (Term.app2 Term.mul nz rd)) .zero) :=
    .mp (.mp (abs_diff_self adm _) (.mp (.mp (.mp (abs_diff_congr_r _ h_nz_rd)
      (.mp (abs_diff_congr_l h_rn_dz _) and_intro)) .trans0) and_intro)) .trans0
  -- Sign product: |rs-sz| * sg(rn+nz) =₀ 0
  -- sg(rn+nz) =₀ sg(0+0) =₀ sg(0) =₀ 0
  let h_rn_nz_sum : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add rn nz) .zero) :=
    let step1 := add_congr_l h_rn nz
    let step2 := add_congr_r (.zero : Term F _ _) h_nz
    let step3 := add_zero_r adm (.zero : Term F _ _)
    .mp (.mp step3 (.mp (.mp (.mp step2 (.mp step1 and_intro)) .trans0) and_intro)) .trans0
  let h_sg_zero : Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.sg (Term.app2 Term.add rn nz)) .zero) :=
    .mp (.mp sg_zero (.mp (sg_congr h_rn_nz_sum) and_intro)) .trans0
  let h_sign : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul
        (Term.app2 Term.abs_diff rs sz)
        (Term.app Term.sg (Term.app2 Term.add rn nz))) .zero) :=
    .mp (.mp (mul_zero adm _) (.mp (mul_congr_r _ h_sg_zero) and_intro)) .trans0
  univ_gen (eq_Q_from_components adm h_cross h_sign)

/-- ⊢ ∀a. eq_Q(add_Q(a, neg_Q(a)), zero_Q) -/
def add_Q_neg :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var .vz)
                (Term.app Term.neg_Q (.var .vz)))
              Term.zero_Q)) :=
  add_Q_neg_core adm

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


/-- `mul_Q_comm` instantiated at two explicit terms, with the resulting formula stated.
See `q_norm` for why the inline `.forall_ax` chain is not affordable. -/
def mul_Q_comm_inst (adm : AdmissibleEqX EqX) (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (eq_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q y x)) := by
  have h := Derivable.mp (Derivable.mp
    (mul_Q_comm (adm := adm) (al := al) (Premises := Premises) (Γ := Γ)) (.forall_ax x))
    (.forall_ax y)
  q_norm using h

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
  let a : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let na := Term.app Term.rat_num a
  let da := Term.app Term.rat_den a
  let one : Term F (Ty.nat :: Γ) Ty.nat := Term.one_Q
  let s1 := Term.app Term.rat_sign one
  let n1 := Term.app Term.rat_num one
  let d1 := Term.app Term.rat_den one
  -- Body of mul_Q
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
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
  have body_eq : (Term.mul_Q : Term F (Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  -- NF: mul_Q(a, one_Q) reduces to rat_encode(sign_nf, num_nf, den_nf)
  let sign_nf := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa s1)
  let num_nf := Term.app2 Term.mul na n1
  let den_nf := Term.app Term.pd (Term.app2 Term.mul da d1)
  have nf : (body.subst0 (one.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_nf num_nf den_nf := by
    simp only [body, a, one, sign_nf, num_nf, den_nf, sa, s1, na, n1, da, d1,
      Term.one_Q, Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      Term.ofNat,
      rat_encode_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
      mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      rat_sign_closed_subst, pd_closed_subst, weaken_subst0_eta]
  let h_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul_Q a one)
        (Term.app3 Term.rat_encode sign_nf num_nf den_nf)) :=
    body_eq ▸ lam2_correct_nf adm body a one nf
  -- one_Q component values
  let hs1 : Derivable F EqX al Premises
      (Formula.eq0 s1 (.app .succ .zero)) :=
    rat_sign_one_Q (adm := adm)
  let hn1 : Derivable F EqX al Premises
      (Formula.eq0 n1 (.app .succ .zero)) :=
    rat_num_one_Q (adm := adm)
  let hd1 : Derivable F EqX al Premises
      (Formula.eq0 d1 (.app .succ .zero)) :=
    rat_den_one_Q (adm := adm)
  -- num_nf = mul(na, n1) =₀ mul(na, S0) =₀ na
  let h_num_s : Derivable F EqX al Premises
      (Formula.eq0 num_nf (Term.app2 Term.mul na (.app .succ .zero))) :=
    mul_congr_r na hn1
  let h_num : Derivable F EqX al Premises (Formula.eq0 num_nf na) :=
    .mp (.mp (mul_one_r adm na) (.mp h_num_s and_intro)) .trans0
  -- den_nf = pd(mul(da, d1)) =₀ pd(mul(da, S0)) =₀ pd(da)
  let h_den_s : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul da d1)
        (Term.app2 Term.mul da (.app .succ .zero))) :=
    mul_congr_r da hd1
  let h_den_s2 : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul da d1) da) :=
    .mp (.mp (mul_one_r adm da) (.mp h_den_s and_intro)) .trans0
  let h_den : Derivable F EqX al Premises
      (Formula.eq0 den_nf (Term.app Term.pd da)) :=
    pd_congr h_den_s2
  -- rat_den(a) unfolds to S(snd_pair(a))
  let rat_den_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    .app .succ (.app Term.snd_pair (.var .vz))
  let h_da_unfold : Derivable F EqX al Premises
      (Formula.eq0 da (.app .succ (.app Term.snd_pair a))) :=
    lam_correct_nf rat_den_body a (by
      simp only [rat_den_body, a, Term.subst0, Term.subst, Term.subst0_map,
        snd_pair_closed_subst])
  -- S(pd(da)) =₀ S(pd(S(snd_pair(a)))) =₀ S(snd_pair(a)) =₀ da
  let h_pd_da : Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.pd da)
        (.app Term.snd_pair a)) :=
    .mp (.mp (pd_succ adm (.app Term.snd_pair a))
      (.mp (pd_congr h_da_unfold) and_intro)) .trans0
  let h_s_pd_da : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app Term.pd da))
        (.app .succ (.app Term.snd_pair a))) :=
    qfer_no_premise_nat_nf h_pd_da
      (r := .app .succ (.var .vz))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map])
  let h_s_pd_da_eq_da : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app Term.pd da)) da) :=
    .mp (.mp (.mp h_da_unfold .sym0) (.mp h_s_pd_da and_intro)) .trans0
  -- S(den_nf) =₀ S(pd(da)) =₀ da
  let h_s_den_nf : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ den_nf) da) :=
    .mp (.mp h_s_pd_da_eq_da
      (.mp (qfer_no_premise_nat_nf h_den
        (r := .app .succ (.var .vz))
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            pd_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            pd_closed_subst])) and_intro)) .trans0
  -- Abbreviations for result components
  let result := Term.app2 Term.mul_Q a one
  let rn := Term.app Term.rat_num result
  let rd := Term.app Term.rat_den result
  let rs := Term.app Term.rat_sign result
  -- rat_num(result) =₀ na
  let h_rn_enc := rat_num_congr h_unfold
  let h_rn_nf : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_num (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
        num_nf) :=
    rat_num_rat_encode adm sign_nf num_nf den_nf (isEven_cases adm sign_nf)
  let h_rn : Derivable F EqX al Premises (Formula.eq0 rn na) :=
    .mp (.mp h_num (.mp (.mp (.mp h_rn_nf (.mp h_rn_enc and_intro)) .trans0) and_intro)) .trans0
  -- rat_den(result) =₀ da
  let h_rd_enc := rat_den_congr h_unfold
  let h_rd_nf : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
        (.app .succ den_nf)) :=
    rat_den_rat_encode adm sign_nf num_nf den_nf
  let h_rd : Derivable F EqX al Premises (Formula.eq0 rd da) :=
    .mp (.mp h_s_den_nf
      (.mp (.mp (.mp h_rd_nf (.mp h_rd_enc and_intro)) .trans0) and_intro)) .trans0
  -- Cross-product condition: |rn * da - na * rd| =₀ 0
  let h_cross_l := mul_congr_l h_rn da   -- rn * da =₀ na * da
  let h_cross_r := mul_congr_r na h_rd   -- na * rd =₀ na * da
  let h_cross_abs : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn da) (Term.app2 Term.mul na rd))
        (Term.app2 Term.abs_diff
          (Term.app2 Term.mul na da) (Term.app2 Term.mul na da))) :=
    .mp (.mp (abs_diff_congr_r _ h_cross_r)
      (.mp (abs_diff_congr_l h_cross_l _) and_intro)) .trans0
  let h_cross : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn da) (Term.app2 Term.mul na rd))
        .zero) :=
    .mp (.mp (abs_diff_self adm _) (.mp h_cross_abs and_intro)) .trans0
  -- Sign condition: |rs - sa| * sg(rn + na) =₀ 0
  -- Step A: Reduce unconditionally: sg(rn + na) =₀ sg(na + na)
  let h_mul_red : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa)
          (Term.app Term.sg (Term.app2 Term.add rn na)))
        (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa)
          (Term.app Term.sg (Term.app2 Term.add na na)))) :=
    mul_congr_r _ (sg_congr (add_congr_l h_rn na))
  -- Step B: Case split na =₀ 0 ∨ ¬(na =₀ 0)
  let h_na_disj : Derivable F EqX al Premises
      (Formula.eq0 na .zero ∨ᶠ ¬ᶠFormula.eq0 na .zero) :=
    .mp eq0_decidable' (.forall_ax na)
  -- Case B1: na =₀ 0 �� |rs-sa| * sg(na+na) =₀ 0
  let b1_nn_zero : Derivable F EqX al Premises
      (Formula.eq0 na .zero →ᶠ
       Formula.eq0 (Term.app2 Term.add na na) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.add (.var .vz) (.var .vz))
        (rs := Term.app2 Term.add na na) (rt := Term.app2 Term.add .zero .zero)
        (by rfl) (by rfl) I_comb
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            add_closed_subst])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            add_closed_subst]))
      (weaken_intro (add_zero_r adm .zero))) .trans0
  let b1_sg_zero : Derivable F EqX al Premises
      (Formula.eq0 na .zero →ᶠ
       Formula.eq0 (Term.app Term.sg (Term.app2 Term.add na na)) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app Term.sg (.var .vz))
        (rs := Term.app Term.sg (Term.app2 Term.add na na))
        (rt := Term.app Term.sg .zero)
        (by rfl) (by rfl) b1_nn_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_closed_subst, add_closed_subst, Term.app2])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_closed_subst]))
      (weaken_intro sg_zero)) .trans0
  let abs_rs_sa := Term.app2 Term.abs_diff rs sa
  let case_b1 : Derivable F EqX al Premises
      (Formula.eq0 na .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs_sa
         (Term.app Term.sg (Term.app2 Term.add na na))) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (r := Term.app2 Term.mul abs_rs_sa.weaken (.var .vz))
        (rs := Term.app2 Term.mul abs_rs_sa
          (Term.app Term.sg (Term.app2 Term.add na na)))
        (rt := Term.app2 Term.mul abs_rs_sa .zero)
        (by rfl) (by rfl) b1_sg_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            mul_Q_closed_subst, sg_closed_subst, add_closed_subst,
            rat_num_closed_subst, weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
            mul_Q_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero adm _))) .trans0
  -- Case B2: ¬(na =₀ 0) → |rs-sa| * sg(na+na) =₀ 0
  -- Strategy: show |rs - sa| =₀ 0 unconditionally when na ≠ 0,
  -- via sub-case on sa ∈ {S0, 0} (from isEven_cases on fst_pair(a)).
  -- First, get sa =₀ S0 ∨ sa =₀ 0
  let ie_fpa := Term.app Term.isEven (Term.app Term.fst_pair a)
  let h_sa_unfold : Derivable F EqX al Premises (Formula.eq0 sa ie_fpa) :=
    lam_correct_nf (Term.app Term.isEven (Term.app Term.fst_pair (.var .vz)) :
      Term F (Ty.nat :: Ty.nat :: Γ) _) a (by
      simp only [Term.subst0, Term.subst, Term.subst0_map,
        isEven_closed_subst, fst_pair_closed_subst]; rfl)
  let h_ie := isEven_cases adm (Term.app Term.fst_pair a)
  let h_sa_cases : Derivable F EqX al Premises
      (Formula.eq0 sa (.app .succ .zero) ∨ᶠ Formula.eq0 sa .zero) :=
    let lift_case (v : Term F (Ty.nat :: Γ) Ty.nat) :
        Derivable F EqX al Premises (Formula.eq0 ie_fpa v →ᶠ Formula.eq0 sa v) :=
      .syllogism (pair_h (weaken_intro h_sa_unfold) I_comb) .trans0
    .mp h_ie (or_elim_rule
      (.syllogism (lift_case _) .or_weak)
      (.syllogism (lift_case _) or_inr))
  -- Unconditional: sign_nf =₀ sg_bar(|sa - S0|) (via s1 =₀ S0)
  let h_sign_nf_reduce : Derivable F EqX al Premises
      (Formula.eq0 sign_nf
        (Term.app Term.sg_bar (Term.app2 Term.abs_diff sa (.app .succ .zero)))) :=
    sg_bar_congr (abs_diff_congr_r sa hs1)
  -- rs_enc = rat_sign(rat_encode(sign_nf, num_nf, den_nf))
  let h_rs_enc := rat_sign_congr h_unfold
  -- Sub-case sa =₀ S0: rs =₀ S0 → |rs - sa| =₀ 0
  -- |S0 - S0| = 0 → sg_bar(0) = S0 → sign_nf =₀ S0 → isEven(S0) =₀ 0 →
  -- rat_sign_encode_pos → rs_enc =₀ S0 → rs =₀ S0 → |rs - S0| =₀ 0
  let h_abs_S0_S0 := abs_diff_self adm (.app .succ .zero : Term F (Ty.nat :: Γ) _)
  let h_sgnf_when_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa (.app .succ .zero) →ᶠ Formula.eq0 sign_nf (.app .succ .zero)) :=
    let S0w : Term F (Ty.nat :: Ty.nat :: Γ) _ := (Term.app .succ .zero : Term F (Ty.nat :: Γ) _).weaken
    let h_abs_cond := qfer_nat_nf
      (r := Term.app2 Term.abs_diff (.var .vz) S0w)
      (rs := Term.app2 Term.abs_diff sa (.app .succ .zero))
      (rt := Term.app2 Term.abs_diff (.app .succ .zero) (.app .succ .zero))
      (by rfl) (by rfl) I_comb
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          abs_diff_closed_subst, rat_sign_closed_subst, weaken_subst0_eta]; rfl)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          abs_diff_closed_subst, weaken_subst0_eta]; rfl)
    let h_abs_zero := .syllogism (pair_h h_abs_cond (weaken_intro h_abs_S0_S0)) .trans0
    let h_sgb := .syllogism (pair_h
      (qfer_nat_nf (r := Term.app Term.sg_bar (.var .vz))
        (rs := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa (.app .succ .zero)))
        (rt := Term.app Term.sg_bar .zero)
        (by rfl) (by rfl) h_abs_zero
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst, Term.app2]; rfl)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map,
            sg_bar_closed_subst]))
      (weaken_intro (sg_bar_zero (Γ := Ty.nat :: Γ)))) .trans0
    .syllogism (pair_h (weaken_intro h_sign_nf_reduce) h_sgb) .trans0
  -- isEven(S0) =₀ 0 (standalone computation)
  let h_isE_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.isEven (.app .succ .zero)) .zero) :=
    let step1 := isEven_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    let step2 := sg_bar_congr (isEven_zero (Γ := Ty.nat :: Γ))
    let step3 := sg_bar_succ adm (.zero : Term F (Ty.nat :: Γ) _)
    let chain12 := .mp (.mp step2 (.mp step1 and_intro)) .trans0
    .mp (.mp step3 (.mp chain12 and_intro)) .trans0
  -- ======== Sub-case sa =₀ S0: show rs =₀ S0, hence |rs-sa| =₀ 0 ========
  let S0 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ .zero
  let h_pos := rat_sign_rat_encode_pos adm (S0 : Term F (Ty.nat :: Γ) _) num_nf den_nf h_isE_S0
  let h_rs_cond_S0 := qfer_nat_nf (by rfl) (by rfl) h_sgnf_when_S0
    (r := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) num_nf.weaken den_nf.weaken))
    (rs := Term.app Term.rat_sign (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
    (rt := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.app .succ .zero) num_nf den_nf))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
  let h_rs_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ Formula.eq0 rs S0) :=
    .syllogism (pair_h (weaken_intro h_rs_enc)
      (.syllogism (pair_h h_rs_cond_S0 (weaken_intro h_pos)) .trans0)) .trans0
  let sg_nn := Term.app Term.sg (Term.app2 Term.add na na)
  let h_abs_step1_S0 := qfer_nat_nf (by rfl) (by rfl) I_comb
    (r := Term.app2 Term.abs_diff rs.weaken (.var .vz))
    (rs := Term.app2 Term.abs_diff rs sa) (rt := Term.app2 Term.abs_diff rs S0)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, mul_Q_closed_subst,
        weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, mul_Q_closed_subst,
        weaken_subst0_eta])
  let h_abs_step2_S0 := qfer_nat_nf (by rfl) (by rfl) h_rs_S0
    (r := Term.app2 Term.abs_diff (.var .vz) S0.weaken)
    (rs := Term.app2 Term.abs_diff rs S0)
    (rt := Term.app2 Term.abs_diff S0 S0)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, rat_sign_closed_subst, mul_Q_closed_subst,
        weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
        abs_diff_closed_subst, weaken_subst0_eta])
  let h_abs_zero_S0 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ Formula.eq0 (Term.app2 Term.abs_diff rs sa) .zero) :=
    .syllogism (pair_h h_abs_step1_S0 (.syllogism (pair_h h_abs_step2_S0
      (weaken_intro h_abs_S0_S0)) .trans0)) .trans0
  let h_product_from_abs : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff rs sa) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn) .zero) :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) I_comb
        (r := Term.app2 Term.mul (.var .vz) sg_nn.weaken)
        (rs := Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn)
        (rt := Term.app2 Term.mul .zero sg_nn)
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, abs_diff_closed_subst, sg_closed_subst, add_closed_subst,
            rat_sign_closed_subst, mul_Q_closed_subst, rat_num_closed_subst,
            weaken_subst0_eta])
        (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
            mul_closed_subst, sg_closed_subst, add_closed_subst,
            rat_num_closed_subst, weaken_subst0_eta]))
      (weaken_intro (mul_zero_l adm sg_nn))) .trans0
  let case_b2_sub1 : Derivable F EqX al Premises
      (Formula.eq0 sa S0 →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn) .zero) :=
    .syllogism h_abs_zero_S0 h_product_from_abs
  -- ======== Sub-case sa =₀ 0: show rs =₀ 0 (under ¬(na=0)), hence |rs-sa| =₀ 0 ========
  -- Step 1: sa=0 → sign_nf=0 (via |0-S0| ≠ 0 → sg_bar(|0-S0|) = 0)
  let h_ne_0_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (¬ᶠFormula.eq0 (Term.app2 Term.abs_diff .zero S0) .zero) :=
    let h_fwd := .mp (abs_diff_eq_zero_iff adm (.zero : Term F (Ty.nat :: Γ) _) S0) .and_weak
    .syllogism (.syllogism h_fwd .sym0)
      (.mp .succ_ne_zero (.forall_ax (.zero : Term F (Ty.nat :: Γ) _)))
  let h_sgb_abs_0_S0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.abs_diff .zero S0)) .zero) :=
    .mp h_ne_0_S0 (.mp (sg_bar_eq_zero_iff adm (Term.app2 Term.abs_diff .zero S0))
      (.syllogism .and_perm .and_weak))
  let h_sgnf_when_0 : Derivable F EqX al Premises
      (Formula.eq0 sa .zero →ᶠ Formula.eq0 sign_nf .zero) :=
    let S0w : Term F (Ty.nat :: Ty.nat :: Γ) _ := (Term.app .succ .zero : Term F (Ty.nat :: Γ) _).weaken
    let h_abs_cond_0 := qfer_nat_nf
      (r := Term.app2 Term.abs_diff (.var .vz) S0w)
      (rs := Term.app2 Term.abs_diff sa (.app .succ .zero))
      (rt := Term.app2 Term.abs_diff .zero (.app .succ .zero))
      (by rfl) (by rfl) I_comb
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          abs_diff_closed_subst, rat_sign_closed_subst, weaken_subst0_eta]; rfl)
      (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          abs_diff_closed_subst, weaken_subst0_eta]; rfl)
    let h_sgb_cond_0 := qfer_nat_nf (by rfl) (by rfl) h_abs_cond_0
      (r := .app Term.sg_bar (.var .vz))
      (rs := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa (.app .succ .zero)))
      (rt := Term.app Term.sg_bar (Term.app2 Term.abs_diff .zero (.app .succ .zero)))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          sg_bar_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst, Term.app2])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          sg_bar_closed_subst, abs_diff_closed_subst, Term.app2])
    .syllogism (pair_h (weaken_intro h_sign_nf_reduce)
      (.syllogism (pair_h h_sgb_cond_0 (weaken_intro h_sgb_abs_0_S0)) .trans0)) .trans0
  -- Step 2: Standalone chain for rat_sign(rat_encode(0, num_nf, den_nf))
  -- = isEven(pd(2*num_nf ∸ isEven(0)))  (replicate rat_sign_rat_encode_neg logic)
  let two_nnf := Term.app2 Term.mul (Term.ofNat 2) num_nf
  let nnf := Term.app2 Term.add num_nf num_nf
  let h_rs_unfold_0 := rat_sign_rat_encode_unfold adm
    (.zero : Term F (Ty.nat :: Γ) _) num_nf den_nf
  let h_monus_ie0 := monus_congr_r two_nnf (isEven_zero (Γ := Ty.nat :: Γ))
  let h_two_nnf_eq_nnf :=
    let h_ms := mul_succ_l adm (.app .succ .zero : Term F (Ty.nat :: Γ) _) num_nf
    let h_m1 := .mp (.mp (mul_one_r adm num_nf)
      (.mp (mul_comm adm (.app .succ .zero) num_nf) and_intro)) .trans0
    .mp (.mp (add_congr_l h_m1 num_nf) (.mp h_ms and_intro)) .trans0
  let h_monus_s0_0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.app2 Term.monus two_nnf (.app .succ .zero))
        (.app Term.pd nnf)) :=
    let hm1 := monus_congr_l h_two_nnf_eq_nnf (.app .succ .zero)
    let hm2 := monus_succ adm nnf .zero
    let hm3 := pd_congr (monus_zero adm nnf)
    .mp (.mp hm3 (.mp (.mp (.mp hm2 (.mp hm1 and_intro)) .trans0) and_intro)) .trans0
  let h_tgt_0 := .mp (.mp h_monus_s0_0 (.mp h_monus_ie0 and_intro)) .trans0
  let h_ie_tgt_0 := isEven_congr h_tgt_0
  let h_ie_chain_0 : Derivable F EqX al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf))
        (.app Term.isEven (.app Term.pd nnf))) :=
    .mp (.mp h_ie_tgt_0 (.mp h_rs_unfold_0 and_intro)) .trans0
  -- Step 3: ¬(na=0) → isEven(pd(nnf)) = 0
  let h_num_fwd : Derivable F EqX al Premises
      (Formula.eq0 num_nf .zero →ᶠ Formula.eq0 na .zero) :=
    .syllogism (pair_h (weaken_intro (.mp h_num .sym0)) I_comb) .trans0
  let h_num_ne : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ ¬ᶠFormula.eq0 num_nf .zero) :=
    contrapositive h_num_fwd
  let h_nnf_ne_from_num : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 num_nf .zero →ᶠ ¬ᶠFormula.eq0 nnf .zero) :=
    let h_fwd := .mp (add_eq_zero_iff adm num_nf num_nf) .and_weak
    contrapositive (.syllogism h_fwd .and_weak)
  let h_nnf_ne : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ ¬ᶠFormula.eq0 nnf .zero) :=
    .syllogism h_num_ne h_nnf_ne_from_num
  let h_nnf_succ : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 nnf (.app .succ (.app Term.pd nnf))) :=
    .syllogism h_nnf_ne (ne_zero_eq_succ_pd adm nnf)
  let h_ie_nnf_eq : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (.app Term.isEven nnf)
         (.app Term.isEven (.app .succ (.app Term.pd nnf)))) :=
    qfer_nat_nf (by rfl) (by rfl) h_nnf_succ
      (r := .app Term.isEven (.var .vz))
      (rs := .app Term.isEven nnf)
      (rt := .app Term.isEven (.app .succ (.app Term.pd nnf)))
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, add_closed_subst, rat_num_closed_subst,
          mul_Q_closed_subst, Term.app2])
      (by simp only [Term.subst0, Term.subst, Term.subst0_map,
          isEven_closed_subst, pd_closed_subst, add_closed_subst,
          rat_num_closed_subst, mul_Q_closed_subst, Term.app2])
  let h_ie_succ_pd := isEven_succ adm (.app Term.pd nnf)
  let h_ie_nnf_sgb : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (.app Term.isEven nnf)
         (.app Term.sg_bar (.app Term.isEven (.app Term.pd nnf)))) :=
    .syllogism (pair_h h_ie_nnf_eq (weaken_intro h_ie_succ_pd)) .trans0
  let h_ie_double_nnf := isEven_double adm num_nf
  let h_sgb_ie_pd_eq_S0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (.app Term.sg_bar (.app Term.isEven (.app Term.pd nnf)))
         (.app .succ .zero)) :=
    .syllogism (pair_h (.syllogism h_ie_nnf_sgb .sym0) (weaken_intro h_ie_double_nnf)) .trans0
  let h_ie_pd_zero : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (.app Term.isEven (.app Term.pd nnf)) .zero) :=
    .syllogism h_sgb_ie_pd_eq_S0
      (sg_bar_eq_S0_implies_zero adm (.app Term.isEven (.app Term.pd nnf)))
  -- Step 4: ¬(na=0) → rat_sign(rat_encode(0, num_nf, den_nf)) =₀ 0
  let h_neg_rs : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf)) .zero) :=
    .syllogism (pair_h (weaken_intro h_ie_chain_0) h_ie_pd_zero) .trans0
  -- Step 5: sa=0 → rs_enc =₀ rat_sign(rat_encode(0, num_nf, den_nf))
  let h_rs_cond_0 := qfer_nat_nf (by rfl) (by rfl) h_sgnf_when_0
    (r := Term.app Term.rat_sign (Term.app3 Term.rat_encode (.var .vz) num_nf.weaken den_nf.weaken))
    (rs := Term.app Term.rat_sign (Term.app3 Term.rat_encode sign_nf num_nf den_nf))
    (rt := Term.app Term.rat_sign (Term.app3 Term.rat_encode .zero num_nf den_nf))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
        rat_sign_closed_subst, rat_encode_closed_subst, weaken_subst0_eta])
  -- Step 6: ¬(na=0) ∧ sa=0 → rs =₀ 0
  let h_rs_0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ Formula.eq0 rs .zero) :=
    .syllogism (pair_h
      (.syllogism (pair_h (.syllogism .and_weak (weaken_intro h_rs_enc))
        (.syllogism and_proj2 h_rs_cond_0)) .trans0)
      (.syllogism .and_weak h_neg_rs)) .trans0
  -- Step 7: ¬(na=0) ∧ sa=0 → |rs - sa| =₀ 0
  let h_rs_eq_sa : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ Formula.eq0 rs sa) :=
    .syllogism (pair_h h_rs_0 (.syllogism and_proj2 .sym0)) .trans0
  let h_abs_zero_0 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ
       Formula.eq0 (Term.app2 Term.abs_diff rs sa) .zero) :=
    .syllogism h_rs_eq_sa (.mp (abs_diff_eq_zero_iff adm rs sa) (.syllogism .and_perm .and_weak))
  let case_b2_sub2 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero ∧ᶠ Formula.eq0 sa .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn) .zero) :=
    .syllogism h_abs_zero_0 h_product_from_abs
  -- ======== Final assembly ========
  let case_b2 : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 na .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn) .zero) :=
    .syllogism (pair_h I_comb (weaken_intro h_sa_cases))
      (.syllogism and_or_dist (or_elim_rule
        (.syllogism and_proj2 case_b2_sub1)
        case_b2_sub2))
  let h_reduced : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa) sg_nn) .zero) :=
    .mp h_na_disj (or_elim_rule case_b1 case_b2)
  let h_sign : Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.mul (Term.app2 Term.abs_diff rs sa)
          (Term.app Term.sg (Term.app2 Term.add rn na)))
        .zero) :=
    .mp (.mp h_reduced (.mp h_mul_red and_intro)) .trans0
  univ_gen (eq_Q_from_components adm h_cross h_sign)

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

/-- From eq_Q(x, zero_Q), derive rat_num(x)*S(0) =₀ 0.
    eq_Q means eq_Q_dec(x, zero_Q) = 0, which after unfolding gives
    |num(x)*den(0) - 0*den(x)| + ... = 0. The cross part gives num(x)*S(0) = 0. -/
private def eq_Q_zero_num_mul (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (eq_Q x Term.zero_Q →ᶠ
       Formula.eq0 (Term.app2 Term.mul (.app Term.rat_num x) (.app .succ .zero)) .zero) :=
  let nx := Term.app Term.rat_num x
  let dx := Term.app Term.rat_den x
  let sx := Term.app Term.rat_sign x
  let zero := (Term.zero_Q : Term F Γ Ty.nat)
  let nz := Term.app Term.rat_num zero
  let dz := Term.app Term.rat_den zero
  let sz := Term.app Term.rat_sign zero
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have body_eq : (Term.eq_Q_dec : Term F Γ _) = Term.lam (Term.lam body) := by rfl
  let cross := Term.app2 Term.abs_diff (Term.app2 Term.mul nx dz) (Term.app2 Term.mul nz dx)
  let sign_part := Term.app2 Term.mul (Term.app2 Term.abs_diff sx sz)
      (Term.app Term.sg (Term.app2 Term.add nx nz))
  have body_nf : (body.subst0 (zero.weaken)).subst0 x =
      Term.app2 Term.add cross sign_part := by
    simp only [body, cross, sign_part, nx, nz, dx, dz, sx, sz, zero,
      Term.zero_Q, Term.pair, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst,
      rat_num_closed_subst, rat_den_closed_subst, rat_sign_closed_subst,
      sg_closed_subst, weaken_subst0_eta]
  let unfold := body_eq ▸ lam2_correct_nf adm body x zero body_nf
  -- eq_Q(x, zero_Q) → NF = 0
  let to_nf_zero : Derivable F EqX al Premises
      (eq_Q x zero →ᶠ Formula.eq0 (Term.app2 Term.add cross sign_part) .zero) :=
    .syllogism (pair_h (weaken_intro_h (.mp unfold .sym0)) I_comb) .trans0
  -- NF = 0 → cross = 0
  let to_cross_zero : Derivable F EqX al Premises
      (eq_Q x zero →ᶠ Formula.eq0 cross .zero) :=
    .syllogism to_nf_zero (.syllogism (Derivable.mp (add_eq_zero_iff adm cross sign_part) .and_weak) .and_weak)
  -- Simplify cross: nz = 0, dz = S(0)
  let h_nz := rat_num_zero_Q (adm := adm)
  let h_dz := rat_den_zero_Q (adm := adm)
  -- nz*dx =₀ 0*dx =₀ 0
  let h_nz_dx : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul nz dx) .zero) :=
    .mp (.mp (mul_zero_l adm dx) (.mp (mul_congr_l h_nz dx) and_intro)) .trans0
  -- nx*dz =₀ nx*S(0)
  let h_nx_dz : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul nx dz) (Term.app2 Term.mul nx (.app .succ .zero))) :=
    mul_congr_r nx h_dz
  -- cross = |nx*dz - nz*dx| =₀ |nx*S(0) - 0| =₀ nx*S(0)
  let h_cross_simp : Derivable F EqX al Premises
      (Formula.eq0 cross (Term.app2 Term.mul nx (.app .succ .zero))) :=
    let h1 := .mp (.mp (abs_diff_congr_r _ h_nz_dx) (.mp (abs_diff_congr_l h_nx_dz _) and_intro)) .trans0
    .mp (.mp (abs_diff_zero_r adm _) (.mp h1 and_intro)) .trans0
  -- Chain: eq_Q(x, zero_Q) → cross = 0 → nx*S(0) = 0
  .syllogism to_cross_zero
    (.syllogism (pair_h (weaken_intro_h (.mp h_cross_simp .sym0)) I_comb) .trans0)

/-- ⊢ ∀a. ¬(lt_Q(a, a))  (irreflexivity) -/
def lt_Q_irrefl :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (¬ᶠ lt_Q (.var .vz) (.var .vz))) :=
  let a : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  -- sub_Q(a,a) = add_Q(a, neg_Q(a))
  let sub_body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add_Q (.var (.vs .vz)) (.app Term.neg_Q (.var .vz))
  have sub_eq : (Term.sub_Q : Term F (Ty.nat :: Γ) _) = Term.lam (Term.lam sub_body) := by rfl
  let add_neg := Term.app2 Term.add_Q a (.app Term.neg_Q a)
  have sub_nf : (sub_body.subst0 (a.weaken)).subst0 a = add_neg := by
    simp only [sub_body, a, add_neg, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_Q_closed_subst, neg_Q_closed_subst, weaken_subst0_eta]
  let h_sub_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.sub_Q a a) add_neg) :=
    sub_eq ▸ lam2_correct_nf adm sub_body a a sub_nf
  -- eq_Q(sub_Q(a,a), zero_Q) via eq_Q(add_neg, zero_Q) and sub = add_neg
  let h_eq_neg : Derivable F EqX al Premises (eq_Q add_neg Term.zero_Q) := by
    have h := Derivable.mp (add_Q_neg (adm := adm) (al := al) (Premises := Premises)) (.forall_ax a)
    q_norm using h
  let h_eq_sub_neg := @eq_Q_from_nat_eq _ _ _ _ _ adm _ _ _ h_sub_unfold
  let trans_inst := eq_Q_trans_inst adm (Term.app2 Term.sub_Q a a) add_neg Term.zero_Q
  let h_eq_sub_zero : Derivable F EqX al Premises (eq_Q (Term.app2 Term.sub_Q a a) Term.zero_Q) :=
    Derivable.mp (Derivable.mp h_eq_neg (.mp h_eq_sub_neg and_intro)) trans_inst
  -- From eq_Q(sub, zero_Q): rat_num(sub)*S(0) = 0 → rat_num(sub) = 0
  let sub_aa := Term.app2 Term.sub_Q a a
  let h_num_mul := eq_Q_zero_num_mul adm sub_aa
  let h_num_zero : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_num sub_aa) .zero) :=
    Derivable.mp h_eq_sub_zero
      (.syllogism h_num_mul (mul_succ_eq_zero_imp adm _ _))
  -- sg_bar(num(sub)) = sg_bar(0) = S(0)
  let h_sgb : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.sg_bar (.app Term.rat_num sub_aa)) (.app .succ .zero)) :=
    .mp (.mp (sg_bar_zero (Premises := Premises)) (.mp (sg_bar_congr h_num_zero) and_intro)) .trans0
  -- Unfold lt_Q_dec(a,a) to |sign(sub) - 1| + sg_bar(num(sub))
  let lt_body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let diff := Term.app2 Term.sub_Q (.var .vz) (.var (.vs .vz))
    Term.app2 Term.add
      (Term.app2 Term.abs_diff (.app Term.rat_sign diff) (.app .succ .zero))
      (.app Term.sg_bar (.app Term.rat_num diff))
  have lt_eq : (Term.lt_Q_dec : Term F (Ty.nat :: Γ) _) = Term.lam (Term.lam lt_body) := by rfl
  let sign_sub := Term.app Term.rat_sign sub_aa
  let num_sub := Term.app Term.rat_num sub_aa
  have lt_nf : (lt_body.subst0 (a.weaken)).subst0 a =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff sign_sub (.app .succ .zero))
        (.app Term.sg_bar num_sub) := by
    simp only [lt_body, sub_aa, sign_sub, num_sub, a,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, sub_Q_closed_subst,
      rat_sign_closed_subst, rat_num_closed_subst, sg_bar_closed_subst,
      weaken_subst0_eta]
  let h_lt_unfold : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.lt_Q_dec a a)
        (Term.app2 Term.add
          (Term.app2 Term.abs_diff sign_sub (.app .succ .zero))
          (.app Term.sg_bar num_sub))) :=
    lt_eq ▸ lam2_correct_nf adm lt_body a a lt_nf
  -- |sign(sub) - 1| + sg_bar(num(sub)) = |sign(sub) - 1| + S(0) = S(|sign(sub) - 1|)
  let abs_term := Term.app2 Term.abs_diff sign_sub (.app .succ .zero)
  let h_add_sgb : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add abs_term (.app Term.sg_bar num_sub))
                   (Term.app2 Term.add abs_term (.app .succ .zero))) :=
    add_congr_r abs_term h_sgb
  let h_add_succ : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add abs_term (.app .succ .zero))
                   (.app .succ (Term.app2 Term.add abs_term .zero))) :=
    add_succ adm abs_term .zero
  let h_add_zero : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (Term.app2 Term.add abs_term .zero))
                   (.app .succ abs_term)) :=
    succ_congr (add_zero_r adm abs_term)
  -- lt_Q_dec(a,a) =₀ S(abs_term)
  let h_lt_eq_succ : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.lt_Q_dec a a) (.app .succ abs_term)) :=
    .mp (.mp h_add_zero (.mp (.mp (.mp h_add_succ (.mp (.mp (.mp h_add_sgb
      (.mp h_lt_unfold and_intro)) .trans0) and_intro)) .trans0) and_intro)) .trans0
  -- lt_Q(a,a) = eq0(lt_Q_dec(a,a), 0). From lt_Q_dec(a,a) = S(abs_term): S(abs_term) = 0 → ⊥
  let h_ne : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ abs_term) .zero →ᶠ ⊥ᶠ) :=
    .mp .succ_ne_zero (.forall_ax abs_term)
  -- lt_Q(a,a) → lt_Q_dec(a,a)=0 → S(abs_term)=0 → ⊥
  -- `trans0` needs `S(abs) = lt_Q_dec(a,a)` on the left, so flip `h_lt_eq_succ` first.
  let h_succ_sym : Derivable F EqX al Premises
      (Formula.eq0 (.app .succ abs_term) (Term.app2 Term.lt_Q_dec a a)) :=
    .mp h_lt_eq_succ .sym0
  let step : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.lt_Q_dec a a) Term.zero →ᶠ ⊥ᶠ) :=
    .syllogism (pair_h (weaken_intro_h h_succ_sym) I_comb) (.syllogism .trans0 h_ne)
  univ_gen step

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

/-- neg_Q(zero_Q) =₀ zero_Q -/
private def neg_Q_zero_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.neg_Q Term.zero_Q) Term.zero_Q) :=
  -- neg_Q = lam(rat_encode(monus(S0, rat_sign(vz)), rat_num(vz), snd_pair(vz)))
  let neg_Q_body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 Term.rat_encode
      (Term.app2 Term.monus (.app .succ .zero)
        (.app Term.rat_sign (.var .vz)))
      (.app Term.rat_num (.var .vz))
      (.app Term.snd_pair (.var .vz))
  have neg_Q_eq : (Term.neg_Q : Term F Γ _) = Term.lam neg_Q_body := by rfl
  have neg_Q_nf : neg_Q_body.subst0 Term.zero_Q =
      Term.app3 Term.rat_encode
        (Term.app2 Term.monus (.app .succ .zero) (.app Term.rat_sign Term.zero_Q))
        (.app Term.rat_num Term.zero_Q)
        (.app Term.snd_pair Term.zero_Q) := by
    simp only [neg_Q_body, Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, monus_closed_subst, rat_sign_closed_subst,
      rat_num_closed_subst, snd_pair_closed_subst]
  let h_unfold := neg_Q_eq ▸ lam_correct_nf neg_Q_body Term.zero_Q neg_Q_nf
  -- monus(S0, rat_sign(zero_Q)) =₀ monus(S0, S0) =₀ 0
  let h_monus := .mp (.mp (monus_self adm (.app Term.succ Term.zero))
    (.mp (monus_congr_r (.app .succ .zero) (rat_sign_zero_Q (adm := adm)))
      and_intro)) Derivable.trans0
  -- neg_Q(zero_Q) =₀ rat_encode(0, 0, 0)
  let h1 := .mp (.mp (rat_encode_congr h_monus
    (rat_num_zero_Q (adm := adm)) (snd_pair_pair adm Term.zero Term.zero))
    (.mp h_unfold and_intro)) Derivable.trans0
  -- rat_encode(0, 0, 0) =₀ pair(monus(mul(2,0), isEven(0)), 0)
  let enc_body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)
  have enc_eq : (Term.rat_encode : Term F Γ _) = Term.lam (Term.lam (Term.lam enc_body)) := by rfl
  let z := (Term.zero : Term F Γ Ty.nat)
  have enc_nf : ((enc_body.subst0 (z.weaken.weaken)).subst0 z.weaken).subst0 z =
      Term.app2 Term.pair
        (Term.app2 Term.monus (Term.app2 Term.mul (Term.ofNat 2) z) (.app Term.isEven z))
        z := by
    simp only [enc_body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      Term.ofNat, pair_closed_subst, monus_closed_subst, mul_closed_subst, isEven_closed_subst,
      weaken_subst0_eta]
  let h_enc_unfold := enc_eq ▸ lam3_correct_nf adm enc_body z z z enc_nf
  -- mul(2, 0) =₀ 0, isEven(0) =₀ S0, so monus(0, S0) =₀ 0
  let h_mon := .mp (.mp (monus_zero_l adm (.app .succ .zero))
    (.mp (.mp (.mp (monus_congr_r _ isEven_zero) (.mp (monus_congr_l (mul_zero adm (Term.ofNat 2)) _) and_intro))
      Derivable.trans0) and_intro)) Derivable.trans0
  -- pair(0, 0) = zero_Q
  let h2 := .mp (.mp (pair_congr h_mon Derivable.refl0)
    (.mp h_enc_unfold and_intro)) Derivable.trans0
  -- Chain: neg_Q(zero_Q) =₀ rat_encode(0,0,0) =₀ pair(0,0) = zero_Q
  .mp (.mp h2 (.mp h1 and_intro)) Derivable.trans0

/-- sub_Q(one_Q, zero_Q) =₀ add_Q(one_Q, zero_Q) -/
private def sub_Q_one_zero_unfold :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.sub_Q Term.one_Q Term.zero_Q)
        (Term.app2 Term.add_Q Term.one_Q Term.zero_Q)) :=
  let sub_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add_Q (.var (.vs .vz)) (.app Term.neg_Q (.var .vz))
  have sub_eq : (Term.sub_Q : Term F Γ _) = Term.lam (Term.lam sub_body) := by rfl
  have sub_nf : (sub_body.subst0 (Term.zero_Q.weaken (σ := Ty.nat))).subst0 Term.one_Q =
      Term.app2 Term.add_Q Term.one_Q (.app Term.neg_Q Term.zero_Q) := by
    simp only [sub_body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_Q_closed_subst, neg_Q_closed_subst, weaken_subst0_eta]
  let h_unfold := sub_eq ▸ lam2_correct_nf adm sub_body Term.one_Q Term.zero_Q sub_nf
  let h_congr := qfer_no_premise_nat_nf (neg_Q_zero_Q (adm := adm))
    (r := Term.app2 Term.add_Q Term.one_Q.weaken (.var .vz))
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        add_Q_closed_subst, weaken_subst0_eta])
    (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
        add_Q_closed_subst, weaken_subst0_eta])
  .mp (.mp h_congr (.mp h_unfold and_intro)) Derivable.trans0

/-- add_Q(one_Q, zero_Q) =₀ one_Q -/
private def add_Q_one_zero (adm : AdmissibleEqX EqX) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.add_Q Term.one_Q Term.zero_Q) Term.one_Q) :=
  -- add_Q body with var (vs vz) = n₁ (first arg), var vz = n₂ (second arg)
  let add_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
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
     Term.app3 Term.rat_encode result_sign result_num result_den_m1)
  have add_eq : (Term.add_Q : Term F Γ _) = Term.lam (Term.lam add_body) := by rfl
  -- Substituted components: one_Q is outer (vs vz), zero_Q is inner (vz)
  let s₁ : Term F Γ Ty.nat := .app Term.rat_sign Term.one_Q
  let p₁ : Term F Γ Ty.nat := .app Term.rat_num Term.one_Q
  let d₁ : Term F Γ Ty.nat := .app Term.rat_den Term.one_Q
  let s₂ : Term F Γ Ty.nat := .app Term.rat_sign Term.zero_Q
  let p₂ : Term F Γ Ty.nat := .app Term.rat_num Term.zero_Q
  let d₂ : Term F Γ Ty.nat := .app Term.rat_den Term.zero_Q
  let a : Term F Γ Ty.nat  := Term.app2 Term.mul p₁ d₂
  let b : Term F Γ Ty.nat  := Term.app2 Term.mul p₂ d₁
  let same : Term F Γ Ty.nat := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
  let result_num : Term F Γ Ty.nat := Term.app3 Term.ite_nat same
    (Term.app2 Term.add a b) (Term.app2 Term.abs_diff a b)
  let result_sign : Term F Γ Ty.nat := Term.app3 Term.ite_nat same s₁
    (Term.app3 Term.ite_nat (Term.app2 Term.geq a b) s₁ s₂)
  let result_den_m1 : Term F Γ Ty.nat := Term.app Term.pd (Term.app2 Term.mul d₁ d₂)
  let nf : Term F Γ Ty.nat := Term.app3 Term.rat_encode result_sign result_num result_den_m1
  have add_nf : (add_body.subst0 (Term.zero_Q.weaken (σ := Ty.nat))).subst0 Term.one_Q = nf := by
    simp only [add_body, nf, result_sign, result_num, result_den_m1, same, a, b,
      s₁, p₁, d₁, s₂, p₂, d₂,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst,
      abs_diff_closed_subst, mul_closed_subst, add_closed_subst, pd_closed_subst,
      rat_sign_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      geq_closed_subst, weaken_subst0_eta]
  let h_unfold := add_eq ▸ lam2_correct_nf adm add_body Term.one_Q Term.zero_Q add_nf
  -- Component values
  let hs₁ := rat_sign_one_Q (adm := adm) (Γ := Γ)   -- s₁ =₀ S0
  let hs₂ := rat_sign_zero_Q (adm := adm) (Γ := Γ)   -- s₂ =₀ S0
  let hp₁ := rat_num_one_Q (adm := adm) (Γ := Γ)     -- p₁ =₀ S0
  let hp₂ := rat_num_zero_Q (adm := adm) (Γ := Γ)    -- p₂ =₀ 0
  let hd₁ := rat_den_one_Q (adm := adm) (Γ := Γ)     -- d₁ =₀ S0
  let hd₂ := rat_den_zero_Q (adm := adm) (Γ := Γ)    -- d₂ =₀ S0
  -- a = mul(p₁, d₂) =₀ mul(S0, S0) =₀ S0
  let ha : Derivable F EqX al Premises (Formula.eq0 a (.app .succ .zero)) :=
    .mp (.mp (mul_one_r adm (.app .succ .zero))
    (.mp (.mp (.mp (mul_congr_r (.app .succ .zero) hd₂)
      (.mp (mul_congr_l hp₁ d₂) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  -- b = mul(p₂, d₁) =₀ mul(0, S0) =₀ 0
  let hb : Derivable F EqX al Premises (Formula.eq0 b .zero) :=
    .mp (.mp (mul_zero_l adm (.app .succ .zero))
    (.mp (.mp (.mp (mul_congr_r .zero hd₁)
      (.mp (mul_congr_l hp₂ d₁) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  -- same = sg_bar(|s₁ - s₂|) =₀ sg_bar(|S0 - S0|) =₀ sg_bar(0) =₀ S0
  -- Step 1: |s₁ - s₂| =₀ |S0 - s₂| (via s₁ =₀ S0)
  let h_abs_l : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff s₁ s₂)
        (Term.app2 Term.abs_diff (.app .succ .zero) s₂)) :=
    qfer_no_premise_nat_nf hs₁
      (r := Term.app2 Term.abs_diff (.var .vz) s₂.weaken)
      (by simp only [s₁, Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])
  -- Step 2: |S0 - s₂| =₀ |S0 - S0| (via s₂ =₀ S0)
  let h_abs_r : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff (.app .succ .zero) s₂)
        (Term.app2 Term.abs_diff (.app .succ .zero) (.app .succ .zero))) :=
    qfer_no_premise_nat_nf hs₂
      (r := Term.app2 Term.abs_diff (Term.app Term.succ Term.zero).weaken (.var .vz))
      (by simp only [s₂, Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])
      (by simp only [s₂, Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])
  -- Chain: |s₁ - s₂| =₀ |S0 - S0| =₀ 0
  let h_abs_ss : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff s₁ s₂) .zero) :=
    .mp (.mp (abs_diff_self adm (.app .succ .zero))
      (.mp (.mp (.mp h_abs_r (.mp h_abs_l and_intro)) Derivable.trans0)
        and_intro)) Derivable.trans0
  let h_same := .mp (.mp (sg_bar_zero (Γ := Γ))
    (.mp (sg_bar_congr h_abs_ss) and_intro)) Derivable.trans0
  -- result_sign = ite(same, s₁, ...) =₀ ite(S0, S0, ...) =₀ S0
  let h_rsign1 := ite_nat_congr_b (x := s₁)
    (y := Term.app3 Term.ite_nat (Term.app2 Term.geq a b) s₁ s₂) h_same
  let h_rsign2 := ite_nat_one adm s₁ (Term.app3 Term.ite_nat (Term.app2 Term.geq a b) s₁ s₂)
  let h_rsign3 := .mp (.mp h_rsign2 (.mp h_rsign1 and_intro)) Derivable.trans0
  let h_rsign := .mp (.mp hs₁ (.mp h_rsign3 and_intro)) Derivable.trans0
  -- result_num = ite(same, add(a, b), ...) =₀ ite(S0, ...) =₀ add(a, b) =₀ add(S0, 0) =₀ S0
  let h_rnum1 := ite_nat_congr_b (x := Term.app2 Term.add a b)
    (y := Term.app2 Term.abs_diff a b) h_same
  let h_rnum2 := ite_nat_one adm (Term.app2 Term.add a b) (Term.app2 Term.abs_diff a b)
  let h_rnum3 := .mp (.mp h_rnum2 (.mp h_rnum1 and_intro)) Derivable.trans0
  -- add(a, b) =₀ add(S0, 0) =₀ S0
  let h_ab := .mp (.mp (add_zero_r adm (.app .succ .zero))
    (.mp (.mp (.mp (add_congr_r (.app .succ .zero) hb)
      (.mp (add_congr_l ha b) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  let h_rnum := .mp (.mp h_ab (.mp h_rnum3 and_intro)) Derivable.trans0
  -- result_den_m1 = pd(mul(d₁, d₂)) =₀ pd(mul(S0, S0)) =₀ pd(S0) =₀ 0
  let h_dd := .mp (.mp (mul_one_r adm (.app .succ .zero))
    (.mp (.mp (.mp (mul_congr_r (.app .succ .zero) hd₂)
      (.mp (mul_congr_l hd₁ d₂) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  let h_rden := .mp (.mp (pd_succ adm Term.zero) (.mp (pd_congr h_dd) and_intro)) Derivable.trans0
  -- NF = rat_encode(result_sign, result_num, result_den_m1) =₀ rat_encode(S0, S0, 0) = one_Q
  -- We need rat_encode(S0, S0, 0) =₀ one_Q
  -- rat_encode(S0, S0, 0) = pair(monus(mul(2, S0), isEven(S0)), 0) = pair(monus(2, 0), 0) = pair(2, 0) = one_Q
  let enc_body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)
  have enc_eq : (Term.rat_encode : Term F Γ _) = Term.lam (Term.lam (Term.lam enc_body)) := by rfl
  let one := (.app Term.succ Term.zero : Term F Γ Ty.nat)
  have enc_nf2 : ((enc_body.subst0 ((Term.zero : Term F Γ _).weaken.weaken)).subst0 one.weaken).subst0 one =
      Term.app2 Term.pair
        (Term.app2 Term.monus (Term.app2 Term.mul (Term.ofNat 2) one)
          (.app Term.isEven one))
        (Term.zero : Term F Γ _) := by
    simp only [enc_body, one, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      Term.ofNat, pair_closed_subst, monus_closed_subst, mul_closed_subst,
      isEven_closed_subst, weaken_subst0_eta]
  let h_enc := enc_eq ▸ lam3_correct_nf adm enc_body one one Term.zero enc_nf2
  -- mul(2, S0) =₀ 2
  let h_mul2 := mul_one_r adm (Term.ofNat 2)
  -- isEven(S0) =₀ sg_bar(isEven(0)) =₀ sg_bar(S0) =₀ 0
  let h_isE1 := .mp (.mp (sg_bar_succ adm Term.zero)
    (.mp (.mp (.mp (sg_bar_congr isEven_zero)
      (.mp (isEven_succ adm Term.zero) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  -- monus(2, 0) =₀ 2
  let h_mon2 := .mp (.mp (monus_zero adm (Term.ofNat 2))
    (.mp (.mp (.mp (monus_congr_r _ h_isE1) (.mp (monus_congr_l h_mul2 _) and_intro))
      Derivable.trans0) and_intro)) Derivable.trans0
  -- pair(2, 0) = one_Q (syntactically)
  let h_pair2 := pair_congr h_mon2 (Derivable.refl0 (t := Term.zero))
  -- rat_encode(S0, S0, 0) =₀ pair(2, 0) = one_Q
  let h_enc_val := .mp (.mp h_pair2 (.mp h_enc and_intro)) Derivable.trans0
  -- NF =₀ rat_encode(S0, S0, 0) =₀ one_Q
  let h_nf_to_enc := rat_encode_congr h_rsign h_rnum h_rden
  let h_nf_to_one := .mp (.mp h_enc_val (.mp h_nf_to_enc and_intro)) Derivable.trans0
  -- add_Q(one_Q, zero_Q) =₀ NF =₀ one_Q
  .mp (.mp h_nf_to_one (.mp h_unfold and_intro)) Derivable.trans0

/-- sub_Q(one_Q, zero_Q) =₀ one_Q -/
private def sub_Q_one_zero (adm : AdmissibleEqX EqX) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.sub_Q Term.one_Q Term.zero_Q) Term.one_Q) :=
  .mp (.mp (add_Q_one_zero adm)
    (.mp (sub_Q_one_zero_unfold (adm := adm)) and_intro)) Derivable.trans0

/-- ⊢ lt_Q(zero_Q, one_Q) -/
def zero_lt_one_Q :
    Derivable F EqX al Premises (Γ := Γ)
      (lt_Q Term.zero_Q Term.one_Q) :=
  -- lt_Q(zero_Q, one_Q) = eq0(lt_Q_dec(zero_Q, one_Q), 0)
  -- lt_Q_dec(zero_Q, one_Q) = add(|rat_sign(D) - S0|, sg_bar(rat_num(D)))
  -- where D = sub_Q(one_Q, zero_Q) =₀ one_Q
  let lt_body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let diff := Term.app2 Term.sub_Q (.var .vz) (.var (.vs .vz))
    Term.app2 Term.add
      (Term.app2 Term.abs_diff (.app Term.rat_sign diff) (.app .succ .zero))
      (.app Term.sg_bar (.app Term.rat_num diff))
  have lt_eq : (Term.lt_Q_dec : Term F Γ _) = Term.lam (Term.lam lt_body) := by rfl
  let D : Term F Γ Ty.nat := Term.app2 Term.sub_Q Term.one_Q Term.zero_Q
  have lt_nf : (lt_body.subst0 (Term.one_Q.weaken (σ := Ty.nat))).subst0 Term.zero_Q =
      Term.app2 Term.add
        (Term.app2 Term.abs_diff (.app Term.rat_sign D) (.app .succ .zero))
        (.app Term.sg_bar (.app Term.rat_num D)) := by
    simp only [lt_body, D, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      sub_Q_closed_subst, add_closed_subst, abs_diff_closed_subst, rat_sign_closed_subst,
      sg_bar_closed_subst, rat_num_closed_subst, weaken_subst0_eta]
  let h_unfold := lt_eq ▸ lam2_correct_nf adm lt_body Term.zero_Q Term.one_Q lt_nf
  -- D = sub_Q(one_Q, zero_Q) =₀ one_Q
  let hD := sub_Q_one_zero adm (Γ := Γ)
  -- rat_sign(D) =₀ rat_sign(one_Q) =₀ S0
  let h_sign := .mp (.mp (rat_sign_one_Q (adm := adm))
    (.mp (rat_sign_congr hD) and_intro)) Derivable.trans0
  -- |rat_sign(D) - S0| =₀ |S0 - S0| =₀ 0
  let h_abs := .mp (.mp (abs_diff_self adm (Term.app Term.succ Term.zero))
    (.mp (qfer_no_premise_nat_nf h_sign
      (r := Term.app2 Term.abs_diff (.var .vz) (Term.app Term.succ Term.zero).weaken)
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])
      (by simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
          abs_diff_closed_subst, weaken_subst0_eta])) and_intro)) Derivable.trans0
  -- rat_num(D) =₀ rat_num(one_Q) =₀ S0
  let h_num := .mp (.mp (rat_num_one_Q (adm := adm))
    (.mp (rat_num_congr hD) and_intro)) Derivable.trans0
  -- sg_bar(rat_num(D)) =₀ sg_bar(S0) =₀ 0
  let h_sgb := .mp (.mp (sg_bar_succ adm Term.zero)
    (.mp (sg_bar_congr h_num) and_intro)) Derivable.trans0
  -- add(0, 0) =₀ 0
  let h_sum := .mp (.mp (add_zero_r adm Term.zero)
    (.mp (.mp (.mp (add_congr_r .zero h_sgb)
      (.mp (add_congr_l h_abs _) and_intro)) Derivable.trans0) and_intro)) Derivable.trans0
  -- Chain: lt_Q_dec(zero_Q, one_Q) =₀ add(...) =₀ 0
  .mp (.mp h_sum (.mp h_unfold and_intro)) Derivable.trans0

-- ── Congruence (eq_Q respects operations) ──────────────────────────────────

/-- Right congruence for add_Q: eq_Q(c,d) → eq_Q(add_Q(a,c), add_Q(a,d)). -/
private def add_Q_right_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var .vz)))))) :=
  sorry


/-- `add_Q_right_congr` instantiated at three explicit terms, with the resulting formula
stated. See `q_norm`. -/
private def add_Q_right_congr_inst (adm : AdmissibleEqX EqX) (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (eq_Q y z →ᶠ eq_Q (Term.app2 Term.add_Q x y) (Term.app2 Term.add_Q x z)) := by
  have h := Derivable.mp (Derivable.mp (Derivable.mp
    (add_Q_right_congr (EqX := EqX) (al := al) (Premises := Premises) (Γ := Γ))
    (.forall_ax x)) (.forall_ax y)) (.forall_ax z)
  q_norm using h

/-- ⊢ ∀a,b,c,d. eq_Q(a,b) ∧ eq_Q(c,d) → eq_Q(add_Q(a,c), add_Q(b,d)) -/
def add_Q_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.add_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
            (Term.app2 Term.add_Q (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  let a : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) _ := .var (.vs (.vs (.vs .vz)))
  let b : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) _ := .var (.vs (.vs .vz))
  let c : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let d : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let aac := Term.app2 Term.add_Q a c
  let aad := Term.app2 Term.add_Q a d
  let abd := Term.app2 Term.add_Q b d
  let ada := Term.app2 Term.add_Q d a
  let adb := Term.app2 Term.add_Q d b
  -- Right congr
  let rc_inst_a := add_Q_right_congr_inst adm a c d
  -- Commutativity instances
  let comm_ad := add_Q_comm_inst adm a d
  let rc_inst_d := add_Q_right_congr_inst adm d a b
  let comm_db := add_Q_comm_inst adm d b
  -- trans helper
  let trans_inst (x y z : Term F _ Ty.nat) := eq_Q_trans_inst adm x y z
  -- eq_Q(a,b) → eq_Q(add_Q(a,d), add_Q(d,b)) via comm_ad + right_congr
  let step2a : Derivable F EqX al Premises (eq_Q a b →ᶠ eq_Q aad adb) :=
    let t1 := trans_inst aad ada adb
    .syllogism (pair_h (weaken_intro comm_ad) rc_inst_d) t1
  -- eq_Q(a,b) → eq_Q(add_Q(a,d), add_Q(b,d)) via step2a + comm_db
  let step2b : Derivable F EqX al Premises (eq_Q a b →ᶠ eq_Q aad abd) :=
    .syllogism (pair_h step2a (weaken_intro comm_db)) (trans_inst aad adb abd)
  -- Combine: eq_Q(a,b) ∧ eq_Q(c,d) → eq_Q(aac, aad) ∧ eq_Q(aad, abd) → eq_Q(aac, abd)
  let combined : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q c d →ᶠ eq_Q aac abd) :=
    .syllogism (pair_h (.syllogism and_proj2 rc_inst_a) (.syllogism .and_weak step2b))
      (trans_inst aac aad abd)
  univ_gen (univ_gen (univ_gen (univ_gen combined)))

/-- S(pd(S(x)*S(y))) =₀ S(x)*S(y). Products of successors are successors, so S∘pd is identity. -/
private def succ_pd_mul_succ (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (.app Term.pd (Term.app2 Term.mul (.app .succ x) (.app .succ y))))
                   (Term.app2 Term.mul (.app .succ x) (.app .succ y))) :=
  let k := Term.app2 Term.add (Term.app2 Term.mul x (.app .succ y)) y
  let h1 := mul_succ_l adm x (.app .succ y)
  let h2 := add_succ adm (Term.app2 Term.mul x (.app .succ y)) y
  let h_eq := .mp (.mp h2 (.mp h1 and_intro)) .trans0
  let h_pd := pd_succ adm k
  let h_pd_eq := .mp (.mp h_pd (.mp (pd_congr h_eq) and_intro)) .trans0
  .mp (.mp (.mp h_eq .sym0) (.mp (succ_congr h_pd_eq) and_intro)) .trans0

/-- S(pd(da*dc)) =₀ da*dc where da = rat_den(a), dc = rat_den(c). -/
private def succ_pd_den_mul (a c : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app .succ (.app Term.pd
          (Term.app2 Term.mul (.app Term.rat_den a) (.app Term.rat_den c))))
        (Term.app2 Term.mul (.app Term.rat_den a) (.app Term.rat_den c))) :=
  let spa := Term.app Term.snd_pair a
  let spc := Term.app Term.snd_pair c
  let h_da := rat_den_unfold_eq a
  let h_dc := rat_den_unfold_eq c
  let h_prod := .mp (.mp (mul_congr_r _ h_dc) (.mp (mul_congr_l h_da _) and_intro)) .trans0
  let h_core := succ_pd_mul_succ adm spa spc
  let h1 := succ_congr (pd_congr h_prod)
  .mp (.mp (.mp h_prod .sym0) (.mp (.mp (.mp h_core (.mp h1 and_intro)) .trans0) and_intro)) .trans0

/-- ⊢ ∀a,c,d. eq_Q(c,d) → eq_Q(mul_Q(a,c), mul_Q(a,d)).
    Right congruence: when the first argument is fixed. -/
private def mul_Q_right_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var .vz)))))) :=
  let a : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs (.vs .vz))
  let c : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let d : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let na := Term.app Term.rat_num a
  let nc := Term.app Term.rat_num c
  let nd := Term.app Term.rat_num d
  let da := Term.app Term.rat_den a
  let dc := Term.app Term.rat_den c
  let dd := Term.app Term.rat_den d
  let sa := Term.app Term.rat_sign a
  let sc := Term.app Term.rat_sign c
  let sd := Term.app Term.rat_sign d
  let mac := Term.app2 Term.mul_Q a c
  let mad := Term.app2 Term.mul_Q a d
  -- Unfold mul_Q body
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
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
  have body_eq : (Term.mul_Q : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  let sign_ac := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sc)
  let num_ac := Term.app2 Term.mul na nc
  let den_ac := Term.app Term.pd (Term.app2 Term.mul da dc)
  let sign_ad := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sd)
  let num_ad := Term.app2 Term.mul na nd
  let den_ad := Term.app Term.pd (Term.app2 Term.mul da dd)
  have nf_ac : (body.subst0 (c.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_ac num_ac den_ac := by
    simp only [body, a, c, sa, sc, na, nc, da, dc, sign_ac, num_ac, den_ac,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
      mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      rat_sign_closed_subst, pd_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  have nf_ad : (body.subst0 (d.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_ad num_ad den_ad := by
    simp only [body, a, d, sa, sd, na, nd, da, dd, sign_ad, num_ad, den_ad,
      Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
      rat_encode_closed_subst, sg_bar_closed_subst, abs_diff_closed_subst,
      mul_closed_subst, rat_num_closed_subst, rat_den_closed_subst,
      rat_sign_closed_subst, pd_closed_subst,
      Term.weaken, Term.rename, Term.Renaming.shift]
  let unfold_ac : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul_Q a c) (Term.app3 Term.rat_encode sign_ac num_ac den_ac)) :=
    body_eq ▸ lam2_correct_nf adm body a c nf_ac
  let unfold_ad : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.mul_Q a d) (Term.app3 Term.rat_encode sign_ad num_ad den_ad)) :=
    body_eq ▸ lam2_correct_nf adm body a d nf_ad
  -- Component equalities for mac
  let h_num_ac : Derivable F EqX al Premises (Formula.eq0 (.app Term.rat_num mac) num_ac) :=
    .mp (.mp (rat_num_rat_encode adm sign_ac num_ac den_ac (isEven_cases adm sign_ac))
      (.mp (rat_num_congr unfold_ac) and_intro)) .trans0
  let h_den_ac : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den mac) (.app .succ den_ac)) :=
    .mp (.mp (rat_den_rat_encode adm sign_ac num_ac den_ac)
      (.mp (rat_den_congr unfold_ac) and_intro)) .trans0
  -- S(pd(da*dc)) = da*dc
  let h_spd_ac := succ_pd_den_mul adm a c
  -- rat_den(mac) = da*dc
  let h_den_ac_eq : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den mac) (Term.app2 Term.mul da dc)) :=
    .mp (.mp h_spd_ac (.mp h_den_ac and_intro)) .trans0
  -- Component equalities for mad (symmetric)
  let h_num_ad : Derivable F EqX al Premises (Formula.eq0 (.app Term.rat_num mad) num_ad) :=
    .mp (.mp (rat_num_rat_encode adm sign_ad num_ad den_ad (isEven_cases adm sign_ad))
      (.mp (rat_num_congr unfold_ad) and_intro)) .trans0
  let h_den_ad : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den mad) (.app .succ den_ad)) :=
    .mp (.mp (rat_den_rat_encode adm sign_ad num_ad den_ad)
      (.mp (rat_den_congr unfold_ad) and_intro)) .trans0
  let h_den_ad_eq : Derivable F EqX al Premises
      (Formula.eq0 (.app Term.rat_den mad) (Term.app2 Term.mul da dd)) :=
    .mp (.mp (succ_pd_den_mul adm a d) (.mp h_den_ad and_intro)) .trans0
  -- ═══ Extract from hypothesis eq_Q(c,d) ═══
  -- Unfold eq_Q_dec(c,d) to |nc*dd - nd*dc| + |sc-sd|*sg(nc+nd)
  let eqd_body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have eqd_body_eq : (Term.eq_Q_dec : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam eqd_body) := by rfl
  let cross_cd := Term.app2 Term.abs_diff (Term.app2 Term.mul nc dd) (Term.app2 Term.mul nd dc)
  let sign_cd := Term.app2 Term.mul (Term.app2 Term.abs_diff sc sd)
      (Term.app Term.sg (Term.app2 Term.add nc nd))
  have eqd_nf : (eqd_body.subst0 (d.weaken)).subst0 c =
      Term.app2 Term.add cross_cd sign_cd := by
    simp only [eqd_body, c, d, nc, nd, dc, dd, sc, sd, cross_cd, sign_cd,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst,
      rat_num_closed_subst, rat_den_closed_subst, rat_sign_closed_subst,
      sg_closed_subst, Term.weaken, Term.rename, Term.Renaming.shift]
  let unfold_eqd := eqd_body_eq ▸ lam2_correct_nf adm eqd_body c d eqd_nf
  let H_to_nf : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0 (Term.app2 Term.add cross_cd sign_cd) .zero) :=
    .syllogism (pair_h (weaken_intro_h (.mp unfold_eqd .sym0)) I_comb) .trans0
  let H_to_cross_cd : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0 cross_cd .zero) :=
    .syllogism H_to_nf (.syllogism (Derivable.mp (add_eq_zero_iff adm cross_cd sign_cd) .and_weak) .and_weak)
  let H_to_sign_cd : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0 sign_cd .zero) :=
    .syllogism H_to_nf (.syllogism (Derivable.mp (add_eq_zero_iff adm cross_cd sign_cd) .and_weak) and_proj2)
  let H_to_eq_cd : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0 (Term.app2 Term.mul nc dd) (Term.app2 Term.mul nd dc)) :=
    .syllogism H_to_cross_cd (abs_diff_zero_fwd adm _ _)
  -- ═══ CROSS PART ═══
  -- Need: |num_ac * den_mad - num_ad * den_mac| = 0
  -- i.e., |na*nc*(da*dd) - na*nd*(da*dc)| = 0
  -- Rearrange: (na*da)*(nc*dd) = (na*da)*(nd*dc), follows from nc*dd = nd*dc
  let H_to_cross : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0
        (Term.app2 Term.abs_diff
          (Term.app2 Term.mul (.app Term.rat_num mac) (.app Term.rat_den mad))
          (Term.app2 Term.mul (.app Term.rat_num mad) (.app Term.rat_den mac)))
        .zero) :=
    -- rat_num(mac)*rat_den(mad) = num_ac*(da*dd) and rat_num(mad)*rat_den(mac) = num_ad*(da*dc)
    -- by substituting the component equalities
    let lhs_eq : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.mul (.app Term.rat_num mac) (.app Term.rat_den mad))
          (Term.app2 Term.mul num_ac (Term.app2 Term.mul da dd))) :=
      .mp (.mp (mul_congr_r _ h_den_ad_eq) (.mp (mul_congr_l h_num_ac _) and_intro)) .trans0
    let rhs_eq : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.mul (.app Term.rat_num mad) (.app Term.rat_den mac))
          (Term.app2 Term.mul num_ad (Term.app2 Term.mul da dc))) :=
      .mp (.mp (mul_congr_r _ h_den_ac_eq) (.mp (mul_congr_l h_num_ad _) and_intro)) .trans0
    -- abs_diff(LHS, RHS) = abs_diff(num_ac*(da*dd), num_ad*(da*dc))
    let h_ad := abs_diff_congr lhs_eq rhs_eq
    -- Now: num_ac*(da*dd) = (na*nc)*(da*dd). Rearrange to (na*da)*(nc*dd).
    -- (na*nc)*(da*dd) = na*(nc*(da*dd)) [assoc]
    -- = na*((nc*da)*dd) [assoc on nc,da,dd... wait, nc*(da*dd)]
    -- Simpler: (na*nc)*(da*dd) and (na*nd)*(da*dc)
    -- multiply H_to_eq_cd (nc*dd = nd*dc) by na*da on the left:
    -- (na*da)*(nc*dd) = (na*da)*(nd*dc)
    let H_scaled := .syllogism H_to_eq_cd (mul_congr_r_imp (Term.app2 Term.mul na da))
    -- Show: (na*nc)*(da*dd) = (na*da)*(nc*dd) and (na*nd)*(da*dc) = (na*da)*(nd*dc)
    -- Both by associativity + commutativity
    -- (na*nc)*(da*dd) = na*(nc*(da*dd)) = na*((da*nc)*dd) ... hmm
    -- Actually: (na*nc)*(da*dd) = ((na*nc)*da)*dd [assoc.sym on (na*nc),da,dd]
    --         = (na*(nc*da))*dd [assoc on na,nc,da]
    --         = (na*(da*nc))*dd [comm nc,da]
    --         = ((na*da)*nc)*dd [assoc.sym on na,da,nc]
    --         = (na*da)*(nc*dd) [assoc on (na*da),nc,dd]
    let e1 := .mp (mul_assoc adm (Term.app2 Term.mul na nc) da dd) .sym0
    let e2 := mul_congr_l (mul_assoc adm na nc da) dd
    let e3 := mul_congr_l (mul_congr_r na (mul_comm adm nc da)) dd
    let e4 := mul_congr_l (.mp (mul_assoc adm na da nc) .sym0) dd
    let e5 := mul_assoc adm (Term.app2 Term.mul na da) nc dd
    let lhs_rearr : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.mul num_ac (Term.app2 Term.mul da dd))
          (Term.app2 Term.mul (Term.app2 Term.mul na da) (Term.app2 Term.mul nc dd))) :=
      .mp (.mp e5 (.mp (.mp (.mp e4 (.mp (.mp (.mp e3 (.mp (.mp (.mp e2 (.mp e1 and_intro))
        .trans0) and_intro)) .trans0) and_intro)) .trans0) and_intro)) .trans0
    -- Symmetric for RHS: (na*nd)*(da*dc) = (na*da)*(nd*dc)
    let f1 := .mp (mul_assoc adm (Term.app2 Term.mul na nd) da dc) .sym0
    let f2 := mul_congr_l (mul_assoc adm na nd da) dc
    let f3 := mul_congr_l (mul_congr_r na (mul_comm adm nd da)) dc
    let f4 := mul_congr_l (.mp (mul_assoc adm na da nd) .sym0) dc
    let f5 := mul_assoc adm (Term.app2 Term.mul na da) nd dc
    let rhs_rearr : Derivable F EqX al Premises
        (Formula.eq0 (Term.app2 Term.mul num_ad (Term.app2 Term.mul da dc))
          (Term.app2 Term.mul (Term.app2 Term.mul na da) (Term.app2 Term.mul nd dc))) :=
      .mp (.mp f5 (.mp (.mp (.mp f4 (.mp (.mp (.mp f3 (.mp (.mp (.mp f2 (.mp f1 and_intro))
        .trans0) and_intro)) .trans0) and_intro)) .trans0) and_intro)) .trans0
    -- H → (na*da)*(nc*dd) = (na*da)*(nd*dc) [from H_scaled]
    -- H → num_ac*(da*dd) = (na*da)*(nc*dd) = (na*da)*(nd*dc) = num_ad*(da*dc)
    let H_to_prod_eq : Derivable F EqX al Premises
        (eq_Q c d →ᶠ Formula.eq0 (Term.app2 Term.mul num_ac (Term.app2 Term.mul da dd))
          (Term.app2 Term.mul num_ad (Term.app2 Term.mul da dc))) :=
      .syllogism (pair_h (weaken_intro_h lhs_rearr) H_scaled) .trans0
      |> fun h => .syllogism (pair_h h (weaken_intro_h (.mp rhs_rearr .sym0))) .trans0
    -- abs_diff of originals = abs_diff of products = 0
    let H_to_ad_zero : Derivable F EqX al Premises
        (eq_Q c d →ᶠ Formula.eq0
          (Term.app2 Term.abs_diff (Term.app2 Term.mul num_ac (Term.app2 Term.mul da dd))
            (Term.app2 Term.mul num_ad (Term.app2 Term.mul da dc))) .zero) :=
      .syllogism H_to_prod_eq
        (.mp (abs_diff_eq_zero_iff adm _ _) (.syllogism .and_perm .and_weak))
    .syllogism (pair_h (weaken_intro_h h_ad) H_to_ad_zero) .trans0
  -- ═══ SIGN PART ═══
  let H_to_sign : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0
        (Term.app2 Term.mul
          (Term.app2 Term.abs_diff (.app Term.rat_sign mac) (.app Term.rat_sign mad))
          (Term.app Term.sg (Term.app2 Term.add (.app Term.rat_num mac) (.app Term.rat_num mad))))
        .zero) :=
    -- PLAN (checked against the available lemmas; not yet written).
    -- Write `numS := rat_num mac + rat_num mad`, `signD := |rat_sign mac − rat_sign mad|`.
    -- Both branches finish through `mul_eq_zero_iff adm signD (sg numS) |> and_proj2`,
    -- fed `.or_weak` (left) or `or_inr` (right). Split with `sg_bar_cases adm numS`, using
    -- the under-hypothesis idiom `.syllogism (pair_h I_comb (weaken_intro …))
    --   (.syllogism and_or_dist (or_elim_rule … …))`.
    --
    -- Branch `sg_bar numS =₀ S0`: `sg_bar_eq_S0_implies_zero` gives `numS =₀ 0`; then
    --   `.qfer (r := .app Term.sg (.var .vz))` plus `sg_zero` gives `sg numS =₀ 0`. No H needed.
    --
    -- Branch `sg_bar numS =₀ 0` (so `numS ≠ 0`): must show `rat_sign mac =₀ rat_sign mad`,
    -- then `abs_diff_eq_zero_iff` closes. Steps:
    --   1. `h_num_ac`/`h_num_ad` rewrite `numS` to `na*nc + na*nd`. From `numS ≠ 0`:
    --      `na ≠ 0`, and `nc ≠ 0 ∨ nd ≠ 0`.
    --   2. `H_to_eq_cd : nc*dd =₀ nd*dc` upgrades that to `nc ≠ 0 ∧ nd ≠ 0`: if `nc =₀ 0`
    --      then `nd*dc =₀ 0`, and `dc` is a successor (`rat_den_unfold_eq`), so
    --      `mul_succ_eq_zero_imp` gives `nd =₀ 0` — contradicting step 1. Symmetrically.
    --   3. `H_to_sign_cd : |sc − sd| * sg(nc + nd) =₀ 0` with `nc + nd ≠ 0`: `mul_eq_zero_iff`
    --      forward plus `sg_zero_fwd` kills the right disjunct, leaving `sc =₀ sd`.
    --   4. `sc =₀ sd` ⟹ `sign_ac =₀ sign_ad` (`abs_diff_congr_r`, `sg_bar_congr`)
    --      ⟹ `isEven sign_ac =₀ isEven sign_ad` (`isEven_congr`).
    --   5. `isEven_cases adm sign_ac`, and in each branch `rat_sign_rat_encode_pos` /
    --      `rat_sign_rat_encode_neg` (the latter needs `num_ac ≠ 0`, which is step 1+2)
    --      applied through `unfold_ac`/`unfold_ad` gives `rat_sign mac =₀ rat_sign mad`.
    sorry
  -- ═══ COMBINE ═══
  -- Unfold eq_Q_dec(mac, mad)
  let eqd2 : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.abs_diff
        (Term.app2 Term.mul (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_den (.var .vz)))
        (Term.app2 Term.mul (Term.app Term.rat_num (.var .vz)) (Term.app Term.rat_den (.var (.vs .vz)))))
      (Term.app2 Term.mul
        (Term.app2 Term.abs_diff (Term.app Term.rat_sign (.var (.vs .vz))) (Term.app Term.rat_sign (.var .vz)))
        (Term.app Term.sg (Term.app2 Term.add (Term.app Term.rat_num (.var (.vs .vz))) (Term.app Term.rat_num (.var .vz)))))
  have eqd2_eq : (Term.eq_Q_dec : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam eqd2) := by rfl
  let cross_mm := Term.app2 Term.abs_diff
    (Term.app2 Term.mul (.app Term.rat_num mac) (.app Term.rat_den mad))
    (Term.app2 Term.mul (.app Term.rat_num mad) (.app Term.rat_den mac))
  let sign_mm := Term.app2 Term.mul
    (Term.app2 Term.abs_diff (.app Term.rat_sign mac) (.app Term.rat_sign mad))
    (Term.app Term.sg (Term.app2 Term.add (.app Term.rat_num mac) (.app Term.rat_num mad)))
  have eqd2_nf : (eqd2.subst0 (mad.weaken)).subst0 mac =
      Term.app2 Term.add cross_mm sign_mm := by
    simp only [eqd2, mac, mad, cross_mm, sign_mm,
      Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, abs_diff_closed_subst, mul_closed_subst,
      rat_num_closed_subst, rat_den_closed_subst, rat_sign_closed_subst,
      sg_closed_subst, mul_Q_closed_subst, weaken_subst0_eta]
  let unfold_mm := eqd2_eq ▸ lam2_correct_nf adm eqd2 mac mad eqd2_nf
  -- H → NF(mac,mad) = 0
  let H_to_nf_zero : Derivable F EqX al Premises
      (eq_Q c d →ᶠ Formula.eq0 (Term.app2 Term.add cross_mm sign_mm) .zero) :=
    .syllogism (pair_h H_to_cross H_to_sign)
      (Derivable.mp (add_eq_zero_iff adm cross_mm sign_mm) (.syllogism .and_perm .and_weak))
  -- eq_Q_dec(mac,mad) = NF → NF = 0 → eq_Q_dec(mac,mad) = 0
  let core : Derivable F EqX al Premises (eq_Q c d →ᶠ eq_Q mac mad) :=
    .syllogism (pair_h (weaken_intro_h unfold_mm) H_to_nf_zero) .trans0
  univ_gen (univ_gen (univ_gen core))


/-- `mul_Q_right_congr` instantiated at three explicit terms, with the resulting formula
stated. See `q_norm`. -/
private def mul_Q_right_congr_inst (adm : AdmissibleEqX EqX) (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (eq_Q y z →ᶠ eq_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q x z)) := by
  have h := Derivable.mp (Derivable.mp (Derivable.mp
    (mul_Q_right_congr (adm := adm) (al := al) (Premises := Premises) (Γ := Γ))
    (.forall_ax x)) (.forall_ax y)) (.forall_ax z)
  q_norm using h

def mul_Q_congr :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          ∧ᶠ eq_Q (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_Q
            (Term.app2 Term.mul_Q (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
            (Term.app2 Term.mul_Q (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  -- Variables: a = var 3, b = var 2, c = var 1, d = var 0
  let a : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs (.vs (.vs .vz)))
  let b : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs (.vs .vz))
  let c : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let d : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let mac := Term.app2 Term.mul_Q a c
  let mad := Term.app2 Term.mul_Q a d
  let mbd := Term.app2 Term.mul_Q b d
  let mda := Term.app2 Term.mul_Q d a
  let mdb := Term.app2 Term.mul_Q d b
  -- Step 1: eq_Q(c,d) → eq_Q(mul_Q(a,c), mul_Q(a,d))  [right congr]
  let rc_inst_a := mul_Q_right_congr_inst adm a c d
  -- rc_inst_a : eq_Q(c,d) → eq_Q(mul_Q(a,c), mul_Q(a,d))
  -- Step 2: eq_Q(a,b) → eq_Q(mul_Q(a,d), mul_Q(b,d))  [left congr via comm]
  -- mul_Q(a,d) =_Q mul_Q(d,a) (comm)
  let comm_ad := mul_Q_comm_inst adm a d
  -- eq_Q(a,b) → eq_Q(mul_Q(d,a), mul_Q(d,b)) (right congr with d fixed)
  let rc_inst_d := mul_Q_right_congr_inst adm d a b
  -- mul_Q(d,b) =_Q mul_Q(b,d) (comm)
  let comm_db := mul_Q_comm_inst adm d b
  -- Chain: eq_Q(a,b) → eq_Q(mul_Q(a,d), mul_Q(d,a)) ∧ eq_Q(mul_Q(d,a), mul_Q(d,b))
  --        → eq_Q(mul_Q(a,d), mul_Q(d,b))
  --        → eq_Q(mul_Q(a,d), mul_Q(d,b)) ∧ eq_Q(mul_Q(d,b), mul_Q(b,d))
  --        → eq_Q(mul_Q(a,d), mul_Q(b,d))
  -- trans: ∀x,y,z. eq_Q(x,y) ∧ eq_Q(y,z) → eq_Q(x,z)
  let trans_inst (x y z : Term F _ Ty.nat) := eq_Q_trans_inst adm x y z
  -- eq_Q(a,b) → eq_Q(mul_Q(d,a), mul_Q(d,b))
  -- step2a: eq_Q(a,b) → eq_Q(mul_Q(a,d), mul_Q(d,b))
  --   = trans(mul_Q(a,d), mul_Q(d,a), mul_Q(d,b)) applied to (comm_ad, rc_inst_d(eq_Q(a,b)))
  let t1 : Derivable F EqX al Premises
      (eq_Q mad mda ∧ᶠ eq_Q mda mdb →ᶠ eq_Q mad mdb) := trans_inst mad mda mdb
  let step2a : Derivable F EqX al Premises
      (eq_Q a b →ᶠ eq_Q mad mdb) :=
    .syllogism (pair_h (weaken_intro comm_ad) rc_inst_d) t1
  let t2 : Derivable F EqX al Premises
      (eq_Q mad mdb ∧ᶠ eq_Q mdb mbd →ᶠ eq_Q mad mbd) := trans_inst mad mdb mbd
  let step2b : Derivable F EqX al Premises
      (eq_Q a b →ᶠ eq_Q mad mbd) :=
    .syllogism (pair_h step2a (weaken_intro comm_db)) t2
  -- Step 3: Combine using eq_Q_trans
  -- eq_Q(a,b) ∧ eq_Q(c,d) → eq_Q(mac, mad) ∧ eq_Q(mad, mbd) → eq_Q(mac, mbd)
  let combined : Derivable F EqX al Premises
      (eq_Q a b ∧ᶠ eq_Q c d →ᶠ eq_Q mac mbd) :=
    .syllogism (pair_h (.syllogism and_proj2 rc_inst_a) (.syllogism .and_weak step2b))
      (trans_inst mac mad mbd)
  univ_gen (univ_gen (univ_gen (univ_gen combined)))

end RationalOrderedField

end Metatheorems
