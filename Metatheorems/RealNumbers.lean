/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Arithmetic

namespace Metatheorems

/-!
# Real Numbers in WE-HA^{ω}

Real numbers are encoded as rapidly converging Cauchy sequences of rationals.
Following §real-numbers of the reference document, the type of reals is
`1 = 0 → 0` (functions ℕ → ℕ), where `x(n)` encodes a rational approximation
to within 2^{-n}.

## Structure

1. **Auxiliary arithmetic**: `max`, `sg`, `isEven`, `triag`, `exp2`
2. **Cantor pairing**: `pair`, `inv_triag`, `fst_pair`, `snd_pair`
3. **Division by 2**: `div2` (via state-pair recursion using pairing)
4. **Rational encoding**: `rat_num`, `rat_den`, `rat_sign`, `rat_encode`
5. **Rational arithmetic**: `neg_Q`, `add_Q`, `sub_Q`, `mul_Q`, `abs_Q`
6. **Rational comparison**: `le_Q_dec`, `lt_Q_dec` (decision terms, 0 = true)
7. **Rational constants**: `encode_nat_Q`, `pow2neg_Q`
8. **Cauchyfication**: `cauchyfy` (f ↦ f̂)
9. **Real operations**: `eq_R`, `lt_R`, `le_R`, `zero_R`, `add_R`
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
-- Section 8: Cauchyfication
-- ============================================================================

-- Given f : ℕ → ℕ (encoding a sequence of rationals), produce f̂ satisfying
-- the Cauchy condition: ∀n. |f̂(n) -_Q f̂(n+1)|_Q <_Q ⟨2^{-n-1}⟩_Q.
--
-- f̂(n) = f(n) if ∀k < n, |f(k) -_Q f(k+1)|_Q < ⟨2^{-k-1}⟩
--         f(k₀) for the least violating k₀ otherwise.
--
-- Implementation: recursion tracking state pair(value, violation_flag).

/-- The Cauchy condition check at step k for sequence f:
    returns 0 if |f(k) -_Q f(k+1)|_Q <_Q ⟨2^{-k-1}⟩_Q, nonzero otherwise.
    Takes f as a term of type nat →ₜ nat in the context. -/
def cauchy_check_at {Γ : Ctx ι} (f : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app2 Term.lt_Q_dec
    (.app Term.abs_Q
      (Term.app2 Term.sub_Q (.app f k) (.app f (.app .succ k))))
    (.app Term.pow2neg_Q (.app .succ k))

/-- Cauchyfication: maps any f : ℕ → ℕ to f̂ satisfying the Cauchy condition.
    Uses primitive recursion with state = pair(current_value, violation_flag).

    state(f, 0) = pair(f(0), 0)
    state(f, Sk) =
      let v = snd(st), val = fst(st)
      if v = 1 then st                              -- violation found, freeze
      else if cauchy_check(f, k) = 0 then pair(f(Sk), 0)  -- still Cauchy
      else pair(val, 1)                              -- first violation
    cauchyfy(f)(n) = fst(state(f, n)) -/
def cauchyfy {Γ : Ctx ι} : Term F Γ ((Ty.nat →ₜ Ty.nat) →ₜ (Ty.nat →ₜ Ty.nat)) :=
  Term.lam (Term.lam
    -- f = var (vs vz), n = var vz
    -- Build state(f, n) via R at ℕ, then extract fst.
    (.app Term.fst_pair
      (Term.app3 (.prec Ty.nat)
        -- base: pair(f(0), 0)
        (Term.app2 Term.pair
          (.app (.var (.vs .vz)) .zero)               -- f(0), f = var (vs vz) in [n, f, ...Γ]
          .zero)
        -- step: λst k. ...
        -- In context [k, st, n, f, ...Γ]:
        --   st = var (vs vz), k = var vz
        --   f = var (vs (vs (vs vz)))
        (Term.lam (Term.lam
          (let st  := Term.var (.vs .vz)
           let k   := Term.var .vz
           let f   := Term.var (.vs (.vs (.vs .vz)))
           let v   := Term.app Term.snd_pair st      -- violation flag
           let val := Term.app Term.fst_pair st       -- current value
           let chk := Term.app2 Term.lt_Q_dec         -- cauchy check at k
             (.app Term.abs_Q (Term.app2 Term.sub_Q (.app f k) (.app f (.app .succ k))))
             (.app Term.pow2neg_Q (.app .succ k))
           -- if v then st else (if chk = 0 then pair(f(Sk), 0) else pair(val, 1))
           Term.app3 Term.ite_nat v st
             (Term.app3 Term.ite_nat (.app Term.sg_bar chk)
               (Term.app2 Term.pair (.app f (.app .succ k)) .zero)
               (Term.app2 Term.pair val (.app .succ .zero))))))
        (.var .vz))))                                -- n

-- ============================================================================
-- Section 9: Real Number Operations
-- ============================================================================

-- === Terms ===

/-- The real number zero: constant sequence 0_ℚ. -/
def zero_R {Γ : Ctx ι} : Term F Γ (realTy ι) :=
  Term.lam Term.zero_Q

/-- The real number one: constant sequence 1_ℚ. -/
def one_R {Γ : Ctx ι} : Term F Γ (realTy ι) :=
  Term.lam Term.one_Q

/-- Embed a natural number into the reals: (n)_ℝ = λk. encode_nat_Q(n). -/
def embed_nat_R {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ realTy ι) :=
  Term.lam (Term.lam
    (.app Term.encode_nat_Q (.var (.vs .vz))))

/-- Real negation: neg_R(f)(n) = neg_Q(f(n)). -/
def neg_R {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam
    -- f = var (vs vz), n = var vz
    (.app Term.neg_Q (.app (.var (.vs .vz)) (.var .vz))))

/-- Real addition: add_R(f, g)(n) = add_Q(f̂(n+1), ĝ(n+1)).
    The shift by 1 ensures the sum has Cauchy rate 2^{-n}
    (each summand has rate 2^{-(n+1)} and errors add). -/
def add_R {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam (Term.lam
    -- f = var (vs (vs vz)), g = var (vs vz), n = var vz
    (let f := Term.var (.vs (.vs .vz))
     let g := Term.var (.vs .vz)
     let n := Term.var .vz
     let n1 := Term.app .succ n
     Term.app2 Term.add_Q
       (Term.app (Term.app Term.cauchyfy f) n1)
       (Term.app (Term.app Term.cauchyfy g) n1))))

/-- Real subtraction: sub_R(f, g) = add_R(f, neg_R(g)). -/
def sub_R {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam
    (Term.app2 Term.add_R (.var (.vs .vz)) (.app Term.neg_R (.var .vz))))

/-- Real multiplication: mul_R(f, g)(n) = mul_Q(f̂(n + b), ĝ(n + b))
    where b = f(0) + g(0) + 2 bounds the operands, ensuring the product
    has Cauchy rate 2^{-n}. -/
def mul_R {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam (Term.lam
    -- f = var (vs (vs vz)), g = var (vs vz), n = var vz
    (let f := Term.var (.vs (.vs .vz))
     let g := Term.var (.vs .vz)
     let n := Term.var .vz
     -- bound b = f(0) + g(0) + 2
     let b := Term.app2 Term.add
       (Term.app2 Term.add (.app f .zero) (.app g .zero))
       (Term.ofNat 2)
     let nb := Term.app2 Term.add n b
     Term.app2 Term.mul_Q
       (Term.app (Term.app Term.cauchyfy f) nb)
       (Term.app (Term.app Term.cauchyfy g) nb))))

/-- Real absolute value: abs_R(f)(n) = abs_Q(f̂(n)). -/
def abs_R {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam
    (.app Term.abs_Q
      (Term.app (Term.app Term.cauchyfy (.var (.vs .vz))) (.var .vz))))

end Term

-- === Formulas ===

/-- Real equality: f₁ =_ℝ f₂ :≡ ∀n. |f̂₁(n+1) -_ℚ f̂₂(n+1)|_ℚ <_ℚ ⟨2^{-n}⟩_ℚ.
    This is a Π₁⁰ formula (∀ over nat, QF body). -/
def eq_R {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    -- In context [nat, ...Γ]: n = var vz, f,g weakened
    (Formula.eq0
      (Term.app2 Term.lt_Q_dec
        (Term.app Term.abs_Q
          (Term.app2 Term.sub_Q
            (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))
            (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))))
        (Term.app Term.pow2neg_Q (.var .vz)))
      Term.zero)

/-- Real strict less-than: f₁ <_ℝ f₂ :≡ ∃n. f̂₂(n+1) -_ℚ f̂₁(n+1) ≥_ℚ ⟨2^{-n}⟩_ℚ.
    This is a Σ₁⁰ formula (∃ over nat, QF body). -/
def lt_R {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.ex Ty.nat
    -- ĝ(n+1) - f̂(n+1) ≥ 2^{-n}, i.e., le_Q_dec(pow2neg(n), sub(ĝ(n+1), f̂(n+1))) = 0
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))))
      Term.zero)

/-- Real less-than-or-equal: f₁ ≤_ℝ f₂ :≡ ¬(f₂ <_ℝ f₁).
    This is a Π₁⁰ formula. -/
def le_R {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.neg (lt_R g f)

-- ============================================================================
-- Key Properties (statements only)
-- ============================================================================

/-- `eq_R` is quantifier-free under the ∀n wrapper, so the whole formula
    is purely universal (Π₁⁰). This is needed for EqX admissibility. -/
theorem eq_R_isPurelyUniversal (f g : Term F Γ (realTy ι)) :
    (eq_R f g).isPurelyUniversal = true := by rfl

/-- `eq_R` commutes with substitution: naturality for the real equality formula.
    This is needed for `AdmissibleEqX.substF_nat` in the metric space case. -/
theorem eq_R_substF {Γ Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (eq_R f g).substF σ = eq_R (f.subst σ) (g.subst σ) := sorry

-- `le_R` is Π₁⁰ (purely universal after unfolding ¬∃ to ∀¬).
-- Note: le_R unfolds to (∃n. body) → ⊥, which is NOT syntactically purely
-- universal in our formula representation. For metric space axioms that need
-- purely universal premises, we would need to reformulate le_R as
-- ∀n. ¬(body) = ∀n. (body → ⊥). This is logically equivalent but
-- syntactically different. See le_R_unfolded below.

/-- Alternative formulation of ≤_ℝ as a syntactically purely universal formula:
    f₁ ≤_ℝ f₂ :≡ ∀n. ¬(ĝ(n+1) -_ℚ f̂(n+1) ≥_ℚ ⟨2^{-n}⟩_ℚ). -/
def le_R_pu {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (Formula.imp
      (Formula.eq0
        (Term.app2 Term.le_Q_dec
          (Term.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))
            (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))))
        Term.zero)
      ⊥ᶠ)

theorem le_R_pu_isPurelyUniversal (f g : Term F Γ (realTy ι)) :
    (le_R_pu f g).isPurelyUniversal = true := by rfl

/-- `le_R_pu` commutes with substitution. -/
theorem le_R_pu_substF {Γ Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (le_R_pu f g).substF σ = le_R_pu (f.subst σ) (g.subst σ) := sorry

-- ============================================================================
-- Rounding: (·)_∘ for embedding [0,∞) into ℕ^ℕ
-- ============================================================================

/-- Rounding for natural numbers: (x⁰)_∘(n) = pair(x · 2^{n+2}, 2^{n+1} - 1).
    This embeds ℕ into ℝ as a term of type ℕ → (ℕ → ℕ). -/
def Term.round_nat {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ realTy ι) :=
  Term.lam (Term.lam
    -- x = var (vs vz), n = var vz
    (Term.app2 Term.pair
      (Term.app2 Term.mul (.var (.vs .vz))
        (.app Term.exp2 (Term.app2 Term.add (.var .vz) (Term.ofNat 2))))
      (.app Term.pd (.app Term.exp2
        (Term.app2 Term.add (.var .vz) (.app .succ .zero))))))

-- ============================================================================
-- Ordered Field Axioms (Derivable in WE-HA^ω)
-- ============================================================================

-- Following Kohlenbach's condition (m): (ℕ^ℕ, +_ℝ, ·_ℝ, 0_ℝ, 1_ℝ, <_ℝ)
-- is an Archimedean ordered field, provably in WE-HA^ω.

variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) →
    Term F Γ (Ty.base i) → Formula F Γ}
  {al : Allowed} {Premises : PremiseSet F}

-- Notation: real-typed variables in context
private abbrev rTy := realTy ι
-- In context [rTy, Γ]: f = var vz
-- In context [rTy, rTy, Γ]: f = var (vs vz), g = var vz
-- In context [rTy, rTy, rTy, Γ]: f = var (vs (vs vz)), g = var (vs vz), h = var vz

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Additive group ──────────────────────────────────────────────────────────

/-- ⊢ ∀f,g : ℝ. f +_ℝ g =_ℝ g +_ℝ f -/
def add_comm_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_R (.var .vz) (.var (.vs .vz)))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. (f +_ℝ g) +_ℝ h =_ℝ f +_ℝ (g +_ℝ h) -/
def add_assoc_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.add_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.add_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀f : ℝ. f +_ℝ 0_ℝ =_ℝ f -/
def add_zero_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz) Term.zero_R)
              (.var .vz))) :=
  sorry

/-- ⊢ ∀f : ℝ. f +_ℝ neg_R(f) =_ℝ 0_ℝ -/
def add_neg_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz)
                (.app Term.neg_R (.var .vz)))
              Term.zero_R)) :=
  sorry

-- ── Multiplicative monoid ───────────────────────────────────────────────────

/-- ⊢ ∀f,g : ℝ. f ·_ℝ g =_ℝ g ·_ℝ f -/
def mul_comm_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.mul_R (.var .vz) (.var (.vs .vz)))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. (f ·_ℝ g) ·_ℝ h =_ℝ f ·_ℝ (g ·_ℝ h) -/
def mul_assoc_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀f : ℝ. f ·_ℝ 1_ℝ =_ℝ f -/
def mul_one_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var .vz) Term.one_R)
              (.var .vz))) :=
  sorry

-- ── Distributivity ──────────────────────────────────────────────────────────

/-- ⊢ ∀f,g,h : ℝ. f ·_ℝ (g +_ℝ h) =_ℝ (f ·_ℝ g) +_ℝ (f ·_ℝ h) -/
def distrib_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))
          (Term.app2 Term.add_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
              (.var .vz))))))) :=
  sorry

-- ── Order ───────────────────────────────────────────────────────────────────

/-- ⊢ ∀f : ℝ. ¬(f <_ℝ f) (irreflexivity of <_ℝ) -/
def lt_irrefl_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.neg (lt_R (.var .vz) (.var .vz)))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g ∧ g <_ℝ h → f <_ℝ h -/
def lt_trans_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        ((lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ lt_R (.var (.vs .vz)) (.var .vz))
          →ᶠ lt_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g → f +_ℝ h <_ℝ g +_ℝ h -/
def lt_add_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          →ᶠ lt_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var .vz))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))))) :=
  sorry

/-- ⊢ ∀f,g : ℝ. 0 <_ℝ f ∧ 0 <_ℝ g → 0 <_ℝ f ·_ℝ g -/
def lt_mul_pos_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        ((lt_R Term.zero_R (.var (.vs .vz))
          ∧ᶠ lt_R Term.zero_R (.var .vz))
          →ᶠ lt_R Term.zero_R
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))) :=
  sorry

/-- ⊢ 0_ℝ <_ℝ 1_ℝ -/
def zero_lt_one_R :
    Derivable F EqX al Premises (Γ := Γ)
      (lt_R Term.zero_R Term.one_R) :=
  sorry

-- ── Archimedean property ────────────────────────────────────────────────────

/-- ⊢ ∀f : ℝ. ∃n⁰. f <_ℝ embed_nat(n) -/
def archimedean_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy
        (Formula.ex Ty.nat
          (lt_R (Term.var (.vs .vz))
                (.app Term.embed_nat_R (.var .vz))))) :=
  sorry

-- ── =_ℝ is an equivalence relation ─────────────────────────────────────────

/-- ⊢ ∀f : ℝ. f =_ℝ f -/
def eq_R_refl :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (eq_R (.var .vz) (.var .vz))) :=
  sorry

/-- ⊢ ∀f,g : ℝ. f =_ℝ g → g =_ℝ f -/
def eq_R_sym :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) (.var .vz) →ᶠ
         eq_R (.var .vz) (.var (.vs .vz))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. f =_ℝ g ∧ g =_ℝ h → f =_ℝ h -/
def eq_R_trans :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ eq_R (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  sorry

-- ── Properties needed for metric space transitivity ─────────────────────────

/-- ⊢ ∀f,g : ℝ. f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0 -/
def add_eq_zero_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) Term.zero_R
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
                   Term.zero_R))) :=
  sorry

/-- ⊢ ∀f,g : ℝ. f ≤_ℝ g ∧ g =_ℝ 0 → f =_ℝ 0 -/
def le_zero_eq_zero_R :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (le_R (.var (.vs .vz)) (.var .vz)
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (.var (.vs .vz)) Term.zero_R))) :=
  sorry

end OrderedFieldAxioms

end Metatheorems
