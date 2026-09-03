/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Terms.Arith

namespace Metatheorems

/-!
# Rational term definitions

The `Term`-level encoding of ℚ, split out of `RationalNumbers.lean` so that it sits **below**
`eqAtType` and `Derivable` in the import order. See `Metatheorems/Terms/Arith.lean` for why.

Only the definitions moved. Every proof about them — including the `closed_subst` lemmas,
which need `Subst` — stays in `RationalNumbers.lean`, above `Derivable`.

Rational numbers are encoded as natural numbers via Cantor pairing of
(sign-adjusted numerator, denominator - 1).
-/

variable {ι κ : Type} {F : κ → Ty ι}

namespace Term

-- ============================================================================
-- Section 1: Auxiliary Arithmetic Terms
-- ============================================================================

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

/-- Division by 2, **rounding UP**: `div2 n = ⌈n/2⌉ = (n+1)/2`, via state-pair recursion.

    state(0) = pair(0, 1)
    state(Sk) = pair(fst(state(k)) + snd(state(k)), sg_bar(snd(state(k))))
    div2(n) = fst_pair(state(n)).

    **The name and the old docstring said `⌊n/2⌋`; that is wrong**, and was corrected on
    2026-09-03 when the semantic mirror was built (`QValBridge.rec_div2_state` proves the true
    invariant `state k = pairN ((k+1)/2) (1 - k%2)`). The step adds `snd` *before* flipping the
    parity flag, so the values run 0,1,1,2,2,… — `div2 1 = 1`, while `⌊1/2⌋ = 0`.

    Nothing downstream is affected. `rat_num = div2 (j + isOdd j)` is `⌈j/2⌉` for both
    parities, which is what the encoding wants, and `div2_zero` / `div2_double` hold of floor
    and ceiling alike. The name is kept only because renaming it would churn every use. -/
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
-- Section 8: Rational Equality (Decision Term)
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

end Metatheorems
