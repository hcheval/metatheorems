/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Terms.Rational
import Metatheorems.Language

namespace Metatheorems

/-!
# Real term and formula definitions

The `Term`- and `Formula`-level encoding of ℝ, split out of `RealNumbers.lean` so that it
sits **below** `eqAtType` and `Derivable` in the import order.

This is the file the whole layering exists for: `eqAtType` at a base type is
`eq_R (dist i s t) 0ℝ`, so `eqAtType` must be able to see `eq_R`, which is defined here.

Only definitions live here. Every proof — the `closed_subst` lemmas, the `cauchyfy` theory,
the ordered-field axioms — stays in `RealNumbers.lean`, above `Derivable`.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}

namespace Term

-- ============================================================================
-- Cauchyfication
-- ============================================================================

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
-- Real Number Operations
-- ============================================================================

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

/-- Rounding for natural numbers: (x⁰)_∘(n) = pair(x · 2^{n+2}, 2^{n+1} - 1).
    This embeds ℕ into ℝ as a term of type ℕ → (ℕ → ℕ). -/
def round_nat {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ realTy ι) :=
  Term.lam (Term.lam
    -- x = var (vs vz), n = var vz
    (Term.app2 Term.pair
      (Term.app2 Term.mul (.var (.vs .vz))
        (.app Term.exp2 (Term.app2 Term.add (.var .vz) (Term.ofNat 2))))
      (.app Term.pd (.app Term.exp2
        (Term.app2 Term.add (.var .vz) (.app .succ .zero))))))

end Term

-- ============================================================================
-- Real Number Formulas
-- ============================================================================

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

/-- Alternative formulation of `≤ℝ` as a syntactically purely universal formula:
    `f ≤ℝ g :≡ ∀n. ¬(f̂(n+1) −ℚ ĝ(n+1) ≥ℚ ⟨2^{-n}⟩ℚ)`, i.e. `¬(g <ℝ f)` spelled out.

**A bug worth remembering, because of how long it survived.** This once negated the body of
`lt_R f g` rather than of `lt_R g f`, so `le_R_pu f g` meant `g ≤ℝ f` — the opposite of
`le_R f g`, and the opposite of what its own docstring claimed. Definition and docstring
agreed with each other and with nothing else, and no consumer cared about the direction until
`Derivable.dist_tri` began asserting the triangle inequality with it. At that point the
constructor was asserting `d(x,y) +ℝ d(y,z) ≤ℝ d(x,z)` — the *reverse* triangle inequality,
satisfied by no metric.

It is now definitionally aligned with `le_R`: `le_R_pu f g` and `le_R f g` unfold to the
same statement, the first as `∀n. ¬…` and the second as `¬∃n. …`. -/
def le_R_pu {Γ : Ctx ι} (f g : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (Formula.imp
      (Formula.eq0
        (Term.app2 Term.le_Q_dec
          (Term.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))
            (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))))
        Term.zero)
      ⊥ᶠ)

end Metatheorems
