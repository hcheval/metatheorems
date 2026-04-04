/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RationalNumbers

namespace Metatheorems

/-!
# Real Numbers in WE-HA^{ω}

Real numbers are encoded as rapidly converging Cauchy sequences of rationals.
Following §real-numbers of the reference document, the type of reals is
`1 = 0 → 0` (functions ℕ → ℕ), where `x(n)` encodes a rational approximation
to within 2^{-n}.

## Structure

1. **Cauchyfication**: `cauchyfy` (f ↦ f̂)
2. **Real operations**: `zero_R`, `one_R`, `add_R`, `neg_R`, `sub_R`, `mul_R`, `abs_R`
3. **Real formulas**: `eq_R`, `lt_R`, `le_R`, `le_R_pu`
4. **Ordered field axioms** (sorry'd)
-/

open Formula

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Section 1: Cauchyfication
-- ============================================================================

namespace Term

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
-- Section 2: Real Number Operations
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

-- ============================================================================
-- Closed term substitution lemmas (real-level)
-- ============================================================================

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

@[simp] private theorem cauchyfy_closed_subst :
    (Term.cauchyfy : Term F Γ _).subst σ = Term.cauchyfy := by
  simp only [Term.cauchyfy, Term.subst, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken, Term.rename, Term.Renaming.ext, Term.Renaming.shift,
    fst_pair_closed_subst, pair_closed_subst, snd_pair_closed_subst,
    lt_Q_dec_closed_subst, abs_Q_closed_subst, sub_Q_closed_subst,
    pow2neg_Q_closed_subst, ite_nat_closed_subst, sg_bar_closed_subst]
@[simp] theorem zero_R_closed_subst :
    (Term.zero_R : Term F Γ _).subst σ = Term.zero_R := by rfl
@[simp] private theorem one_R_closed_subst :
    (Term.one_R : Term F Γ _).subst σ = Term.one_R := by rfl
@[simp] private theorem embed_nat_R_closed_subst :
    (Term.embed_nat_R : Term F Γ _).subst σ = Term.embed_nat_R := by rfl
@[simp] private theorem neg_R_closed_subst :
    (Term.neg_R : Term F Γ _).subst σ = Term.neg_R := by rfl
private theorem add_closed_subst :
    (Term.add : Term F Γ _).subst σ = Term.add := by rfl

@[simp] private theorem add_R_closed_subst :
    (Term.add_R : Term F Γ _).subst σ = Term.add_R := by
  simp only [Term.add_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_Q_closed_subst, cauchyfy_closed_subst]
@[simp] private theorem sub_R_closed_subst :
    (Term.sub_R : Term F Γ _).subst σ = Term.sub_R := by
  simp only [Term.sub_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_R_closed_subst, neg_R_closed_subst]
@[simp] private theorem mul_R_closed_subst :
    (Term.mul_R : Term F Γ _).subst σ = Term.mul_R := by
  simp only [Term.mul_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift, Term.ofNat,
    mul_Q_closed_subst, cauchyfy_closed_subst, add_closed_subst]
@[simp] private theorem abs_R_closed_subst :
    (Term.abs_R : Term F Γ _).subst σ = Term.abs_R := by
  simp only [Term.abs_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    abs_Q_closed_subst, cauchyfy_closed_subst]

end ClosedSubst

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

-- ============================================================================
-- Key Properties
-- ============================================================================

/-- `eq_R` is quantifier-free under the ∀n wrapper, so the whole formula
    is purely universal (Π₁⁰). This is needed for EqX admissibility. -/
theorem eq_R_isPurelyUniversal (f g : Term F Γ (realTy ι)) :
    (eq_R f g).isPurelyUniversal = true := by rfl

/-- `eq_R` commutes with substitution: naturality for the real equality formula.
    This is needed for `AdmissibleEqX.substF_nat` in the metric space case. -/
theorem eq_R_substF {Γ Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (eq_R f g).substF σ = eq_R (f.subst σ) (g.subst σ) := by
  simp only [eq_R, Formula.substF, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext,
    lt_Q_dec_closed_subst, abs_Q_closed_subst, sub_Q_closed_subst,
    cauchyfy_closed_subst, pow2neg_Q_closed_subst]

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
    (le_R_pu f g).substF σ = le_R_pu (f.subst σ) (g.subst σ) := by
  simp only [le_R_pu, Formula.substF, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext,
    le_Q_dec_closed_subst, sub_Q_closed_subst, cauchyfy_closed_subst,
    pow2neg_Q_closed_subst]

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
