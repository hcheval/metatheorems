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
-- The `cauchyfy` recursion, named
-- ============================================================================
--
-- `cauchyfy` is a `prec` over a `pair(value, violation flag)` state, buried under two
-- lambdas. Nothing can be said about it until that state is a term one can name, so these
-- three definitions expose it, and `cauchyfy_unfold` is the single beta step that connects
-- them to `Term.cauchyfy` itself.

namespace Term

variable {Γ : Ctx ι}

/-- The base of `cauchyfy`'s recursion: `pair(f 0, 0)` — value `f 0`, flag clear. -/
def cauchyBase (f : Term F Γ (realTy ι)) : Term F Γ Ty.nat :=
  Term.app2 Term.pair (.app f .zero) .zero

/-- The step of `cauchyfy`'s recursion, as a function of `(state, index)`. -/
def cauchyStep (f : Term F Γ (realTy ι)) :
    Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
      (Term.app3 Term.ite_nat
        (.app Term.sg_bar (cauchy_check_at (f.weaken.weaken) (.var .vz)))
        (Term.app2 Term.pair
          (.app (f.weaken.weaken) (.app .succ (.var .vz))) .zero)
        (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
          (.app .succ .zero)))))

/-- The state of the recursion after `n` steps. `cauchyfy f n` is its first component. -/
def cauchyState (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app3 (.prec Ty.nat) (cauchyBase f) (cauchyStep f) n

-- The state's two components are `fst_pair (cauchyState f n)` — the value, which is
-- `cauchyfy f n` — and `snd_pair (cauchyState f n)` — the violation flag, `0` while the
-- Cauchy check has held at every index so far and `1` from the first failure onwards.
-- They are deliberately *not* given names: `prw` finds its pattern by descending through
-- `Term.app`/`app2`/`app3` nodes, and a named wrapper would hide `cauchyState` from it.

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
  (adm : AdmissibleEqX EqX)

-- Notation: real-typed variables in context
private abbrev rTy := realTy ι
-- In context [rTy, Γ]: f = var vz
-- In context [rTy, rTy, Γ]: f = var (vs vz), g = var vz
-- In context [rTy, rTy, rTy, Γ]: f = var (vs (vs vz)), g = var (vs vz), h = var vz

-- ============================================================================
-- `cauchyfy` theory
-- ============================================================================

section Cauchyfy

variable {Γ : Ctx ι}

/-- `Term.weaken_subst0` in the shape simp leaves behind once `Term.weaken` has been
unfolded to `Term.rename`. Without it the last `subst0` of a beta step does not close. -/
private theorem subst0_rename_vs {Γ : Ctx ι} {τ ρ : Ty ι}
    (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (fun {_τ} => Term.subst0_map s) (Term.rename (fun {_τ} => Var.vs) t) = t :=
  Term.weaken_subst0 t s

/-- The body `cauchyfy` compiles to, in the two-variable context `[n, f, …Γ]`. -/
private def cauchyfy_body : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat :=
  .app Term.fst_pair
    (Term.app3 (.prec Ty.nat)
      (Term.app2 Term.pair (.app (.var (.vs .vz)) .zero) .zero)
      (Term.lam (Term.lam
        (Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
          (Term.app3 Term.ite_nat
            (.app Term.sg_bar
              (Term.app2 Term.lt_Q_dec
                (.app Term.abs_Q (Term.app2 Term.sub_Q
                  (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))
                  (.app (.var (.vs (.vs (.vs .vz)))) (.app .succ (.var .vz)))))
                (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
            (Term.app2 Term.pair
              (.app (.var (.vs (.vs (.vs .vz)))) (.app .succ (.var .vz))) .zero)
            (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
              (.app .succ .zero))))))
      (.var .vz))

/-- The one beta step: `cauchyfy f n =₀ fst_pair (state f n)`. Everything else about
`cauchyfy` is reasoning about `cauchyState`, which is an ordinary `prec`. -/
def cauchyfy_unfold (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy f n)
        (.app Term.fst_pair (Term.cauchyState f n))) :=
  have body_eq : (Term.cauchyfy : Term F Γ _) = Term.lam (Term.lam cauchyfy_body) := by rfl
  have nf : ((cauchyfy_body : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat).subst0
      (n.weaken)).subst0 f = .app Term.fst_pair (Term.cauchyState f n) := by
    simp only [cauchyfy_body, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
      Term.cauchy_check_at, Term.subst0, Term.subst, Term.subst0_map, Term.Subst.ext,
      Term.app2, Term.app3, Term.weaken, Term.rename, Term.Renaming.shift,
      subst0_rename_vs, closed_subst]
  body_eq ▸ lam2_correct_nf adm cauchyfy_body f n nf

/-- Congruence under `fst_pair`. -/
private def fst_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair s) (.app Term.fst_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.fst_pair (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- Congruence under `snd_pair`. -/
private def snd_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair s) (.app Term.snd_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.snd_pair (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- The recursion's base case, as a statement about the state. -/
def cauchyState_zero (f : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.cauchyState f Term.zero) (Term.cauchyBase f)) :=
  Derivable.rec_zero (ρ := Ty.nat) (y := Term.cauchyBase f) (z := Term.cauchyStep f)

/-- The recursion's step, as a statement about the state. -/
def cauchyState_succ (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.cauchyState f (.app .succ n))
        (Term.app2 (Term.cauchyStep f) (Term.cauchyState f n) n)) :=
  Derivable.rec_succ (ρ := Ty.nat) (y := Term.cauchyBase f) (z := Term.cauchyStep f) (x := n)

/-- The body of `cauchyStep`, in the two-variable context `[k, st, …Γ]`. -/
private def cauchyStep_body (f : Term F Γ (realTy ι)) :
    Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
  Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
    (Term.app3 Term.ite_nat
      (.app Term.sg_bar (Term.cauchy_check_at (f.weaken.weaken) (.var .vz)))
      (Term.app2 Term.pair
        (.app (f.weaken.weaken) (.app .succ (.var .vz))) .zero)
      (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
        (.app .succ .zero)))

/-- One step of the recursion, beta-reduced. -/
def cauchyStep_unfold (f : Term F Γ (realTy ι)) (st k : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 (Term.cauchyStep f) st k)
        (Term.app3 Term.ite_nat (.app Term.snd_pair st) st
          (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f k))
            (Term.app2 Term.pair (.app f (.app .succ k)) .zero)
            (Term.app2 Term.pair (.app Term.fst_pair st) (.app .succ .zero))))) :=
  have body_eq : Term.cauchyStep f = Term.lam (Term.lam (cauchyStep_body f)) := by rfl
  have nf : (((cauchyStep_body f).subst0 (k.weaken)).subst0 st) =
      Term.app3 Term.ite_nat (.app Term.snd_pair st) st
        (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f k))
          (Term.app2 Term.pair (.app f (.app .succ k)) .zero)
          (Term.app2 Term.pair (.app Term.fst_pair st) (.app .succ .zero))) := by
    simp only [cauchyStep_body, Term.cauchy_check_at, Term.subst0, Term.subst,
      Term.subst0_map, Term.app2, Term.app3, Term.weaken, Term.Renaming.shift,
      subst0_rename_vs, closed_subst]
  body_eq ▸ lam2_correct_nf adm (cauchyStep_body f) st k nf

/-- The step, with the state's two components exposed. -/
def cauchyState_succ_unfold (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.cauchyState f (.app .succ n))
        (Term.app3 Term.ite_nat (.app Term.snd_pair (Term.cauchyState f n))
          (Term.cauchyState f n)
          (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f n))
            (Term.app2 Term.pair (.app f (.app .succ n)) .zero)
            (Term.app2 Term.pair (.app Term.fst_pair (Term.cauchyState f n))
              (.app .succ .zero))))) :=
  qtrans (cauchyState_succ f n) (cauchyStep_unfold adm f (Term.cauchyState f n) n)

/-- Once the flag is set the state freezes. -/
def cauchyState_frozen (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n)) (Term.cauchyState f n)) := by
  pmode
  pintro h
  prw (cauchyState_succ_unfold adm f n)
  prwby h
  pthm (ite_nat_one adm (Term.cauchyState f n) _)

/-- Flag clear and the Cauchy check passing at `n`: the next value is `f (n+1)`. -/
def cauchyState_advance (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) .zero
        ∧ᶠ Formula.eq0 (.app Term.sg_bar (Term.cauchy_check_at f n)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n))
         (Term.app2 Term.pair (.app f (.app .succ n)) .zero)) := by
  pmode
  pintro hyp
  pdestruct hyp with h0 h1
  prw (cauchyState_succ_unfold adm f n)
  prwby h0
  prwby h1
  pthm (qtrans (ite_nat_zero adm _ _) (ite_nat_one adm _ _))

/-- Flag clear and the Cauchy check failing at `n`: the value freezes and the flag is set. -/
def cauchyState_trip (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) .zero
        ∧ᶠ Formula.eq0 (.app Term.sg_bar (Term.cauchy_check_at f n)) .zero →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n))
         (Term.app2 Term.pair (.app Term.fst_pair (Term.cauchyState f n))
           (.app .succ .zero))) := by
  pmode
  pintro hyp
  pdestruct hyp with h0 h1
  prw (cauchyState_succ_unfold adm f n)
  prwby h0
  prwby h1
  pthm (qtrans (ite_nat_zero adm _ _) (ite_nat_zero adm _ _))

/-- The flag starts clear. -/
def cFlag_zero (f : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f Term.zero)) .zero) :=
  qtrans (snd_pair_congr (cauchyState_zero f))
    (snd_pair_pair adm (.app f .zero) Term.zero)

/-- The value starts at `f 0`. -/
def cVal_zero (f : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (Formula.eq0 (.app Term.fst_pair (Term.cauchyState f Term.zero)) (.app f .zero)) :=
  qtrans (fst_pair_congr (cauchyState_zero f))
    (fst_pair_pair adm (.app f .zero) Term.zero)

/-- `f̂(0) =₀ f(0)`: cauchyfication does not move the first term. -/
def cauchyfy_zero (f : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy f Term.zero) (.app f .zero)) :=
  qtrans (cauchyfy_unfold adm f Term.zero) (cVal_zero adm f)

-- ── The invariant ──────────────────────────────────────────────────────────
--
-- Everything above is one step of the recursion. This is the induction: at every index the
-- state is in one of exactly two shapes. Without it nothing pins the flag down to `{0,1}`,
-- and `ite_nat` on anything else computes garbage.

/-- The invariant formula, in context `[n, …Γ]`. -/
private def invF (f : Term F Γ (realTy ι)) : Formula F (Ty.nat :: Γ) :=
  (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz))) .zero
      ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz)))
          (.app f.weaken (.var .vz)))
    ∨ᶠ Formula.eq0 (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz)))
        (.app .succ .zero)

/-- The invariant at an explicit index. -/
private abbrev invAt (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) : Formula F Γ :=
  (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f s)) .zero
      ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f s)) (.app f s))
    ∨ᶠ Formula.eq0 (.app Term.snd_pair (Term.cauchyState f s)) (.app .succ .zero)

private theorem invF_subst0 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    (invF f).subst0 s = invAt f s := by
  simp only [invF, invAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.subst0, Formula.substF, Term.subst,
    Term.subst0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, subst_subst0_map_weaken, closed_subst]

private theorem invF_substVar0 (f : Term F Γ (realTy ι)) :
    Formula.substVar0 (invF f) (.app .succ (.var .vz)) =
      invAt f.weaken (.app .succ (.var .vz)) := by
  simp only [invF, invAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.substVar0, Formula.substF, Term.subst,
    Term.substVar0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, weaken_substVar0, closed_subst]

/-- **The `cauchyfy` invariant.** At every index the state is in one of exactly two shapes:
either the flag is clear and the value is `f n` verbatim, or the flag is set. Nothing else
about `cauchyfy` can be proved without this — in particular nothing pins the flag down to
`{0, 1}`, and `ite_nat` applied to anything else computes garbage. -/
def cauchy_inv (f : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises (Formula.all Ty.nat (invF f)) :=
  let base : Derivable F EqX al Premises ((invF f).subst0 Term.zero) :=
    invF_subst0 f Term.zero ▸
      Derivable.mp (Derivable.mp (cVal_zero adm f)
        (Derivable.mp (cFlag_zero adm f) and_intro)) .or_weak
  let fw : Term F (Ty.nat :: Γ) (realTy ι) := f.weaken
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let step : Derivable F EqX al Premises
      (invF f →ᶠ Formula.substVar0 (invF f) (.app .succ (.var .vz))) :=
    invF_substVar0 f ▸ (by
      pmode
      pintro ih
      pcases ih with hL | hR
      · pdestruct hL with h0 _hv
        pfrom hsg := sg_bar_cases adm (Term.cauchy_check_at fw nv)
        pcases hsg with hs1 | hs0
        · -- the Cauchy check passes at `n`: the value advances to `f (n+1)`
          pconj h0 hs1 with hboth
          papplym (cauchyState_advance adm fw nv) in hboth with hst
          pleft
          psplit
          · prwby hst
            pthm (snd_pair_pair adm (.app fw (.app .succ nv)) Term.zero)
          · prwby hst
            pthm (fst_pair_pair adm (.app fw (.app .succ nv)) Term.zero)
        · -- the check fails: the flag trips
          pconj h0 hs0 with hboth
          papplym (cauchyState_trip adm fw nv) in hboth with hst
          pright
          prwby hst
          pthm (snd_pair_pair adm (.app Term.fst_pair (Term.cauchyState fw nv))
            (.app .succ .zero))
      · -- already tripped: the state freezes, so the flag stays set
        papplym (cauchyState_frozen adm fw nv) in hR with hst
        pright
        prwby hst
        pexact hR)
  .induction base (univ_gen step)

end Cauchyfy

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
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  -- `f̂(n+1) −ℚ f̂(n+1) =ℚ 0`, and `2^{-n} ≤ℚ 0` contradicts `0 <ℚ 2^{-n}`.
  let step : Derivable F EqX al Premises
      (le_Q e (Term.app2 Term.sub_Q A A) →ᶠ ⊥ᶠ) :=
    .syllogism
      (le_Q_congr adm e (Term.app2 Term.sub_Q A A) e Term.zero_Q
        (eq_Q_refl_inst adm e) (sub_Q_self adm A))
      (.syllogism (pair_h (weaken_intro_h (zero_lt_pow2neg_Q adm (.var .vz))) I_comb)
        (lt_Q_le_Q_absurd adm Term.zero_Q e))
  univ_gen (.exist_rule step)

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

/-- ⊢ ∀f : ℝ. f =_ℝ f

`eq_R` is not an equation, so this is not `refl`: it says `|f̂(n+1) −ℚ f̂(n+1)|ℚ <ℚ 2^{-n}`,
which is `0 <ℚ 2^{-n}` transported along `abs_Q_sub_self`. -/
def eq_R_refl :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (eq_R (.var .vz) (.var .vz))) :=
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen
    (Derivable.mp (zero_lt_pow2neg_Q adm (.var .vz))
      (lt_Q_congr adm Term.zero_Q e (.app Term.abs_Q (Term.app2 Term.sub_Q A A)) e
        (eqQsym adm (abs_Q_sub_self adm A)) (eq_Q_refl_inst adm e))))

/-- ⊢ ∀f,g : ℝ. f =_ℝ g → g =_ℝ f -/
def eq_R_sym :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) (.var .vz) →ᶠ
         eq_R (.var .vz) (.var (.vs .vz))))) :=
  let A : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var (.vs .vz)))) (.app .succ (.var .vz))
  let B : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen (forall_map
    (lt_Q_congr adm (.app Term.abs_Q (Term.app2 Term.sub_Q A B)) e
        (.app Term.abs_Q (Term.app2 Term.sub_Q B A)) e
      (abs_diff_Q_comm adm A B) (eq_Q_refl_inst adm e))))

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

-- ============================================================================
-- Axiom hygiene: every axiom claimed proved above is checked here
-- ============================================================================
-- A falling `sorry` count is not evidence (CLAUDE.md note 9); these are.

#print axioms eq_R_refl
#print axioms eq_R_sym
#print axioms lt_irrefl_R

end Metatheorems
