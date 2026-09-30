/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Mul

namespace Metatheorems

/-!
# Order-side plumbing for the `<_ℝ` axioms

The kit `Order.lean`'s four order proofs (`lt_add_R`, `lt_mul_pos_R`, `archimedean_R`,
`lt_trans_R_core`) need: implication-form `≤_ℚ` transitivity, cancellation and subtraction
monotonicity, the dyadic product `2^{-a} ·_ℚ 2^{-b} =_ℚ 2^{-(a+b)}`, the persistence of a
positive lower bound under `cauchyfy` drift, and the `Formula.weakenBy`/`substF` normal-form
theorems that let the nested `∃`-eliminations be done at the Lean level with
`Derivable.exist_rule`.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderBounds

variable {Γ : Ctx ι}

/-- `=₀`-congruence for `succ` (the ones elsewhere are `private`). -/
def succ_congr_o {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) (by qb_nf) (by qb_nf)

-- ── Implication-form `≤_ℚ` transitivity, with one side a Lean-level fact ─────

/-- `b ≤ℚ c` (Lean-level) turns `a ≤ℚ b` into `a ≤ℚ c`, as an object implication. -/
def le_Q_trans_r (a : Term F Γ Ty.nat) {b c : Term F Γ Ty.nat}
    (hbc : Derivable F al Premises (le_Q b c)) :
    Derivable F al Premises (le_Q a b →ᶠ le_Q a c) :=
  Derivable.syllogism (pair_h I_comb (weaken_intro_h hbc)) (le_Q_trans a b c)

/-- `a ≤ℚ b` (Lean-level) turns `b ≤ℚ c` into `a ≤ℚ c`, as an object implication. -/
def le_Q_trans_l {a b : Term F Γ Ty.nat} (c : Term F Γ Ty.nat)
    (hab : Derivable F al Premises (le_Q a b)) :
    Derivable F al Premises (le_Q b c →ᶠ le_Q a c) :=
  Derivable.syllogism (pair_h (weaken_intro_h hab) I_comb) (le_Q_trans a b c)

-- ── Cancellation and subtraction monotonicity ───────────────────────────────

/-- Cancelling a common right summand in a `≤_ℚ` — the mirror of `lt_Q_add_cancel`. -/
def le_Q_add_cancel (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) →ᶠ le_Q a b) :=
  le_Q_of_eq_Q_diff (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) a b
    (sub_Q_add_cancel a b c)

/-- Negation is antitone for `≤_ℚ`. -/
def neg_Q_antitone (y y' : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q y y' →ᶠ le_Q (.app Term.neg_Q y') (.app Term.neg_Q y)) :=
  le_Q_of_eq_Q_diff y y' (.app Term.neg_Q y') (.app Term.neg_Q y)
    (eqQsym (sub_Q_neg_neg y y'))

/-- `a ≤ℚ b +ℚ s → a −ℚ s ≤ℚ b`. -/
def le_Q_sub_of_le_add_r (a b s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a (Term.app2 Term.add_Q b s) →ᶠ le_Q (Term.app2 Term.sub_Q a s) b) :=
  let ns : Term F Γ Ty.nat := .app Term.neg_Q s
  Derivable.syllogism
    (le_Q_add a (Term.app2 Term.add_Q b s) ns)
    (le_Q_congr (Term.app2 Term.add_Q a ns)
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q b s) ns)
      (Term.app2 Term.sub_Q a s) b
      (eqQsym (sub_Q_eq_add_neg a s))
      (eqQtrans (add_Q_assoc_inst b s ns)
        (eqQtrans (addQr b (add_Q_neg_inst s)) (add_Q_zero_inst b))))

/-- `y ≤ℚ y'` (Lean-level) gives `x −ℚ y' ≤ℚ x −ℚ y`. -/
def sub_Q_mono_r (x : Term F Γ Ty.nat) {y y' : Term F Γ Ty.nat}
    (h : Derivable F al Premises (le_Q y y')) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.sub_Q x y') (Term.app2 Term.sub_Q x y)) :=
  let ny : Term F Γ Ty.nat := .app Term.neg_Q y
  let ny' : Term F Γ Ty.nat := .app Term.neg_Q y'
  Derivable.mp
    (Derivable.mp (Derivable.mp h (neg_Q_antitone y y')) (le_Q_add_l x ny' ny))
    (le_Q_congr (Term.app2 Term.add_Q x ny') (Term.app2 Term.add_Q x ny)
      (Term.app2 Term.sub_Q x y') (Term.app2 Term.sub_Q x y)
      (eqQsym (sub_Q_eq_add_neg x y')) (eqQsym (sub_Q_eq_add_neg x y)))

-- ── The dyadic product ──────────────────────────────────────────────────────

/-- **`2^{-a} ·ℚ 2^{-b} =ℚ 2^{-(a+b)}`** — the quantitative heart of `lt_mul_pos_R`.
Proved through the parts, in the style of `encode_pow2_mul`: sign `1·1`, numerator `1·1`,
denominator `2^a · 2^b =₀ 2^{a+b}` by `exp2_add`. -/
def pow2neg_Q_mul (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (.app Term.pow2neg_Q a) (.app Term.pow2neg_Q b))
        (.app Term.pow2neg_Q (Term.app2 Term.add a b))) :=
  let Pa : Term F Γ Ty.nat := .app Term.pow2neg_Q a
  let Pb : Term F Γ Ty.nat := .app Term.pow2neg_Q b
  let L : Term F Γ Ty.nat := Term.app2 Term.mul_Q Pa Pb
  let R : Term F Γ Ty.nat := .app Term.pow2neg_Q (Term.app2 Term.add a b)
  let one : Term F Γ Ty.nat := .app .succ .zero
  let sL : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign L) one) :=
    rat_sign_mul_Q_pos Pa Pb (rat_sign_pow2neg_Q a) (rat_sign_pow2neg_Q b)
  let sR : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign R) one) :=
    rat_sign_pow2neg_Q (Term.app2 Term.add a b)
  let hnumL : Derivable F al Premises (Formula.eq0 (.app Term.rat_num L) one) :=
    qtrans (rat_num_mul_Q Pa Pb)
      (qtrans (mul_congr_l (rat_num_pow2neg_Q a) (.app Term.rat_num Pb))
        (qtrans (mul_congr_r one (rat_num_pow2neg_Q b)) (mul_one_r one)))
  let hp : Derivable F al Premises (Formula.eq0 (posN L) (posN R)) :=
    qtrans (qtrans (posN_of_sign_one L sL) hnumL)
      (Derivable.mp (qtrans (posN_of_sign_one R sR)
        (rat_num_pow2neg_Q (Term.app2 Term.add a b))) Derivable.sym0)
  let hn : Derivable F al Premises (Formula.eq0 (negN L) (negN R)) :=
    qtrans (negN_of_sign_one L sL)
      (Derivable.mp (negN_of_sign_one R sR) Derivable.sym0)
  let hd : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den L) (.app Term.rat_den R)) :=
    qtrans (rat_den_mul_Q Pa Pb)
      (qtrans (mul_congr_l (rat_den_pow2neg_Q a) (.app Term.rat_den Pb))
        (qtrans (mul_congr_r (.app Term.exp2 a) (rat_den_pow2neg_Q b))
          (qtrans (Derivable.mp (exp2_add a b) Derivable.sym0)
            (Derivable.mp (rat_den_pow2neg_Q (Term.app2 Term.add a b))
              Derivable.sym0))))
  eq_Q_of_pos_neg L R hp hn hd

-- ── Persistence of a positive lower bound under drift ───────────────────────

/-- **A `<_ℝ`-witness lower bound persists, halved, at every later index**:
`2^{-n} ≤ℚ f̂(n+1)` gives `2^{-(n+1)} ≤ℚ f̂((n+1)+j)`, because the total drift from `n+1`
is at most `2^{-(n+1)}` (`cauchyfy_shift_le`), which is exactly half the bound. -/
def cauchyfy_lb_imp (f : Term F Γ (realTy ι)) (n j : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.pow2neg_Q n) (Term.app2 Term.cauchyfy f (.app .succ n)) →ᶠ
       le_Q (.app Term.pow2neg_Q (.app .succ n))
         (Term.app2 Term.cauchyfy f (Term.app2 Term.add (.app .succ n) j))) :=
  let A : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ n)
  let B : Term F Γ Ty.nat :=
    Term.app2 Term.cauchyfy f (Term.app2 Term.add (.app .succ n) j)
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q n
  let P1 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  let d : Term F Γ Ty.nat := Term.app2 Term.sub_Q A B
  -- A − B ≤ |A − B| ≤ 2^{-(n+1)}
  let hd : Derivable F al Premises (le_Q d P1) :=
    leQt (le_Q_self_abs d) (cauchyfy_shift_le f (.app .succ n) j)
  -- B + (A − B) ≤ B + P1
  let hstep : Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q B d) (Term.app2 Term.add_Q B P1)) :=
    Derivable.mp hd (le_Q_add_l B d P1)
  Derivable.syllogism
    (le_Q_congr P A P (Term.app2 Term.add_Q B d)
      (eq_Q_refl_inst P) (eqQsym (add_Q_sub_cancel A B)))
    (Derivable.syllogism (le_Q_trans_r P hstep)
      (Derivable.syllogism
        (le_Q_congr P (Term.app2 Term.add_Q B P1)
          (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q B P1)
          (eqQsym (pow2neg_Q_halve n)) (eq_Q_refl_inst (Term.app2 Term.add_Q B P1)))
        (le_Q_add_cancel P1 B P1)))

-- ── Object-level multiplication monotonicity ────────────────────────────────
--
-- `le_Q_zero_mul` / `le_Q_mul_mono_l` (QBounds) take Lean-level premises; these are the
-- same content as object implications.

/-- `0 ≤ℚ x ∧ 0 ≤ℚ y → 0 ≤ℚ x·y`, as an object formula. -/
def le_Q_zero_mul_o (x y : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q Term.zero_Q x ∧ᶠ le_Q Term.zero_Q y →ᶠ
        le_Q Term.zero_Q (Term.app2 Term.mul_Q x y)) := by
  pmode
  pintro hyp
  pdestruct hyp with hx hy
  papplym (le_Q_zero_parts x) in hx with hnx
  papplym (le_Q_zero_parts y) in hy with hny
  papplym (le_Q_zero_of_parts (Term.app2 Term.mul_Q x y))
  prw (negN_mul_Q x y)
  prwby hnx
  prwby hny
  prw (mul_zero (posN x))
  prw (mul_zero_l (posN y))
  prw (add_zero_r (Term.zero : Term F Γ Ty.nat))
  prefl

/-- `0 ≤ x, 0 ≤ y, x ≤ X, y ≤ Y → x·y ≤ X·Y`, all four order facts object-level. -/
def le_Q_mul_o (x X y Y : Term F Γ Ty.nat) :
    Derivable F al Premises
      ((le_Q Term.zero_Q x ∧ᶠ le_Q Term.zero_Q y) ∧ᶠ (le_Q x X ∧ᶠ le_Q y Y) →ᶠ
        le_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X Y)) := by
  pmode
  pintro hyp
  pdestruct hyp with h0 h1
  pdestruct h0 with hx0 hy0
  pdestruct h1 with hxX hyY
  papplym (le_Q_trans (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y)
    (Term.app2 Term.mul_Q X Y))
  psplit
  · -- x·y ≤ X·y, via 0 ≤ (X−x)·y
    papplym (le_Q_of_zero_sub (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y))
    papplym (le_Q_zero_congr
      (Term.app2 Term.mul_Q (Term.app2 Term.sub_Q X x) y)
      (Term.app2 Term.sub_Q (Term.app2 Term.mul_Q X y) (Term.app2 Term.mul_Q x y))
      (sub_Q_mul_distrib X x y))
    papplym (le_Q_zero_mul_o (Term.app2 Term.sub_Q X x) y)
    psplit
    · papplym (le_Q_to_zero_sub x X)
      pexact hxX
    · pexact hy0
  · -- X·y ≤ X·Y, via 0 ≤ (Y−y)·X and 0 ≤ X
    papplym (le_Q_of_zero_sub (Term.app2 Term.mul_Q X y) (Term.app2 Term.mul_Q X Y))
    papplym (le_Q_zero_congr
      (Term.app2 Term.mul_Q (Term.app2 Term.sub_Q Y y) X)
      (Term.app2 Term.sub_Q (Term.app2 Term.mul_Q X Y) (Term.app2 Term.mul_Q X y))
      (eqQtrans (sub_Q_mul_distrib Y y X)
        (sub_Q_congr (mul_Q_comm_inst Y X) (mul_Q_comm_inst y X))))
    papplym (le_Q_zero_mul_o (Term.app2 Term.sub_Q Y y) X)
    psplit
    · papplym (le_Q_to_zero_sub y Y)
      pexact hyY
    · papplym (le_Q_trans Term.zero_Q x X)
      psplit
      · pexact hx0
      · pexact hxX

-- ── `lt_R` under substitution and weakening ─────────────────────────────────

/-- `lt_R` commutes with substitution — the `lt_R` twin of `eq_R_substF`. -/
theorem lt_R_substF {Δ : Ctx ι} (f g : Term F Γ (realTy ι))
    (σ : Term.Subst F Γ Δ) :
    (lt_R f g).substF σ = lt_R (f.subst σ) (g.subst σ) := by
  simp only [lt_R, Formula.substF, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext,
    le_Q_dec_closed_subst, sub_Q_closed_subst,
    cauchyfy_closed_subst, pow2neg_Q_closed_subst]

/-- `Formula.weakenBy` distributes over `→ᶠ` (definitionally). -/
theorem Formula.weakenBy_imp {ρ : Ty ι} (A B : Formula F Γ) :
    Formula.weakenBy ρ (A →ᶠ B) =
      (Formula.weakenBy ρ A →ᶠ Formula.weakenBy ρ B) := rfl

/-- `weakenBy` of a `lt_R` is `lt_R` of the weakened reals. -/
theorem lt_R_weakenBy {ρ : Ty ι} (f g : Term F Γ (realTy ι)) :
    Formula.weakenBy ρ (lt_R f g) = lt_R f.weaken g.weaken := by
  rw [← Formula.substF_shift_eq_weakenBy, lt_R_substF,
    Term.subst_shift_eq_weaken, Term.subst_shift_eq_weaken]

/-- Weakening a composed product (the one in `Mul.lean` is `private`). -/
theorem mul_R_app_weaken2 {Δ : Ctx ι} {ρ : Ty ι} (f g : Term F Δ (realTy ι)) :
    (Term.app2 Term.mul_R f g).weaken (σ := ρ) =
      Term.app2 Term.mul_R f.weaken g.weaken := by
  show Term.app2 ((Term.mul_R : Term F Δ _).weaken) f.weaken g.weaken = _
  rw [show (Term.mul_R : Term F Δ _).weaken (σ := ρ) = Term.mul_R by
    rw [Term.weaken, Term.rename_eq_subst]; exact mul_R_closed_subst _]

/-- `lt_R` as an explicit `∃`, with the body in the `le_Q`/`app2` spelling the order proofs
use — definitionally the same formula, but *syntactically* the one `ltBody_weakenBy` and the
proof-mode tactics match. -/
theorem lt_R_ex (u v : Term F Γ (realTy ι)) :
    lt_R u v = Formula.ex Ty.nat
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz))))) := rfl

/-- `lt_R 0ℝ u` with the body's `zero_R.weaken` folded back to `zero_R`, so that
`cauchyfy_zero_R` matches it. -/
theorem lt_R_zero_ex (u : Term F Γ (realTy ι)) :
    lt_R Term.zero_R u = Formula.ex Ty.nat
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ (.var .vz))))) := by
  unfold lt_R
  rw [zero_R_weaken]
  rfl

/-- `weakenBy` of the `lt_R`-body shape, computed: the bound variable moves to `vs vz`, the
two reals pick up a `.weaken`, the constants stay put. -/
theorem ltBody_weakenBy (c₁ c₂ : Term F (Ty.nat :: Γ) (realTy ι)) :
    Formula.weakenBy Ty.nat
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy c₁ (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy c₂ (.app .succ (.var .vz))))) =
      le_Q (.app Term.pow2neg_Q (.var (.vs .vz)))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy c₁.weaken (.app .succ (.var (.vs .vz))))
          (Term.app2 Term.cauchyfy c₂.weaken (.app .succ (.var (.vs .vz))))) := by
  rw [← Formula.substF_shift_eq_weakenBy]
  simp only [le_Q, Formula.substF, Term.subst, Term.app2,
    le_Q_dec_closed_subst, sub_Q_closed_subst, cauchyfy_closed_subst,
    pow2neg_Q_closed_subst]
  simp only [Term.subst_shift_eq_weaken]
  rfl

end OrderBounds

end Metatheorems
