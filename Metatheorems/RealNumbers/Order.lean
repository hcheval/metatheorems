/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.OrderBounds

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Order ───────────────────────────────────────────────────────────────────

/-- ⊢ ∀f : ℝ. ¬(f <_ℝ f) (irreflexivity of <_ℝ) -/
def lt_irrefl_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.neg (lt_R (.var .vz) (.var .vz)))) :=
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  -- `f̂(n+1) −ℚ f̂(n+1) =ℚ 0`, and `2^{-n} ≤ℚ 0` contradicts `0 <ℚ 2^{-n}`.
  let step : Derivable F al Premises
      (le_Q e (Term.app2 Term.sub_Q A A) →ᶠ ⊥ᶠ) :=
    .syllogism
      (le_Q_congr e (Term.app2 Term.sub_Q A A) e Term.zero_Q
        (eq_Q_refl_inst e) (sub_Q_self A))
      (.syllogism (pair_h (weaken_intro_h (zero_lt_pow2neg_Q (.var .vz))) I_comb)
        (lt_Q_le_Q_absurd Term.zero_Q e))
  univ_gen (.exist_rule step)

-- `lt_trans_R` is PROVED, further down: it rests on `lt_shift`, which needs
-- `cauchyfy_cauchy` and the `≤ℚ`/`<ℚ` toolkit stated below.

/-- The inner implication of `lt_add_R`, with the hypothesis's witness a bound variable.

The witness for the conclusion is `w := n + rat_den e`, where
`e := 2^{-(n+1)} −ℚ (|f̂(n+1)−f̂(n+2)| +ℚ |ĝ(n+1)−ĝ(n+2)|)` is the **Cauchy slack at the
hypothesis's own index** — positive for every `f`, `g` because `cauchyState_cauchy`'s check
is strict. A crude telescope is short by a factor of two at every index (REALS_PLAN §0.03);
keeping the first step's slack out of the telescope is what closes the gap:
`D(w+2) ≥ D(n+1) − (cf + 2^{-(n+2)}) − (cg + 2^{-(n+2)}) ≥ 2^{-(n+1)} − (cf+cg) = e ≥ 2^{-w}`,
the last step by `pow2neg_rat_den_le`. The `+ℝ h` on both sides cancels exactly
(`sub_Q_add_cancel`), so `h` never enters the estimate. -/
private def lt_add_inner (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
       →ᶠ
       lt_R (Term.app2 Term.add_R f.weaken h.weaken)
            (Term.app2 Term.add_R g.weaken h.weaken)) :=
  let Γ' := Ty.nat :: Γ
  let n : Term F Γ' Ty.nat := .var .vz
  let fw : Term F Γ' (realTy ι) := f.weaken
  let gw : Term F Γ' (realTy ι) := g.weaken
  let hw : Term F Γ' (realTy ι) := h.weaken
  let A1 : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy fw (.app .succ n)
  let A2 : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy fw (.app .succ (.app .succ n))
  let B1 : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy gw (.app .succ n)
  let B2 : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy gw (.app .succ (.app .succ n))
  let cf : Term F Γ' Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q A1 A2)
  let cg : Term F Γ' Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q B1 B2)
  let P1 : Term F Γ' Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  let P2 : Term F Γ' Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ n))
  let s : Term F Γ' Ty.nat := Term.app2 Term.add_Q cf cg
  let e : Term F Γ' Ty.nat := Term.app2 Term.sub_Q P1 s
  let r : Term F Γ' Ty.nat := .app Term.rat_den e
  let w : Term F Γ' Ty.nat := Term.app2 Term.add n r
  let As : Term F Γ' Ty.nat :=
    Term.app2 Term.cauchyfy fw (Term.app2 Term.add (.app .succ (.app .succ n)) r)
  let Bs : Term F Γ' Ty.nat :=
    Term.app2 Term.cauchyfy gw (Term.app2 Term.add (.app .succ (.app .succ n)) r)
  let Asw : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy fw (.app .succ (.app .succ w))
  let Bsw : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy gw (.app .succ (.app .succ w))
  let Hsw : Term F Γ' Ty.nat := Term.app2 Term.cauchyfy hw (.app .succ (.app .succ w))
  let D1 : Term F Γ' Ty.nat := Term.app2 Term.sub_Q B1 A1
  let D2 : Term F Γ' Ty.nat := Term.app2 Term.sub_Q Bs As
  let aa : Term F Γ' Ty.nat := Term.app2 Term.sub_Q B1 Bs
  let nb : Term F Γ' Ty.nat := Term.app2 Term.sub_Q As A1
  -- cf + cg <ℚ 2^{-(n+1)}, strictly, hence 0 <ℚ e
  let hs : Derivable F al Premises (Γ := Γ')
      (lt_Q s (Term.app2 Term.add_Q P2 P2)) :=
    Derivable.mp
      (Derivable.mp (cauchyfy_cauchy gw (.app .succ n))
        (Derivable.mp (cauchyfy_cauchy fw (.app .succ n)) and_intro))
      (lt_Q_add_both cf cg P2 P2)
  let hsP1 : Derivable F al Premises (Γ := Γ') (lt_Q s P1) :=
    Derivable.mp hs
      (lt_Q_congr s (Term.app2 Term.add_Q P2 P2) s P1
        (eq_Q_refl_inst s) (pow2neg_Q_halve (.app .succ n)))
  let hpos : Derivable F al Premises (Γ := Γ') (lt_Q Term.zero_Q e) :=
    Derivable.mp hsP1 (lt_Q_to_zero_sub s P1)
  -- 2^{-w} ≤ℚ e
  let hwe : Derivable F al Premises (Γ := Γ') (le_Q (.app Term.pow2neg_Q w) e) :=
    leQt (pow2neg_Q_le_add_r n r) (Derivable.mp hpos (pow2neg_rat_den_le e))
  -- the exact split D1 =ℚ D2 + (nb + aa), as in `lt_shift1`
  let hDid : Derivable F al Premises (Γ := Γ')
      (eq_Q D1 (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))) :=
    eqQtrans (sub_Q_trans_split A1 Bs B1)
      (eqQtrans (addQl (sub_Q_trans_split A1 As Bs) aa)
        (eqQtrans (addQl (add_Q_comm_inst nb D2) aa)
          (add_Q_assoc_inst D2 nb aa)))
  -- aa ≤ cg + 2^{-(n+2)} : one strict step kept out, then the telescope
  let haa : Derivable F al Premises (Γ := Γ')
      (le_Q aa (Term.app2 Term.add_Q cg P2)) :=
    leQt (le_Q_self_abs aa)
      (leQt (abs_Q_sub_triangle B1 B2 Bs)
        (Derivable.mp (cauchyfy_shift_le gw (.app .succ (.app .succ n)) r)
          (le_Q_add_l cg (.app Term.abs_Q (Term.app2 Term.sub_Q B2 Bs)) P2)))
  -- nb ≤ cf + 2^{-(n+2)}, mirrored through `abs_diff_Q_comm`
  let hnb : Derivable F al Premises (Γ := Γ')
      (le_Q nb (Term.app2 Term.add_Q cf P2)) :=
    leQt (le_Q_self_abs nb)
      (Derivable.mp
        (leQt (abs_Q_sub_triangle A1 A2 As)
          (Derivable.mp (cauchyfy_shift_le fw (.app .succ (.app .succ n)) r)
            (le_Q_add_l cf (.app Term.abs_Q (Term.app2 Term.sub_Q A2 As)) P2)))
        (le_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A1 As))
          (Term.app2 Term.add_Q cf P2)
          (.app Term.abs_Q (Term.app2 Term.sub_Q As A1))
          (Term.app2 Term.add_Q cf P2)
          (abs_diff_Q_comm A1 As) (eq_Q_refl_inst (Term.app2 Term.add_Q cf P2))))
  -- nb + aa ≤ s + 2^{-(n+1)}
  let hsum : Derivable F al Premises (Γ := Γ')
      (le_Q (Term.app2 Term.add_Q nb aa) (Term.app2 Term.add_Q s P1)) :=
    Derivable.mp
      (Derivable.mp
        (Derivable.mp haa (Derivable.mp hnb and_intro))
        (le_Q_add_both nb aa (Term.app2 Term.add_Q cf P2) (Term.app2 Term.add_Q cg P2)))
      (le_Q_congr (Term.app2 Term.add_Q nb aa)
        (Term.app2 Term.add_Q (Term.app2 Term.add_Q cf P2) (Term.app2 Term.add_Q cg P2))
        (Term.app2 Term.add_Q nb aa) (Term.app2 Term.add_Q s P1)
        (eq_Q_refl_inst (Term.app2 Term.add_Q nb aa))
        (eqQtrans (add_Q_shuffle cf P2 cg P2)
          (addQr s (pow2neg_Q_halve (.app .succ n)))))
  -- D1 ≤ D2 + (s + 2^{-(n+1)})
  let hD1b : Derivable F al Premises (Γ := Γ')
      (le_Q D1 (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1))) :=
    Derivable.mp
      (Derivable.mp hsum (le_Q_add_l D2 (Term.app2 Term.add_Q nb aa)
        (Term.app2 Term.add_Q s P1)))
      (le_Q_congr (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))
        (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1))
        D1 (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1))
        (eqQsym hDid)
        (eq_Q_refl_inst (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1))))
  -- (n+2)+r =₀ w+2, and the goal-side difference is D2 with `h` cancelled
  let hIdx : Derivable F al Premises (Γ := Γ')
      (Formula.eq0 (Term.app2 Term.add (.app .succ (.app .succ n)) r)
        (.app .succ (.app .succ w))) :=
    qtrans (add_succ_l (.app .succ n) r) (succ_congr_o (add_succ_l n r))
  let hyEq : Derivable F al Premises (Γ := Γ')
      (eq_Q D2
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy (Term.app2 Term.add_R gw hw) (.app .succ w))
          (Term.app2 Term.cauchyfy (Term.app2 Term.add_R fw hw) (.app .succ w)))) :=
    eqQtrans
      (sub_Q_congr (eqQ_of_nat_eq' (cauchyfy_idx_nat' gw hIdx))
        (eqQ_of_nat_eq' (cauchyfy_idx_nat' fw hIdx)))
      (eqQtrans (eqQsym (sub_Q_add_cancel Asw Bsw Hsw))
        (sub_Q_congr
          (eqQsym (eqQ_of_nat_eq' (cauchyfy_add_R gw hw (.app .succ w))))
          (eqQsym (eqQ_of_nat_eq' (cauchyfy_add_R fw hw (.app .succ w))))))
  by
  pmode
  pintro a
  pexists w
  canorm
  papplym (le_Q_congr (.app Term.pow2neg_Q w) D2 (.app Term.pow2neg_Q w)
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy (Term.app2 Term.add_R gw hw) (.app .succ w))
      (Term.app2 Term.cauchyfy (Term.app2 Term.add_R fw hw) (.app .succ w)))
    (eq_Q_refl_inst (.app Term.pow2neg_Q w)) hyEq)
  papplym (le_Q_trans_l D2 hwe)
  papplym (le_Q_sub_of_le_add_r P1 D2 s)
  papplym (le_Q_add_cancel P1 (Term.app2 Term.add_Q D2 s) P1)
  papplym (le_Q_congr (.app Term.pow2neg_Q n)
    (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1))
    (Term.app2 Term.add_Q P1 P1)
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q D2 s) P1)
    (eqQsym (pow2neg_Q_halve n)) (eqQsym (add_Q_assoc_inst D2 s P1)))
  papplym (le_Q_trans (.app Term.pow2neg_Q n) D1
    (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q s P1)))
  psplit
  · pexact a
  · pthm hD1b

/-- `f <ℝ g → f +ℝ h <ℝ g +ℝ h`, at explicit reals. The single `∃`-elimination is a
Lean-level `Derivable.exist_rule`. -/
def lt_add_R_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (lt_R f g →ᶠ
        lt_R (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h)) := by
  refine Derivable.exist_rule ?_
  rw [lt_R_weakenBy, add_R_app_weaken, add_R_app_weaken]
  exact lt_add_inner f g h

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g → f +_ℝ h <_ℝ g +_ℝ h -/
def lt_add_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          →ᶠ lt_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var .vz))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))))) :=
  univ_gen (univ_gen (univ_gen
    (lt_add_R_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- The core of `lt_mul_pos_R`, at the two witnesses as bound variables: `n₂ = vz` from
`0 <ℝ g`, `n₁ = vs vz` from `0 <ℝ f`.

Each hypothesis `2^{-nᵢ} ≤ℚ ·̂(nᵢ+1)` persists, halved, at every later index
(`cauchyfy_lb_imp`), so at the product's own index `S = (m+1)+b` both factors are bounded
below by `2^{-(nᵢ+1)}`, and the product by `2^{-(n₁+1)}·2^{-(n₂+1)} =ℚ 2^{-m}`
(`pow2neg_Q_mul`) with `m := (n₁+n₂)+2` — exactly the witness `lt_R` wants. -/
private def lt_mul_pos_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Ty.nat :: Γ)
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ (.var .vz))))
       →ᶠ
       (le_Q (.app Term.pow2neg_Q (.var (.vs .vz)))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken.weaken (.app .succ (.var (.vs .vz))))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ (.var (.vs .vz)))))
       →ᶠ
       lt_R Term.zero_R (Term.app2 Term.mul_R f.weaken.weaken g.weaken.weaken))) :=
  let Γ₂ := Ty.nat :: Ty.nat :: Γ
  let n1 : Term F Γ₂ Ty.nat := .var (.vs .vz)
  let n2 : Term F Γ₂ Ty.nat := .var .vz
  let F2 : Term F Γ₂ (realTy ι) := f.weaken.weaken
  let G2 : Term F Γ₂ (realTy ι) := g.weaken.weaken
  let m : Term F Γ₂ Ty.nat := .app .succ (.app .succ (Term.app2 Term.add n1 n2))
  let b : Term F Γ₂ Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.add (.app F2 .zero) (.app G2 .zero)) (Term.ofNat 2)
  let S : Term F Γ₂ Ty.nat := Term.app2 Term.add (.app .succ m) b
  let P1 : Term F Γ₂ Ty.nat := .app Term.pow2neg_Q (.app .succ n1)
  let P2 : Term F Γ₂ Ty.nat := .app Term.pow2neg_Q (.app .succ n2)
  let Fs : Term F Γ₂ Ty.nat := Term.app2 Term.cauchyfy F2 S
  let Gs : Term F Γ₂ Ty.nat := Term.app2 Term.cauchyfy G2 S
  -- (n₁+1) + (n₂+1) =₀ m
  let hm : Derivable F al Premises (Γ := Γ₂) (Formula.eq0
      (Term.app2 Term.add (.app .succ n1) (.app .succ n2)) m) :=
    qtrans (add_succ (.app .succ n1) n2) (succ_congr_o (add_succ_l n1 n2))
  -- (n₂+1) + (n₁+1) =₀ m
  let hm' : Derivable F al Premises (Γ := Γ₂) (Formula.eq0
      (Term.app2 Term.add (.app .succ n2) (.app .succ n1)) m) :=
    qtrans (add_succ (.app .succ n2) n1)
      (succ_congr_o (qtrans (add_succ_l n2 n1) (succ_congr_o (add_comm n2 n1))))
  -- (n₁+1) + ((n₂+2) + b) =₀ (m+1) + b
  let hIf : Derivable F al Premises (Γ := Γ₂) (Formula.eq0
      (Term.app2 Term.add (.app .succ n1)
        (Term.app2 Term.add (.app .succ (.app .succ n2)) b)) S) :=
    qtrans
      (Derivable.mp (add_assoc (.app .succ n1) (.app .succ (.app .succ n2)) b)
        Derivable.sym0)
      (add_congr_l (qtrans (add_succ (.app .succ n1) (.app .succ n2))
        (succ_congr_o hm)) b)
  -- (n₂+1) + ((n₁+2) + b) =₀ (m+1) + b
  let hIg : Derivable F al Premises (Γ := Γ₂) (Formula.eq0
      (Term.app2 Term.add (.app .succ n2)
        (Term.app2 Term.add (.app .succ (.app .succ n1)) b)) S) :=
    qtrans
      (Derivable.mp (add_assoc (.app .succ n2) (.app .succ (.app .succ n1)) b)
        Derivable.sym0)
      (add_congr_l (qtrans (add_succ (.app .succ n2) (.app .succ n1))
        (succ_congr_o hm')) b)
  by
  pmode
  pintro hb
  pintro ha
  -- clean the two hypotheses: `x −ℚ 0̂(·) =ℚ x`
  papplym (le_Q_congr (.app Term.pow2neg_Q n1)
    (Term.app2 Term.sub_Q (Term.app2 Term.cauchyfy F2 (.app .succ n1))
      (Term.app2 Term.cauchyfy Term.zero_R (.app .succ n1)))
    (.app Term.pow2neg_Q n1) (Term.app2 Term.cauchyfy F2 (.app .succ n1))
    (eq_Q_refl_inst (.app Term.pow2neg_Q n1))
    (eqQtrans
      (sub_Q_congr (eq_Q_refl_inst (Term.app2 Term.cauchyfy F2 (.app .succ n1)))
        (eqQ_of_nat_eq' (cauchyfy_zero_R (.app .succ n1))))
      (sub_Q_zero_Q (Term.app2 Term.cauchyfy F2 (.app .succ n1))))) in ha with haf
  papplym (le_Q_congr (.app Term.pow2neg_Q n2)
    (Term.app2 Term.sub_Q (Term.app2 Term.cauchyfy G2 (.app .succ n2))
      (Term.app2 Term.cauchyfy Term.zero_R (.app .succ n2)))
    (.app Term.pow2neg_Q n2) (Term.app2 Term.cauchyfy G2 (.app .succ n2))
    (eq_Q_refl_inst (.app Term.pow2neg_Q n2))
    (eqQtrans
      (sub_Q_congr (eq_Q_refl_inst (Term.app2 Term.cauchyfy G2 (.app .succ n2)))
        (eqQ_of_nat_eq' (cauchyfy_zero_R (.app .succ n2))))
      (sub_Q_zero_Q (Term.app2 Term.cauchyfy G2 (.app .succ n2))))) in hb with hag
  -- persist the bounds to the product's index
  papplym (cauchyfy_lb_imp F2 n1
    (Term.app2 Term.add (.app .succ (.app .succ n2)) b)) in haf with hafs
  papplym (le_Q_congr P1
    (Term.app2 Term.cauchyfy F2 (Term.app2 Term.add (.app .succ n1)
      (Term.app2 Term.add (.app .succ (.app .succ n2)) b)))
    P1 Fs (eq_Q_refl_inst P1)
    (eqQ_of_nat_eq' (cauchyfy_idx_nat' F2 hIf))) in hafs with hFs
  papplym (cauchyfy_lb_imp G2 n2
    (Term.app2 Term.add (.app .succ (.app .succ n1)) b)) in hag with hags
  papplym (le_Q_congr P2
    (Term.app2 Term.cauchyfy G2 (Term.app2 Term.add (.app .succ n2)
      (Term.app2 Term.add (.app .succ (.app .succ n1)) b)))
    P2 Gs (eq_Q_refl_inst P2)
    (eqQ_of_nat_eq' (cauchyfy_idx_nat' G2 hIg))) in hags with hGs
  -- the witness
  pexists m
  canorm
  -- evaluate the outer cauchyfy on the product, drop the `−ℚ 0`
  papplym (le_Q_congr (.app Term.pow2neg_Q m)
    (Term.app2 Term.mul_Q Fs Gs)
    (.app Term.pow2neg_Q m)
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy (Term.app2 Term.mul_R F2 G2) (.app .succ m))
      (Term.app2 Term.cauchyfy Term.zero_R (.app .succ m)))
    (eq_Q_refl_inst (.app Term.pow2neg_Q m))
    (eqQsym (eqQtrans
      (sub_Q_congr (eqQ_of_nat_eq' (cauchyfy_mul_R F2 G2 (.app .succ m)))
        (eqQ_of_nat_eq' (cauchyfy_zero_R (.app .succ m))))
      (sub_Q_zero_Q (Term.app2 Term.mul_Q Fs Gs)))))
  -- 2^{-m} =ℚ 2^{-(n₁+1)} ·ℚ 2^{-(n₂+1)}
  papplym (le_Q_congr (Term.app2 Term.mul_Q P1 P2) (Term.app2 Term.mul_Q Fs Gs)
    (.app Term.pow2neg_Q m) (Term.app2 Term.mul_Q Fs Gs)
    (eqQtrans (pow2neg_Q_mul (.app .succ n1) (.app .succ n2))
      (eqQ_of_nat_eq' (pow2neg_idx_nat' hm)))
    (eq_Q_refl_inst (Term.app2 Term.mul_Q Fs Gs)))
  -- and the product bound
  papplym (le_Q_mul_o P1 Fs P2 Gs)
  psplit
  · psplit
    · pthm (Derivable.mp (zero_lt_pow2neg_Q (.app .succ n1))
        (lt_Q_imp_le_Q Term.zero_Q P1))
    · pthm (Derivable.mp (zero_lt_pow2neg_Q (.app .succ n2))
        (lt_Q_imp_le_Q Term.zero_Q P2))
  · psplit
    · pexact hFs
    · pexact hGs

/-- `0 <ℝ f ∧ 0 <ℝ g → 0 <ℝ f·g`, at explicit reals. The two `∃`-eliminations happen at
the Lean level with `Derivable.exist_rule` — exit 3 of the note at `lt_trans_R_core` — so
no nested `pobtain` ever occurs. -/
def lt_mul_pos_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      ((lt_R Term.zero_R f ∧ᶠ lt_R Term.zero_R g) →ᶠ
        lt_R Term.zero_R (Term.app2 Term.mul_R f g)) := by
  refine Derivable.importation ?_
  rw [lt_R_zero_ex f]
  refine Derivable.exist_rule ?_
  simp only [Formula.weakenBy_imp, lt_R_weakenBy, zero_R_weaken, mul_R_app_weaken2]
  refine Derivable.mp ?_ flip_comb
  rw [lt_R_zero_ex g.weaken]
  refine Derivable.exist_rule ?_
  simp only [Formula.weakenBy_imp, ltBody_weakenBy, lt_R_weakenBy, zero_R_weaken,
    mul_R_app_weaken2]
  exact lt_mul_pos_core f g

/-- ⊢ ∀f,g : ℝ. 0 <_ℝ f ∧ 0 <_ℝ g → 0 <_ℝ f ·_ℝ g -/
def lt_mul_pos_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        ((lt_R Term.zero_R (.var (.vs .vz))
          ∧ᶠ lt_R Term.zero_R (.var .vz))
          →ᶠ lt_R Term.zero_R
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))) :=
  univ_gen (univ_gen (lt_mul_pos_R_core (.var (.vs .vz)) (.var .vz)))

/-- ⊢ 0_ℝ <_ℝ 1_ℝ -/
def zero_lt_one_R :
    Derivable F al Premises (Γ := Γ)
      (lt_R Term.zero_R Term.one_R) :=
  -- `2^{-0} = 1_ℚ`, and both sides are constant, so the witness is `n = 0`:
  -- `1̂(1) −ℚ 0̂(1) = 1_ℚ −ℚ 0_ℚ = 1_ℚ ≥ℚ 2^{-0}`.
  let pow0 : Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.pow2neg_Q Term.zero) Term.one_Q) := by
    pmode
    prw (pow2neg_Q_unfold Term.zero)
    prw exp2_zero
    prw (pd_succ Term.zero)
    prefl
  let body : Derivable F al Premises (Γ := Γ)
      (Formula.eq0
        (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q Term.zero)
          (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy Term.one_R (.app .succ Term.zero))
            (Term.app2 Term.cauchyfy Term.zero_R (.app .succ Term.zero))))
        Term.zero) := by
    pmode
    prw (cauchyfy_one_R (.app .succ Term.zero))
    prw (cauchyfy_zero_R (.app .succ Term.zero))
    prw (sub_Q_one_zero)
    prw pow0
    pthm (le_Q_refl Term.one_Q)
  have nf : (Formula.eq0
      (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy (Term.one_R : Term F Γ _).weaken
            (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy (Term.zero_R : Term F Γ _).weaken
            (.app .succ (.var .vz)))))
      Term.zero).subst0 Term.zero =
      Formula.eq0
        (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q Term.zero)
          (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy Term.one_R (.app .succ Term.zero))
            (Term.app2 Term.cauchyfy Term.zero_R (.app .succ Term.zero))))
        Term.zero := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      subst_subst0_map_weaken, cauchyfy_closed_subst, closed_subst]
  Derivable.mp (nf ▸ body) (Derivable.exist_ax Term.zero _)

-- ── Archimedean property ────────────────────────────────────────────────────

/-- The body of `archimedean_R` at a fixed real `f = var vz`.

The witness is `S (S (f 0))`: its ℚ-value is `(⟨f 0⟩ +ℚ 1) +ℚ 1` (`encode_succ` twice), and
`cauchyfy_mag_le` bounds every cauchyfied value of `f` by `⟨f 0⟩ +ℚ 1`, so the gap is at
least `1 =ℚ 2^{-0}` and the inner witness is `0`. Both `∃`-introductions are Lean-level
`Derivable.exist_ax` steps with `subst0` normal-form lemmas, in the style of
`zero_lt_one_R`. -/
private def archimedean_body :
    Derivable F al Premises (Γ := realTy ι :: Γ)
      (Formula.ex Ty.nat
        (lt_R (Term.var (.vs .vz)) (.app Term.embed_nat_R (.var .vz)))) :=
  let fv : Term F (realTy ι :: Γ) (realTy ι) := .var .vz
  let t : Term F (realTy ι :: Γ) Ty.nat := .app .succ (.app .succ (.app fv .zero))
  let E1 : Term F (realTy ι :: Γ) Ty.nat :=
    Term.app2 Term.add_Q (.app Term.encode_nat_Q (.app fv .zero)) Term.one_Q
  let X : Term F (realTy ι :: Γ) Ty.nat := Term.app2 Term.add_Q E1 Term.one_Q
  let f1 : Term F (realTy ι :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy fv (.app .succ .zero)
  let Ct : Term F (realTy ι :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy (.app Term.embed_nat_R t) (.app .succ .zero)
  -- f̂(1) ≤ ⟨f 0⟩ + 1
  let h1 : Derivable F al Premises (le_Q f1 E1) :=
    leQt (le_Q_self_abs f1) (cauchyfy_mag_le fv (.app .succ .zero))
  -- ⟨t⟩ =ℚ (⟨f 0⟩ + 1) + 1
  let hEt : Derivable F al Premises (eq_Q (.app Term.encode_nat_Q t) X) :=
    eqQtrans (encode_succ (.app .succ (.app fv .zero)))
      (addQl (encode_succ (.app fv .zero)) Term.one_Q)
  -- 1 ≤ X − f̂(1)
  let s0 : Derivable F al Premises
      (le_Q Term.one_Q (Term.app2 Term.sub_Q X f1)) :=
    Derivable.mp (sub_Q_mono_r X h1)
      (le_Q_congr (Term.app2 Term.sub_Q X E1) (Term.app2 Term.sub_Q X f1)
        Term.one_Q (Term.app2 Term.sub_Q X f1)
        (add_Q_sub_cancel_l E1 Term.one_Q)
        (eq_Q_refl_inst (Term.app2 Term.sub_Q X f1)))
  -- 1 ≤ Ĉ(1) − f̂(1), where Ĉ = the embedded witness
  let s2 : Derivable F al Premises
      (le_Q Term.one_Q (Term.app2 Term.sub_Q Ct f1)) :=
    Derivable.mp s0
      (le_Q_congr Term.one_Q (Term.app2 Term.sub_Q X f1)
        Term.one_Q (Term.app2 Term.sub_Q Ct f1)
        (eq_Q_refl_inst Term.one_Q)
        (sub_Q_congr
          (eqQtrans (eqQsym hEt)
            (eqQsym (eqQ_of_nat_eq' (cauchyfy_embed t (.app .succ .zero)))))
          (eq_Q_refl_inst f1)))
  -- 2^{-0} ≤ Ĉ(1) − f̂(1)
  let s3 : Derivable F al Premises
      (le_Q (.app Term.pow2neg_Q Term.zero) (Term.app2 Term.sub_Q Ct f1)) :=
    Derivable.mp s2
      (le_Q_congr Term.one_Q (Term.app2 Term.sub_Q Ct f1)
        (.app Term.pow2neg_Q Term.zero) (Term.app2 Term.sub_Q Ct f1)
        (eqQsym (eqQ_of_nat_eq' pow2neg_zero_eq_one))
        (eq_Q_refl_inst (Term.app2 Term.sub_Q Ct f1)))
  -- inner ∃-introduction at witness 0
  have nf2 : (le_Q (.app Term.pow2neg_Q (.var .vz))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy
          ((.app Term.embed_nat_R t : Term F (realTy ι :: Γ) (realTy ι)).weaken)
          (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy (fv.weaken) (.app .succ (.var .vz))))).subst0
        Term.zero
      = le_Q (.app Term.pow2neg_Q Term.zero) (Term.app2 Term.sub_Q Ct f1) := by
    simp only [le_Q, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, subst_subst0_map_weaken, cauchyfy_closed_subst, closed_subst]
    rfl
  let inner : Derivable F al Premises
      (lt_R fv (.app Term.embed_nat_R t)) :=
    Derivable.mp (nf2 ▸ s3) (Derivable.exist_ax Term.zero _)
  have nf1 : (lt_R (Term.var (.vs .vz)) (.app Term.embed_nat_R (.var .vz))
      : Formula F (Ty.nat :: realTy ι :: Γ)).subst0 t
      = lt_R fv (.app Term.embed_nat_R t) := by
    simp only [Formula.subst0, lt_R_substF, Term.subst, Term.subst0_map,
      embed_nat_R_closed_subst]
    rfl
  Derivable.mp (nf1 ▸ inner) (Derivable.exist_ax t _)

/-- ⊢ ∀f : ℝ. ∃n⁰. f <_ℝ embed_nat(n) -/
def archimedean_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (Formula.ex Ty.nat
          (lt_R (Term.var (.vs .vz))
                (.app Term.embed_nat_R (.var .vz))))) :=
  univ_gen archimedean_body

-- ── `<_ℝ` moves to a later index, and `lt_trans_R` ──────────────────────────
--
-- `lt_R f g` is `∃n. 2^{-n} ≤ℚ ĝ(n+1) −ℚ f̂(n+1)`, so transitivity has to combine two
-- witnesses at *different* indices (REALS_PLAN §0.4 flags this; it is why `lt_trans_R` was
-- never "a lift of `lt_Q_trans`"). The device is that a witness at `n` is also a witness at
-- every later index, **with the bound shrinking at exactly the dyadic rate**:
--
--     2^{-n} ≤ℚ D(n)   ⟹   2^{-(n+k)} ≤ℚ D(n+k),      D(p) := ĝ(p+1) −ℚ f̂(p+1)
--
-- `lt_shift1` is one step of that and `lt_shift` iterates it. The one-step estimate is not
-- tight — moving from `n` to `n+1` costs `2^{-(n+2)}` on each of the two sequences, i.e.
-- `2^{-(n+1)}` in total, which is exactly the amount the bound is allowed to lose — but it is
-- *strictly* less, and that strictness is what keeps the non-strict `≤ℚ` conclusion true.
--
-- With it, transitivity needs no `max`: shifting the first witness by `n₂` and the second by
-- `n₁` lands both at `n₁ +ℕ n₂`, where they simply add.

/-- **One index of slack.** A `<_ℝ` witness at `n` is a witness at `n+1`.

`D(n) −ℚ D(n+1)` is `(ĝ(n+1) −ℚ ĝ(n+2)) +ℚ (f̂(n+2) −ℚ f̂(n+1))`, and both parts are below
`2^{-(n+2)}` strictly — `le_Q_self_abs` turns each `cauchyfy` bound from a bound on `|·|` into
the directed bound that is actually needed. Their sum is therefore strictly below `2^{-(n+1)}`,
so `2^{-(n+1)} +ℚ 2^{-(n+1)} = 2^{-n} ≤ℚ D(n) <ℚ D(n+1) +ℚ 2^{-(n+1)}` and one cancellation
finishes it. -/
def lt_shift1 (f g : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.pow2neg_Q n)
            (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy g (.app .succ n))
              (Term.app2 Term.cauchyfy f (.app .succ n)))
       →ᶠ
       le_Q (.app Term.pow2neg_Q (.app .succ n))
            (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy g (.app .succ (.app .succ n)))
              (Term.app2 Term.cauchyfy f (.app .succ (.app .succ n))))) := by
  let u1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy g (.app .succ n)
  let u2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy g (.app .succ (.app .succ n))
  let v1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ n)
  let v2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ (.app .succ n))
  let D1 : Term F Γ Ty.nat := Term.app2 Term.sub_Q u1 v1
  let D2 : Term F Γ Ty.nat := Term.app2 Term.sub_Q u2 v2
  let aa : Term F Γ Ty.nat := Term.app2 Term.sub_Q u1 u2
  let nb : Term F Γ Ty.nat := Term.app2 Term.sub_Q v2 v1
  let P  : Term F Γ Ty.nat := .app Term.pow2neg_Q n
  let P1 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  let Q  : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ n))
  have hid : Derivable F al Premises
      (eq_Q D1 (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))) :=
    eqQtrans (sub_Q_trans_split v1 u2 u1)
      (eqQtrans (addQl (sub_Q_trans_split v1 v2 u2) aa)
        (eqQtrans (addQl (add_Q_comm_inst nb D2) aa)
          (add_Q_assoc_inst D2 nb aa)))
  pmode
  pintro h
  phave ha : lt_Q aa Q
  · papplym (le_lt_Q_trans aa (.app Term.abs_Q aa) Q)
    psplit
    · pthm (le_Q_self_abs aa)
    · pthm (cauchyfy_cauchy g (.app .succ n))
  phave hnb : lt_Q nb Q
  · papplym (le_lt_Q_trans nb (.app Term.abs_Q nb) Q)
    psplit
    · pthm (le_Q_self_abs nb)
    · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q v1 v2)) Q
        (.app Term.abs_Q nb) Q (abs_diff_Q_comm v1 v2) (eq_Q_refl_inst Q))
      pthm (cauchyfy_cauchy f (.app .succ n))
  phave hsum : lt_Q (Term.app2 Term.add_Q nb aa) P1
  · papplym (lt_Q_congr (Term.app2 Term.add_Q nb aa) (Term.app2 Term.add_Q Q Q)
      (Term.app2 Term.add_Q nb aa) P1
      (eq_Q_refl_inst (Term.app2 Term.add_Q nb aa)) (pow2neg_Q_halve (.app .succ n)))
    papplym (lt_Q_add_both nb aa Q Q)
    psplit
    · pexact hnb
    · pexact ha
  phave hD1 : lt_Q D1 (Term.app2 Term.add_Q D2 P1)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))
      (Term.app2 Term.add_Q D2 P1) D1 (Term.app2 Term.add_Q D2 P1)
      (eqQsym hid) (eq_Q_refl_inst (Term.app2 Term.add_Q D2 P1)))
    papplym (lt_Q_add_l D2 (Term.app2 Term.add_Q nb aa) P1)
    pexact hsum
  phave hlt : lt_Q (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q D2 P1)
  · papplym (lt_Q_congr P (Term.app2 Term.add_Q D2 P1)
      (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q D2 P1)
      (eqQsym (pow2neg_Q_halve n)) (eq_Q_refl_inst (Term.app2 Term.add_Q D2 P1)))
    papplym (le_lt_Q_trans P D1 (Term.app2 Term.add_Q D2 P1))
    psplit
    · pexact h
    · pexact hD1
  papplym (lt_Q_imp_le_Q P1 D2)
  papplym (lt_Q_add_cancel P1 D2 P1)
  pexact hlt

/-- **The shift, iterated.** `∀k ∀p. 2^{-p} ≤ℚ D(p) → 2^{-(p+k)} ≤ℚ D(p+k)`.

Induction on `k`, one `lt_shift1` per round; the index bookkeeping is `add_succ` against
`add_succ_l`, exactly as in `eqR_tail`. -/
def lt_shift (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat (Formula.all Ty.nat
        (le_Q (.app Term.pow2neg_Q (.var .vz))
              (Term.app2 Term.sub_Q
                (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var .vz)))
                (Term.app2 Term.cauchyfy f.weaken.weaken (.app .succ (.var .vz))))
          →ᶠ
         le_Q (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
              (Term.app2 Term.sub_Q
                (Term.app2 Term.cauchyfy g.weaken.weaken
                  (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
                (Term.app2 Term.cauchyfy f.weaken.weaken
                  (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))) := by
  pmode
  pinduction
  · canorm
    pforall
    pintro h
    prw (add_zero_r (.var .vz))
    pexact h
  · pforall
    pintro ih
    canorm
    pforall
    pintro h
    papplym (lt_shift1 f.weaken.weaken g.weaken.weaken (.var .vz)) in h with h1
    pinst ih (.app .succ (.var .vz)) with ihp
    canorm
    -- `p +ℕ (k+1) =₀ (p+1) +ℕ k`; rewriting the goal rather than `ihp` because
    -- `prw … in h` needs an atomic hypothesis and `ihp` is an implication
    prw (qtrans (add_succ (.var .vz) (.var (.vs .vz)))
      (Derivable.mp (add_succ_l (.var .vz) (.var (.vs .vz))) Derivable.sym0))
    papply ihp
    pexact h1

/-- `lt_shift` at explicit `p` and `k`, with both `∀`-instantiations already normalised.

Doing this at the Lean level rather than with `pfrom`/`pinst` inside the proof mode is not
cosmetic: as a proof-mode hypothesis the instantiated statement has to be matched against the
goal by `pexact`, and with `Term.cauchyfy` on both sides that match runs into the
delta-expansion blow-up (measured: a heartbeat timeout). As a Lean-level implication it is fed
to `papplym … in … with …`, which never inspects the goal. -/
def lt_shift_at (f g : Term F Γ (realTy ι)) (p k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.pow2neg_Q p)
            (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy g (.app .succ p))
              (Term.app2 Term.cauchyfy f (.app .succ p)))
       →ᶠ
       le_Q (.app Term.pow2neg_Q (Term.app2 Term.add p k))
            (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy g (.app .succ (Term.app2 Term.add p k)))
              (Term.app2 Term.cauchyfy f (.app .succ (Term.app2 Term.add p k))))) := by
  have hh := Derivable.mp (Derivable.mp
    (lt_shift (al := al) (Premises := Premises) f g) (.forall_ax k)) (.forall_ax p)
  simpa only [lt_Q, le_Q, eq_Q, Formula.subst0, Formula.substF, Formula.neg,
    Term.subst0, Term.subst, Term.subst0_map, Term.Subst.ext, Term.app2,
    Term.weaken_subst_ext, Term.weaken_subst0, subst_subst0_map_weaken,
    cauchyfy_closed_subst, closed_subst] using hh

/-- `f <_ℝ g ∧ g <_ℝ h → f <_ℝ h`, at explicit reals.

The two witnesses are shifted to the common index `n₁ +ℕ n₂` — the first by `n₂`, the second
by `n₁` and then `add_comm` — where the two differences simply add:
`(ĥ −ℚ ĝ) +ℚ (ĝ −ℚ f̂) = ĥ −ℚ f̂`. Only one of the two shifted bounds is spent as a bound; the
other contributes through `0_ℚ ≤ℚ 2^{-m} ≤ℚ ĥ −ℚ ĝ`, which is why no `max` and no doubling of
the dyadic scale is needed.

**CLOSED 2026-09-03 via exit 3 of the note that used to stand here.** The history, kept
because it is a worked example of the display-hiding trap family (CLAUDE.md note 12): the
first attempt ran **two nested `pobtain`s**, and `pm_exE` wraps every earlier hypothesis in
`Formula.weakenBy`, which the delaborator hides — `pexact` on the wrapped hypothesis was a
measured heartbeat timeout, not a type error. Adding `Term.subst_shift_eq_weaken` /
`Formula.substF_shift_eq_weakenBy` to `canorm` (exit 1) was necessary but not sufficient:
the failure moved to `canorm` itself timing out on the large packed goal. What landed is
exit 3 — **both `∃`-eliminations happen at the Lean level with `Derivable.exist_rule`**
(`lt_R_ex` presents the antecedent in the `le_Q` spelling, `ltBody_weakenBy` /
`lt_R_weakenBy` compute the `weakenBy` the rule's premise carries, `flip_comb` swaps the
antecedents between the two peels), so no `pobtain` ever runs and no hypothesis is ever
wrapped. `lt_trans_inner` below then sees the two witnesses as plain bound variables and is
a short forward proof over `lt_shift_at`. The same assembly closed `lt_mul_pos_R` and
`lt_add_R`. -/
private def lt_trans_inner (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Ty.nat :: Γ)
      (le_Q (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy h.weaken.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var .vz))))
       →ᶠ
       (le_Q (.app Term.pow2neg_Q (.var (.vs .vz)))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var (.vs .vz))))
          (Term.app2 Term.cauchyfy f.weaken.weaken (.app .succ (.var (.vs .vz)))))
       →ᶠ
       lt_R f.weaken.weaken h.weaken.weaken)) :=
  let Γ₂ := Ty.nat :: Ty.nat :: Γ
  let n1 : Term F Γ₂ Ty.nat := .var (.vs .vz)
  let n2 : Term F Γ₂ Ty.nat := .var .vz
  let F2 : Term F Γ₂ (realTy ι) := f.weaken.weaken
  let G2 : Term F Γ₂ (realTy ι) := g.weaken.weaken
  let H2 : Term F Γ₂ (realTy ι) := h.weaken.weaken
  let m : Term F Γ₂ Ty.nat := Term.app2 Term.add n1 n2
  let M : Term F Γ₂ Ty.nat := .app .succ m
  let Fm : Term F Γ₂ Ty.nat := Term.app2 Term.cauchyfy F2 M
  let Gm : Term F Γ₂ Ty.nat := Term.app2 Term.cauchyfy G2 M
  let Hm : Term F Γ₂ Ty.nat := Term.app2 Term.cauchyfy H2 M
  let hcomm : Derivable F al Premises (Γ := Γ₂)
      (Formula.eq0 (Term.app2 Term.add n2 n1) m) := add_comm n2 n1
  by
  pmode
  pintro b
  pintro a
  -- shift both witnesses to the common index m = n₁ + n₂
  papplym (lt_shift_at F2 G2 n1 n2) in a with hA
  papplym (lt_shift_at G2 H2 n2 n1) in b with hB0
  papplym (le_Q_congr (.app Term.pow2neg_Q (Term.app2 Term.add n2 n1))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy H2 (.app .succ (Term.app2 Term.add n2 n1)))
      (Term.app2 Term.cauchyfy G2 (.app .succ (Term.app2 Term.add n2 n1))))
    (.app Term.pow2neg_Q m)
    (Term.app2 Term.sub_Q Hm Gm)
    (eqQ_of_nat_eq' (pow2neg_idx_nat' hcomm))
    (sub_Q_congr
      (eqQ_of_nat_eq' (cauchyfy_idx_nat' H2 (succ_congr_o hcomm)))
      (eqQ_of_nat_eq' (cauchyfy_idx_nat' G2 (succ_congr_o hcomm))))) in hB0 with hB
  -- only one bound is spent as a bound; the other through 0 ≤ 2^{-m} ≤ ĥ − ĝ
  papplym (le_Q_trans_l (Term.app2 Term.sub_Q Hm Gm)
    (Derivable.mp (zero_lt_pow2neg_Q m)
      (lt_Q_imp_le_Q Term.zero_Q (.app Term.pow2neg_Q m)))) in hB with hz
  pexists m
  canorm
  papplym (le_Q_congr
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q m) Term.zero_Q)
    (Term.app2 Term.add_Q (Term.app2 Term.sub_Q Gm Fm) (Term.app2 Term.sub_Q Hm Gm))
    (.app Term.pow2neg_Q m)
    (Term.app2 Term.sub_Q Hm Fm)
    (add_Q_zero_inst (.app Term.pow2neg_Q m))
    (eqQsym (sub_Q_trans_split Fm Gm Hm)))
  papplym (le_Q_add_both (.app Term.pow2neg_Q m) Term.zero_Q
    (Term.app2 Term.sub_Q Gm Fm) (Term.app2 Term.sub_Q Hm Gm))
  psplit
  · pexact hA
  · pexact hz

/-- `f <ℝ g ∧ g <ℝ h → f <ℝ h`, at explicit reals.

The two witnesses are shifted to the common index `n₁ +ℕ n₂` — the first by `n₂`, the second
by `n₁` and then `add_comm` — where the two differences simply add:
`(ĥ −ℚ ĝ) +ℚ (ĝ −ℚ f̂) = ĥ −ℚ f̂`. See the note at `lt_trans_inner` for the assembly. -/
def lt_trans_R_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (lt_R f g ∧ᶠ lt_R g h →ᶠ lt_R f h) := by
  refine Derivable.importation ?_
  rw [lt_R_ex f g]
  refine Derivable.exist_rule ?_
  simp only [Formula.weakenBy_imp, lt_R_weakenBy]
  refine Derivable.mp ?_ flip_comb
  rw [lt_R_ex g.weaken h.weaken]
  refine Derivable.exist_rule ?_
  simp only [Formula.weakenBy_imp, ltBody_weakenBy, lt_R_weakenBy]
  exact lt_trans_inner f g h

/- HISTORICAL — the nested-`pobtain` script that could not be completed (it died at the
`pexact a` marked below: a heartbeat timeout on a `weakenBy`-wrapped hypothesis). Kept
because it is the measured failure that forced the Lean-level `exist_rule` assembly above;
its estimate steps live on inside `lt_trans_inner`.

  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  pobtain hfg with a
  canorm
  pobtain hgh with b
  -- the second `pobtain` weakens the *first* witness's hypothesis under a binder, leaving a
  -- bare `renameF (ext vs)` that `q_cons_norm` does not touch; this is `anorm_ren`'s first
  -- step, which turns that renaming into the `Subst.cons` normal form `canorm` understands
  simp only [Formula.renameF_ext_eq_substF_cons, Formula.renameF_eq_substF]
  canorm
  pexists (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))
  canorm
  phave ha2 : le_Q (.app Term.pow2neg_Q (.var (.vs .vz)))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var (.vs .vz))))
        (Term.app2 Term.cauchyfy f.weaken.weaken (.app .succ (.var (.vs .vz)))))
  · pexact a
  papplym (lt_shift_at f.weaken.weaken g.weaken.weaken (.var (.vs .vz)) (.var .vz))
    in ha2 with hA
  papplym (lt_shift_at g.weaken.weaken h.weaken.weaken (.var .vz) (.var (.vs .vz)))
    in b with hB0
  prw (add_comm (.var .vz) (.var (.vs .vz))) in hB0 with hB
  phave hzero : le_Q Term.zero_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
  · papplym (lt_Q_imp_le_Q Term.zero_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    papplym (lt_le_Q_trans Term.zero_Q
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    psplit
    · pthm (zero_lt_pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    · pexact hB
  papplym (le_Q_congr
    (Term.app2 Term.add_Q
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))) Term.zero_Q)
    (Term.app2 Term.add_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy f.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
    (add_Q_zero_inst
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
    (eqQsym (sub_Q_trans_split
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))))
  papplym (le_Q_add_both
    (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    Term.zero_Q
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
  psplit
  · pexact hA
  · pexact hzero
-/

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g ∧ g <_ℝ h → f <_ℝ h -/
def lt_trans_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        ((lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ lt_R (.var (.vs .vz)) (.var .vz))
          →ᶠ lt_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  univ_gen (univ_gen (univ_gen
    (lt_trans_R_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

end OrderedFieldAxioms

end Metatheorems
