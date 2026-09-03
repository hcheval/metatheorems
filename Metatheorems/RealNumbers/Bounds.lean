/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Estimates
import Metatheorems.RealNumbers.QBounds

namespace Metatheorems

/-!
# Magnitude bounds for cauchyfied sequences

The cauchyfy-level layer between `QBounds.lean` (pure ℚ-code facts) and the two consumers:
`abs_R_bound` (`Metric.lean`) and `mul_R_check` (`Mul.lean`). The central estimate is
`cauchyfy_mag_le`: `|ŵ(y)|_ℚ ≤_ℚ ⟨w 0⟩_ℚ +_ℚ 1_ℚ` for **any** `w` — one telescope from
index 0 (`cauchyfy_shift_le` at `p = 0`, worth `2^{-0} = 1`) plus the code-dominates fact
`abs_le_encode` at `ŵ(0) = w 0`.
-/

open Formula

variable {ι : Type} {F : ι → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section Bounds

variable {Γ : Ctx ι}

-- ── Small Lean-level plumbing ───────────────────────────────────────────────

/-- `=₀` implies `=_ℚ` (public version of the helper private to `Mul.lean`). -/
def eqQ_of_nat_eq' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (eq_Q s t) :=
  qtrans
    (qfer_no_premise_nat_nf (Derivable.mp h Derivable.sym0)
      (r := Term.app2 Term.eq_Q_dec s.weaken (.var .vz))
      (by qb_nf) (by qb_nf))
    (eq_Q_refl_inst s)

/-- Congruence for `cauchyfy` in its index, at the level of `=₀`. -/
def cauchyfy_idx_nat' (h : Term F Γ (realTy ι)) {s t : Term F Γ Ty.nat}
    (he : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy h s) (Term.app2 Term.cauchyfy h t)) :=
  qfer_no_premise_nat_nf he (r := Term.app2 Term.cauchyfy h.weaken (.var .vz))
    (by qb_nf) (by qb_nf)

/-- Congruence for `pow2neg_Q` in its index, at the level of `=₀`. -/
def pow2neg_idx_nat' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.pow2neg_Q s) (.app Term.pow2neg_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.pow2neg_Q (.var .vz))
    (by qb_nf) (by qb_nf)

/-- Congruence for `abs_Q`, at the level of `=₀`. -/
def abs_Q_congr_nat {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.abs_Q s) (.app Term.abs_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.abs_Q (.var .vz))
    (by qb_nf) (by qb_nf)

-- ── Beta lemmas for `abs_R` and `embed_nat_R` ───────────────────────────────

/-- `(|w|_ℝ)(x) =₀ |ŵ(x)|_ℚ` — the two beta steps of `abs_R`. -/
def abs_R_apply (w : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app (.app Term.abs_R w) x)
        (.app Term.abs_Q (Term.app2 Term.cauchyfy w x))) :=
  lam2_correct_nf
    (.app Term.abs_Q (Term.app2 Term.cauchyfy (.var (.vs .vz)) (.var .vz))
      : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat)
    w x (by qb_nf)

/-- `((m)_ℝ)(x) =₀ ⟨m⟩_ℚ` — the embedded natural is the constant sequence at its code. -/
def embed_nat_R_apply (m : Term F Γ Ty.nat) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app (.app Term.embed_nat_R m) x) (.app Term.encode_nat_Q m)) :=
  lam2_correct_nf
    (.app Term.encode_nat_Q (.var (.vs .vz)) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    m x (by qb_nf)

private theorem abs_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.abs_R : Term F Δ _).weaken (σ := ρ) = Term.abs_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact abs_R_closed_subst _

theorem abs_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (w : Term F Δ (realTy ι)) :
    (Term.app Term.abs_R w).weaken (σ := ρ) = .app Term.abs_R w.weaken := by
  show Term.app (Term.weaken Term.abs_R) w.weaken = _
  rw [abs_R_weaken]

private theorem embed_nat_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.embed_nat_R : Term F Δ _).weaken (σ := ρ) = Term.embed_nat_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact embed_nat_R_closed_subst _

theorem embed_nat_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (m : Term F Δ Ty.nat) :
    (Term.app Term.embed_nat_R m).weaken (σ := ρ) = .app Term.embed_nat_R m.weaken := by
  show Term.app (Term.weaken Term.embed_nat_R) m.weaken = _
  rw [embed_nat_R_weaken]

/-- The Cauchy check passes for `(m)_ℝ` at every index: it is a constant sequence. Spelled
out rather than written with `Term.cauchy_check_at`, for the usual `prw` reason. -/
def embed_nat_R_check (m : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (.app Term.embed_nat_R m.weaken) (.var .vz))
            (.app (.app Term.embed_nat_R m.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (embed_nat_R_apply m.weaken (.var .vz))
  prw (embed_nat_R_apply m.weaken (.app .succ (.var .vz)))
  pthm (lt_Q_abs_sub_self (.app Term.encode_nat_Q m.weaken) (.app .succ (.var .vz)))

/-- `cauchyfy` is the identity on `(m)_ℝ`, and its value is `⟨m⟩_ℚ`. -/
def cauchyfy_embed (m : Term F Γ Ty.nat) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.embed_nat_R m) s)
        (.app Term.encode_nat_Q m)) :=
  qtrans
    (cauchyfy_id (.app Term.embed_nat_R m)
      (embed_nat_R_app_weaken m ▸ embed_nat_R_check m) s)
    (embed_nat_R_apply m s)

-- ── The magnitude bound ─────────────────────────────────────────────────────

/-- **`|ŵ(y)|_ℚ ≤_ℚ ⟨w 0⟩_ℚ +_ℚ 1_ℚ` for any `w` whatsoever** — a cauchyfied value's
magnitude is dominated by the code of the sequence's own first element, plus the total
travel `2^{-0} = 1` the telescope allows from index `0`. -/
def cauchyfy_mag_le (w : Term F Γ (realTy ι)) (y : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.cauchyfy w y))
        (Term.app2 Term.add_Q (.app Term.encode_nat_Q (.app w Term.zero)) Term.one_Q)) :=
  let wy : Term F Γ Ty.nat := Term.app2 Term.cauchyfy w y
  let w0 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy w Term.zero
  let diff : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q w0 wy)
  -- |ŵ(y)| ≤ |ŵ(0)| + |ŵ(0) − ŵ(y)|
  let h1 : Derivable F al Premises
      (le_Q (.app Term.abs_Q wy)
        (Term.app2 Term.add_Q (.app Term.abs_Q w0) diff)) :=
    abs_Q_le_add_diff wy w0
  -- |ŵ(0)| =₀ |w 0| ≤ ⟨w 0⟩
  let h2 : Derivable F al Premises
      (le_Q (.app Term.abs_Q w0) (.app Term.encode_nat_Q (.app w Term.zero))) :=
    Derivable.mp (abs_le_encode (.app w Term.zero))
      (le_Q_congr _ _ _ _
        (eqQ_of_nat_eq'
          (Derivable.mp (abs_Q_congr_nat (cauchyfy_zero w)) Derivable.sym0))
        (eq_Q_refl_inst _))
  -- |ŵ(0) − ŵ(y)| ≤ 2^{-0} =₀ 1
  let h3 : Derivable F al Premises (le_Q diff Term.one_Q) :=
    Derivable.mp
      (cauchyfy_shift_le w Term.zero y)
      (le_Q_congr _ _ _ _
        (eqQ_of_nat_eq'
          (abs_Q_congr_nat
            (qfer_no_premise_nat_nf (add_zero_l y)
              (r := Term.app2 Term.sub_Q w0.weaken
                (Term.app2 Term.cauchyfy w.weaken (.var .vz)))
              (by qb_nf; rfl) (by qb_nf; rfl))))
        (eqQ_of_nat_eq' pow2neg_zero_eq_one))
  leQt h1
    (Derivable.mp (Derivable.mp h3 (Derivable.mp h2 and_intro))
      (le_Q_add_both (.app Term.abs_Q w0) diff
        (.app Term.encode_nat_Q (.app w Term.zero)) Term.one_Q))

-- ── Assembly pieces for the multiplicative axioms ───────────────────────────

/-- `univ_gen` of the pointwise strict bound, folded into `=_ℝ` (definitionally the same
formula). The two composed reals stay Lean-level parameters throughout, so no `prw` ever
sees them. -/
def eq_R_of_lt_bound (u v : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))))
        (.app Term.pow2neg_Q (.var .vz)))) :
    Derivable F al Premises (eq_R u v) :=
  univ_gen h

/-- **The dyadic conversion of one move**: `(⟨c⟩+1)·2^{-p} ≤_ℚ 2^{-j}` once
`p = (c+1) + (j + w)` at ℕ — the magnitude `⟨c⟩+1 ≤ ⟨2^{c+1}⟩` eats `c+1` of the exponent,
`w` is discarded, and `j` remains. -/
def mag_dyadic_le (c p j w : Term F Γ Ty.nat)
    (hp : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add (.app .succ c) (Term.app2 Term.add j w)) p)) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q
        (Term.app2 Term.add_Q (.app Term.encode_nat_Q c) Term.one_Q)
        (.app Term.pow2neg_Q p))
        (.app Term.pow2neg_Q j)) :=
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q p
  let B : Term F Γ Ty.nat :=
    Term.app2 Term.add_Q (.app Term.encode_nat_Q c) Term.one_Q
  let eSc : Term F Γ Ty.nat := .app Term.encode_nat_Q (.app .succ c)
  let e2c : Term F Γ Ty.nat := .app Term.encode_nat_Q (.app Term.exp2 (.app .succ c))
  let e1 : Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q B P) (Term.app2 Term.mul_Q eSc P)) :=
    mulQl (eqQsym (encode_succ c)) P
  let l1 : Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q eSc P) (Term.app2 Term.mul_Q e2c P)) :=
    le_Q_mul_mono_l eSc e2c P
      (encode_le (.app .succ c) (.app Term.exp2 (.app .succ c))
        (exp2_ge_self_inst (.app .succ c)))
      (Derivable.mp (zero_lt_pow2neg_Q p) (lt_Q_imp_le_Q _ _))
  let e2 : Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q e2c P)
        (.app Term.pow2neg_Q (Term.app2 Term.add j w))) :=
    eqQtrans
      (mulQr e2c (eqQ_of_nat_eq' (Derivable.mp (pow2neg_idx_nat' hp) Derivable.sym0)))
      (encode_pow2_mul (.app .succ c) (Term.app2 Term.add j w))
  leQt
    (Derivable.mp l1 (le_Q_congr _ _ _ _ (eqQsym e1) e2))
    (pow2neg_Q_le_add j w)

/-- The strict variant: `(⟨c⟩+1)·2^{-p} <_ℚ 2^{-j}`, via `c+2 ≤ 2^{c+1}`. This is where the
strictness of each check/estimate comes from. -/
def mag_dyadic_lt (c p j w : Term F Γ Ty.nat)
    (hp : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add (.app .succ c) (Term.app2 Term.add j w)) p)) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.mul_Q
        (Term.app2 Term.add_Q (.app Term.encode_nat_Q c) Term.one_Q)
        (.app Term.pow2neg_Q p))
        (.app Term.pow2neg_Q j)) :=
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q p
  let B : Term F Γ Ty.nat :=
    Term.app2 Term.add_Q (.app Term.encode_nat_Q c) Term.one_Q
  let eSc : Term F Γ Ty.nat := .app Term.encode_nat_Q (.app .succ c)
  let e2c : Term F Γ Ty.nat := .app Term.encode_nat_Q (.app Term.exp2 (.app .succ c))
  let e1 : Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q B P) (Term.app2 Term.mul_Q eSc P)) :=
    mulQl (eqQsym (encode_succ c)) P
  let l1 : Derivable F al Premises
      (lt_Q (Term.app2 Term.mul_Q eSc P) (Term.app2 Term.mul_Q e2c P)) :=
    lt_Q_mul_mono_l eSc e2c P
      (encode_lt (.app .succ c) (.app Term.exp2 (.app .succ c))
        (succ_succ_le_exp2_succ c))
      (zero_lt_pow2neg_Q p)
  let e2 : Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q e2c P)
        (.app Term.pow2neg_Q (Term.app2 Term.add j w))) :=
    eqQtrans
      (mulQr e2c (eqQ_of_nat_eq' (Derivable.mp (pow2neg_idx_nat' hp) Derivable.sym0)))
      (encode_pow2_mul (.app .succ c) (Term.app2 Term.add j w))
  Derivable.mp
    (Derivable.mp (pow2neg_Q_le_add j w)
      (Derivable.mp
        (Derivable.mp l1 (lt_Q_congr _ _ _ _ (eqQsym e1) e2))
        and_intro))
    (lt_le_Q_trans _ _ (.app Term.pow2neg_Q j))

/-- Local `S`-congruence (the one in `RationalNumbers.lean` is private). -/
private def succ_congr₀ {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) (by qb_nf) (by qb_nf)

/-- `(p+1) + ((s+1) + q) =₀ s + ((q + p) + 2)` — the ℕ identity each move's dyadic
conversion consumes, with the `(q+p)`-ordered bound. -/
def nat_shuffle1 (p q s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0
        (Term.app2 Term.add (.app .succ p) (Term.app2 Term.add (.app .succ s) q))
        (Term.app2 Term.add s
          (Term.app2 Term.add (Term.app2 Term.add q p) (Term.ofNat 2)))) :=
  let sq : Term F Γ Ty.nat := Term.app2 Term.add s q
  let qp : Term F Γ Ty.nat := Term.app2 Term.add q p
  -- LHS =₀ S (S (p + (s + q)))
  let hL : Derivable F al Premises
      (Formula.eq0
        (Term.app2 Term.add (.app .succ p) (Term.app2 Term.add (.app .succ s) q))
        (.app .succ (.app .succ (Term.app2 Term.add p sq)))) :=
    qtrans (add_succ_l p (Term.app2 Term.add (.app .succ s) q))
      (succ_congr₀ (qtrans (add_congr_r p (add_succ_l s q))
        (add_succ p sq)))
  -- RHS =₀ S (S (s + (q + p)))
  let hR : Derivable F al Premises
      (Formula.eq0
        (Term.app2 Term.add s (Term.app2 Term.add qp (Term.ofNat 2)))
        (.app .succ (.app .succ (Term.app2 Term.add s qp)))) :=
    qtrans
      (add_congr_r s
        (qtrans (add_succ qp (.app .succ .zero))
          (succ_congr₀ (qtrans (add_succ qp .zero) (succ_congr₀ (add_zero_r qp))))))
      (qtrans (add_succ s (.app .succ qp)) (succ_congr₀ (add_succ s qp)))
  -- middle: p + (s + q) =₀ s + (q + p)
  let mid : Derivable F al Premises (Formula.eq0 (Term.app2 Term.add p sq) (Term.app2 Term.add s qp)) :=
    qtrans (add_comm p sq) (add_assoc s q p)
  qtrans hL
    (qtrans (succ_congr₀ (succ_congr₀ mid)) (Derivable.mp hR Derivable.sym0))

/-- The mirror of `nat_shuffle1`, with the `(p+q)`-ordered bound. -/
def nat_shuffle2 (p q s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0
        (Term.app2 Term.add (.app .succ p) (Term.app2 Term.add (.app .succ s) q))
        (Term.app2 Term.add s
          (Term.app2 Term.add (Term.app2 Term.add p q) (Term.ofNat 2)))) :=
  qtrans (nat_shuffle1 p q s)
    (add_congr_r s (add_congr_l (add_comm q p) (Term.ofNat 2)))

end Bounds

end Metatheorems
