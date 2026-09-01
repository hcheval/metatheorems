import Metatheorems.RealNumbers

namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι}
variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) →
    Term F Γ (Ty.base i) → Formula F Γ}
  {al : Allowed} {Premises : PremiseSet F}
  (adm : AdmissibleEqX EqX)

variable {Γ : Ctx ι}

-- ============================================================================
-- ℝ: the one-step estimate
-- ============================================================================

/-- Substitution is natural in `cauchyState`. Without this the substitutions an induction
leaves behind cannot be pushed past the recursion without delta-expanding it. -/
@[simp] theorem cauchyState_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)
    (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    (Term.cauchyState f n).subst σ = Term.cauchyState (f.subst σ) (n.subst σ) := by
  simp only [Term.cauchyState, Term.cauchyBase, Term.cauchyStep, Term.cauchy_check_at,
    Term.subst, Term.Subst.ext, Term.app2, Term.app3, Term.weaken_subst_ext, closed_subst]
  rfl

/-- `f̂(n)`, in the form the `cauchyfy` theory states its facts about. -/
abbrev cV (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  .app Term.fst_pair (Term.cauchyState f n)

/-- `|f̂(n) −ℚ ĥ(n)|ℚ`. -/
abbrev cDiff (f h : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  .app Term.abs_Q (Term.app2 Term.sub_Q (cV f n) (cV h n))

/-- **The one-step estimate.** `|f̂(q) −ℚ ĥ(q)| <ℚ 2^{-q} +ℚ |f̂(q+1) −ℚ ĥ(q+1)|`.

Both `cauchyfy` steps are *strict*, and their sum is exactly `2^{-q}`; carrying that
strictness is the whole reason `eq_R_trans` closes at all. -/
def cauchy_pair_step (f h : Term F Γ (realTy ι)) (q : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (lt_Q (cDiff f h q)
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) (cDiff f h (.app .succ q)))) :=
  let a  : Term F Γ Ty.nat := cV f q
  let a' : Term F Γ Ty.nat := cV f (.app .succ q)
  let b  : Term F Γ Ty.nat := cV h q
  let b' : Term F Γ Ty.nat := cV h (.app .succ q)
  let X : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a')
  let Y : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a' b')
  let Z : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q b' b)
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ q)
  by
  pmode
  pfrom hX := cauchyState_cauchy adm f q
  pfrom hZ0 := cauchyState_cauchy adm h q
  papplym (lt_Q_congr adm (.app Term.abs_Q (Term.app2 Term.sub_Q b b')) e Z e
      (abs_diff_Q_comm adm b b') (eq_Q_refl_inst adm e)) in hZ0 with hZ
  phave hXZ : lt_Q (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
  · papplym (lt_Q_congr adm (Term.app2 Term.add_Q X Z) (Term.app2 Term.add_Q e e)
      (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
      (eq_Q_refl_inst adm (Term.app2 Term.add_Q X Z)) (pow2neg_Q_halve adm q))
    papplym (lt_Q_add_both adm X Z e e)
    psplit
    · pexact hX
    · pexact hZ
  phave htri : le_Q (cDiff f h q) (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
  · papplym (le_Q_trans adm (cDiff f h q)
      (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y))
    psplit
    · papplym (le_Q_trans adm (cDiff f h q)
        (Term.app2 Term.add_Q X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b)))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
      psplit
      · pthm (abs_Q_sub_triangle adm a a' b)
      · papplym (le_Q_add_both adm X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b))
          X (Term.app2 Term.add_Q Y Z))
        psplit
        · pthm (le_Q_refl adm X)
        · pthm (abs_Q_sub_triangle adm a' b' b)
    · papplym (le_Q_congr adm (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
        (eq_Q_refl_inst adm (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
        (eqQtrans adm (addQr adm X (add_Q_comm_inst adm Y Z))
          (eqQsym adm (add_Q_assoc_inst adm X Z Y))))
      pthm (le_Q_refl adm (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
  papplym (le_lt_Q_trans adm (cDiff f h q)
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) Y))
  psplit
  · pexact htri
  · papplym (lt_Q_add_inst adm (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q) Y)
    pexact hXZ

/-- `q_ord_norm`, with the `cauchyfy` state and the two display abbreviations folded in. -/
macro "canorm" : tactic =>
  `(tactic| (try q_cons_norm
             simp only [cDiff, cV, cauchyState_subst,
               lt_Q, le_Q, eq_Q,
               Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst,
               Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               Term.weaken_subst0, subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, ProofMode.succVar0, closed_subst]
             try q_cons_norm))

/-- **The telescoping induction.** From `∀p. X_p <ℚ 2^{-p} +ℚ 2^{-p}` (where
`X_p := |f̂(p+1) −ℚ ĥ(p+1)|`) and the one-step estimate, `∀k ∀p. X_p <ℚ 2^{-p} +ℚ 2^{-(p+k)}`.

Each round of the induction spends one `cauchyfy` step on each side — together exactly
`2^{-(p+1)} +ℚ 2^{-(p+1)} =ℚ 2^{-p}` — and pushes the residual one index further out. -/
def eqR_hyp (f h : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz))))

def eqR_tail (f h : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
            (.app Term.pow2neg_Q
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))) := by
  pmode
  pintro hh
  pinduction
  · -- base: `2^{-(p+0)}` is `2^{-p}`
    canorm
    pforall
    pspecialize hh with h1
    canorm
    prw (add_zero_r adm (.var .vz))
    pexact h1
  · pforall
    pintro ih
    canorm
    pforall
    pinst ih (.app .succ (.var .vz)) with ihp
    canorm
    prw (add_succ_l adm (.var .vz) (.var (.vs .vz))) in ihp with ihp2
    prw (add_succ adm (.var .vz) (.var (.vs .vz)))
    papplym (lt_Q_congr adm
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
      (eq_Q_refl_inst adm _)
      (eqQtrans adm
        (eqQsym adm (add_Q_assoc_inst adm
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        (addQl adm (pow2neg_Q_halve adm (.var .vz))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    papplym (lt_Q_trans_inst adm
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    psplit
    · pthm (cauchy_pair_step adm f.weaken.weaken h.weaken.weaken
        (.app .succ (.var .vz)))
    · papplym (lt_Q_add_l adm (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      pexact ihp2

/-- **The Archimedean squeeze.** The telescoping estimate holds for *every* `k`, so the
strict `<ℚ 2^{-p} +ℚ 2^{-(p+k)}` collapses to a non-strict `≤ℚ 2^{-p}`.

`pow2neg_rat_den_le` supplies the index: if the excess `r := X_p −ℚ 2^{-p}` were positive,
`2^{-(p + den r)} ≤ℚ 2^{-den r} ≤ℚ r` and the estimate at `k := den r` gives `X_p <ℚ X_p`. -/
def eqR_le (f h : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (le_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_tail adm f h) in hh with hT
  pforall
  pfrom hdic := le_Q_or_lt_Q adm
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
  pcases hdic with hle | hgt
  · pexact hle
  · pexfalso
    papplym (lt_Q_to_zero_sub adm (.app Term.pow2neg_Q (.var .vz))
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))) in hgt with hpos
    papplym (pow2neg_rat_den_le adm (Term.app2 Term.sub_Q
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) in hpos with hd
    pinst hT (.app Term.rat_den (Term.app2 Term.sub_Q
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) with hT1
    canorm
    pinst hT1 (.var .vz) with hT2
    canorm
    phave hchain : le_Q
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
    · papplym (le_Q_add_l adm (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (le_Q_trans adm
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (.app Term.pow2neg_Q (.app Term.rat_den (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz)))))
        (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      psplit
      · pthm (pow2neg_Q_le_add_r adm (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      · pexact hd
    phave hXX : lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
                     (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    · papplym (lt_Q_congr adm
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (eq_Q_refl_inst adm _)
        (add_Q_sub_cancel adm
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (lt_le_Q_trans adm
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      psplit
      · pexact hT2
      · pexact hchain
    papplym (lt_Q_irrefl_inst adm
      (cDiff f.weaken h.weaken (.app .succ (.var .vz))))
    pexact hXX

/-- **The strict estimate.** One more `cauchyfy` step on top of the non-strict one: the step
is strict and costs `2^{-(n+1)}`, the squeeze at `n+1` costs `2^{-(n+1)}`, and they sum to
exactly `2^{-n}`. This is where the tightness of `eq_R` is finally paid for. -/
def eqR_strict (f h : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_le adm f h) in hh with hle
  pforall
  pinst hle (.app .succ (.var .vz)) with hle1
  canorm
  papplym (lt_Q_congr adm
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
    (eq_Q_refl_inst adm _)
    (pow2neg_Q_halve adm (.var .vz)))
  papplym (lt_le_Q_trans adm
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz)))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
  psplit
  · pthm (cauchy_pair_step adm f.weaken h.weaken (.app .succ (.var .vz)))
  · papplym (le_Q_add_l adm (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    pexact hle1

/-- The base of the induction, from the two `=_ℝ` hypotheses: one triangle inequality at
each index. -/
def eqR_hyp_of (f g h : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises
      (eq_R f g ∧ᶠ eq_R g h →ᶠ eqR_hyp f h) := by
  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  pforall
  pspecialize hfg with h1
  pspecialize hgh with h2
  canorm
  prw (cauchyfy_unfold adm f.weaken (.app .succ (.var .vz))) in h1 with h1a
  prw (cauchyfy_unfold adm g.weaken (.app .succ (.var .vz))) in h1a with h1b
  prw (cauchyfy_unfold adm g.weaken (.app .succ (.var .vz))) in h2 with h2a
  prw (cauchyfy_unfold adm h.weaken (.app .succ (.var .vz))) in h2a with h2b
  papplym (le_lt_Q_trans adm
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
      (.app Term.pow2neg_Q (.var .vz))))
  psplit
  · pthm (abs_Q_sub_triangle adm (cV f.weaken (.app .succ (.var .vz)))
      (cV g.weaken (.app .succ (.var .vz))) (cV h.weaken (.app .succ (.var .vz))))
  · papplym (lt_Q_add_both adm
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)) (.app Term.pow2neg_Q (.var .vz)))
    psplit
    · pexact h1b
    · pexact h2b

/-- Transitivity of `=_ℝ` at explicit reals. -/
def eq_R_trans_core (f g h : Term F Γ (realTy ι)) :
    Derivable F EqX al Premises (eq_R f g ∧ᶠ eq_R g h →ᶠ eq_R f h) := by
  pmode
  pintro hyp
  papplym (eqR_hyp_of adm f g h) in hyp with hH0
  papplym (eqR_strict adm f h) in hH0 with hst
  pforall
  pspecialize hst with hs1
  canorm
  prw (cauchyfy_unfold adm f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold adm h.weaken (.app .succ (.var .vz)))
  pexact hs1

end Metatheorems
