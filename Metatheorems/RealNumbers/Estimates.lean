/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Cauchyfy

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── The tightness estimate behind `eq_R_trans` ─────────────────────────────
--
-- `eq_R`'s bound is exactly tight — `2^{-n} = 2·2^{-(n+1)}` — so no route through
-- "|f̂−ĝ| + |ĝ−ĥ| at a common index" closes: every such estimate overshoots by exactly one
-- dyadic step, at *every* choice of index. (REALS_PLAN.md §0.5 records this, and its
-- proposed five-term split does not in fact close either: it collects `2·2^{-(m-1)}` from
-- the two hypotheses where the telescope only returns `2·2^{-m}`.)
--
-- What does work is a *limit* argument made finite:
--
--   1. `cauchy_pair_step`  — one step, strict: `X_q <ℚ 2^{-q} +ℚ X_{q+1}`, where
--      `X_q := |f̂(q) −ℚ ĥ(q)|`. Two strict `cauchyfy` steps at `2^{-(q+1)}` each.
--   2. `eqR_tail`  — iterate it: `∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}`. Induction on `k`.
--   3. `eqR_le`  — squeeze: holding for *every* `k`, that gives `X_{p+1} ≤ℚ 2^{-p}`.
--      `pow2neg_rat_den_le` supplies the index at which the dyadic scale falls below the
--      hypothetical excess. This is where the strict `<` is traded for a non-strict `≤`.
--   4. `eqR_strict`  — spend one *more* step: `X_{n+1} <ℚ 2^{-(n+1)} +ℚ X_{n+2}` with
--      `X_{n+2} ≤ℚ 2^{-(n+1)}` gives `X_{n+1} <ℚ 2^{-n}` — strictly, because step 1 is.
--
-- Steps 3 and 4 together are the finite surrogate for "`|f̂(p) − F| < 2^{-p}` strictly".

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
    Derivable F al Premises
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
  pfrom hX := cauchyState_cauchy f q
  pfrom hZ0 := cauchyState_cauchy h q
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q b b')) e Z e
      (abs_diff_Q_comm b b') (eq_Q_refl_inst e)) in hZ0 with hZ
  phave hXZ : lt_Q (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q X Z) (Term.app2 Term.add_Q e e)
      (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
      (eq_Q_refl_inst (Term.app2 Term.add_Q X Z)) (pow2neg_Q_halve q))
    papplym (lt_Q_add_both X Z e e)
    psplit
    · pexact hX
    · pexact hZ
  phave htri : le_Q (cDiff f h q) (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
  · papplym (le_Q_trans (cDiff f h q)
      (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y))
    psplit
    · papplym (le_Q_trans (cDiff f h q)
        (Term.app2 Term.add_Q X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b)))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
      psplit
      · pthm (abs_Q_sub_triangle a a' b)
      · papplym (le_Q_add_both X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b))
          X (Term.app2 Term.add_Q Y Z))
        psplit
        · pthm (le_Q_refl X)
        · pthm (abs_Q_sub_triangle a' b' b)
    · papplym (le_Q_congr (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
        (eq_Q_refl_inst (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
        (eqQtrans (addQr X (add_Q_comm_inst Y Z))
          (eqQsym (add_Q_assoc_inst X Z Y))))
      pthm (le_Q_refl (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
  papplym (le_lt_Q_trans (cDiff f h q)
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) Y))
  psplit
  · pexact htri
  · papplym (lt_Q_add_inst (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q) Y)
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
               weaken_substVar0, ProofMode.succVar0, closed_subst,
               -- `pm_exE` maps `Formula.weakenBy` over the hypothesis context, so a
               -- hypothesis obtained by an *earlier* `pobtain` carries that wrapper while
               -- the goal carries hand-written `.weaken`s.  Turn the wrapper into a
               -- substitution, let the rules above push it inward, then fold the terms
               -- back to `.weaken` with `Term.subst_shift_eq_weaken`.
               ← Formula.substF_shift_eq_weakenBy, Term.subst_shift_eq_weaken]
             try q_cons_norm))

/-- The base of the telescoping induction: `∀p. |f̂(p+1) −ℚ ĥ(p+1)| <ℚ 2^{-p} +ℚ 2^{-p}`. -/
def eqR_hyp (f h : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz))))

/-- **The telescoping induction.** From `eqR_hyp` and the one-step estimate,
`∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}`.

Each round spends one `cauchyfy` step on each side — together exactly
`2^{-(p+1)} +ℚ 2^{-(p+1)} =ℚ 2^{-p}` — and pushes the residual one index further out. -/
def eqR_tail (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
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
    prw (add_zero_r (.var .vz))
    pexact h1
  · pforall
    pintro ih
    canorm
    pforall
    pinst ih (.app .succ (.var .vz)) with ihp
    canorm
    prw (add_succ_l (.var .vz) (.var (.vs .vz))) in ihp with ihp2
    prw (add_succ (.var .vz) (.var (.vs .vz)))
    papplym (lt_Q_congr
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
      (eq_Q_refl_inst _)
      (eqQtrans
        (eqQsym (add_Q_assoc_inst
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        (addQl (pow2neg_Q_halve (.var .vz))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    papplym (lt_Q_trans_inst
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    psplit
    · pthm (cauchy_pair_step f.weaken.weaken h.weaken.weaken
        (.app .succ (.var .vz)))
    · papplym (lt_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      pexact ihp2

/-- **The Archimedean squeeze.** The telescoping estimate holds for *every* `k`, so the
strict `<ℚ 2^{-p} +ℚ 2^{-(p+k)}` collapses to a non-strict `≤ℚ 2^{-p}`.

`pow2neg_rat_den_le` supplies the index: if the excess `r := X_{p+1} −ℚ 2^{-p}` were positive,
`2^{-(p + den r)} ≤ℚ 2^{-den r} ≤ℚ r` and the estimate at `k := den r` gives `X <ℚ X`. -/
def eqR_le (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (le_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_tail f h) in hh with hT
  pforall
  pfrom hdic := le_Q_or_lt_Q
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
  pcases hdic with hle | hgt
  · pexact hle
  · pexfalso
    papplym (lt_Q_to_zero_sub (.app Term.pow2neg_Q (.var .vz))
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))) in hgt with hpos
    papplym (pow2neg_rat_den_le (Term.app2 Term.sub_Q
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
    · papplym (le_Q_add_l (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (le_Q_trans
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
      · pthm (pow2neg_Q_le_add_r (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      · pexact hd
    phave hXX : lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
                     (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    · papplym (lt_Q_congr
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (eq_Q_refl_inst _)
        (add_Q_sub_cancel
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (lt_le_Q_trans
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
    papplym (lt_Q_irrefl_inst
      (cDiff f.weaken h.weaken (.app .succ (.var .vz))))
    pexact hXX

/-- **The strict estimate.** One more `cauchyfy` step on top of the non-strict one: the step
is strict and costs `2^{-(n+1)}`, the squeeze at `n+1` costs `2^{-(n+1)}`, and they sum to
exactly `2^{-n}`. This is where the tightness of `eq_R` is finally paid for. -/
def eqR_strict (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_le f h) in hh with hle
  pforall
  pinst hle (.app .succ (.var .vz)) with hle1
  canorm
  papplym (lt_Q_congr
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
    (eq_Q_refl_inst _)
    (pow2neg_Q_halve (.var .vz)))
  papplym (lt_le_Q_trans
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz)))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
  psplit
  · pthm (cauchy_pair_step f.weaken h.weaken (.app .succ (.var .vz)))
  · papplym (le_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    pexact hle1

/-- The base of the induction, from the two `=_ℝ` hypotheses: one triangle inequality at
each index. -/
def eqR_hyp_of (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f g ∧ᶠ eq_R g h →ᶠ eqR_hyp f h) := by
  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  pforall
  pspecialize hfg with h1
  pspecialize hgh with h2
  canorm
  prw (cauchyfy_unfold f.weaken (.app .succ (.var .vz))) in h1 with h1a
  prw (cauchyfy_unfold g.weaken (.app .succ (.var .vz))) in h1a with h1b
  prw (cauchyfy_unfold g.weaken (.app .succ (.var .vz))) in h2 with h2a
  prw (cauchyfy_unfold h.weaken (.app .succ (.var .vz))) in h2a with h2b
  papplym (le_lt_Q_trans
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
      (.app Term.pow2neg_Q (.var .vz))))
  psplit
  · pthm (abs_Q_sub_triangle (cV f.weaken (.app .succ (.var .vz)))
      (cV g.weaken (.app .succ (.var .vz))) (cV h.weaken (.app .succ (.var .vz))))
  · papplym (lt_Q_add_both
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)) (.app Term.pow2neg_Q (.var .vz)))
    psplit
    · pexact h1b
    · pexact h2b

/-- Transitivity of `=_ℝ` at explicit reals. -/
def eq_R_trans_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R f g ∧ᶠ eq_R g h →ᶠ eq_R f h) := by
  pmode
  pintro hyp
  papplym (eqR_hyp_of f g h) in hyp with hH0
  papplym (eqR_strict f h) in hH0 with hst
  pforall
  pspecialize hst with hs1
  canorm
  prw (cauchyfy_unfold f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold h.weaken (.app .succ (.var .vz)))
  pexact hs1

/-- `f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0`, at explicit reals.

`add_R` shifts by one, and `cauchyfy_add_R` says that shift is all it does, so the two
hypotheses are read one index in — where each is bounded by `2^{-(n+1)}`, and the two sum to
exactly `2^{-n}`. No telescoping is needed: unlike `eq_R_trans` this one is not tight. -/
private def add_eq_zero_R_gen (f g u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises
      (eq_R f Term.zero_R ∧ᶠ eq_R g Term.zero_R →ᶠ eq_R u Term.zero_R) := by
  pmode
  pintro hyp
  pdestruct hyp with hf hg
  pforall
  pinst hf (.app .succ (.var .vz)) with hf1
  pinst hg (.app .succ (.var .vz)) with hg1
  canorm
  prw (cauchyfy_zero_R (.app .succ (.app .succ (.var .vz)))) in hf1 with hf2
  prw (cauchyfy_zero_R (.app .succ (.app .succ (.var .vz)))) in hg1 with hg2
  prw (cauchyfy_zero_R (.app .succ (.var .vz)))
  prw hu
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
      Term.zero_Q))
    (Term.app2 Term.add_Q
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · papplym (le_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
        (Term.app2 Term.add_Q Term.zero_Q Term.zero_Q)))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
        Term.zero_Q))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (abs_Q_congr (sub_Q_congr
        (eq_Q_refl_inst (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
        (add_Q_zero_inst Term.zero_Q)))
      (eq_Q_refl_inst _))
    pthm (abs_Q_sub_add_split Term.zero_Q Term.zero_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
  · papplym (lt_Q_congr
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (.app Term.pow2neg_Q (.app .succ (.var .vz))))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (.app Term.pow2neg_Q (.var .vz))
      (eq_Q_refl_inst _)
      (pow2neg_Q_halve (.var .vz)))
    papplym (lt_Q_add_both
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    psplit
    · pexact hf2
    · pexact hg2

/-- `f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0`, at explicit reals.

The sum is fed in through `add_eq_zero_R_gen`'s abstract `u` rather than rewritten inside the
goal: `prw` would have to push a substitution through `Term.add_R`, which is the
delta-expansion blow-up CLAUDE.md's build-cost section warns about (measured here: a
heartbeat timeout). As a Lean-level parameter it costs nothing. -/
def add_eq_zero_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f Term.zero_R ∧ᶠ eq_R g Term.zero_R →ᶠ
       eq_R (Term.app2 Term.add_R f g) Term.zero_R) :=
  add_eq_zero_R_gen f g (Term.app2 Term.add_R f g)
    ((add_R_app_weaken f g).symm ▸
      cauchyfy_add_R f.weaken g.weaken (.app .succ (.var .vz)))

-- ── =_ℝ is an equivalence relation ─────────────────────────────────────────

/-- ⊢ ∀f : ℝ. f =_ℝ f

`eq_R` is not an equation, so this is not `refl`: it says `|f̂(n+1) −ℚ f̂(n+1)|ℚ <ℚ 2^{-n}`,
which is `0 <ℚ 2^{-n}` transported along `abs_Q_sub_self`. -/
def eq_R_refl :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (eq_R (.var .vz) (.var .vz))) :=
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen
    (Derivable.mp (zero_lt_pow2neg_Q (.var .vz))
      (lt_Q_congr Term.zero_Q e (.app Term.abs_Q (Term.app2 Term.sub_Q A A)) e
        (eqQsym (abs_Q_sub_self A)) (eq_Q_refl_inst e))))

/-- ⊢ ∀f,g : ℝ. f =_ℝ g → g =_ℝ f -/
def eq_R_sym :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) (.var .vz) →ᶠ
         eq_R (.var .vz) (.var (.vs .vz))))) :=
  let A : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var (.vs .vz)))) (.app .succ (.var .vz))
  let B : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen (forall_map
    (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A B)) e
        (.app Term.abs_Q (Term.app2 Term.sub_Q B A)) e
      (abs_diff_Q_comm A B) (eq_Q_refl_inst e))))

/-- Symmetry of `=_ℝ` at explicit reals — the `_core` companion of `eq_R_sym`, in the same
style as `eq_R_trans_core` / `add_eq_zero_R_core`.

Instantiating the `∀`-quantified `eq_R_sym` at two terms means pushing two `subst0`s through
`eq_R`; taking the terms as parameters skips that entirely, and the proof is `eq_R_sym`'s own
body with `f`/`g` in place of the two bound variables. Used by
`MetricSpace.admissibleEqX.eqx_sym`. -/
def eq_R_sym_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R f g →ᶠ eq_R g f) :=
  let A : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy f.weaken) (.app .succ (.var .vz))
  let B : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy g.weaken) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  forall_map
    (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A B)) e
        (.app Term.abs_Q (Term.app2 Term.sub_Q B A)) e
      (abs_diff_Q_comm A B) (eq_Q_refl_inst e))

/-- ⊢ ∀f,g,h : ℝ. f =_ℝ g ∧ g =_ℝ h → f =_ℝ h -/
def eq_R_trans :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ eq_R (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  univ_gen (univ_gen (univ_gen
    (eq_R_trans_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

-- ── ℚ helpers: `|·|_ℚ` against a two-sided bound ────────────────────────────
--
-- Everything in this block is a ℚ fact; it lives here rather than in
-- `RationalNumbers.lean` only because that file is another workstream's. The two
-- load-bearing ones are `le_Q_self_abs` (`z ≤_ℚ |z|_ℚ`, which is how a *directed*
-- estimate is recovered from a `cauchyfy` bound) and `abs_Q_lt_of_two_sided`
-- (`z <_ℚ c` and `−z <_ℚ c` give `|z| <_ℚ c`, which is how an `eq_R` goal is discharged
-- from a pair of one-sided bounds). Neither existed; REALS_PLAN §0.8 item 1 lists the
-- family as missing.
--
-- The route is `le_Q_of_cross` throughout: it turns a `≤_ℚ` goal into ℕ arithmetic on
-- signed cross products, with no `sub_Q` anywhere.

/-- `0_ℚ −_ℚ x =_ℚ −_ℚ x`. -/
def sub_Q_zero_l (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q Term.zero_Q x) (.app Term.neg_Q x)) :=
  eqQtrans (sub_Q_eq_add_neg Term.zero_Q x)
    (eqQtrans (add_Q_comm_inst Term.zero_Q (.app Term.neg_Q x))
      (add_Q_zero_inst (.app Term.neg_Q x)))

/-- **`z ≤_ℚ |z|_ℚ`**, and no sign case is needed: the cross criterion asks
`posN z · D ≤ (posN z + negN z) · D + negN z · D`, which holds outright. -/
def le_Q_self_abs (z : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q z (.app Term.abs_Q z)) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  let P : Term F Γ Ty.nat := Term.app2 Term.mul (posN z) D
  let N : Term F Γ Ty.nat := Term.app2 Term.mul (negN z) D
  pmode
  papplym (le_Q_of_cross z (.app Term.abs_Q z))
  prw (negN_abs_Q z)
  prw (posN_abs_Q z)
  prw (rat_den_abs_Q z)
  prw (mul_zero_l D)
  prw (add_zero_l P)
  papplym (monus_le_of_eq_add P
    (Term.app2 Term.add (Term.app2 Term.mul (.app Term.rat_num z) D) N)
    (Term.app2 Term.add N N))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prw (add_mul (posN z) (negN z) D)
  pthm (qtrans (add_assoc P N N) (add_comm P (Term.app2 Term.add N N)))

/-- `|z|_ℚ ≤_ℚ z` when `z`'s negative part vanishes, i.e. when `0 ≤_ℚ z`. -/
def abs_Q_le_self_of_negN_zero (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (negN z) .zero →ᶠ le_Q (.app Term.abs_Q z) z) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  pmode
  pintro h
  papplym (le_Q_of_cross (.app Term.abs_Q z) z)
  prw (rat_den_abs_Q z)
  prw (posN_abs_Q z)
  prw (negN_abs_Q z)
  prw (mul_zero_l D)
  prw (add_zero_r (Term.app2 Term.mul (posN z) D))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prwby h
  prw (add_zero_r (posN z))
  prw (mul_zero_l D)
  prw (add_zero_l (Term.app2 Term.mul (posN z) D))
  pthm (monus_self (Term.app2 Term.mul (posN z) D))

/-- `|z|_ℚ ≤_ℚ −_ℚ z` when `z`'s positive part vanishes, i.e. when `z ≤_ℚ 0`. -/
def abs_Q_le_neg_of_posN_zero (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (posN z) .zero →ᶠ le_Q (.app Term.abs_Q z) (.app Term.neg_Q z)) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  pmode
  pintro h
  papplym (le_Q_of_cross (.app Term.abs_Q z) (.app Term.neg_Q z))
  prw (rat_den_abs_Q z)
  prw (rat_den_neg_Q z)
  prw (posN_abs_Q z)
  prw (negN_abs_Q z)
  prw (negN_neg_Q z)
  prw (posN_neg_Q z)
  prw (mul_zero_l D)
  prw (add_zero_r (Term.app2 Term.mul (negN z) D))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prwby h
  prw (add_zero_l (negN z))
  prw (mul_zero_l D)
  prw (add_zero_l (Term.app2 Term.mul (negN z) D))
  pthm (monus_self (Term.app2 Term.mul (negN z) D))

/-- `|z|_ℚ` is bounded by `z` or by `−_ℚ z` — the dichotomy `|z| = max(z, −z)` in the only
form the encoding supports. The case split is on `0 ≤_ℚ z` versus `z <_ℚ 0`, not on the sign
bit, because `le_Q_zero_parts` / `lt_Q_zero_parts` already convert those into the vanishing of
one signed part, and `prw` cannot see inside `posN`/`negN`. -/
def abs_Q_le_cases (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q z) z ∨ᶠ le_Q (.app Term.abs_Q z) (.app Term.neg_Q z)) := by
  pmode
  pfrom hc := le_Q_or_lt_Q Term.zero_Q z
  pcases hc with hnn | hneg
  · pleft
    papplym (le_Q_zero_parts z) in hnn with hz
    papplym (abs_Q_le_self_of_negN_zero z) in hz with hle
    pexact hle
  · pright
    papplym (lt_Q_to_zero_sub z Term.zero_Q) in hneg with h1
    papplym (lt_Q_zero_congr (Term.app2 Term.sub_Q Term.zero_Q z) (.app Term.neg_Q z)
      (sub_Q_zero_l z)) in h1 with h2
    papplym (lt_Q_zero_parts (.app Term.neg_Q z)) in h2 with h3
    pdestruct h3 with h4 _h5
    prw (negN_neg_Q z) in h4 with h6
    papplym (abs_Q_le_neg_of_posN_zero z) in h6 with hle
    pexact hle

/-- **The two-sided bound**: `z <_ℚ c` and `−_ℚ z <_ℚ c` give `|z|_ℚ <_ℚ c`. -/
def abs_Q_lt_of_two_sided (z c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q z c ∧ᶠ lt_Q (.app Term.neg_Q z) c →ᶠ lt_Q (.app Term.abs_Q z) c) := by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  pfrom hc := abs_Q_le_cases z
  pcases hc with hA | hB
  · papplym (le_lt_Q_trans (.app Term.abs_Q z) z c)
    psplit
    · pexact hA
    · pexact h1
  · papplym (le_lt_Q_trans (.app Term.abs_Q z) (.app Term.neg_Q z) c)
    psplit
    · pexact hB
    · pexact h2

/-- `¬(a ≤_ℚ b)` gives `b <_ℚ a`. The `≤_ℚ`/`<_ℚ` dichotomy is decidable in the encoding, so
this is `le_Q_or_lt_Q` and needs no Markov step. -/
def lt_Q_of_not_le_Q (a b : Term F Γ Ty.nat) :
    Derivable F al Premises (¬ᶠ(le_Q a b) →ᶠ lt_Q b a) := by
  pmode
  pintro h
  pfrom hc := le_Q_or_lt_Q a b
  pcases hc with hle | hlt
  · pexfalso
    papply h
    pexact hle
  · pexact hlt

/-- Cancelling a common right summand in a `<_ℚ`. `<_ℚ` sees its arguments only through the
`eq_Q` class of their difference, so this is `sub_Q_add_cancel` read backwards. -/
def lt_Q_add_cancel (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) →ᶠ lt_Q a b) :=
  lt_Q_of_eq_Q_diff (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) a b
    (sub_Q_add_cancel a b c)

/-- …and on the left. -/
def lt_Q_add_cancel_l (c a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.add_Q c a) (Term.app2 Term.add_Q c b) →ᶠ lt_Q a b) :=
  Derivable.syllogism
    (lt_Q_congr (Term.app2 Term.add_Q c a) (Term.app2 Term.add_Q c b)
      (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c)
      (add_Q_comm_inst c a) (add_Q_comm_inst c b))
    (lt_Q_add_cancel a b c)

-- ── The `cauchyfy` estimates, phrased on `cauchyfy` itself ──────────────────

/-- `cauchyState_cauchy` with `cauchyfy_unfold` applied on both sides:
`|f̂(n) −ℚ f̂(n+1)|ℚ <ℚ 2^{-(n+1)}`. -/
def cauchyfy_cauchy (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f n)
              (Term.app2 Term.cauchyfy f (.app .succ n))))
            (.app Term.pow2neg_Q (.app .succ n))) := by
  pmode
  prw (cauchyfy_unfold f n)
  prw (cauchyfy_unfold f (.app .succ n))
  pthm (cauchyState_cauchy f n)

/-- **Two `cauchyfy` steps**: `|f̂(m) −ℚ f̂(m+2)|ℚ <ℚ 2^{-m}`.

The two steps cost `2^{-(m+1)}` and `2^{-(m+2)}`; relaxing the second to `2^{-(m+1)}` still
leaves the sum `2^{-m}`, so no telescoping induction is needed — this is a *fixed* two-step
estimate, unlike the unbounded one `eq_R_trans` needs. -/
def cauchyfy_two_step (f : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f m)
              (Term.app2 Term.cauchyfy f (.app .succ (.app .succ m)))))
            (.app Term.pow2neg_Q m)) := by
  let a  : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f m
  let a1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ m)
  let a2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ (.app .succ m))
  let X : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a1)
  let Y : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a1 a2)
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ m)
  pmode
  pfrom hX := cauchyfy_cauchy f m
  pfrom hY0 := cauchyfy_cauchy f (.app .succ m)
  phave hY : lt_Q Y e
  · papplym (lt_le_Q_trans Y (.app Term.pow2neg_Q (.app .succ (.app .succ m))) e)
    psplit
    · pexact hY0
    · pthm (pow2neg_Q_le_succ (.app .succ m))
  papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q a a2))
    (Term.app2 Term.add_Q X Y) (.app Term.pow2neg_Q m))
  psplit
  · pthm (abs_Q_sub_triangle a a1 a2)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q X Y) (Term.app2 Term.add_Q e e)
      (Term.app2 Term.add_Q X Y) (.app Term.pow2neg_Q m)
      (eq_Q_refl_inst (Term.app2 Term.add_Q X Y)) (pow2neg_Q_halve m))
    papplym (lt_Q_add_both X Y e e)
    psplit
    · pexact hX
    · pexact hY

-- ── The symbolic-shift telescope ───────────────────────────────────────────
--
-- `cauchyfy_two_step` is a *fixed* two-step estimate.  What `mul_one_R` (and, with
-- `mul_R_check`, `distrib_R` / `mul_assoc_R`) needs is the same estimate over *symbolically
-- many* steps: `mul_R`'s index shift `b = f(0) +ℕ g(0) +ℕ 2` depends on the arguments, so
-- comparing `(f ·ℝ 1ℝ)^(n+1) = f̂(n+1+b)` with `f̂(n+1)` is a telescope of `b` steps.
--
-- The statement has to **carry the remaining slack**, or the induction step has none:
--
--     ∀k ∀p.  |f̂(p) −ℚ f̂(p+k)|  +ℚ  2^{-(p+k)}  ≤ℚ  2^{-p}
--
-- Base `k = 0`: `0 +ℚ 2^{-p} ≤ℚ 2^{-p}`.  Step: split off `|f̂(p+k) −ℚ f̂(p+k+1)| <ℚ
-- `2^{-(p+k+1)}` by `cauchyfy_cauchy`, and pay for it with the carried `2^{-(p+k)}` — which is
-- exactly `2^{-(p+k+1)} +ℚ 2^{-(p+k+1)}` (`pow2neg_Q_halve`), so one half funds the new step
-- and the other becomes the new carried slack.  Nothing is spent, which is why the conclusion
-- stays `≤ℚ 2^{-p}` at every `k`.
--
-- The `+ℚ`-form is used rather than REALS_PLAN §0.5 item 3's `≤ℚ 2^{-p} −ℚ 2^{-(p+k)}`: the
-- two say the same thing, but the difference form needs `sub_Q` cancellation lemmas at every
-- step, while the `+ℚ` form is pure `le_Q_add_both` / `add_Q_assoc_inst` bookkeeping.

/-- `e =ℚ |a −ℚ a| +ℚ e` — the telescope's base case, as pure ℚ algebra. -/
private def tele_base_eq (a e : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q e (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q a a)) e)) :=
  eqQsym (eqQtrans (addQl (abs_Q_sub_self a) e)
    (eqQtrans (add_Q_comm_inst Term.zero_Q e) (add_Q_zero_inst e)))

/-- `(D +ℚ 2^{-(m+1)}) +ℚ 2^{-(m+1)} =ℚ D +ℚ 2^{-m}` — the telescope's carried slack, which
funds the new `cauchyfy` step *and* the next round's slack. -/
private def tele_carry_eq (d m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.add_Q d (.app Term.pow2neg_Q (.app .succ m)))
          (.app Term.pow2neg_Q (.app .succ m)))
        (Term.app2 Term.add_Q d (.app Term.pow2neg_Q m))) :=
  eqQtrans
    (add_Q_assoc_inst d (.app Term.pow2neg_Q (.app .succ m))
      (.app Term.pow2neg_Q (.app .succ m)))
    (addQr d (pow2neg_Q_halve m))

/-- **The symbolic-shift telescope**: `∀k ∀p. |f̂(p) −ℚ f̂(p+k)| +ℚ 2^{-(p+k)} ≤ℚ 2^{-p}`.

Unlike `eqR_tail` this mentions a *single* sequence and states the estimate on
`f̂(p) −ℚ f̂(p+k)` itself, which is what a symbolic index shift needs. -/
def cauchyfy_tele (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat (Formula.all Ty.nat
        (le_Q
          (Term.app2 Term.add_Q
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
            (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
          (.app Term.pow2neg_Q (.var .vz))))) := by
  pmode
  pinduction
  · -- base: `p +ℕ 0` is `p`, and `|f̂(p) −ℚ f̂(p)| =ℚ 0ℚ`
    canorm
    pforall
    prw (add_zero_r (.var .vz))
    papplym (le_Q_congr
      (.app Term.pow2neg_Q (.var .vz)) (.app Term.pow2neg_Q (.var .vz))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.var .vz))
          (Term.app2 Term.cauchyfy f.weaken (.var .vz))))
        (.app Term.pow2neg_Q (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz))
      (tele_base_eq (Term.app2 Term.cauchyfy f.weaken (.var .vz))
        (.app Term.pow2neg_Q (.var .vz)))
      (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
    pthm (le_Q_refl (.app Term.pow2neg_Q (.var .vz)))
  · pforall
    pintro ih
    canorm
    pforall
    pinst ih (.var .vz) with ihp
    canorm
    prw (add_succ (.var .vz) (.var (.vs .vz)))
    papplym (le_Q_trans
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
          (Term.app2 Term.cauchyfy f.weaken.weaken
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
          (Term.app2 Term.cauchyfy f.weaken.weaken
            (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
      (.app Term.pow2neg_Q (.var .vz)))
    psplit
    · -- `|f̂(p) − f̂(m+1)| +ℚ 2^{-(m+1)} ≤ℚ |f̂(p) − f̂(m)| +ℚ 2^{-m}`, `m := p +ℕ k`
      papplym (le_Q_congr
        (Term.app2 Term.add_Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        (Term.app2 Term.add_Q
          (Term.app2 Term.add_Q
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
            (.app Term.pow2neg_Q
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        (Term.app2 Term.add_Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        (Term.app2 Term.add_Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
        (eq_Q_refl_inst _)
        (tele_carry_eq
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
      papplym (le_Q_add_both
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
          (Term.app2 Term.cauchyfy f.weaken.weaken
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))
        (Term.app2 Term.add_Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
      psplit
      · -- the triangle inequality, with the new step bounded by `cauchyfy_cauchy`
        papplym (le_Q_trans
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
          (Term.app2 Term.add_Q
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
          (Term.app2 Term.add_Q
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
            (.app Term.pow2neg_Q
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        psplit
        · pthm (abs_Q_sub_triangle
            (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
            (Term.app2 Term.cauchyfy f.weaken.weaken
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
        · papplym (le_Q_add_l
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken (.var .vz))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
            (.app Term.pow2neg_Q
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          papplym (lt_Q_imp_le_Q
            (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
              (Term.app2 Term.cauchyfy f.weaken.weaken
                (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
            (.app Term.pow2neg_Q
              (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
          pthm (cauchyfy_cauchy f.weaken.weaken
            (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
      · pthm (le_Q_refl (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
    · pexact ihp

/-- `cauchyfy_tele` at explicit `p` and `k`. -/
def cauchyfy_tele_at (f : Term F Γ (realTy ι)) (p k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q
        (Term.app2 Term.add_Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f p)
            (Term.app2 Term.cauchyfy f (Term.app2 Term.add p k))))
          (.app Term.pow2neg_Q (Term.app2 Term.add p k)))
        (.app Term.pow2neg_Q p)) := by
  have h := Derivable.mp (Derivable.mp
    (cauchyfy_tele (al := al) (Premises := Premises) f) (.forall_ax k)) (.forall_ax p)
  simpa only [lt_Q, le_Q, eq_Q, Formula.subst0, Formula.substF, Term.subst,
    Term.subst0_map_vz, Term.subst0_map_vs, Term.Subst.ext_vz, Term.Subst.ext_vs,
    Term.weaken_var, Term.app2, Term.weaken_subst0, subst_subst0_map_weaken,
    Term.weaken_subst_ext, cauchyfy_closed_subst, closed_subst] using h

/-- **The telescope, in the form the multiplicative axioms use**:
`|f̂(p) −ℚ f̂(p +ℕ k)| ≤ℚ 2^{-p}`, for a *symbolic* shift `k`.

The carried slack `2^{-(p+k)}` is non-negative, so it can simply be dropped. -/
def cauchyfy_shift_le (f : Term F Γ (realTy ι)) (p k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f p)
              (Term.app2 Term.cauchyfy f (Term.app2 Term.add p k))))
            (.app Term.pow2neg_Q p)) := by
  let D : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (Term.app2 Term.cauchyfy f p)
    (Term.app2 Term.cauchyfy f (Term.app2 Term.add p k)))
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (Term.app2 Term.add p k)
  pmode
  papplym (le_Q_trans D (Term.app2 Term.add_Q D e) (.app Term.pow2neg_Q p))
  psplit
  · papplym (le_Q_congr (Term.app2 Term.add_Q D Term.zero_Q) (Term.app2 Term.add_Q D e)
      D (Term.app2 Term.add_Q D e) (add_Q_zero_inst D) (eq_Q_refl_inst _))
    papplym (le_Q_add_l D Term.zero_Q e)
    papplym (lt_Q_imp_le_Q Term.zero_Q e)
    pthm (zero_lt_pow2neg_Q (Term.app2 Term.add p k))
  · pthm (cauchyfy_tele_at f p k)

end OrderedFieldAxioms

end Metatheorems
