/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Order

namespace Metatheorems

/-!
# The non-strict order `≤_ℝ`

Before this file the ℝ layer had a complete **strict**-order package (`Order.lean`:
`lt_add_R`, `lt_trans_R`, `lt_mul_pos_R`, `lt_irrefl_R`, `zero_lt_one_R`, `archimedean_R`)
and, for `≤_ℝ`, only *conversions* — `le_R_of_le_R_pu`, `le_R_pu_of_le_R`, `le_R_all`,
`le_R_of_all`, `le_R_of_bound` (`Field.lean`), plus the `clamp01` bounds and `approx_le_R`.
There was no reflexivity, no transitivity and no additive monotonicity.

That was a real blocker rather than a gap in taste: `Derivable.dist_tri` and every space
axiom in the tower (`WHyperbolic`, `CAT0`, `Normed`) are stated with `≤_ℝ` through
`le_R_pu`, so **two triangle inequalities could not be chained**. `BaseEquality.dist_tri_chain`
is the first consumer.

## What `≤_ℝ` is, and which estimates are tight

`le_R f g` is `¬(g <_ℝ f)`, and `le_R_all`/`le_R_of_all` pin that down completely:

    f ≤_ℝ g   ⟺   ∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}.

Everything here is stated against that characterisation, and — following the layer's rule,
*triage by tightness, not by shape* — the results split cleanly in two:

* **Slack-free, no engine.** `le_R_refl_core`, `le_R_of_eq_R_core`, `le_R_antisymm_core`,
  `lt_imp_le_R_core` and both additive-monotonicity lemmas close directly. Monotonicity is
  the interesting case: `add_R`'s `+1` index shift means the goal at index `n` is a statement
  about `f̂(n+2)`, where the hypothesis is available with bound `2^{-(n+1)}` — *half* the
  budget, so the common summand cancels exactly (`sub_Q_add_cancel`) and a single
  `pow2neg_Q_le_succ` finishes. No telescope, no squeeze.
* **Tight — the engine is unavoidable.** Transitivity is not: at a common index the two
  hypotheses give `2^{-n} +ℚ 2^{-n} = 2^{-(n-1)}`, and moving to a farther index costs
  `2·2^{-(n+1)} = 2^{-n}` by `cauchyfy_shift_le`, which is the *whole* budget. Every finite
  choice overshoots, exactly as for `eq_R_trans` (see `Estimates.lean`'s header).

So `le_R_trans_core` is proved by the **one-sided mirror of the `eqR_tail`/`eqR_le`/
`eqR_strict` telescope**: `leR_pair_step`, `leR_tail`, `leR_le`, `leR_strict`, on the signed
difference `sDiff` where the `eq_R` engine uses the absolute value `cDiff`. The mirror is
exact — the only new ingredient is that a signed one-step estimate must bound the two
`cauchyfy` drifts *directionally*, which `le_Q_self_abs` supplies, exactly as `lt_shift1`
already does for `<_ℝ`.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

/-- `f̂(n) −ℚ ĥ(n)`, the **signed** difference — the `≤_ℝ` counterpart of `Estimates.cDiff`,
which is its absolute value. `le_R f g` is `∀n. sDiff f g (n+1) <ℚ 2^{-n}`. -/
abbrev sDiff (f h : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app2 Term.sub_Q (Term.app2 Term.cauchyfy f n) (Term.app2 Term.cauchyfy h n)

/-- `canorm` with `sDiff` unfolded first: `canorm` pushes substitutions through `Term.app2`
spines, and a named wrapper hides its contents (CLAUDE.md note 12). -/
macro "lnorm" : tactic =>
  `(tactic| (try simp only [sDiff]
             canorm))

-- ── The telescope, one-sided ────────────────────────────────────────────────

/-- **The one-step estimate, signed**: `D(q) <ℚ 2^{-q} +ℚ D(q+1)`, where
`D(q) := f̂(q) −ℚ ĥ(q)`.

The signed analogue of `cauchy_pair_step`, and structurally identical to `lt_shift1`'s core:
`D(q) =ℚ D(q+1) +ℚ ((ĥ(q+1) −ℚ ĥ(q)) +ℚ (f̂(q) −ℚ f̂(q+1)))`, and each of the two drift terms is
below `2^{-(q+1)}` — *directionally*, via `le_Q_self_abs` on top of `cauchyfy_cauchy` — so
their sum is strictly below `2^{-q}`. -/
def leR_pair_step (f h : Term F Γ (realTy ι)) (q : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (sDiff f h q)
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) (sDiff f h (.app .succ q)))) := by
  let u1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f q
  let u2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ q)
  let v1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy h q
  let v2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy h (.app .succ q)
  let D1 : Term F Γ Ty.nat := Term.app2 Term.sub_Q u1 v1
  let D2 : Term F Γ Ty.nat := Term.app2 Term.sub_Q u2 v2
  let aa : Term F Γ Ty.nat := Term.app2 Term.sub_Q u1 u2
  let nb : Term F Γ Ty.nat := Term.app2 Term.sub_Q v2 v1
  let P  : Term F Γ Ty.nat := .app Term.pow2neg_Q q
  let E  : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ q)
  have hid : Derivable F al Premises
      (eq_Q D1 (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))) :=
    eqQtrans (sub_Q_trans_split v1 u2 u1)
      (eqQtrans (addQl (sub_Q_trans_split v1 v2 u2) aa)
        (eqQtrans (addQl (add_Q_comm_inst nb D2) aa)
          (add_Q_assoc_inst D2 nb aa)))
  pmode
  phave ha : lt_Q aa E
  · papplym (le_lt_Q_trans aa (.app Term.abs_Q aa) E)
    psplit
    · pthm (le_Q_self_abs aa)
    · pthm (cauchyfy_cauchy f q)
  phave hnb : lt_Q nb E
  · papplym (le_lt_Q_trans nb (.app Term.abs_Q nb) E)
    psplit
    · pthm (le_Q_self_abs nb)
    · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q v1 v2)) E
        (.app Term.abs_Q nb) E (abs_diff_Q_comm v1 v2) (eq_Q_refl_inst E))
      pthm (cauchyfy_cauchy h q)
  phave hsum : lt_Q (Term.app2 Term.add_Q nb aa) P
  · papplym (lt_Q_congr (Term.app2 Term.add_Q nb aa) (Term.app2 Term.add_Q E E)
      (Term.app2 Term.add_Q nb aa) P
      (eq_Q_refl_inst (Term.app2 Term.add_Q nb aa)) (pow2neg_Q_halve q))
    papplym (lt_Q_add_both nb aa E E)
    psplit
    · pexact hnb
    · pexact ha
  papplym (lt_Q_congr (Term.app2 Term.add_Q D2 (Term.app2 Term.add_Q nb aa))
    (Term.app2 Term.add_Q D2 P) D1 (Term.app2 Term.add_Q P D2)
    (eqQsym hid) (add_Q_comm_inst D2 P))
  papplym (lt_Q_add_l D2 (Term.app2 Term.add_Q nb aa) P)
  pexact hsum

/-- The base of the one-sided telescope: `∀p. D(p+1) <ℚ 2^{-p} +ℚ 2^{-p}`. -/
def leR_hyp (f h : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (lt_Q (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz))))

/-- **The telescoping induction, one-sided.** `∀k ∀p. D(p+1) <ℚ 2^{-p} +ℚ 2^{-(p+k)}`.

The mirror of `eqR_tail`: each round spends one `leR_pair_step` — exactly
`2^{-(p+1)} +ℚ 2^{-(p+1)} =ℚ 2^{-p}` — and pushes the residual one index further out. -/
def leR_tail (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (leR_hyp f h →ᶠ
       Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
            (.app Term.pow2neg_Q
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))) := by
  pmode
  pintro hh
  pinduction
  · lnorm
    pforall
    pspecialize hh with h1
    lnorm
    prw (add_zero_r (.var .vz))
    pexact h1
  · pforall
    pintro ih
    lnorm
    pforall
    pinst ih (.app .succ (.var .vz)) with ihp
    lnorm
    prw (add_succ_l (.var .vz) (.var (.vs .vz))) in ihp with ihp2
    prw (add_succ (.var .vz) (.var (.vs .vz)))
    papplym (lt_Q_congr
      (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
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
      (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    psplit
    · pthm (leR_pair_step f.weaken.weaken h.weaken.weaken
        (.app .succ (.var .vz)))
    · papplym (lt_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (sDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      pexact ihp2

/-- **The Archimedean squeeze, one-sided.** The telescoping estimate holds for every `k`, so
the strict `<ℚ 2^{-p} +ℚ 2^{-(p+k)}` collapses to `≤ℚ 2^{-p}`. Mirror of `eqR_le`. -/
def leR_le (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (leR_hyp f h →ᶠ
       Formula.all Ty.nat
        (le_Q (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (leR_tail f h) in hh with hT
  pforall
  pfrom hdic := le_Q_or_lt_Q
    (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
  pcases hdic with hle | hgt
  · pexact hle
  · pexfalso
    papplym (lt_Q_to_zero_sub (.app Term.pow2neg_Q (.var .vz))
      (sDiff f.weaken h.weaken (.app .succ (.var .vz)))) in hgt with hpos
    papplym (pow2neg_rat_den_le (Term.app2 Term.sub_Q
      (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) in hpos with hd
    pinst hT (.app Term.rat_den (Term.app2 Term.sub_Q
      (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) with hT1
    lnorm
    pinst hT1 (.var .vz) with hT2
    lnorm
    phave hchain : le_Q
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
    · papplym (le_Q_add_l (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (Term.app2 Term.sub_Q
          (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (le_Q_trans
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (.app Term.pow2neg_Q (.app Term.rat_den (Term.app2 Term.sub_Q
          (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz)))))
        (Term.app2 Term.sub_Q
          (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      psplit
      · pthm (pow2neg_Q_le_add_r (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      · pexact hd
    phave hXX : lt_Q (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
                     (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
    · papplym (lt_Q_congr
        (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
        (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (eq_Q_refl_inst _)
        (add_Q_sub_cancel
          (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (lt_le_Q_trans
        (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      psplit
      · pexact hT2
      · pexact hchain
    papplym (lt_Q_irrefl_inst
      (sDiff f.weaken h.weaken (.app .succ (.var .vz))))
    pexact hXX

/-- **The strict estimate, one-sided.** One more `leR_pair_step` on top of the non-strict
squeeze: the step is strict and costs `2^{-(n+1)}`, the squeeze at `n+1` costs `2^{-(n+1)}`,
and they sum to exactly `2^{-n}`. Mirror of `eqR_strict`. -/
def leR_strict (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (leR_hyp f h →ᶠ
       Formula.all Ty.nat
        (lt_Q (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (leR_le f h) in hh with hle
  pforall
  pinst hle (.app .succ (.var .vz)) with hle1
  lnorm
  papplym (lt_Q_congr
    (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
    (eq_Q_refl_inst _)
    (pow2neg_Q_halve (.var .vz)))
  papplym (lt_le_Q_trans
    (sDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (sDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz)))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
  psplit
  · pthm (leR_pair_step f.weaken h.weaken (.app .succ (.var .vz)))
  · papplym (le_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (sDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    pexact hle1

-- ── The package ─────────────────────────────────────────────────────────────

/-- **Reflexivity**: `⊢ f ≤_ℝ f`. `f̂(n+1) −ℚ f̂(n+1) =ℚ 0 <ℚ 2^{-n}` — slack-free but
trivially so, since the difference is literally zero. -/
def le_R_refl_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f f) :=
  le_R_of_bound f f (by
    pmode
    papplym (lt_Q_congr Term.zero_Q (.app Term.pow2neg_Q (.var .vz))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.var .vz))
      (eqQsym (sub_Q_self (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
      (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
    pthm (zero_lt_pow2neg_Q (.var .vz)))

/-- ⊢ ∀f : ℝ. f ≤_ℝ f -/
def le_R_refl :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (le_R (.var .vz) (.var .vz))) :=
  univ_gen (le_R_refl_core (.var .vz))

/-- **`=_ℝ` implies `≤_ℝ`**: a two-sided bound is in particular a one-sided one.
`le_Q_self_abs` is the whole content; no estimate moves. -/
def le_R_of_eq_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R f g →ᶠ le_R f g) := by
  pmode
  pintro h
  papplym (le_R_of_all f g)
  pforall
  pspecialize h with h1
  lnorm
  papplym (le_lt_Q_trans
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pthm (le_Q_self_abs (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
  · pexact h1

/-- **Irreflexivity of `<_ℝ` at an explicit real** — `lt_irrefl_R` with the `∀` peeled, which
is what `lt_imp_le_R_core` needs and what `Order.lean` does not provide. Same proof. -/
def lt_irrefl_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (Formula.neg (lt_R f f)) :=
  let A : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  let step : Derivable F al Premises
      (le_Q e (Term.app2 Term.sub_Q A A) →ᶠ ⊥ᶠ) :=
    .syllogism
      (le_Q_congr e (Term.app2 Term.sub_Q A A) e Term.zero_Q
        (eq_Q_refl_inst e) (sub_Q_self A))
      (.syllogism (pair_h (weaken_intro_h (zero_lt_pow2neg_Q (.var .vz))) I_comb)
        (lt_Q_le_Q_absurd Term.zero_Q e))
  .exist_rule step

/-- **`<_ℝ` implies `≤_ℝ`.** Purely logical, given the strict package: `le_R f g` is
`¬(g <_ℝ f)`, so a second strict inequality the other way would give `f <_ℝ f` by
`lt_trans_R_core`, which `lt_irrefl_R_core` refutes. No estimate is touched. -/
def lt_imp_le_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (lt_R f g →ᶠ le_R f g) := by
  pmode
  pintro hfg
  pintro hgf
  papplym (lt_irrefl_R_core f)
  papplym (lt_trans_R_core f g f)
  psplit
  · pexact hfg
  · pexact hgf

/-- **Transitivity of `≤_ℝ`** — the one genuinely tight statement here, and the reason the
one-sided telescope above exists. See this file's header for why no direct estimate closes. -/
def le_R_trans_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f g ∧ᶠ le_R g h →ᶠ le_R f h) := by
  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  papplym (le_R_all f g) in hfg with hb1
  papplym (le_R_all g h) in hgh with hb2
  -- the base of the telescope: one split difference at each index
  phave hH0 : leR_hyp f h
  · pforall
    pspecialize hb1 with h1
    pspecialize hb2 with h2
    lnorm
    papplym (lt_Q_congr
      (Term.app2 Term.add_Q
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy h.weaken (.app .succ (.var .vz))))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz)))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.var .vz))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz)))
      (eqQsym (sub_Q_trans_split
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
      (eq_Q_refl_inst _))
    papplym (lt_Q_add_both
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.var .vz))))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.var .vz)) (.app Term.pow2neg_Q (.var .vz)))
    psplit
    · pexact h2
    · pexact h1
  papplym (leR_strict f h) in hH0 with hst
  papplym (le_R_of_all f h)
  pforall
  pspecialize hst with hs1
  lnorm
  pexact hs1

/-- ⊢ ∀f,g,h : ℝ. f ≤_ℝ g ∧ g ≤_ℝ h → f ≤_ℝ h -/
def le_R_trans :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        ((le_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ le_R (.var (.vs .vz)) (.var .vz))
          →ᶠ le_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  univ_gen (univ_gen (univ_gen
    (le_R_trans_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- **Antisymmetry**: two opposite one-sided bounds at the same index are a two-sided bound,
which is exactly `eq_R`. `abs_Q_lt_of_two_sided` does it in one step — no estimate moves, so
this is *not* in the tight regime despite `eq_R` being the tight formula. -/
def le_R_antisymm_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f g ∧ᶠ le_R g f →ᶠ eq_R f g) := by
  pmode
  pintro hyp
  pdestruct hyp with hfg hgf
  papplym (le_R_all f g) in hfg with hb1
  papplym (le_R_all g f) in hgf with hb2
  pforall
  pspecialize hb1 with h1
  pspecialize hb2 with h2
  lnorm
  papplym (abs_Q_lt_of_two_sided
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pexact h1
  · papplym (lt_Q_congr
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.var .vz))
      (.app Term.neg_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
      (.app Term.pow2neg_Q (.var .vz))
      (eqQsym (neg_Q_sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
      (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
    pexact h2

/-- **`≤_ℝ` respects `=_ℝ` on both sides.** Free from transitivity plus `le_R_of_eq_R_core`;
what makes the chained triangle inequality statable in whichever associativity the caller
wants. -/
def le_R_congr (f g f' g' : Term F Γ (realTy ι))
    (hf : Derivable F al Premises (eq_R f' f))
    (hg : Derivable F al Premises (eq_R g g')) :
    Derivable F al Premises (le_R f g →ᶠ le_R f' g') := by
  pmode
  pintro h
  papplym (le_R_trans_core f' g g')
  psplit
  · papplym (le_R_trans_core f' f g)
    psplit
    · papplym (le_R_of_eq_R_core f' f)
      pthm hf
    · pexact h
  · papplym (le_R_of_eq_R_core g g')
    pthm hg

-- ── Additive monotonicity ───────────────────────────────────────────────────
--
-- `add_R f g n = add_Q (f̂(n+1), ĝ(n+1))` — the `+1` shift.  So the goal at index `n` is a
-- statement about index `n+2`, where the hypothesis carries the bound `2^{-(n+1)}`.  Half the
-- budget is left over; `pow2neg_Q_le_succ` spends it and nothing else is needed.

/-- `(c +ℚ b) −ℚ (c +ℚ a) =ℚ b −ℚ a` — `sub_Q_add_cancel` with the *left* summand common. -/
private def sub_Q_add_cancel_l (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (Term.app2 Term.add_Q c b) (Term.app2 Term.add_Q c a))
        (Term.app2 Term.sub_Q b a)) :=
  eqQtrans (sub_Q_congr (add_Q_comm_inst c b) (add_Q_comm_inst c a))
    (sub_Q_add_cancel a b c)

/-- **Right additive monotonicity**: `f ≤_ℝ g → f +_ℝ h ≤_ℝ g +_ℝ h`. -/
def le_R_add_mono_r_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f g →ᶠ le_R (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h)) := by
  pmode
  pintro hyp
  papplym (le_R_all f g) in hyp with hb
  papplym (le_R_of_all (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h))
  simp only [add_R_app_weaken]
  pforall
  pinst hb (.app .succ (.var .vz)) with hb1
  lnorm
  prw (cauchyfy_add_R f.weaken h.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_add_R g.weaken h.weaken (.app .succ (.var .vz)))
  papplym (lt_Q_congr
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz))))))
    (.app Term.pow2neg_Q (.var .vz))
    (eqQsym (sub_Q_add_cancel
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz))))))
    (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
  papplym (lt_le_Q_trans
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pexact hb1
  · pthm (pow2neg_Q_le_succ (.var .vz))

/-- **Left additive monotonicity**: `f ≤_ℝ g → h +_ℝ f ≤_ℝ h +_ℝ g`.

Proved directly rather than through `add_comm_R` and `le_R_congr`: the estimate is the same
one, and going round by commutativity would spend two `=_ℝ` congruences for nothing. -/
def le_R_add_mono_l_core (h f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f g →ᶠ le_R (Term.app2 Term.add_R h f) (Term.app2 Term.add_R h g)) := by
  pmode
  pintro hyp
  papplym (le_R_all f g) in hyp with hb
  papplym (le_R_of_all (Term.app2 Term.add_R h f) (Term.app2 Term.add_R h g))
  simp only [add_R_app_weaken]
  pforall
  pinst hb (.app .succ (.var .vz)) with hb1
  lnorm
  prw (cauchyfy_add_R h.weaken f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_add_R h.weaken g.weaken (.app .succ (.var .vz)))
  papplym (lt_Q_congr
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
    (.app Term.pow2neg_Q (.var .vz))
    (eqQsym (sub_Q_add_cancel_l
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz))))))
    (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
  papplym (lt_le_Q_trans
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pexact hb1
  · pthm (pow2neg_Q_le_succ (.var .vz))

/-- **Two-sided additive monotonicity**: `f ≤_ℝ g → h ≤_ℝ k → f +_ℝ h ≤_ℝ g +_ℝ k`.

This is the form the metric proofs want, and it is derived — not re-proved — from the two
one-sided lemmas plus transitivity, through the common middle term `g +_ℝ h`. -/
def le_R_add_mono_core (f g h k : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f g ∧ᶠ le_R h k →ᶠ
        le_R (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g k)) := by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  papplym (le_R_trans_core (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h)
    (Term.app2 Term.add_R g k))
  psplit
  · papplym (le_R_add_mono_r_core f g h)
    pexact h1
  · papplym (le_R_add_mono_l_core g h k)
    pexact h2

end OrderedFieldAxioms

end Metatheorems
