/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Order
import Metatheorems.RealNumbers.Approx

namespace Metatheorems

/-!
# The non-strict order `≤_ℝ`

`le_R f g` is `¬(g <_ℝ f)`, and `le_R_all`/`le_R_of_all` characterise it:

    f ≤_ℝ g   ⟺   ∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}.

This file proves the package: reflexivity, transitivity, antisymmetry, `=_ℝ ⟹ ≤_ℝ`,
`<_ℝ ⟹ ≤_ℝ`, respect for `=_ℝ`, additive monotonicity, and the reverse-triangle lemmas.
Transitivity is the tight statement, proved by the one-sided mirror of the `eq_R` telescope
(`leR_pair_step`, `leR_tail`, `leR_le`, `leR_strict`, on the signed difference `sDiff`); the
rest close directly.
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
one-sided telescope above exists. -/
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
-- Slack-free: `add_R`'s `+1` shift leaves half the budget, spent by `pow2neg_Q_le_succ`.

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

/-- **Left additive monotonicity**: `f ≤_ℝ g → h +_ℝ f ≤_ℝ h +_ℝ g`. -/
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

-- ── Subtraction: `f ≤ g +ℝ h → f −ℝ h ≤ g` ──────────────────────────────────
--
-- The ℝ content of the reverse triangle inequality (`BaseEquality.dist_rev_tri`).
--
-- As a direct estimate the statement is tight, but it is algebraically
-- `f +ℝ (−ℝ h) ≤ (g +ℝ h) +ℝ (−ℝ h) =ℝ g`: right monotonicity, then the cancellation
-- `(g +ℝ h) +ℝ (−ℝ h) ≤ℝ g`, chained by `le_R_trans_core`. No new estimate is written.

/-- `neg_R_app_weaken` is private to `Negation.lean`; re-derived here. -/
private theorem neg_R_app_weaken' {Δ : Ctx ι} {ρ : Ty ι} (g : Term F Δ (realTy ι)) :
    (Term.app Term.neg_R g).weaken (σ := ρ) = Term.app Term.neg_R g.weaken := by
  show Term.app ((Term.neg_R : Term F Δ _).weaken) g.weaken = _
  rw [Term.weaken, Term.rename_eq_subst, neg_R_closed_subst]

/-- `neg_Q` congruence at `=₀` (`neg_Q_nat` is private to `Negation.lean`). -/
private def negQ_nat' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.neg_Q s) (.app Term.neg_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.neg_Q (.var .vz)) (by qb_nf) (by qb_nf)

/-- **`f −ℝ g =ℝ f +ℝ (−ℝ g)`.** The two cauchyfications agree on the nose at every index —
`cauchyfy_sub_R` on the left, `cauchyfy_add_R` then `cauchyfy_neg` on the right — so this is
`eq_R_of_cauchyfy_eqQ` with no estimate. -/
def sub_R_eq_add_neg_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.sub_R f g) (Term.app2 Term.add_R f (.app Term.neg_R g))) :=
  eq_R_of_cauchyfy_eqQ (Term.app2 Term.sub_R f g)
    (Term.app2 Term.add_R f (.app Term.neg_R g)) (by
    rw [sub_R_app_weaken, add_R_app_weaken, neg_R_app_weaken']
    exact eqQ_of_nat_eq'
      (qtrans (cauchyfy_sub_R f.weaken g.weaken (.app .succ (.var .vz)))
        (Derivable.mp
          (qtrans
            (cauchyfy_add_R f.weaken (.app Term.neg_R g.weaken) (.app .succ (.var .vz)))
            (addQ_r_nat (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
              (cauchyfy_neg g.weaken (.app .succ (.app .succ (.var .vz))))))
          Derivable.sym0)))

/-- **`−ℝ (f −ℝ g) =ℝ g −ℝ f`.** Again on the nose at every index: both sides cauchyfy to
`ĝ(n+2) +ℚ (−ℚ f̂(n+2))` up to `neg_Q_add_Q`, `neg_Q_neg_Q` and commutativity. -/
def neg_sub_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (.app Term.neg_R (Term.app2 Term.sub_R f g)) (Term.app2 Term.sub_R g f)) :=
  eq_R_of_cauchyfy_eqQ (.app Term.neg_R (Term.app2 Term.sub_R f g))
    (Term.app2 Term.sub_R g f) (by
    rw [neg_R_app_weaken', sub_R_app_weaken, sub_R_app_weaken]
    let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
    let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
    let A : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
    let C : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken s2
    let nA : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q A
    let nC : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q C
    -- left: `−ℚ (A +ℚ −ℚ C)`
    have hl : Derivable F al Premises (Γ := Ty.nat :: Γ)
        (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.neg_R (Term.app2 Term.sub_R f.weaken g.weaken)) s1)
          (.app Term.neg_Q (Term.app2 Term.add_Q A nC))) :=
      qtrans (cauchyfy_neg (Term.app2 Term.sub_R f.weaken g.weaken) s1)
        (negQ_nat' (cauchyfy_sub_R f.weaken g.weaken s1))
    -- right: `C +ℚ −ℚ A`
    have hr : Derivable F al Premises (Γ := Ty.nat :: Γ)
        (Formula.eq0 (Term.app2 Term.cauchyfy (Term.app2 Term.sub_R g.weaken f.weaken) s1)
          (Term.app2 Term.add_Q C nA)) :=
      cauchyfy_sub_R g.weaken f.weaken s1
    exact eqQtrans (eqQ_of_nat_eq' hl)
      (eqQtrans (neg_Q_add_Q A nC)
        (eqQtrans (addQr nA (neg_Q_neg_Q C))
          (eqQtrans (add_Q_comm_inst nA C)
            (eqQ_of_nat_eq' (Derivable.mp hr Derivable.sym0))))))

/-- **Cancellation, one-sided**: `(g +ℝ h) +ℝ (−ℝ h) ≤ℝ g`. Associativity, `add_neg_R_core`
under `g +ℝ ·` (monotonicity in place of an `=ℝ`-congruence for `+ℝ`, which does not exist),
and `add_zero_R_core`, chained by `le_R_trans_core`. -/
def add_neg_cancel_le_R_core (g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.add_R (Term.app2 Term.add_R g h) (.app Term.neg_R h)) g) := by
  let nh : Term F Γ (realTy ι) := .app Term.neg_R h
  let lhs : Term F Γ (realTy ι) := Term.app2 Term.add_R (Term.app2 Term.add_R g h) nh
  let mid : Term F Γ (realTy ι) := Term.app2 Term.add_R g (Term.app2 Term.add_R h nh)
  let mid0 : Term F Γ (realTy ι) := Term.app2 Term.add_R g Term.zero_R
  pmode
  papply (le_R_trans_core lhs mid g)
  psplit
  · papply (le_R_of_eq_R_core lhs mid)
    pthm (add_assoc_R_core g h nh)
  · papply (le_R_trans_core mid mid0 g)
    psplit
    · papply (le_R_add_mono_l_core g (Term.app2 Term.add_R h nh) Term.zero_R)
      papply (le_R_of_eq_R_core (Term.app2 Term.add_R h nh) Term.zero_R)
      pthm (add_neg_R_core h)
    · papply (le_R_of_eq_R_core mid0 g)
      pthm (add_zero_R_core g)

/-- **`f ≤ℝ g +ℝ h → f −ℝ h ≤ℝ g`** — the ℝ content of the reverse triangle inequality.
See the section comment for why no new estimate is needed although the statement is tight. -/
def le_sub_R_of_le_add_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f (Term.app2 Term.add_R g h) →ᶠ le_R (Term.app2 Term.sub_R f h) g) := by
  let nh : Term F Γ (realTy ι) := .app Term.neg_R h
  let fn : Term F Γ (realTy ι) := Term.app2 Term.add_R f nh
  let gn : Term F Γ (realTy ι) := Term.app2 Term.add_R (Term.app2 Term.add_R g h) nh
  pmode
  pintro hyp
  papply (le_R_trans_core (Term.app2 Term.sub_R f h) fn g)
  psplit
  · papply (le_R_of_eq_R_core (Term.app2 Term.sub_R f h) fn)
    pthm (sub_R_eq_add_neg_R_core f h)
  · papply (le_R_trans_core fn gn g)
    psplit
    · papply (le_R_add_mono_r_core f (Term.app2 Term.add_R g h) nh)
      pexact hyp
    · pthm (add_neg_cancel_le_R_core g h)

/-- `a ≤ℚ A → a −ℚ b ≤ℚ A −ℚ b` — the first-argument half of `Interval.lean`'s `sub_Q_mono`,
re-derived here so that `LeOrder` need not import the `[0,1]` module for one lemma. -/
private def sub_Q_mono_l (a A b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a A →ᶠ le_Q (Term.app2 Term.sub_Q a b) (Term.app2 Term.sub_Q A b)) := by
  pmode
  pintro h1
  papplym (le_Q_congr
    (Term.app2 Term.add_Q a (.app Term.neg_Q b))
    (Term.app2 Term.add_Q A (.app Term.neg_Q b))
    (Term.app2 Term.sub_Q a b) (Term.app2 Term.sub_Q A b)
    (eqQsym (sub_Q_eq_add_neg a b)) (eqQsym (sub_Q_eq_add_neg A b)))
  papplym (le_Q_add_both a (.app Term.neg_Q b) A (.app Term.neg_Q b))
  psplit
  · pexact h1
  · pthm (le_Q_refl (.app Term.neg_Q b))

/-- **`w ≤ℝ v ∧ −ℝ w ≤ℝ v → |w|ℝ ≤ℝ v`.** Slack-free: `|ŵ|ℚ` is one of `ŵ`, `−ℚ ŵ` up to
`≤ℚ` (`abs_Q_le_cases`), and `cauchyfy_abs_R`/`cauchyfy_neg` are identities, so each case is
the corresponding hypothesis at the same index. -/
def abs_R_le_of_le_le_core (w v : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R w v ∧ᶠ le_R (.app Term.neg_R w) v →ᶠ le_R (.app Term.abs_R w) v) := by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  papplym (le_R_all w v) in h1 with hb1
  papplym (le_R_all (.app Term.neg_R w) v) in h2 with hb2
  papply (le_R_of_all (.app Term.abs_R w) v)
  simp only [abs_R_app_weaken, neg_R_app_weaken']
  pforall
  pspecialize hb1 with hc1
  pspecialize hb2 with hc2
  lnorm
  prw (cauchyfy_abs_R w.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_neg w.weaken (.app .succ (.var .vz))) in hc2 with hc2'
  pfrom hc := abs_Q_le_cases (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))
  pcases hc with hA | hB
  · papply (le_lt_Q_trans _
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))) _)
    psplit
    · papply (sub_Q_mono_l _ _ _)
      pexact hA
    · pexact hc1
  · papply (le_lt_Q_trans _
      (Term.app2 Term.sub_Q
        (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))) _)
    psplit
    · papply (sub_Q_mono_l _ _ _)
      pexact hB
    · pexact hc2'

end OrderedFieldAxioms

end Metatheorems
