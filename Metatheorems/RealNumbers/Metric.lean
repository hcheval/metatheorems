/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Field
import Metatheorems.RealNumbers.Bounds

namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Properties needed for metric space transitivity ─────────────────────────

/-- ⊢ ∀f,g : ℝ. f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0 -/
def add_eq_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) Term.zero_R
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
                   Term.zero_R))) :=
  univ_gen (univ_gen (add_eq_zero_R_core (.var (.vs .vz)) (.var .vz)))

/-- `0_ℝ ≤_ℝ f ∧ f ≤_ℝ g ∧ g =_ℝ 0_ℝ → f =_ℝ 0_ℝ`, at explicit reals.

**The old statement of `le_zero_eq_zero_R` — without the first conjunct — was FALSE**, and the
counterexample is worth keeping. Take `f := λn.⟨−1⟩_ℚ` and `g := 0_ℝ`. Then

* `le_R f g` unfolds to `¬ lt_R g f`, i.e. `¬∃n (f̂(n+1) −_ℚ ĝ(n+1) ≥_ℚ 2^{-n})`. Here that
  difference is `−1`, which is below every `2^{-n}`, so the `∃` is empty and `f ≤_ℝ g` holds;
* `g =_ℝ 0_ℝ` holds (`cauchyfy_zero_R`);
* `f =_ℝ 0_ℝ` fails already at `n = 0`: it asks `|−1|_ℚ <_ℚ ⟨2^{-0}⟩_ℚ`, i.e. `1 <_ℚ 1`.

So that formula was false in the standard model and hence not derivable: `f ≤_ℝ 0` says
nothing about how far *below* `0` the real `f` is. Adding `0_ℝ ≤_ℝ f` repairs it, and the
repaired form is what is proved here (2026-09-02).

The estimate, at the goal's index `n`. Write `a_k := f̂(k)`, `b_k := ĝ(k)`.

* **lower bound** `−a_{n+1} <ℚ 2^{-n}` — `0_ℝ ≤_ℝ f` read at `n`, directly;
* **upper bound** `a_{n+1} <ℚ 2^{-n}` — three steps, at index `n+2` rather than `n`, because
  reading the two hypotheses at `n` gives only `2^{-n} + 2^{-n}` and overshoots:
  `f ≤_ℝ g` at `n+2` gives `a_{n+3} −ℚ b_{n+3} <ℚ 2^{-(n+2)}`, `g =_ℝ 0` at `n+2` gives
  `b_{n+3} <ℚ 2^{-(n+2)}` (through `le_Q_self_abs`), so `a_{n+3} <ℚ 2^{-(n+1)}`; and
  `cauchyfy_two_step` moves back from `n+3` to `n+1` for another `2^{-(n+1)}`.

Both bounds are then folded into `|a_{n+1}| <ℚ 2^{-n}` by `abs_Q_lt_of_two_sided`. Unlike
`eq_R_trans` this needs no telescoping induction — the shift is a fixed two steps.

`eqAtType_trans_base` (`BaseEquality.lean`) still has to supply `0_ℝ ≤_ℝ d(x,z)` from the
pseudometric axioms; `nonneg_of_add_self_nonneg` below is the ℝ-side half of that, and
`dist_nonneg` is the assembly. -/
def le_zero_eq_zero_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R Term.zero_R f ∧ᶠ le_R f g ∧ᶠ eq_R g Term.zero_R →ᶠ eq_R f Term.zero_R) :=
  let n   : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n
  let n2  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n1
  let n3  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n2
  let a   : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n1
  let a3  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n3
  let b3  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken n3
  let P   : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n
  let P1  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n1
  let P2  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n2
  by
  pmode
  pintro hyp
  pdestruct hyp with h01 h3
  pdestruct h01 with h0 h12
  papplym (le_R_all Term.zero_R f) in h0 with p0
  papplym (le_R_all f g) in h12 with p12
  pforall
  pinst p0 n with q0
  pinst p12 n2 with q1
  pinst h3 n2 with q2
  canorm
  -- the lower bound, straight from `0_ℝ ≤_ℝ f` at `n`
  prw (cauchyfy_zero_R n1) in q0 with q0a
  papplym (lt_Q_congr (Term.app2 Term.sub_Q Term.zero_Q a) P (.app Term.neg_Q a) P
    (sub_Q_zero_l a) (eq_Q_refl_inst P)) in q0a with hlow
  -- `g =_ℝ 0` at `n+2`, turned into the directed bound `b_{n+3} <ℚ 2^{-(n+2)}`
  prw (cauchyfy_zero_R n3) in q2 with q2a
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q b3 Term.zero_Q)) P2
    (.app Term.abs_Q b3) P2 (abs_Q_congr (sub_Q_zero_Q b3)) (eq_Q_refl_inst P2)) in q2a with q2b
  phave hb3 : lt_Q b3 P2
  · papplym (le_lt_Q_trans b3 (.app Term.abs_Q b3) P2)
    psplit
    · pthm (le_Q_self_abs b3)
    · pexact q2b
  -- adding the two at `n+2`: `a_{n+3} <ℚ 2^{-(n+1)}`
  phave ha3 : lt_Q a3 P1
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a3 b3) b3)
      (Term.app2 Term.add_Q P2 P2) a3 P1
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q a3 b3) b3) (add_Q_sub_cancel a3 b3))
      (pow2neg_Q_halve n1))
    papplym (lt_Q_add_both (Term.app2 Term.sub_Q a3 b3) b3 P2 P2)
    psplit
    · pexact q1
    · pexact hb3
  -- two `cauchyfy` steps back from `n+3` to `n+1`
  phave hstep : lt_Q (Term.app2 Term.sub_Q a a3) P1
  · papplym (le_lt_Q_trans (Term.app2 Term.sub_Q a a3)
      (.app Term.abs_Q (Term.app2 Term.sub_Q a a3)) P1)
    psplit
    · pthm (le_Q_self_abs (Term.app2 Term.sub_Q a a3))
    · pthm (cauchyfy_two_step f.weaken n1)
  phave hup : lt_Q a P
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a a3) a3)
      (Term.app2 Term.add_Q P1 P1) a P
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q a a3) a3) (add_Q_sub_cancel a a3))
      (pow2neg_Q_halve n))
    papplym (lt_Q_add_both (Term.app2 Term.sub_Q a a3) a3 P1 P1)
    psplit
    · pexact hstep
    · pexact ha3
  -- fold the two one-sided bounds into the `eq_R` goal
  prw (cauchyfy_zero_R n1)
  papplym (lt_Q_congr (.app Term.abs_Q a) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q a Term.zero_Q)) P
    (abs_Q_congr (eqQsym (sub_Q_zero_Q a))) (eq_Q_refl_inst P))
  papplym (abs_Q_lt_of_two_sided a P)
  psplit
  · pexact hup
  · pexact hlow

/-- ⊢ ∀f,g : ℝ. 0_ℝ ≤_ℝ f ∧ f ≤_ℝ g ∧ g =_ℝ 0_ℝ → f =_ℝ 0_ℝ

The repaired form of the old (false) `le_zero_eq_zero_R`; see `le_zero_eq_zero_R_core` for
the counterexample to the version without `0_ℝ ≤_ℝ f`, and for the estimate. -/
def le_zero_eq_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (le_R Term.zero_R (.var (.vs .vz))
          ∧ᶠ le_R (.var (.vs .vz)) (.var .vz)
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (.var (.vs .vz)) Term.zero_R))) :=
  univ_gen (univ_gen (le_zero_eq_zero_R_core (.var (.vs .vz)) (.var .vz)))

/-- `0_ℝ ≤_ℝ u → 0_ℝ ≤_ℝ f` where `u` is *any* real whose cauchyfication is `f̂(·+1) +ℚ f̂(·+1)`.

The sum is fed in through an abstract `u` rather than rewritten inside the goal, for the same
reason `add_eq_zero_R_gen` does it: `prw` at a goal containing `Term.add_R` has to push a
substitution through that constant, and that is the delta-expansion blow-up CLAUDE.md's
build-cost section warns about.

The argument, contrapositively — `le_R` on both sides is a negated `∃`, so a witness `n`
against `0_ℝ ≤_ℝ f` has to be turned into a witness against `0_ℝ ≤_ℝ u`, and the *same* index
works. Writing `c := −ℚ f̂(n+1)`, `b := −ℚ f̂(n+2)`:

    2^{-n} ≤ℚ c                              -- the given witness at n
    c <ℚ 2^{-(n+2)} +ℚ b                      -- one `cauchyfy` step, |c −ℚ b| = |f̂(n+1) −ℚ f̂(n+2)|
    2^{-n} <ℚ 2^{-(n+1)} +ℚ b                 -- and 2^{-(n+2)} ≤ℚ 2^{-(n+1)}
    2^{-(n+1)} <ℚ b                           -- cancel, since 2^{-n} =ℚ 2^{-(n+1)} +ℚ 2^{-(n+1)}
    2^{-n} <ℚ b +ℚ b                          -- double

and `b +ℚ b` is `−ℚ û(n+1)`. Note the margin: the Cauchy step costs `2^{-(n+2)}` where a whole
`2^{-(n+1)}` is available, so this is not a tight estimate and needs no telescoping. -/
private def nonneg_of_add_self_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises (le_R Term.zero_R u →ᶠ le_R Term.zero_R f) :=
  let n  : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n
  let n2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n1
  let a  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n1
  let a' : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n2
  let c  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q a
  let b  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q a'
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n1
  let Q  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n2
  -- `c −ℚ b =ℚ f̂(n+2) −ℚ f̂(n+1)`: negation reverses the difference.
  let hCB : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (Term.app2 Term.sub_Q c b) (Term.app2 Term.sub_Q a' a)) :=
    eqQtrans (sub_Q_eq_add_neg c b)
      (eqQtrans (addQr c (neg_Q_neg_Q a'))
        (eqQtrans (add_Q_comm_inst c a') (eqQsym (sub_Q_eq_add_neg a' a))))
  let hAbs : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q c b))
            (.app Term.abs_Q (Term.app2 Term.sub_Q a a'))) :=
    eqQtrans (abs_Q_congr hCB) (abs_diff_Q_comm a' a)
  by
  pmode
  pintro hsum
  pintro hex
  pobtain hex with hn
  canorm
  prw (cauchyfy_zero_R n1) in hn with hn1
  papplym (le_Q_congr P (Term.app2 Term.sub_Q Term.zero_Q a) P c
    (eq_Q_refl_inst P) (sub_Q_zero_l a)) in hn1 with hPc
  phave hcb : lt_Q (Term.app2 Term.sub_Q c b) Q
  · papplym (le_lt_Q_trans (Term.app2 Term.sub_Q c b)
      (.app Term.abs_Q (Term.app2 Term.sub_Q c b)) Q)
    psplit
    · pthm (le_Q_self_abs (Term.app2 Term.sub_Q c b))
    · pthm (Derivable.mp (cauchyfy_cauchy f.weaken n1)
        (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q a a')) Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q c b)) Q
          (eqQsym hAbs) (eq_Q_refl_inst Q)))
  phave hcQb : lt_Q c (Term.app2 Term.add_Q Q b)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q c b) b)
      (Term.app2 Term.add_Q Q b) c (Term.app2 Term.add_Q Q b)
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q c b) b) (add_Q_sub_cancel c b))
      (eq_Q_refl_inst (Term.app2 Term.add_Q Q b)))
    papplym (lt_le_Q_add (Term.app2 Term.sub_Q c b) b Q b)
    psplit
    · pexact hcb
    · pthm (le_Q_refl b)
  phave hPQb : lt_Q P (Term.app2 Term.add_Q Q b)
  · papplym (le_lt_Q_trans P c (Term.app2 Term.add_Q Q b))
    psplit
    · pexact hPc
    · pexact hcQb
  phave hPP1b : lt_Q P (Term.app2 Term.add_Q P1 b)
  · papplym (lt_le_Q_trans P (Term.app2 Term.add_Q Q b) (Term.app2 Term.add_Q P1 b))
    psplit
    · pexact hPQb
    · pthm (Derivable.mp (pow2neg_Q_le_succ n1) (le_Q_add Q P1 b))
  phave hP1b : lt_Q P1 b
  · papplym (lt_Q_add_cancel_l P1 P1 b)
    papplym (lt_Q_congr P (Term.app2 Term.add_Q P1 b)
      (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q P1 b)
      (eqQsym (pow2neg_Q_halve n)) (eq_Q_refl_inst (Term.app2 Term.add_Q P1 b)))
    pexact hPP1b
  -- the same index `n` refutes `0_ℝ ≤_ℝ u`
  papply hsum
  pexists n
  canorm
  prw (cauchyfy_zero_R n1)
  prw hu
  papplym (le_Q_congr P (Term.app2 Term.add_Q b b) P
    (Term.app2 Term.sub_Q Term.zero_Q (Term.app2 Term.add_Q a' a'))
    (eq_Q_refl_inst P)
    (eqQsym (eqQtrans (sub_Q_zero_l (Term.app2 Term.add_Q a' a')) (neg_Q_add_Q a' a'))))
  papplym (lt_Q_imp_le_Q P (Term.app2 Term.add_Q b b))
  papplym (lt_Q_congr (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q b b) P
    (Term.app2 Term.add_Q b b) (pow2neg_Q_halve n)
    (eq_Q_refl_inst (Term.app2 Term.add_Q b b)))
  papplym (lt_Q_add_both P1 P1 b b)
  psplit
  · pexact hP1b
  · pexact hP1b

/-- `0_ℝ ≤_ℝ f +_ℝ f → 0_ℝ ≤_ℝ f`, at an explicit real.

This is the ℝ-side half of the non-negativity of a pseudo-metric: with `ax_refl`, `ax_sym` and
`ax_triangle` one gets `0 =_ℝ d(x,x) ≤_ℝ d(x,y) +_ℝ d(y,x) =_ℝ d(x,y) +_ℝ d(x,y)`, and this
lemma converts that into `0_ℝ ≤_ℝ d(x,y)` — the hypothesis `le_zero_eq_zero_R` needs and whose
absence made the old statement of that lemma false. -/
def nonneg_of_add_self_nonneg_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R Term.zero_R (Term.app2 Term.add_R f f) →ᶠ le_R Term.zero_R f) :=
  nonneg_of_add_self_gen f (Term.app2 Term.add_R f f)
    ((add_R_app_weaken f f).symm ▸
      cauchyfy_add_R f.weaken f.weaken (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. 0_ℝ ≤_ℝ f +_ℝ f → 0_ℝ ≤_ℝ f -/
def nonneg_of_add_self_nonneg :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (le_R Term.zero_R (Term.app2 Term.add_R (.var .vz) (.var .vz))
          →ᶠ le_R Term.zero_R (.var .vz))) :=
  univ_gen (nonneg_of_add_self_nonneg_core (.var .vz))

/-- **`0_ℝ ≤_ℝ f` from the doubled ℚ estimate.** The caller supplies

    `∀n. (−ℚ f̂(n+2)) +ℚ (−ℚ f̂(n+2)) <ℚ 2^{-n}`

and gets `0_ℝ ≤_ℝ f`. This packages `le_R_of_bound`, the two `Term.weaken` computations, the
`cauchyfy_zero_R` / `cauchyfy_add_R` rewrites and `nonneg_of_add_self_nonneg_core`, so that a
caller never has to see `f +_ℝ f` at all — which matters, because pushing a substitution
through `Term.add_R` is the delta-expansion blow-up the build-cost notes warn about.

`dist_nonneg` (`BaseEquality.lean`) is the one consumer, and the doubling is not an artefact:
the triangle inequality at `(x, y, x)` bounds `0` by `d(x,y) + d(y,x)`, which symmetry turns
into `2·d(x,y)` and nothing smaller. -/
def nonneg_R_of_double_bound (f : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (Term.app2 Term.add_Q
               (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
                  (.app .succ (.app .succ (.var .vz)))))
               (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
                  (.app .succ (.app .succ (.var .vz))))))
            (.app Term.pow2neg_Q (.var .vz)))) :
    Derivable F al Premises (le_R Term.zero_R f) :=
  let d2 : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz)))
  let pn : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  Derivable.mp
    (le_R_of_bound Term.zero_R (Term.app2 Term.add_R f f) (by
      rw [zero_R_weaken, add_R_app_weaken]
      pmode
      prw (cauchyfy_zero_R (.app .succ (.var .vz)))
      prw (cauchyfy_add_R f.weaken f.weaken (.app .succ (.var .vz)))
      papplym (lt_Q_congr (Term.app2 Term.add_Q (.app Term.neg_Q d2) (.app Term.neg_Q d2)) pn
        (Term.app2 Term.sub_Q Term.zero_Q (Term.app2 Term.add_Q d2 d2)) pn
        (eqQsym (eqQtrans (sub_Q_zero_l (Term.app2 Term.add_Q d2 d2)) (neg_Q_add_Q d2 d2)))
        (eq_Q_refl_inst pn))
      pthm h))
    (nonneg_of_add_self_nonneg_core f)

-- ── From Kohlenbach, *Applied Proof Theory*, §4.1 ───────────────────────────
--
-- Three facts the book states and uses but does not prove. They are NOT in
-- `Metateorema-New3`, which is why they were missing here; added 2026-09-01
-- after reading the book directly.
--
-- Note the book's own calibration of effort: it calls the ℚ ordered-field
-- package "easily verified" (p. 79) — that is the ~4,600 lines of
-- `RationalNumbers.lean` — and asserts the ℝ package in one parenthesis
-- (p. 80) with no proof at all.

/-- The constant real sequence at a rational code — the book's `r ↦ λn.⟨r⟩` embedding
    of ℚ into ℝ (p. 80). `⟨2^{-k}⟩_ℝ` is `const_R (pow2neg_Q k)`. -/
def const_R {Γ : Ctx ι} (q : Term F Γ Ty.nat) : Term F Γ (realTy ι) :=
  Term.lam q.weaken

/-- **Lemma 4.2** (Kohlenbach p. 80). `f̂(k)` is a rational `2^{-k}`-approximation of `f`:

    `WE-HA^ω↾ ⊢ ∀f,k. |f −_ℝ λn.f̂(k)|_ℝ <_ℝ ⟨2^{-k}⟩_ℝ`

    This is the workhorse for the tightness estimates that block Class C — it is what
    lets a proof move between a real and a rational approximation of it at a chosen
    index, which is exactly what the five-term split needs.

    **Worked out 2026-09-01; see `REALS_PLAN.md` §0.8.** The goal reduces to
    `∃n. 2^{-k} −ℚ |f̂(n+2) −ℚ f̂(k)| ≥ℚ 2^{-n}`, and the crude telescoping bound falls short
    by a factor of 4 *at every `n`*. The witness has to be `n := max(k, rat_den d)` with
    `d := 2^{-(k+1)} −ℚ |f̂(k) −ℚ f̂(k+1)|` — the Cauchy slack at index `k`, positive for
    every `f` because `cauchyState_cauchy` is strict. `pow2neg_rat_den_le` (proved) is the
    Archimedean step that makes that witness work; what is still missing is the triangle
    inequality (forward *and* reverse), the refined telescoping induction, and
    `cauchyfy_const` at an arbitrary constant. Note that with `le_R` in place of `lt_R` the
    statement is Π₁⁰ and needs no witness at all. -/
def approx_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all Ty.nat
        (lt_R
          (Term.app Term.abs_R
            (Term.app2 Term.sub_R
              (.var (.vs .vz))
              (const_R (Term.app (Term.app Term.cauchyfy (.var (.vs .vz))) (.var .vz)))))
          (const_R (.app Term.pow2neg_Q (.var .vz)))))) :=
  sorry

/-- **Lemma 4.3** (Kohlenbach p. 80). Cauchy completeness of ℝ:

    `∀Φ^{1(0)}(∀n,m,k (n ≤ m → n ≤ k → |Φm −_ℝ Φk|_ℝ ≤_ℝ ⟨2^{-n}⟩)
                → ∃f¹ ∀n (|Φn −_ℝ f|_ℝ ≤_ℝ ⟨2^{-n}⟩))`

    The book notes the witness is definable outright — `f k := Φ(k+3)(k+3)` — so the
    `∃` should not need to be found by search. -/
def cauchy_complete_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all (Ty.nat →ₜ rTy)
        (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
            (Formula.eq0 (Term.app2 Term.monus (.var (.vs (.vs .vz))) (.var (.vs .vz)))
               Term.zero →ᶠ
             Formula.eq0 (Term.app2 Term.monus (.var (.vs (.vs .vz))) (.var .vz))
               Term.zero →ᶠ
             le_R
               (Term.app Term.abs_R
                 (Term.app2 Term.sub_R
                   (Term.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
                   (Term.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))))
               (const_R (.app Term.pow2neg_Q (.var (.vs (.vs .vz))))))))
          →ᶠ Formula.ex rTy (Formula.all Ty.nat
              (le_R
                (Term.app Term.abs_R
                  (Term.app2 Term.sub_R
                    (Term.app (.var (.vs (.vs .vz))) (.var .vz))
                    (.var (.vs .vz))))
                (const_R (.app Term.pow2neg_Q (.var .vz))))))) :=
  sorry

/-- The estimate behind `abs_R_bound`, at the bound index `x₀` of the context `nat :: Γ'`:
`(|β|_ℝ)^(x₀+1) −_ℚ ((β(0)+1)_ℝ)^(x₀+1) <_ℚ 2^{-x₀}`.

The whole content is `(|β|_ℝ)^(s) ≤_ℚ ⟨β(0)+1⟩_ℚ`:

    X̂(s) ≤ |X̂(s)| ≤ |X̂(0)| + |X̂(0) − X̂(s)| ≤ |β(0)|_ℚ + 2^{-0} ≤ ⟨β(0)⟩ + 1 = ⟨β(0)+1⟩

with `abs_le_encode` (a code dominates the magnitude it encodes) supplying the third step
and the telescope from index `0` (`cauchyfy_shift_le`, worth `2^{-0} = 1`) the second. The
right-hand side cauchyfies to exactly `⟨β(0)+1⟩` (`cauchyfy_embed`), and `sub_lt_of_le`
turns the `≤` into the strict bound against `0 <_ℚ 2^{-x₀}`. -/
private def abs_R_bound_est {Γ' : Ctx ι} (β : Term F (Ty.nat :: Γ') (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ')
      (lt_Q
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy (.app Term.abs_R β) (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy
            (.app Term.embed_nat_R (.app .succ (.app β Term.zero)))
            (.app .succ (.var .vz))))
        (.app Term.pow2neg_Q (.var .vz))) :=
  let s : Term F (Ty.nat :: Γ') Ty.nat := .app .succ (.var .vz)
  let X : Term F (Ty.nat :: Γ') (realTy ι) := .app Term.abs_R β
  let Xs : Term F (Ty.nat :: Γ') Ty.nat := Term.app2 Term.cauchyfy X s
  let X0 : Term F (Ty.nat :: Γ') Ty.nat := Term.app2 Term.cauchyfy X Term.zero
  let c0 : Term F (Ty.nat :: Γ') Ty.nat := .app β Term.zero
  let E : Term F (Ty.nat :: Γ') (realTy ι) := .app Term.embed_nat_R (.app .succ c0)
  let Es : Term F (Ty.nat :: Γ') Ty.nat := Term.app2 Term.cauchyfy E s
  let target : Term F (Ty.nat :: Γ') Ty.nat := .app Term.encode_nat_Q (.app .succ c0)
  let D : Term F (Ty.nat :: Γ') Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q X0 Xs)
  -- X̂(s) ≤ |X̂(s)| ≤ |X̂(0)| + |X̂(0) − X̂(s)|
  let h1 : Derivable F al Premises (le_Q Xs (.app Term.abs_Q Xs)) := le_Q_self_abs Xs
  let h2 : Derivable F al Premises
      (le_Q (.app Term.abs_Q Xs) (Term.app2 Term.add_Q (.app Term.abs_Q X0) D)) :=
    abs_Q_le_add_diff Xs X0
  -- |X̂(0) − X̂(s)| ≤ 2^{-0} =₀ 1
  let h3 : Derivable F al Premises (le_Q D Term.one_Q) :=
    Derivable.mp (cauchyfy_shift_le X Term.zero s)
      (le_Q_congr _ _ _ _
        (eqQ_of_nat_eq'
          (abs_Q_congr_nat
            (qfer_no_premise_nat_nf (add_zero_l s)
              (r := Term.app2 Term.sub_Q X0.weaken
                (Term.app2 Term.cauchyfy X.weaken (.var .vz)))
              (by qb_nf; rfl) (by qb_nf; rfl))))
        (eqQ_of_nat_eq' pow2neg_zero_eq_one))
  -- X̂(0) =₀ |β(0)|_ℚ, so |X̂(0)| ≤ ⟨β(0)⟩ by code-dominates
  let e_all : Derivable F al Premises (Formula.eq0 X0 (.app Term.abs_Q c0)) :=
    qtrans (qtrans (cauchyfy_zero X) (abs_R_apply β Term.zero))
      (abs_Q_congr_nat (cauchyfy_zero β))
  let h4 : Derivable F al Premises
      (le_Q (.app Term.abs_Q X0) (.app Term.encode_nat_Q c0)) :=
    Derivable.mp (abs_le_encode c0)
      (le_Q_congr _ _ _ _
        (eqQsym (eqQtrans (eqQ_of_nat_eq' (abs_Q_congr_nat e_all)) (abs_Q_abs_Q c0)))
        (eq_Q_refl_inst _))
  -- assemble: X̂(s) ≤ ⟨β(0)⟩ + 1 =_ℚ ⟨β(0)+1⟩ =₀ Ê(s)
  let h5 : Derivable F al Premises
      (le_Q Xs (Term.app2 Term.add_Q (.app Term.encode_nat_Q c0) Term.one_Q)) :=
    leQt (leQt h1 h2)
      (Derivable.mp (Derivable.mp h3 (Derivable.mp h4 and_intro))
        (le_Q_add_both (.app Term.abs_Q X0) D (.app Term.encode_nat_Q c0) Term.one_Q))
  let h7 : Derivable F al Premises (le_Q Xs target) :=
    Derivable.mp h5
      (le_Q_congr _ _ _ _ (eq_Q_refl_inst Xs) (eqQsym (encode_succ c0)))
  let h8 : Derivable F al Premises (Formula.eq0 Es target) :=
    cauchyfy_embed (.app .succ c0) s
  let h9 : Derivable F al Premises (le_Q Xs Es) :=
    Derivable.mp h7
      (le_Q_congr _ _ _ _ (eq_Q_refl_inst Xs) (eqQsym (eqQ_of_nat_eq' h8)))
  sub_lt_of_le Xs Es (.app Term.pow2neg_Q (.var .vz)) h9
    (zero_lt_pow2neg_Q (.var .vz))

/-- Kohlenbach p. 430 (cited as Remark `rmrk:bound-on-real` in `real-numbers.tex`):

    `|α|_ℝ ≤_ℝ (α(0) + 1)_ℝ`

    This is the majorization fact `mul_R`'s operand bound silently relies on — a code
    dominates the magnitude it encodes. It is Kohlenbach's lemma, not an invention of
    this development, and `mul_R` should not be "fixed" to avoid it. -/
def abs_R_bound :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (le_R (Term.app Term.abs_R (.var .vz))
              (Term.app Term.embed_nat_R
                (.app .succ (Term.app (.var .vz) Term.zero))))) :=
  univ_gen
    (le_R_of_bound (.app Term.abs_R (.var .vz))
      (.app Term.embed_nat_R (.app .succ (Term.app (.var .vz) Term.zero)))
      (by
        rw [abs_R_app_weaken, embed_nat_R_app_weaken]
        exact abs_R_bound_est (Term.var Var.vz).weaken))

end OrderedFieldAxioms

end Metatheorems
