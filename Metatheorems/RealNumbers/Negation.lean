/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Field

namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── `cauchyfy` commutes with negation, and `add_neg_R` ──────────────────────
--
-- `add_zero_R` and `add_assoc_R` above needed no new `cauchyfy` theory, because `add_R`'s
-- own `cauchyfy_add_R` already says everything about the composite. **`add_neg_R` does**,
-- and this is the one place in the additive package where that bites:
-- `neg_R f = λn. neg_Q (f n)` applies to the *raw* `f`, not to `f̂`, so nothing yet relates
-- `(neg_R f)^` to `f̂` — and `f` is an arbitrary `ℕ → ℕ`, so `neg_R f` is not Cauchy and
-- `cauchyfy_id` does not apply either.
--
-- What makes it work is that the two recursions run in *lockstep*, on the nose:
--
--     state(neg_R f, n)  =₀  pair( neg_Q (fst_pair (state(f, n))), snd_pair (state(f, n)) )
--
-- — same flag, negated value, at *every* index. The value half is immediate; the flag half
-- is the content, because the Cauchy check is taken on the raw sequences and
-- `|neg_Q a −ℚ neg_Q b|` is only `eq_Q`-equal to `|a −ℚ b|`, not `=₀`-equal. So the flags
-- agree only because `lt_Q_dec`'s *decision* is `eq_Q`-invariant, which is what
-- `sg_bar_congr_iff` below is for: it turns the two-way implication `lt_Q_congr` supplies
-- into the `=₀` equality of `sg_bar` values that `cauchyState_advance` / `cauchyState_trip`
-- demand.
--
-- (This is the same machinery `add_comm_R` / `mul_comm_R` are blocked on — see REALS_PLAN
-- §0.2 — but only in the special case where the two sequences are related by a *fixed*
-- ℚ-operation, so the induction needs no object-level hypothesis beyond its own IH.)

/-- `sg_bar u =₀ sg_bar v` whenever `u` and `v` vanish together.

The bridge from "`lt_Q` is `eq_Q`-invariant" (an equivalence of *formulas*, which is all
`lt_Q_congr` gives) to "the flag bits are equal" (an `=₀` fact about `lt_Q_dec`, which is what
the `cauchyfy` recursion branches on). Note `sg_bar` is the *complement* indicator here —
`sg_bar 0 =₀ S0`, `sg_bar (S n) =₀ 0` — which is why the case split reads the way it does. -/
private def sg_bar_congr_iff (u v : Term F Γ Ty.nat) :
    Derivable F al Premises
      ((Formula.eq0 u Term.zero →ᶠ Formula.eq0 v Term.zero)
        ∧ᶠ (Formula.eq0 v Term.zero →ᶠ Formula.eq0 u Term.zero) →ᶠ
       Formula.eq0 (.app Term.sg_bar u) (.app Term.sg_bar v)) := by
  pmode
  pintro h
  pdestruct h with h1 h2
  pfrom hcu := sg_bar_cases u
  pcases hcu with hu1 | hu0
  · -- `sg_bar u = S0`, i.e. `u = 0`; carry it across to `v` and back up
    papplym (sg_bar_eq_S0_implies_zero u) in hu1 with huz
    phave hv1 : Formula.eq0 (.app Term.sg_bar v) (.app .succ .zero)
    · phave hvz : Formula.eq0 v Term.zero
      · papply h1
        pexact huz
      prwby hvz
      pthm sg_bar_zero
    prwby hu1
    prwby hv1
    prefl
  · -- `sg_bar u = 0`, i.e. `u ≠ 0`; likewise
    pfrom hiu := sg_bar_eq_zero_iff u
    pdestruct hiu with hiuF _hiuB
    phave hunz : ¬ᶠ(Formula.eq0 u Term.zero)
    · papply hiuF
      pexact hu0
    phave hv0 : Formula.eq0 (.app Term.sg_bar v) Term.zero
    · pfrom hiv := sg_bar_eq_zero_iff v
      pdestruct hiv with _hivF hivB
      papply hivB
      pintro hvz
      papply hunz
      papply h2
      pexact hvz
    prwby hu0
    prwby hv0
    prefl

/-- `neg_R(f)(x) =₀ neg_Q(f x)` — the two beta steps of `neg_R`. -/
def neg_R_apply (f : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.neg_R f x) (.app Term.neg_Q (.app f x))) :=
  lam2_correct_nf
    (.app Term.neg_Q (.app (.var (.vs .vz)) (.var .vz)))
    f x
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.Subst.ext,
          subst_subst0_map_weaken, closed_subst])

private theorem neg_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.neg_R : Term F Δ _).weaken (σ := ρ) = Term.neg_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact neg_R_closed_subst _

private theorem neg_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f : Term F Δ (realTy ι)) :
    (Term.app Term.neg_R f).weaken (σ := ρ) = Term.app Term.neg_R f.weaken := by
  show Term.app (Term.weaken Term.neg_R) f.weaken = _
  rw [neg_R_weaken]

/-- Congruence under `neg_Q`, at the level of `=₀`. -/
private def neg_Q_nat {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.neg_Q s) (.app Term.neg_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.neg_Q (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- Congruence for `pair` in its first argument, at the level of `=₀`. -/
private def pair_l_nat (c : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.pair s c) (Term.app2 Term.pair t c)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.pair (.var .vz) c.weaken)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- The Cauchy checks of `f` and of `neg_R f` agree *as bits*. The two checked quantities are
only `eq_Q`-equal — `|neg_Q a −ℚ neg_Q b|ℚ` is `|b −ℚ a|ℚ` re-encoded — so this is exactly
where `sg_bar_congr_iff` is spent. -/
private def neg_check_sg (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0
        (.app Term.sg_bar (Term.cauchy_check_at (.app Term.neg_R f) n))
        (.app Term.sg_bar (Term.cauchy_check_at f n))) := by
  let A : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (Term.app2 Term.neg_R f n) (Term.app2 Term.neg_R f (.app .succ n)))
  let B : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (.app f n) (.app f (.app .succ n)))
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  have hAB : Derivable F al Premises (eq_Q A B) := by
    pmode
    prw (neg_R_apply f n)
    prw (neg_R_apply f (.app .succ n))
    pthm (eqQtrans (abs_Q_congr (sub_Q_neg_neg (.app f n) (.app f (.app .succ n))))
      (abs_diff_Q_comm (.app f (.app .succ n)) (.app f n)))
  pmode
  papplym (sg_bar_congr_iff (Term.app2 Term.lt_Q_dec A P) (Term.app2 Term.lt_Q_dec B P))
  psplit
  · pthm (lt_Q_congr A P B P hAB (eq_Q_refl_inst P))
  · pthm (lt_Q_congr B P A P (eqQsym hAB) (eq_Q_refl_inst P))

-- The lockstep claim is written out at both of its occurrences rather than given a name.
-- `canorm` normalises substitutions with `simp only`, which does not unfold a named
-- `Formula` definition, so a `negF` abbreviation would hide the whole statement from the
-- induction's own bookkeeping — the same reason the file has no `cVal`/`cFlag` wrappers.

/-- The lockstep claim at an explicit index. -/
abbrev negAt (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (Term.cauchyState (.app Term.neg_R f) s)
    (Term.app2 Term.pair
      (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f s)))
      (.app Term.snd_pair (Term.cauchyState f s)))

private theorem negF_subst0 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    (Formula.eq0 (Term.cauchyState (.app Term.neg_R f.weaken) (.var .vz))
        (Term.app2 Term.pair
          (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz))))
          (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz))))).subst0 s
      = negAt f s := by
  simp only [negAt, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
    Term.app2, cauchyState_subst, neg_R_closed_subst, subst_subst0_map_weaken, closed_subst]

/-- **`cauchyfy` and negation run in lockstep.** At every index the negated sequence's state
is the original's with the value negated and the flag copied verbatim.

Three cases, exactly as in `cauchy_inv`: the flag was already set (both freeze), the flag is
clear and the check passes (both advance, to `neg_Q (f (n+1))` and `f (n+1)`), or the flag is
clear and the check fails (both trip, freezing the values they already hold). The checks agree
by `neg_check_sg`, which is the only step that is not bookkeeping. -/
def cauchyState_neg (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat
        (Formula.eq0 (Term.cauchyState (.app Term.neg_R f.weaken) (.var .vz))
          (Term.app2 Term.pair
            (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz))))
            (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz)))))) := by
  let fw : Term F (Ty.nat :: Γ) (realTy ι) := f.weaken
  let gw : Term F (Ty.nat :: Γ) (realTy ι) := .app Term.neg_R fw
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let V : Term F (Ty.nat :: Γ) Ty.nat := .app Term.fst_pair (Term.cauchyState fw nv)
  let Φ : Term F (Ty.nat :: Γ) Ty.nat := .app Term.snd_pair (Term.cauchyState fw nv)
  pmode
  pinduction
  · -- base: both states are their bases, and `neg_R f 0 =₀ neg_Q (f 0)`
    canorm
    prw (cVal_zero f)
    prw (cFlag_zero f)
    pthm (qtrans (cauchyState_zero (.app Term.neg_R f))
      (pair_l_nat Term.zero (neg_R_apply f Term.zero)))
  · pforall
    pintro ih
    canorm
    pfrom hinv := cauchy_inv_at fw nv
    pcases hinv with hL | hR
    · pdestruct hL with h0 _hv
      phave hsnd0 : Formula.eq0 (.app Term.snd_pair (Term.cauchyState gw nv)) Term.zero
      · prwby ih
        prw (snd_pair_pair (.app Term.neg_Q V) Φ)
        pexact h0
      pfrom hsg := sg_bar_cases (Term.cauchy_check_at fw nv)
      pcases hsg with hs1 | hs0
      · -- the check passes: both advance
        phave hsgn : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at gw nv)) (.app .succ .zero)
        · prw (neg_check_sg fw nv)
          pexact hs1
        pconj hsnd0 hsgn with hbn
        papplym (cauchyState_advance gw nv) in hbn with hgn
        pconj h0 hs1 with hbf
        papplym (cauchyState_advance fw nv) in hbf with hfn
        prwby hgn
        prwby hfn
        prw (fst_pair_pair (.app fw (.app .succ nv)) Term.zero)
        prw (snd_pair_pair (.app fw (.app .succ nv)) Term.zero)
        prw (neg_R_apply fw (.app .succ nv))
        prefl
      · -- the check fails: both trip, and both values freeze where they are
        phave hsgn : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at gw nv)) Term.zero
        · prw (neg_check_sg fw nv)
          pexact hs0
        pconj hsnd0 hsgn with hbn
        papplym (cauchyState_trip gw nv) in hbn with hgn
        pconj h0 hs0 with hbf
        papplym (cauchyState_trip fw nv) in hbf with hfn
        prwby hgn
        prwby hfn
        prw (fst_pair_pair V (.app .succ Term.zero))
        prw (snd_pair_pair V (.app .succ Term.zero))
        prwby ih
        prw (fst_pair_pair (.app Term.neg_Q V) Φ)
        prefl
    · -- already tripped: both states freeze
      phave hsnd1 : Formula.eq0
          (.app Term.snd_pair (Term.cauchyState gw nv)) (.app .succ .zero)
      · prwby ih
        prw (snd_pair_pair (.app Term.neg_Q V) Φ)
        pexact hR
      papplym (cauchyState_frozen gw nv) in hsnd1 with hgn
      papplym (cauchyState_frozen fw nv) in hR with hfn
      prwby hgn
      prwby hfn
      pexact ih

/-- The lockstep claim at an explicit index. -/
def cauchyState_neg_at (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises (negAt f s) :=
  negF_subst0 f s ▸ Derivable.mp (cauchyState_neg f) (.forall_ax s)

/-- **`(neg_R f)^(k) =₀ neg_Q (f̂(k))`** — cauchyfication commutes with negation, on the nose.
-/
def cauchyfy_neg (f : Term F Γ (realTy ι)) (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.neg_R f) k)
        (.app Term.neg_Q (Term.app2 Term.cauchyfy f k))) :=
  qtrans (cauchyfy_unfold (.app Term.neg_R f) k)
    (qtrans (fst_pair_congr (cauchyState_neg_at f k))
      (qtrans (fst_pair_pair
          (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f k)))
          (.app Term.snd_pair (Term.cauchyState f k)))
        (neg_Q_nat (Derivable.mp (cauchyfy_unfold f k) Derivable.sym0))))

/-- `u =_ℝ 0_ℝ` for any `u` whose cauchyfication is `f̂(·+2) +ℚ (−ℚ f̂(·+2))`.

Once `cauchyfy_neg` has put the sum in that shape there is no estimate left at all: the sum is
`eq_Q`-zero outright, and `0_ℚ <ℚ 2^{-n}`. -/
private def add_neg_R_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
            (.app .succ (.app .succ (.var .vz)))))))) :
    Derivable F al Premises (eq_R u Term.zero_R) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let A2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let S  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q A2 (.app Term.neg_Q A2)
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  pmode
  pforall
  canorm
  prw hu
  prw (cauchyfy_zero_R s1)
  papplym (lt_Q_congr Term.zero_Q P
    (.app Term.abs_Q (Term.app2 Term.sub_Q S Term.zero_Q)) P
    (eqQsym (eqQtrans (abs_Q_congr (eqQtrans (sub_Q_zero_Q S) (add_Q_neg_inst A2)))
      abs_Q_zero_Q))
    (eq_Q_refl_inst P))
  pthm (zero_lt_pow2neg_Q (.var .vz))

/-- `f +_ℝ neg_R(f) =_ℝ 0_ℝ`, at an explicit real. -/
def add_neg_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.add_R f (.app Term.neg_R f)) Term.zero_R) :=
  add_neg_R_gen f (Term.app2 Term.add_R f (.app Term.neg_R f)) (by
    rw [add_R_app_weaken, neg_R_app_weaken]
    exact qtrans
      (cauchyfy_add_R f.weaken (.app Term.neg_R f.weaken) (.app .succ (.var .vz)))
      (addQ_r_nat _ (cauchyfy_neg f.weaken (.app .succ (.app .succ (.var .vz))))))

/-- ⊢ ∀f : ℝ. f +_ℝ neg_R(f) =_ℝ 0_ℝ -/
def add_neg_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz)
                (.app Term.neg_R (.var .vz)))
              Term.zero_R)) :=
  univ_gen (add_neg_R_core (.var .vz))

-- ── `cauchyfy` respects pointwise `=_ℚ` ─────────────────────────────────────
--
-- This is REALS_PLAN §0.2's second option, the one it called out of reach: "an `eq_Q`-level
-- congruence for `cauchyfy`: pointwise `f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n`… an induction carrying an
-- object-level hypothesis, so it needs `seq_induction` and the weakened-hypothesis plumbing".
--
-- It needs neither. The pointwise hypothesis is taken as a **Lean-level schema** — a function
-- from index terms to derivations — so it is available at whatever index each case of the
-- induction asks for, and nothing has to be carried through the induction except the
-- invariant itself. Plain `pinduction` suffices, exactly as for `cauchyState_neg`; that lemma
-- is this one specialised to `v := neg_R u`, where the value halves happen to agree on the
-- nose so the first conjunct could be stated with `=₀`.
--
-- The invariant is a conjunction because the two halves of the state behave differently: the
-- **values** agree only up to `=_ℚ`, but the **flags** must agree on the nose, since
-- `cauchyState_advance`/`_trip` branch on them. `check_sg_congr` is what keeps the flags in
-- step, and it is the only step that is not bookkeeping.

/-- If `u` and `v` agree at `n` and `n+1` up to `=_ℚ`, their Cauchy checks agree **as bits**.
The generic form of `neg_check_sg`; `sg_bar_congr_iff` is again where the work happens. -/
private def check_sg_congr (u v : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat)
    (hn : Derivable F al Premises (eq_Q (.app u n) (.app v n)))
    (hn1 : Derivable F al Premises
      (eq_Q (.app u (.app .succ n)) (.app v (.app .succ n)))) :
    Derivable F al Premises
      (Formula.eq0
        (.app Term.sg_bar (Term.cauchy_check_at u n))
        (.app Term.sg_bar (Term.cauchy_check_at v n))) := by
  let A : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (.app u n) (.app u (.app .succ n)))
  let B : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (.app v n) (.app v (.app .succ n)))
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  have hAB : Derivable F al Premises (eq_Q A B) := abs_Q_congr (sub_Q_congr hn hn1)
  pmode
  papplym (sg_bar_congr_iff (Term.app2 Term.lt_Q_dec A P) (Term.app2 Term.lt_Q_dec B P))
  psplit
  · pthm (lt_Q_congr A P B P hAB (eq_Q_refl_inst P))
  · pthm (lt_Q_congr B P A P (eqQsym hAB) (eq_Q_refl_inst P))

/-- **The `cauchyfy` recursions of two pointwise-`=_ℚ` sequences run in step**: equal flags,
and values equal up to `=_ℚ`. -/
def cauchyState_congr (u v : Term F Γ (realTy ι))
    (h0 : Derivable F al Premises (eq_Q (.app u .zero) (.app v .zero)))
    (hS : ∀ x : Term F (Ty.nat :: Γ) Ty.nat,
      Derivable F al Premises (eq_Q (.app u.weaken x) (.app v.weaken x))) :
    Derivable F al Premises
      (Formula.all Ty.nat
        (eq_Q (.app Term.fst_pair (Term.cauchyState u.weaken (.var .vz)))
              (.app Term.fst_pair (Term.cauchyState v.weaken (.var .vz)))
          ∧ᶠ Formula.eq0
              (.app Term.snd_pair (Term.cauchyState u.weaken (.var .vz)))
              (.app Term.snd_pair (Term.cauchyState v.weaken (.var .vz))))) := by
  let uw : Term F (Ty.nat :: Γ) (realTy ι) := u.weaken
  let vw : Term F (Ty.nat :: Γ) (realTy ι) := v.weaken
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ nv
  pmode
  pinduction
  · canorm
    psplit
    · prw (cVal_zero u)
      prw (cVal_zero v)
      pthm h0
    · prw (cFlag_zero u)
      prw (cFlag_zero v)
      prefl
  · pforall
    pintro ih
    canorm
    pdestruct ih with ihv ihf
    pfrom hinv := cauchy_inv_at uw nv
    pcases hinv with hL | hR
    · pdestruct hL with h0u _hval
      phave h0v : Formula.eq0 (.app Term.snd_pair (Term.cauchyState vw nv)) Term.zero
      · psym in ihf with ihfs
        prwby ihfs
        pexact h0u
      pfrom hsg := sg_bar_cases (Term.cauchy_check_at uw nv)
      pcases hsg with hs1 | hs0
      · -- the check passes for `u`, hence for `v`: both advance
        phave hsgv : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at vw nv)) (.app .succ .zero)
        · prw (check_sg_congr vw uw nv (eqQsym (hS nv)) (eqQsym (hS n1)))
          pexact hs1
        pconj h0u hs1 with hbu
        papplym (cauchyState_advance uw nv) in hbu with hun
        pconj h0v hsgv with hbv
        papplym (cauchyState_advance vw nv) in hbv with hvn
        -- `prwby` needs an equation, so the conjunction is split before it is used
        psplit
        · prwby hun
          prwby hvn
          prw (fst_pair_pair (.app uw n1) Term.zero)
          prw (fst_pair_pair (.app vw n1) Term.zero)
          pthm (hS n1)
        · prwby hun
          prwby hvn
          prw (snd_pair_pair (.app uw n1) Term.zero)
          prw (snd_pair_pair (.app vw n1) Term.zero)
          prefl
      · -- the check fails for `u`, hence for `v`: both trip, both values freeze
        phave hsgv : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at vw nv)) Term.zero
        · prw (check_sg_congr vw uw nv (eqQsym (hS nv)) (eqQsym (hS n1)))
          pexact hs0
        pconj h0u hs0 with hbu
        papplym (cauchyState_trip uw nv) in hbu with hun
        pconj h0v hsgv with hbv
        papplym (cauchyState_trip vw nv) in hbv with hvn
        psplit
        · prwby hun
          prwby hvn
          prw (fst_pair_pair (.app Term.fst_pair (Term.cauchyState uw nv))
            (.app .succ Term.zero))
          prw (fst_pair_pair (.app Term.fst_pair (Term.cauchyState vw nv))
            (.app .succ Term.zero))
          pexact ihv
        · prwby hun
          prwby hvn
          prw (snd_pair_pair (.app Term.fst_pair (Term.cauchyState uw nv))
            (.app .succ Term.zero))
          prw (snd_pair_pair (.app Term.fst_pair (Term.cauchyState vw nv))
            (.app .succ Term.zero))
          prefl
    · -- already tripped: both states freeze
      phave hRv : Formula.eq0
          (.app Term.snd_pair (Term.cauchyState vw nv)) (.app .succ .zero)
      · psym in ihf with ihfs
        prwby ihfs
        pexact hR
      papplym (cauchyState_frozen uw nv) in hR with hun
      papplym (cauchyState_frozen vw nv) in hRv with hvn
      psplit
      · prwby hun
        prwby hvn
        pexact ihv
      · prwby hun
        prwby hvn
        pexact ihf

private theorem congF_subst0 (u v : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    ((eq_Q (.app Term.fst_pair (Term.cauchyState u.weaken (.var .vz)))
           (.app Term.fst_pair (Term.cauchyState v.weaken (.var .vz)))
        ∧ᶠ Formula.eq0
            (.app Term.snd_pair (Term.cauchyState u.weaken (.var .vz)))
            (.app Term.snd_pair (Term.cauchyState v.weaken (.var .vz)))).subst0 s)
      = (eq_Q (.app Term.fst_pair (Term.cauchyState u s))
              (.app Term.fst_pair (Term.cauchyState v s))
          ∧ᶠ Formula.eq0 (.app Term.snd_pair (Term.cauchyState u s))
              (.app Term.snd_pair (Term.cauchyState v s))) := by
  simp only [eq_Q, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
    Term.app2, cauchyState_subst, subst_subst0_map_weaken, closed_subst]

/-- **`cauchyfy` respects pointwise `=_ℚ`.** REALS_PLAN §0.2's `cauchyfy_congr_eqQ`. -/
def cauchyfy_congr (u v : Term F Γ (realTy ι))
    (h0 : Derivable F al Premises (eq_Q (.app u .zero) (.app v .zero)))
    (hS : ∀ x : Term F (Ty.nat :: Γ) Ty.nat,
      Derivable F al Premises (eq_Q (.app u.weaken x) (.app v.weaken x)))
    (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.cauchyfy u k) (Term.app2 Term.cauchyfy v k)) := by
  have hst := congF_subst0 u v k ▸
    Derivable.mp (cauchyState_congr u v h0 hS) (.forall_ax k)
  pmode
  prw (cauchyfy_unfold u k)
  prw (cauchyfy_unfold v k)
  pfrom hc := hst
  pdestruct hc with h1 _h2
  pexact h1

/-- **`=_ℚ` at every cauchyfied index is `=_ℝ`.** No estimate: the difference is `=_ℚ`-zero
and `0_ℚ <_ℚ 2^{-n}`. Stated on abstract `u`, `v` so that no `prw` ever sees a composed real
— the `Term.add_R` / `Term.mul_R` delta-expansion trap. -/
def eq_R_of_cauchyfy_eqQ (u v : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
            (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz))))) :
    Derivable F al Premises (eq_R u v) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let X  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy u.weaken s1
  let Y  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy v.weaken s1
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  pmode
  pforall
  canorm
  papplym (lt_Q_congr Term.zero_Q P (.app Term.abs_Q (Term.app2 Term.sub_Q X Y)) P
    (eqQsym (eqQtrans (abs_Q_congr (sub_Q_congr h (eq_Q_refl_inst Y)))
      (abs_Q_sub_self Y)))
    (eq_Q_refl_inst P))
  pthm (zero_lt_pow2neg_Q (.var .vz))

end OrderedFieldAxioms

end Metatheorems
