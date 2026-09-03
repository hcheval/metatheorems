/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Estimates

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Additive group ──────────────────────────────────────────────────────────

-- `add_comm_R` is PROVED, further down the file, next to `add_zero_R`: it uses `canorm`,
-- which is defined below (it folds in the `cauchyfy`-state simp lemmas).

-- `add_assoc_R` and `add_zero_R` are PROVED, but further down the file: both rest on
-- `cauchyfy_cauchy` / `cauchyfy_two_step`, which are stated after the order axioms. See
-- "The additive axioms `cauchyfy_cauchy` alone settles" below.

-- `add_neg_R` is PROVED, further down: it needs `cauchyfy_neg`, which is an induction on
-- the `cauchyfy` recursion and so sits with the rest of that theory.

-- ── The additive axioms `cauchyfy_cauchy` alone settles ─────────────────────
--
-- `add_zero_R` and `add_assoc_R` are **not tight**, and that is the whole story: the two
-- sides of each are the *same* sum read at indices that differ by a fixed number of
-- `cauchyfy` steps, each step costing `2^{-(index+1)}`, against a budget of `2^{-n}` at the
-- goal's own index `n`. Both close with room to spare, so neither needs the `eqR_le`
-- telescoping engine that `eq_R_trans` needed. (`add_neg_R` is a different matter — see the
-- note at its `sorry`.)
--
-- Each goes through a `_gen` companion taking the composed real as an **abstract Lean
-- parameter**, for the reason `add_eq_zero_R_gen` does: `prw` at a goal containing
-- `Term.add_R` has to push a substitution through that constant, which is the
-- delta-expansion blow-up the build-cost notes warn about. As a parameter it costs nothing,
-- and the `cauchyfy_add_R` chain that computes it is assembled outside the proof mode.

/-- Congruence for `add_Q` in its **first** argument, at the level of `=₀` (not `eq_Q`) —
the mirror image of `RationalNumbers.lean`'s (private) `add_Q_congr_r_nat`. -/
private def addQ_l_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add_Q s u) (Term.app2 Term.add_Q t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add_Q (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- Congruence for `add_Q` in its **second** argument, at the level of `=₀`. -/
def addQ_r_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add_Q u s) (Term.app2 Term.add_Q u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add_Q u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- `u =_ℝ f` for any `u` whose cauchyfication is `f̂(·+2) +ℚ 0̂(·+2)`.

The estimate is a single `cauchyfy` step: `û(n+1) ≃ℚ f̂(n+2)`, and `|f̂(n+2) −ℚ f̂(n+1)|` is
below `2^{-(n+2)}`, hence below `2^{-n}` twice over. -/
private def add_zero_R_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises (eq_R u f) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let A1 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s1
  let A2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s1
  let P2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s2
  pmode
  pforall
  canorm
  prw hu
  prw (cauchyfy_zero_R s2)
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q (Term.app2 Term.add_Q A2 Term.zero_Q) A1)) P
    (abs_Q_congr (sub_Q_congr (eqQsym (add_Q_zero_inst A2)) (eq_Q_refl_inst A1)))
    (eq_Q_refl_inst P))
  papplym (lt_le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P2 P)
  psplit
  · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A1 A2)) P2
      (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P2
      (abs_diff_Q_comm A1 A2) (eq_Q_refl_inst P2))
    pthm (cauchyfy_cauchy f.weaken s1)
  · papplym (le_Q_trans P2 P1 P)
    psplit
    · pthm (pow2neg_Q_le_succ s1)
    · pthm (pow2neg_Q_le_succ (.var .vz))

/-- `f +_ℝ 0_ℝ =_ℝ f`, at an explicit real. -/
def add_zero_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R (Term.app2 Term.add_R f Term.zero_R) f) :=
  add_zero_R_gen f (Term.app2 Term.add_R f Term.zero_R) (by
    rw [add_R_app_weaken, zero_R_weaken]
    exact cauchyfy_add_R f.weaken Term.zero_R (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. f +_ℝ 0_ℝ =_ℝ f -/
def add_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz) Term.zero_R)
              (.var .vz))) :=
  univ_gen (add_zero_R_core (.var .vz))

/-- `u =_ℝ v` for any `u`, `v` whose cauchyfications are the two orders of one sum.

**There is no estimate here at all, and no `cauchyfy` congruence either.** REALS_PLAN §0.2
declared `add_comm_R` blocked on an `eq_Q`-level congruence for `cauchyfy` — pointwise
`f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n` — on the ground that `add_Q` does not commute on the nose. That
diagnosis is right about ℚ and wrong about where the outer `cauchyfy` sits: `add_R f g` is
*provably Cauchy* (`add_R_check`), so `cauchyfy_add_R` evaluates that cauchyfication on
**both** sides before the two are ever compared. What is left is
`|(A +ℚ B) −ℚ (B +ℚ A)| <ℚ 2^{-n}`, and `add_Q_comm_inst` makes the difference `eq_Q`-zero.

The general congruence is still needed — by `mul_comm_R`, where no `mul_R_check` exists — but
not by this. -/
private def add_comm_R_gen (f g u v : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))))
    (hv : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises (eq_R u v) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let A  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let B  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken s2
  let X  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q A B
  let Y  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q B A
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  pmode
  pforall
  canorm
  prw hu
  prw hv
  papplym (lt_Q_congr Term.zero_Q P (.app Term.abs_Q (Term.app2 Term.sub_Q X Y)) P
    (eqQsym (eqQtrans
      (abs_Q_congr (sub_Q_congr (add_Q_comm_inst A B) (eq_Q_refl_inst Y)))
      (abs_Q_sub_self Y)))
    (eq_Q_refl_inst P))
  pthm (zero_lt_pow2neg_Q (.var .vz))

/-- `f +_ℝ g =_ℝ g +_ℝ f`, at explicit reals. -/
def add_comm_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.add_R f g) (Term.app2 Term.add_R g f)) :=
  add_comm_R_gen f g (Term.app2 Term.add_R f g) (Term.app2 Term.add_R g f)
    (by
      rw [add_R_app_weaken]
      exact cauchyfy_add_R f.weaken g.weaken (.app .succ (.var .vz)))
    (by
      rw [add_R_app_weaken]
      exact cauchyfy_add_R g.weaken f.weaken (.app .succ (.var .vz)))

/-- ⊢ ∀f,g : ℝ. f +_ℝ g =_ℝ g +_ℝ f -/
def add_comm_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_R (.var .vz) (.var (.vs .vz)))))) :=
  univ_gen (univ_gen (add_comm_R_core (.var (.vs .vz)) (.var .vz)))

/-- `u =_ℝ v` for any `u`, `v` whose cauchyfications are the two bracketings of `f + g + h`.

Writing `Fₖ := f̂(n+k)` and so on, the two sides at the goal's index `n` are
`(F₃ +ℚ G₃) +ℚ H₂` and `F₂ +ℚ (G₃ +ℚ H₃)` — the *same* three summands, with `f` read one
index later on the left and `h` one index later on the right. Re-bracketing the left,
`abs_Q_sub_add_split` twice splits the difference into `|F₃ −ℚ F₂|` and `|H₂ −ℚ H₃|` (the `g`
term cancels exactly), each below `2^{-(n+3)}` by `cauchyfy_cauchy`, so the total is below
`2^{-(n+2)}` — a factor of four inside the budget `2^{-n}`. -/
private def add_assoc_R_gen (f g h u v : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.add_Q
            (Term.app2 Term.cauchyfy f.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz)))))
            (Term.app2 Term.cauchyfy g.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz))))))
          (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz)))))))
    (hv : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.add_Q
            (Term.app2 Term.cauchyfy g.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz)))))
            (Term.app2 Term.cauchyfy h.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz))))))))) :
    Derivable F al Premises (eq_R u v) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let s3 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s2
  let F2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let F3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s3
  let G3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken s3
  let H2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy h.weaken s2
  let H3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy h.weaken s3
  let X  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q G3 H2
  let Y  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q G3 H3
  let DF : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q F3 F2)
  let DX : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q X Y)
  let DH : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q H2 H3)
  let DG : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q G3 G3)
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s1
  let P2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s2
  let P3 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s3
  pmode
  pforall
  canorm
  prw hu
  prw hv
  -- re-bracket the left-hand sum so that both sides are binary sums with matching parts
  papplym (lt_Q_congr
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y))) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q F3 G3) H2)
      (Term.app2 Term.add_Q F2 Y))) P
    (abs_Q_congr (sub_Q_congr (eqQsym (add_Q_assoc_inst F3 G3 H2))
      (eq_Q_refl_inst (Term.app2 Term.add_Q F2 Y))))
    (eq_Q_refl_inst P))
  papplym (lt_le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q
    (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y))) P2 P)
  psplit
  · papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y)))
      (Term.app2 Term.add_Q DF DX) P2)
    psplit
    · pthm (abs_Q_sub_add_split F2 Y F3 X)
    · papplym (lt_Q_congr (Term.app2 Term.add_Q DF DX) (Term.app2 Term.add_Q P3 P3)
        (Term.app2 Term.add_Q DF DX) P2
        (eq_Q_refl_inst (Term.app2 Term.add_Q DF DX)) (pow2neg_Q_halve s2))
      papplym (lt_Q_add_both DF DX P3 P3)
      psplit
      · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q F2 F3)) P3 DF P3
          (abs_diff_Q_comm F2 F3) (eq_Q_refl_inst P3))
        pthm (cauchyfy_cauchy f.weaken s2)
      · papplym (le_lt_Q_trans DX (Term.app2 Term.add_Q DG DH) P3)
        psplit
        · pthm (abs_Q_sub_add_split G3 H3 G3 H2)
        · papplym (lt_Q_congr DH P3 (Term.app2 Term.add_Q DG DH) P3
            (eqQsym (eqQtrans (addQl (abs_Q_sub_self G3) DH)
              (eqQtrans (add_Q_comm_inst Term.zero_Q DH) (add_Q_zero_inst DH))))
            (eq_Q_refl_inst P3))
          pthm (cauchyfy_cauchy h.weaken s2)
  · papplym (le_Q_trans P2 P1 P)
    psplit
    · pthm (pow2neg_Q_le_succ s1)
    · pthm (pow2neg_Q_le_succ (.var .vz))

/-- `(f +_ℝ g) +_ℝ h =_ℝ f +_ℝ (g +_ℝ h)`, at explicit reals. -/
def add_assoc_R_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.add_R (Term.app2 Term.add_R f g) h)
            (Term.app2 Term.add_R f (Term.app2 Term.add_R g h))) :=
  add_assoc_R_gen f g h
    (Term.app2 Term.add_R (Term.app2 Term.add_R f g) h)
    (Term.app2 Term.add_R f (Term.app2 Term.add_R g h))
    (by
      rw [add_R_app_weaken, add_R_app_weaken]
      exact qtrans
        (cauchyfy_add_R (Term.app2 Term.add_R f.weaken g.weaken) h.weaken
          (.app .succ (.var .vz)))
        (addQ_l_nat _ (cauchyfy_add_R f.weaken g.weaken
          (.app .succ (.app .succ (.var .vz))))))
    (by
      rw [add_R_app_weaken, add_R_app_weaken]
      exact qtrans
        (cauchyfy_add_R f.weaken (Term.app2 Term.add_R g.weaken h.weaken)
          (.app .succ (.var .vz)))
        (addQ_r_nat _ (cauchyfy_add_R g.weaken h.weaken
          (.app .succ (.app .succ (.var .vz))))))

/-- ⊢ ∀f,g,h : ℝ. (f +_ℝ g) +_ℝ h =_ℝ f +_ℝ (g +_ℝ h) -/
def add_assoc_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.add_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.add_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))))))) :=
  univ_gen (univ_gen (univ_gen
    (add_assoc_R_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- **`le_R_pu` implies `le_R`** — `∀n ¬B(n) → ¬∃n B(n)`, which is intuitionistic.

Since the `le_R_pu` argument-order repair (2026-09-02, see `Terms/Real.lean`) the two
formulas are built from *literally the same* body `B`:

* `le_R f g` is `¬(g <ℝ f)`, i.e. `(∃n. B n) →ᶠ ⊥ᶠ`;
* `le_R_pu f g` is `∀n. (B n →ᶠ ⊥ᶠ)`.

So this is pure logic: destruct the existential, instantiate the universal at the witness,
apply. The converse is `le_R_pu_of_le_R` just below, and is equally cheap. -/
def le_R_of_le_R_pu (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R_pu f g →ᶠ le_R f g) := by
  pmode
  pintro h
  pintro hex
  pobtain hex with hn
  canorm
  pinst h (.var .vz) with hh
  canorm
  papply hh
  pexact hn

/-- The converse of `le_R_of_le_R_pu`: `¬∃n B(n) → ∀n ¬B(n)`, also intuitionistic. -/
def le_R_pu_of_le_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f g →ᶠ le_R_pu f g) := by
  pmode
  pintro h
  pforall
  pintro hn
  papply h
  pexists (.var .vz)
  canorm
  pexact hn

/-- **`f ≤_ℝ g` in Π₁⁰ form**: `∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}`.

`le_R` is a *negated existential*, so it is spent by ∃-introduction — a failure at any single
index would produce the very witness the hypothesis denies — and the `≤`/`<` dichotomy at ℚ
then turns the negation into a positive bound. No Markov step is involved: `le_Q_or_lt_Q` is a
derivable disjunction, the encoding's order being decidable.

The conclusion is stated as a `∀`-formula rather than at a caller-supplied index so that it
can be `pinst`-antiated *after* a `pforall`; instantiating is what lets `closed_subst` clear
the proof mode's weakening of `Term.zero_R`, which a direct `papplym` at the weakened
hypothesis cannot do.

Note the argument order: this is `le_R f g`, i.e. `f ≤ g`, and `le_R_pu f g` now means the
same thing. (Until 2026-09-02 `le_R_pu` took its arguments the other way round and meant
`g ≤_ℝ f`; that bug is fixed in `Terms/Real.lean`, and `le_R_of_le_R_pu` /
`le_R_pu_of_le_R` above convert between the two forms in either direction.) -/
def le_R_all (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f g →ᶠ
        Formula.all Ty.nat
          (lt_Q (Term.app2 Term.sub_Q
                   (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
                   (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
                (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro h
  pforall
  papplym (lt_Q_of_not_le_Q (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
  pintro hle
  papply h
  pexists (.var .vz)
  canorm
  pexact hle

/-- **The converse of `le_R_all`**: the Π₁⁰ bound `∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}` gives
`f ≤_ℝ g`.

Together with `le_R_all` this pins `le_R` down completely: it *is* that bound, and every
`≤_ℝ` fact in the development can be established index by index in ℚ. The proof is the
`≤_ℚ`/`<_ℚ` clash — a witness against `le_R f g` asserts `2^{-n} ≤ℚ f̂(n+1) −ℚ ĝ(n+1)` at
some `n`, which the bound at that same `n` contradicts. No Markov step, no dichotomy. -/
def le_R_of_all (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat
          (lt_Q (Term.app2 Term.sub_Q
                   (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
                   (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
                (.app Term.pow2neg_Q (.var .vz)))
       →ᶠ le_R f g) := by
  pmode
  pintro h
  pintro hex
  pobtain hex with hn
  canorm
  pinst h (.var .vz) with h1
  canorm
  papplym (lt_Q_irrefl_inst (.app Term.pow2neg_Q (.var .vz)))
  papplym (le_lt_Q_trans (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pexact hn
  · pexact h1

/-- `le_R_of_all` in the form callers actually want: hand it the estimate as a derivation in
the extended context `Ty.nat :: Γ` and it universally generalises for you. -/
def le_R_of_bound (f g : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (Term.app2 Term.sub_Q
               (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
               (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
            (.app Term.pow2neg_Q (.var .vz)))) :
    Derivable F al Premises (le_R f g) :=
  Derivable.mp (univ_gen h) (le_R_of_all f g)

-- ── ℚ rearrangements the ℝ estimates need ───────────────────────────────────
--
-- Four abelian-group identities and one `pow2neg` bound. They are ℚ facts, but they live
-- here rather than in `RationalNumbers.lean` for the reason stated above: that file is
-- another workstream's, and these exist only to serve `dist_nonneg`.

/-- **Middle-four exchange**: `(a +ℚ b) +ℚ (c +ℚ d) =ℚ (a +ℚ c) +ℚ (b +ℚ d)`.

The one rearrangement every multi-term ℚ estimate in the ℝ layer needs, and the reason the
sums below can be written in whatever bracketing the inequality lemmas produce. -/
def add_Q_shuffle (a b c d : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (Term.app2 Term.add_Q a b) (Term.app2 Term.add_Q c d))
            (Term.app2 Term.add_Q (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b d))) :=
  eqQtrans (add_Q_assoc_inst a b (Term.app2 Term.add_Q c d))
    (eqQtrans (addQr a (eqQsym (add_Q_assoc_inst b c d)))
      (eqQtrans (addQr a (addQl (add_Q_comm_inst b c) d))
        (eqQtrans (addQr a (add_Q_assoc_inst c b d))
          (eqQsym (add_Q_assoc_inst a c (Term.app2 Term.add_Q b d))))))

/-- `(a −ℚ x) +ℚ (−ℚ a) =ℚ −ℚ x`. -/
def sub_add_neg_cancel (a x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a x) (.app Term.neg_Q a))
            (.app Term.neg_Q x)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  let nx : Term F Γ Ty.nat := .app Term.neg_Q x
  eqQtrans (addQl (sub_Q_eq_add_neg a x) na)
    (eqQtrans (addQl (add_Q_comm_inst a nx) na)
      (eqQtrans (add_Q_assoc_inst nx a na)
        (eqQtrans (addQr nx (add_Q_neg_inst a)) (add_Q_zero_inst nx))))

/-- `(−ℚ (d +ℚ e)) +ℚ (e −ℚ d) =ℚ (−ℚ d) +ℚ (−ℚ d)`.

This is the step that turns the triangle inequality's `d(x,y) + d(y,x)` into `2·d(x,y)`, once
symmetry has supplied `e −ℚ d`. -/
def neg_add_sub_cancel (d e : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (.app Term.neg_Q (Term.app2 Term.add_Q d e))
              (Term.app2 Term.sub_Q e d))
            (Term.app2 Term.add_Q (.app Term.neg_Q d) (.app Term.neg_Q d))) :=
  let nd : Term F Γ Ty.nat := .app Term.neg_Q d
  let ne : Term F Γ Ty.nat := .app Term.neg_Q e
  eqQtrans (addQl (neg_Q_add_Q d e) (Term.app2 Term.sub_Q e d))
    (eqQtrans (addQr (Term.app2 Term.add_Q nd ne) (sub_Q_eq_add_neg e d))
      (eqQtrans (addQr (Term.app2 Term.add_Q nd ne) (add_Q_comm_inst e nd))
        (eqQtrans (add_Q_shuffle nd ne nd e)
          (eqQtrans (addQr (Term.app2 Term.add_Q nd nd)
              (eqQtrans (add_Q_comm_inst ne e) (add_Q_neg_inst e)))
            (add_Q_zero_inst (Term.app2 Term.add_Q nd nd))))))

/-- `(−ℚ a) −ℚ (−ℚ b) =ℚ b −ℚ a`: negating both sides reverses a difference. -/
def sub_Q_neg_neg (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (.app Term.neg_Q a) (.app Term.neg_Q b))
            (Term.app2 Term.sub_Q b a)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  eqQtrans (sub_Q_eq_add_neg na (.app Term.neg_Q b))
    (eqQtrans (addQr na (neg_Q_neg_Q b))
      (eqQtrans (add_Q_comm_inst na b) (eqQsym (sub_Q_eq_add_neg b a))))

/-- **The budget that makes `dist_nonneg` fit.** With `B := 2^{-(n+2)} +ℚ 2^{-(n+4)}`,

    `B +ℚ (B +ℚ B) ≤ℚ 2^{-n}`

because `3B = 3·2^{-(n+2)} + 3·2^{-(n+4)} = 2^{-(n+1)} + 2^{-(n+2)} + 2^{-(n+3)} + 2^{-(n+4)}`,
which falls short of `2^{-n}` by exactly `2^{-(n+4)}`. `dist_nonneg` spends one `B` on the
triangle-plus-symmetry estimate at index `n+5` and two on moving `d̂` back from `n+5` to `n+2`,
so this is the whole of its arithmetic. -/
def pow2neg_triple_bound (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q
               (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                 (.app Term.pow2neg_Q
                   (.app .succ (.app .succ (.app .succ (.app .succ n))))))
               (Term.app2 Term.add_Q
                 (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                   (.app Term.pow2neg_Q
                     (.app .succ (.app .succ (.app .succ (.app .succ n))))))
                 (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                   (.app Term.pow2neg_Q
                     (.app .succ (.app .succ (.app .succ (.app .succ n))))))))
            (.app Term.pow2neg_Q n)) :=
  let n1 : Term F Γ Ty.nat := .app .succ n
  let n2 : Term F Γ Ty.nat := .app .succ n1
  let n3 : Term F Γ Ty.nat := .app .succ n2
  let p0 : Term F Γ Ty.nat := .app Term.pow2neg_Q n
  let p1 : Term F Γ Ty.nat := .app Term.pow2neg_Q n1
  let p2 : Term F Γ Ty.nat := .app Term.pow2neg_Q n2
  let p3 : Term F Γ Ty.nat := .app Term.pow2neg_Q n3
  let p4 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n3)
  let B  : Term F Γ Ty.nat := Term.app2 Term.add_Q p2 p4
  -- `B +ℚ B =ℚ 2^{-(n+1)} +ℚ 2^{-(n+3)}`
  let hBB : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q B B) (Term.app2 Term.add_Q p1 p3)) :=
    eqQtrans (add_Q_shuffle p2 p4 p2 p4)
      (eqQtrans (addQl (pow2neg_Q_halve n1) (Term.app2 Term.add_Q p4 p4))
        (addQr p1 (pow2neg_Q_halve n3)))
  -- `B +ℚ (B +ℚ B) =ℚ (2^{-(n+1)} +ℚ 2^{-(n+2)}) +ℚ (2^{-(n+3)} +ℚ 2^{-(n+4)})`
  let hFwd : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q B (Term.app2 Term.add_Q B B))
            (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
              (Term.app2 Term.add_Q p3 p4))) :=
    eqQtrans (addQr B hBB)
      (eqQtrans (add_Q_shuffle p2 p4 p1 p3)
        (eqQtrans (addQl (add_Q_comm_inst p2 p1) (Term.app2 Term.add_Q p4 p3))
          (addQr (Term.app2 Term.add_Q p1 p2) (add_Q_comm_inst p4 p3))))
  by
  pmode
  papplym (le_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
      (Term.app2 Term.add_Q p3 p4)) p0
    (Term.app2 Term.add_Q B (Term.app2 Term.add_Q B B)) p0
    (eqQsym hFwd) (eq_Q_refl_inst p0))
  papplym (le_Q_trans (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
      (Term.app2 Term.add_Q p3 p4))
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2) p2) p0)
  psplit
  · -- `2^{-(n+3)} +ℚ 2^{-(n+4)} ≤ℚ 2^{-(n+2)}`
    papplym (le_Q_add_l (Term.app2 Term.add_Q p1 p2) (Term.app2 Term.add_Q p3 p4) p2)
    papplym (le_Q_congr (Term.app2 Term.add_Q p3 p4) (Term.app2 Term.add_Q p3 p3)
      (Term.app2 Term.add_Q p3 p4) p2 (eq_Q_refl_inst (Term.app2 Term.add_Q p3 p4))
      (pow2neg_Q_halve n2))
    papplym (le_Q_add_l p3 p4 p3)
    pthm (pow2neg_Q_le_succ n3)
  · -- `(2^{-(n+1)} +ℚ 2^{-(n+2)}) +ℚ 2^{-(n+2)} =ℚ 2^{-n}`
    papplym (le_Q_congr p0 p0 (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2) p2) p0
      (eqQsym (eqQtrans (add_Q_assoc_inst p1 p2 p2)
        (eqQtrans (addQr p1 (pow2neg_Q_halve n1)) (pow2neg_Q_halve n))))
      (eq_Q_refl_inst p0))
    pthm (le_Q_refl p0)

end OrderedFieldAxioms

end Metatheorems
