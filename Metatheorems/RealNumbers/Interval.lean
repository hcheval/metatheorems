/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.OrderBounds
import Metatheorems.RealNumbers.Bounds

namespace Metatheorems

/-!
# The `[0,1]` representation: `clamp01`

W-hyperbolic spaces have `W : X × X × [0,1] → X`, and `∀λ ∈ [0,1]` is a quantifier over a
*subset* of type 1, which the metatheorem cannot take. Kohlenbach's move is to represent
`[0,1]` so that **every** `f : ℕ → ℕ` codes an element of it, via a retraction `f ↦ λ̃(f)`
landing in `[0,1]` and identical (as a real) on codes already there. Then `∀λ∈[0,1] A(λ)`
is literally `∀f¹ A(λ̃ f)` — unrestricted, no side condition. The payoff is uniformity: every
element of `[0,1]` is majorized by one fixed function, so bounds extracted from a hyperbolic
space come out independent of `λ`.

Here `λ̃` is `clamp01`:

    clamp01_Q q  :=  if q ≤ℚ 0ℚ then 0ℚ else if 1ℚ ≤ℚ q then 1ℚ else q
    clamp01 f    :=  λ n. clamp01_Q (f̂ n)

and the four results are

1. `clamp01_check` / `cauchyfy_clamp01` — `clamp01 f` is Cauchy, via the ℚ-level
   1-Lipschitz fact `clamp01_Q_lip : |clamp01_Q a −ℚ clamp01_Q b| ≤ℚ |a −ℚ b|`;
2. `clamp01_nonneg : ∀f. 0ℝ ≤ℝ clamp01 f`;
3. `clamp01_le_one : ∀f. clamp01 f ≤ℝ 1ℝ`;
4. `clamp01_eq : ∀f. 0ℝ ≤ℝ f → f ≤ℝ 1ℝ → clamp01 f =ℝ f`.

No index shift is needed anywhere.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

-- Definitions

namespace Term

/-- Clamp a rational code into `[0,1]`:
`clamp01_Q q = if q ≤ℚ 0ℚ then 0ℚ else if 1ℚ ≤ℚ q then 1ℚ else q`.

`le_Q_dec a b` is `0` exactly when `a ≤ℚ b`, and `ite_nat b x y` is `x` at `b = 1`, `y` at
`b = 0`, so each test is `sg_bar` of a decision term. -/
def clamp01_Q {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 Term.ite_nat
      (.app Term.sg_bar (Term.app2 Term.le_Q_dec (.var .vz) Term.zero_Q))
      Term.zero_Q
      (Term.app3 Term.ite_nat
        (.app Term.sg_bar (Term.app2 Term.le_Q_dec Term.one_Q (.var .vz)))
        Term.one_Q
        (.var .vz)))

/-- The retraction `ℝ → [0,1]`: `clamp01 f n = clamp01_Q (f̂ n)`. No index shift — clamping
is 1-Lipschitz, so the Cauchy rate of `f̂` is inherited verbatim (`clamp01_check`). -/
def clamp01 {Γ : Ctx ι} : Term F Γ (realTy ι →ₜ realTy ι) :=
  Term.lam (Term.lam
    -- f = var (vs vz), n = var vz
    (.app Term.clamp01_Q (Term.app2 Term.cauchyfy (.var (.vs .vz)) (.var .vz))))

end Term

-- Closed-term substitution and weakening

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

@[simp] theorem clamp01_Q_closed_subst :
    (Term.clamp01_Q : Term F Γ _).subst σ = Term.clamp01_Q := by
  simp only [Term.clamp01_Q, Term.subst, Term.Subst.ext, Term.app2, Term.app3, closed_subst]

attribute [closed_subst] clamp01_Q_closed_subst

@[simp] theorem clamp01_closed_subst :
    (Term.clamp01 : Term F Γ _).subst σ = Term.clamp01 := by
  simp only [Term.clamp01, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift, closed_subst]

attribute [closed_subst] clamp01_closed_subst

end ClosedSubst

section Interval

variable {Γ : Ctx ι}

theorem clamp01_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.clamp01 : Term F Δ _).weaken (σ := ρ) = Term.clamp01 := by
  rw [Term.weaken, Term.rename_eq_subst]; exact clamp01_closed_subst _

theorem clamp01_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f : Term F Δ (realTy ι)) :
    (Term.app Term.clamp01 f).weaken (σ := ρ) = .app Term.clamp01 f.weaken := by
  show Term.app (Term.weaken Term.clamp01) f.weaken = _
  rw [clamp01_weaken]

private theorem one_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.one_R : Term F Δ (realTy ι)).weaken (σ := ρ) = Term.one_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_R_closed_subst _

-- Beta lemmas

/-- `clamp01_Q a =₀ ite_nat (sg_bar (le_Q_dec a 0ℚ)) 0ℚ (ite_nat (sg_bar (le_Q_dec 1ℚ a)) 1ℚ a)`
— the one beta step. -/
def clamp01_Q_apply (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.clamp01_Q a)
        (Term.app3 Term.ite_nat
          (.app Term.sg_bar (Term.app2 Term.le_Q_dec a Term.zero_Q))
          Term.zero_Q
          (Term.app3 Term.ite_nat
            (.app Term.sg_bar (Term.app2 Term.le_Q_dec Term.one_Q a))
            Term.one_Q
            a))) :=
  lam_correct_nf
    (Term.app3 Term.ite_nat
      (.app Term.sg_bar (Term.app2 Term.le_Q_dec (.var .vz) Term.zero_Q))
      Term.zero_Q
      (Term.app3 Term.ite_nat
        (.app Term.sg_bar (Term.app2 Term.le_Q_dec Term.one_Q (.var .vz)))
        Term.one_Q
        (.var .vz)) : Term F (Ty.nat :: Γ) Ty.nat)
    a (by qb_nf)

/-- `(clamp01 f)(x) =₀ clamp01_Q (f̂(x))` — the two beta steps of `clamp01`. -/
def clamp01_apply (f : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app (.app Term.clamp01 f) x)
        (.app Term.clamp01_Q (Term.app2 Term.cauchyfy f x))) :=
  lam2_correct_nf
    (.app Term.clamp01_Q (Term.app2 Term.cauchyfy (.var (.vs .vz)) (.var .vz))
      : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat)
    f x (by qb_nf)

-- Evaluating `clamp01_Q` under the three order hypotheses

/-- `b <ℚ a` makes the test `a ≤ℚ b` fail: `sg_bar (le_Q_dec a b) =₀ 0`. -/
private def sg_bar_le_dec_of_lt (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q b a →ᶠ Formula.eq0 (.app Term.sg_bar (Term.app2 Term.le_Q_dec a b)) .zero) := by
  pmode
  pintro h
  papplym (Derivable.mp (sg_bar_eq_zero_iff (Term.app2 Term.le_Q_dec a b)) and_proj2)
  pintro hle
  papplym (lt_Q_le_Q_absurd b a)
  psplit
  · pexact h
  · pexact hle

/-- `a ≤ℚ 0ℚ → clamp01_Q a =₀ 0ℚ`. -/
def clamp01_Q_of_le_zero (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a Term.zero_Q →ᶠ Formula.eq0 (.app Term.clamp01_Q a) Term.zero_Q) := by
  pmode
  pintro h
  prw (clamp01_Q_apply a)
  prwby h
  prw sg_bar_zero
  pthm (ite_nat_one _ _)

/-- `0ℚ <ℚ a → 1ℚ ≤ℚ a → clamp01_Q a =₀ 1ℚ`. -/
def clamp01_Q_of_one_le (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q Term.zero_Q a →ᶠ le_Q Term.one_Q a →ᶠ
        Formula.eq0 (.app Term.clamp01_Q a) Term.one_Q) := by
  pmode
  pintro h0
  pintro h1
  papplym (sg_bar_le_dec_of_lt a Term.zero_Q) in h0 with s0
  prw (clamp01_Q_apply a)
  prwby s0
  prwby h1
  prw sg_bar_zero
  pthm (qtrans (ite_nat_zero _ _) (ite_nat_one _ _))

/-- `0ℚ <ℚ a → a <ℚ 1ℚ → clamp01_Q a =₀ a`. -/
def clamp01_Q_of_lt_one (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q Term.zero_Q a →ᶠ lt_Q a Term.one_Q →ᶠ
        Formula.eq0 (.app Term.clamp01_Q a) a) := by
  pmode
  pintro h0
  pintro h1
  papplym (sg_bar_le_dec_of_lt a Term.zero_Q) in h0 with s0
  papplym (sg_bar_le_dec_of_lt Term.one_Q a) in h1 with s1
  prw (clamp01_Q_apply a)
  prwby s0
  prwby s1
  pthm (qtrans (ite_nat_zero _ _) (ite_nat_zero _ _))

-- `clamp01_Q` lands in `[0,1]`

/-- `0ℚ ≤ℚ 1ℚ`. -/
private def zero_le_one_Q :
    Derivable F al Premises (Γ := Γ) (le_Q Term.zero_Q Term.one_Q) :=
  Derivable.mp zero_lt_one_Q (lt_Q_imp_le_Q _ _)

/-- `0ℚ ≤ℚ clamp01_Q a`. -/
def clamp01_Q_nonneg (a : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q Term.zero_Q (.app Term.clamp01_Q a)) := by
  pmode
  pfrom c0 := le_Q_or_lt_Q a Term.zero_Q
  pcases c0 with ha | ha
  · papplym (clamp01_Q_of_le_zero a) in ha with e
    prwby e
    pthm (le_Q_refl Term.zero_Q)
  · pfrom c1 := le_Q_or_lt_Q Term.one_Q a
    pcases c1 with hb | hb
    · papplym (clamp01_Q_of_one_le a) in ha with k
      papply k in hb with e
      prwby e
      pthm zero_le_one_Q
    · papplym (clamp01_Q_of_lt_one a) in ha with k
      papply k in hb with e
      prwby e
      papplym (lt_Q_imp_le_Q Term.zero_Q a)
      pexact ha

/-- `clamp01_Q a ≤ℚ 1ℚ`. -/
def clamp01_Q_le_one (a : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q (.app Term.clamp01_Q a) Term.one_Q) := by
  pmode
  pfrom c0 := le_Q_or_lt_Q a Term.zero_Q
  pcases c0 with ha | ha
  · papplym (clamp01_Q_of_le_zero a) in ha with e
    prwby e
    pthm zero_le_one_Q
  · pfrom c1 := le_Q_or_lt_Q Term.one_Q a
    pcases c1 with hb | hb
    · papplym (clamp01_Q_of_one_le a) in ha with k
      papply k in hb with e
      prwby e
      pthm (le_Q_refl Term.one_Q)
    · papplym (clamp01_Q_of_lt_one a) in ha with k
      papply k in hb with e
      prwby e
      papplym (lt_Q_imp_le_Q a Term.one_Q)
      pexact hb

-- The 1-Lipschitz estimate

/-- Subtraction is monotone in the first argument and antitone in the second:
`a ≤ℚ A ∧ B ≤ℚ b → a −ℚ b ≤ℚ A −ℚ B`. -/
def sub_Q_mono (a A B b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a A ∧ᶠ le_Q B b →ᶠ
        le_Q (Term.app2 Term.sub_Q a b) (Term.app2 Term.sub_Q A B)) := by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  papplym (neg_Q_antitone B b) in h2 with h3
  papplym (le_Q_congr
    (Term.app2 Term.add_Q a (.app Term.neg_Q b))
    (Term.app2 Term.add_Q A (.app Term.neg_Q B))
    (Term.app2 Term.sub_Q a b) (Term.app2 Term.sub_Q A B)
    (eqQsym (sub_Q_eq_add_neg a b)) (eqQsym (sub_Q_eq_add_neg A B)))
  papplym (le_Q_add_both a (.app Term.neg_Q b) A (.app Term.neg_Q B))
  psplit
  · pexact h1
  · pexact h3

/-- The shape every case of the Lipschitz estimate has: once the two clamped values are
known (`clamp01_Q a =₀ ca`, `clamp01_Q b =₀ cb`), monotonicity and non-expansiveness are
statements about `ca`, `cb` alone. -/
private def lip_case (a b ca cb : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.clamp01_Q a) ca →ᶠ
       Formula.eq0 (.app Term.clamp01_Q b) cb →ᶠ
       le_Q cb ca ∧ᶠ le_Q (Term.app2 Term.sub_Q ca cb) (Term.app2 Term.sub_Q a b) →ᶠ
       le_Q (.app Term.clamp01_Q b) (.app Term.clamp01_Q a)
         ∧ᶠ le_Q (Term.app2 Term.sub_Q (.app Term.clamp01_Q a) (.app Term.clamp01_Q b))
               (Term.app2 Term.sub_Q a b)) := by
  pmode
  pintro ea
  pintro eb
  pintro h
  pdestruct h with h1 h2
  psplit
  · prwby ea
    prwby eb
    pexact h1
  · prwby ea
    prwby eb
    pexact h2

/-- **The 1-Lipschitz estimate, ordered case**: for `b ≤ℚ a`,
`|clamp01_Q a −ℚ clamp01_Q b|ℚ ≤ℚ |a −ℚ b|ℚ`.

`clamp01_Q` is monotone and non-expansive, so with `z := clamp01_Q a −ℚ clamp01_Q b` one has
`0 ≤ℚ z ≤ℚ a −ℚ b`, hence `|z| = z ≤ a −ℚ b ≤ |a −ℚ b|`. The two facts are established by a
case split on where `a` and then `b` fall, each case `lip_case` fed two order facts. -/
def clamp01_Q_lip_core (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q b a →ᶠ
        le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
                (.app Term.clamp01_Q a) (.app Term.clamp01_Q b)))
             (.app Term.abs_Q (Term.app2 Term.sub_Q a b))) := by
  let Ca : Term F Γ Ty.nat := .app Term.clamp01_Q a
  let Cb : Term F Γ Ty.nat := .app Term.clamp01_Q b
  let z : Term F Γ Ty.nat := Term.app2 Term.sub_Q Ca Cb
  let d : Term F Γ Ty.nat := Term.app2 Term.sub_Q a b
  let Q0 : Term F Γ Ty.nat := Term.zero_Q
  let Q1 : Term F Γ Ty.nat := Term.one_Q
  pmode
  pintro hba
  phave hboth : le_Q Cb Ca ∧ᶠ le_Q z d
  · pfrom c0 := le_Q_or_lt_Q a Q0
    pcases c0 with ha0 | ha0
    · -- `a ≤ 0`, hence `b ≤ 0`: both clamp to `0`
      phave hb0 : le_Q b Q0
      · papplym (le_Q_trans b a Q0)
        psplit
        · pexact hba
        · pexact ha0
      papplym (clamp01_Q_of_le_zero a) in ha0 with ea
      papplym (clamp01_Q_of_le_zero b) in hb0 with eb
      papplym (lip_case a b Q0 Q0)
      · pexact ea
      · pexact eb
      · psplit
        · pthm (le_Q_refl Q0)
        · papplym (le_Q_congr Q0 d (Term.app2 Term.sub_Q Q0 Q0) d
            (eqQsym (sub_Q_self Q0)) (eq_Q_refl_inst d))
          papplym (le_Q_to_zero_sub b a)
          pexact hba
    · -- `0 < a`
      pfrom c1 := le_Q_or_lt_Q Q1 a
      pcases c1 with ha1 | ha1
      · -- `1 ≤ a`: `a` clamps to `1`
        papplym (clamp01_Q_of_one_le a) in ha0 with ka
        papply ka in ha1 with ea
        pfrom d0 := le_Q_or_lt_Q b Q0
        pcases d0 with hb0 | hb0
        · -- `b ≤ 0`: `b` clamps to `0`
          papplym (clamp01_Q_of_le_zero b) in hb0 with eb
          papplym (lip_case a b Q1 Q0)
          · pexact ea
          · pexact eb
          · psplit
            · pthm zero_le_one_Q
            · papplym (sub_Q_mono Q1 a b Q0)
              psplit
              · pexact ha1
              · pexact hb0
        · pfrom d1 := le_Q_or_lt_Q Q1 b
          pcases d1 with hb1 | hb1
          · -- `1 ≤ b`: `b` clamps to `1`
            papplym (clamp01_Q_of_one_le b) in hb0 with kb
            papply kb in hb1 with eb
            papplym (lip_case a b Q1 Q1)
            · pexact ea
            · pexact eb
            · psplit
              · pthm (le_Q_refl Q1)
              · papplym (le_Q_congr Q0 d (Term.app2 Term.sub_Q Q1 Q1) d
                  (eqQsym (sub_Q_self Q1)) (eq_Q_refl_inst d))
                papplym (le_Q_to_zero_sub b a)
                pexact hba
          · -- `0 < b < 1`: `b` is fixed
            papplym (clamp01_Q_of_lt_one b) in hb0 with kb
            papply kb in hb1 with eb
            papplym (lip_case a b Q1 b)
            · pexact ea
            · pexact eb
            · psplit
              · papplym (lt_Q_imp_le_Q b Q1)
                pexact hb1
              · papplym (sub_Q_mono Q1 a b b)
                psplit
                · pexact ha1
                · pthm (le_Q_refl b)
      · -- `0 < a < 1`: `a` is fixed
        papplym (clamp01_Q_of_lt_one a) in ha0 with ka
        papply ka in ha1 with ea
        pfrom d0 := le_Q_or_lt_Q b Q0
        pcases d0 with hb0 | hb0
        · -- `b ≤ 0`: `b` clamps to `0`
          papplym (clamp01_Q_of_le_zero b) in hb0 with eb
          papplym (lip_case a b a Q0)
          · pexact ea
          · pexact eb
          · psplit
            · papplym (lt_Q_imp_le_Q Q0 a)
              pexact ha0
            · papplym (sub_Q_mono a a b Q0)
              psplit
              · pthm (le_Q_refl a)
              · pexact hb0
        · pfrom d1 := le_Q_or_lt_Q Q1 b
          pcases d1 with hb1 | hb1
          · -- `1 ≤ b ≤ a < 1`: absurd
            pexfalso
            papplym (lt_Q_le_Q_absurd a Q1)
            psplit
            · pexact ha1
            · papplym (le_Q_trans Q1 b a)
              psplit
              · pexact hb1
              · pexact hba
          · -- `0 < b < 1`: `b` is fixed
            papplym (clamp01_Q_of_lt_one b) in hb0 with kb
            papply kb in hb1 with eb
            papplym (lip_case a b a b)
            · pexact ea
            · pexact eb
            · psplit
              · pexact hba
              · pthm (le_Q_refl d)
  pdestruct hboth with hmono hlip
  papplym (le_Q_to_zero_sub Cb Ca) in hmono with hz
  papplym (le_Q_zero_parts z) in hz with hzn
  papplym (abs_Q_le_self_of_negN_zero z) in hzn with habs
  papplym (le_Q_trans (.app Term.abs_Q z) z (.app Term.abs_Q d))
  psplit
  · pexact habs
  · papplym (le_Q_trans z d (.app Term.abs_Q d))
    psplit
    · pexact hlip
    · pthm (le_Q_self_abs d)

/-- **`clamp01_Q` is 1-Lipschitz**: `|clamp01_Q a −ℚ clamp01_Q b|ℚ ≤ℚ |a −ℚ b|ℚ`. The
unordered form of `clamp01_Q_lip_core`, by `le_Q_or_lt_Q` and the symmetry of `|· −ℚ ·|`. -/
def clamp01_Q_lip (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (.app Term.clamp01_Q a) (.app Term.clamp01_Q b)))
           (.app Term.abs_Q (Term.app2 Term.sub_Q a b))) := by
  let Ca : Term F Γ Ty.nat := .app Term.clamp01_Q a
  let Cb : Term F Γ Ty.nat := .app Term.clamp01_Q b
  pmode
  pfrom c := le_Q_or_lt_Q b a
  pcases c with hba | hab
  · papplym (clamp01_Q_lip_core a b)
    pexact hba
  · papplym (lt_Q_imp_le_Q a b) in hab with hab'
    papplym (clamp01_Q_lip_core b a) in hab' with h
    papplym (le_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q Cb Ca))
      (.app Term.abs_Q (Term.app2 Term.sub_Q b a))
      (.app Term.abs_Q (Term.app2 Term.sub_Q Ca Cb))
      (.app Term.abs_Q (Term.app2 Term.sub_Q a b))
      (abs_diff_Q_comm Cb Ca) (abs_diff_Q_comm b a))
    pexact h

-- Result 1: `clamp01 f` is Cauchy, so `cauchyfy` fixes it

/-- The Cauchy check passes for `clamp01 f` at every index, for **any** `f`: `f̂` is Cauchy
by `cauchyfy_cauchy`, and `clamp01_Q_lip` transfers its rate verbatim. Spelled out rather
than written with `Term.cauchy_check_at`, for the usual `prw` reason. -/
def clamp01_check (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (.app Term.clamp01 f.weaken) (.var .vz))
            (.app (.app Term.clamp01 f.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  let a0 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken (.var .vz)
  let a1 : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))
  pmode
  prw (clamp01_apply f.weaken (.var .vz))
  prw (clamp01_apply f.weaken (.app .succ (.var .vz)))
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (.app Term.clamp01_Q a0) (.app Term.clamp01_Q a1)))
    (.app Term.abs_Q (Term.app2 Term.sub_Q a0 a1))
    (.app Term.pow2neg_Q (.app .succ (.var .vz))))
  psplit
  · pthm (clamp01_Q_lip a0 a1)
  · pthm (cauchyfy_cauchy f.weaken (.var .vz))

/-- **`(clamp01 f)^(s) =₀ clamp01_Q (f̂(s))`** — `cauchyfy` is the identity on `clamp01 f`,
for any `f`. -/
def cauchyfy_clamp01 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.clamp01 f) s)
        (.app Term.clamp01_Q (Term.app2 Term.cauchyfy f s))) :=
  qtrans
    (cauchyfy_id (.app Term.clamp01 f) (clamp01_app_weaken f ▸ clamp01_check f) s)
    (clamp01_apply f s)

-- Results 2 and 3: `0ℝ ≤ℝ clamp01 f ≤ℝ 1ℝ`

/-- `0ℝ ≤ℝ clamp01 f`, at an explicit real. The pointwise content is
`0ℚ −ℚ clamp01_Q (f̂(n+1)) <ℚ 2^{-n}`, from `0ℚ ≤ℚ clamp01_Q (·)` and `0ℚ <ℚ 2^{-n}`. -/
def clamp01_nonneg_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R Term.zero_R (.app Term.clamp01 f)) :=
  le_R_of_bound Term.zero_R (.app Term.clamp01 f) (by
    rw [zero_R_weaken, clamp01_app_weaken]
    pmode
    prw (cauchyfy_zero_R (.app .succ (.var .vz)))
    prw (cauchyfy_clamp01 f.weaken (.app .succ (.var .vz)))
    pthm (sub_lt_of_le Term.zero_Q
      (.app Term.clamp01_Q (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.var .vz))
      (clamp01_Q_nonneg _) (zero_lt_pow2neg_Q _)))

/-- ⊢ ∀f : ℝ. 0ℝ ≤ℝ clamp01 f -/
def clamp01_nonneg :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (le_R Term.zero_R (.app Term.clamp01 (.var .vz)))) :=
  univ_gen (clamp01_nonneg_core (.var .vz))

/-- `clamp01 f ≤ℝ 1ℝ`, at an explicit real. -/
def clamp01_le_one_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R (.app Term.clamp01 f) Term.one_R) :=
  le_R_of_bound (.app Term.clamp01 f) Term.one_R (by
    rw [one_R_weaken', clamp01_app_weaken]
    pmode
    prw (cauchyfy_one_R (.app .succ (.var .vz)))
    prw (cauchyfy_clamp01 f.weaken (.app .succ (.var .vz)))
    pthm (sub_lt_of_le
      (.app Term.clamp01_Q (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
      Term.one_Q
      (.app Term.pow2neg_Q (.var .vz))
      (clamp01_Q_le_one _) (zero_lt_pow2neg_Q _)))

/-- ⊢ ∀f : ℝ. clamp01 f ≤ℝ 1ℝ -/
def clamp01_le_one :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (le_R (.app Term.clamp01 (.var .vz)) Term.one_R)) :=
  univ_gen (clamp01_le_one_core (.var .vz))

-- Result 4: `clamp01` is the identity on `[0,1]`

/-- `0ℝ ≤ℝ f → f ≤ℝ 1ℝ → u =ℝ f` for any `u` whose cauchyfication is `clamp01_Q (f̂(·))`.

The composed real is fed in through an abstract `u`, as `add_zero_R_gen` does. No estimate is
spent: the clamp's drift is exactly what `≤ℝ` measures. -/
private def clamp01_eq_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (.app Term.clamp01_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))) :
    Derivable F al Premises
      (le_R Term.zero_R f →ᶠ le_R f Term.one_R →ᶠ eq_R u f) := by
  let n  : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n
  let a  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n1
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n
  let Q0 : Term F (Ty.nat :: Γ) Ty.nat := Term.zero_Q
  let Q1 : Term F (Ty.nat :: Γ) Ty.nat := Term.one_Q
  pmode
  pintro h0
  pintro h1
  papplym (le_R_all Term.zero_R f) in h0 with p0
  papplym (le_R_all f Term.one_R) in h1 with p1
  pforall
  pinst p0 n with q0
  pinst p1 n with q1
  canorm
  prw (cauchyfy_zero_R n1) in q0 with q0a
  prw (cauchyfy_one_R n1) in q1 with q1a
  prw hu
  pfrom c0 := le_Q_or_lt_Q a Q0
  pcases c0 with ha0 | ha0
  · -- `a ≤ 0`: the drift is `0 −ℚ a ≥ 0`, and `0ℝ ≤ℝ f` at `n` bounds it
    papplym (clamp01_Q_of_le_zero a) in ha0 with e
    prwby e
    papplym (le_Q_to_zero_sub a Q0) in ha0 with hz
    papplym (le_Q_zero_parts (Term.app2 Term.sub_Q Q0 a)) in hz with hzn
    papplym (abs_Q_le_self_of_negN_zero (Term.app2 Term.sub_Q Q0 a)) in hzn with habs
    papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q Q0 a))
      (Term.app2 Term.sub_Q Q0 a) P)
    psplit
    · pexact habs
    · pexact q0a
  · pfrom c1 := le_Q_or_lt_Q Q1 a
    pcases c1 with ha1 | ha1
    · -- `1 ≤ a`: the drift is `1 −ℚ a`, of magnitude `a −ℚ 1 ≥ 0`, bounded by `f ≤ℝ 1ℝ`
      papplym (clamp01_Q_of_one_le a) in ha0 with k
      papply k in ha1 with e
      prwby e
      papplym (le_Q_to_zero_sub Q1 a) in ha1 with hz
      papplym (le_Q_zero_parts (Term.app2 Term.sub_Q a Q1)) in hz with hzn
      papplym (abs_Q_le_self_of_negN_zero (Term.app2 Term.sub_Q a Q1)) in hzn with habs
      papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q a Q1)) P
        (.app Term.abs_Q (Term.app2 Term.sub_Q Q1 a)) P
        (abs_diff_Q_comm a Q1) (eq_Q_refl_inst P))
      papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q a Q1))
        (Term.app2 Term.sub_Q a Q1) P)
      psplit
      · pexact habs
      · pexact q1a
    · -- `0 < a < 1`: the clamp is the identity
      papplym (clamp01_Q_of_lt_one a) in ha0 with k
      papply k in ha1 with e
      prwby e
      pthm (lt_Q_abs_sub_self a n)

/-- `0ℝ ≤ℝ f → f ≤ℝ 1ℝ → clamp01 f =ℝ f`, at an explicit real. -/
def clamp01_eq_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R Term.zero_R f →ᶠ le_R f Term.one_R →ᶠ eq_R (.app Term.clamp01 f) f) :=
  clamp01_eq_gen f (.app Term.clamp01 f) (by
    rw [clamp01_app_weaken]
    exact cauchyfy_clamp01 f.weaken (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. 0ℝ ≤ℝ f → f ≤ℝ 1ℝ → clamp01 f =ℝ f

`clamp01` is a retraction onto `[0,1]`: together with `clamp01_nonneg` and `clamp01_le_one`
this is what lets `∀λ ∈ [0,1] A(λ)` be written as the unrestricted `∀f¹ A(clamp01 f)`. -/
def clamp01_eq :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (le_R Term.zero_R (.var .vz) →ᶠ le_R (.var .vz) Term.one_R →ᶠ
          eq_R (.app Term.clamp01 (.var .vz)) (.var .vz))) :=
  univ_gen (clamp01_eq_core (.var .vz))

end Interval

end Metatheorems
