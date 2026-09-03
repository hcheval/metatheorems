/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Negation

namespace Metatheorems

open Formula

variable {ι : Type} {F : ι → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Multiplicative monoid ───────────────────────────────────────────────────

-- `mul_comm_R` is PROVED, further down the file: it needs `cauchyfy_congr`, which is an
-- induction on the `cauchyfy` recursion and so sits with the rest of that theory.

/-- ⊢ ∀f,g,h : ℝ. (f ·_ℝ g) ·_ℝ h =_ℝ f ·_ℝ (g ·_ℝ h) -/
def mul_assoc_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

-- `mul_one_R` is PROVED, at the bottom of the file: it needs `mul_R_apply` (below) and the
-- symbolic-shift telescope `cauchyfy_shift_le` (`Estimates.lean`).

-- ── Distributivity ──────────────────────────────────────────────────────────

/-- ⊢ ∀f,g,h : ℝ. f ·_ℝ (g +_ℝ h) =_ℝ (f ·_ℝ g) +_ℝ (f ·_ℝ h) -/
def distrib_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))
          (Term.app2 Term.add_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
              (.var .vz))))))) :=
  sorry

-- ── `mul_comm_R` ────────────────────────────────────────────────────────────
--
-- Unlike `add_R`, `mul_R` is **not** known to be Cauchy — there is no `mul_R_check`, and
-- supplying one is the majorization argument of REALS_PLAN §1 — so `cauchyfy` cannot be
-- evaluated away on either side. This is where `cauchyfy_congr` earns its keep: the two raw
-- sequences are pointwise `=_ℚ`, and that is enough.
--
-- The one wrinkle `add_R` does not have is that `mul_R`'s index depends on its arguments:
-- `mul_R f g (n) = f̂(n +ℕ b) ·ℚ ĝ(n +ℕ b)` with `b = f(0) +ℕ g(0) +ℕ 2`, so swapping the
-- arguments swaps the two summands inside `b`. `Arithmetic.add_comm` repairs that at ℕ,
-- underneath `cauchyfy`, before `mul_Q_comm_inst` is spent.

private theorem mul_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.mul_R : Term F Δ _).weaken (σ := ρ) = Term.mul_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact mul_R_closed_subst _

private theorem mul_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f g : Term F Δ (realTy ι)) :
    (Term.app2 Term.mul_R f g).weaken (σ := ρ) =
      Term.app2 Term.mul_R f.weaken g.weaken := by
  show Term.app2 (Term.weaken Term.mul_R) f.weaken g.weaken = _
  rw [mul_R_weaken]

/-- `(f ·_ℝ g)(x) =₀ f̂(x +ℕ b) ·_ℚ ĝ(x +ℕ b)` with `b = f(0) +ℕ g(0) +ℕ 2` — the three beta
steps of `mul_R`. The bound `b` is spelled out rather than named: a named wrapper would hide
it from `prw`, and `add_comm` has to reach inside it. -/
def mul_R_apply (f g : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app3 Term.mul_R f g x)
        (Term.app2 Term.mul_Q
          (Term.app2 Term.cauchyfy f
            (Term.app2 Term.add x (Term.app2 Term.add
              (Term.app2 Term.add (.app f .zero) (.app g .zero)) (Term.ofNat 2))))
          (Term.app2 Term.cauchyfy g
            (Term.app2 Term.add x (Term.app2 Term.add
              (Term.app2 Term.add (.app f .zero) (.app g .zero)) (Term.ofNat 2)))))) :=
  lam3_correct_nf
    (Term.app2 Term.mul_Q
      (Term.app2 Term.cauchyfy (.var (.vs (.vs .vz)))
        (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app (.var (.vs (.vs .vz))) .zero)
            (.app (.var (.vs .vz)) .zero))
          (Term.ofNat 2))))
      (Term.app2 Term.cauchyfy (.var (.vs .vz))
        (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app (.var (.vs (.vs .vz))) .zero)
            (.app (.var (.vs .vz)) .zero))
          (Term.ofNat 2)))))
    f g x
    (by
      simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.Subst.ext,
        Term.ofNat, Term.weaken_var, subst_subst0_map_weaken, closed_subst])

/-- Congruence for `cauchyfy` in its **index**, at the level of `=₀`. -/
private def cauchyfy_idx_nat (h : Term F Γ (realTy ι)) {s t : Term F Γ Ty.nat}
    (he : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy h s) (Term.app2 Term.cauchyfy h t)) :=
  qfer_no_premise_nat_nf he (r := Term.app2 Term.cauchyfy h.weaken (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- Congruence for `mul_Q` in its first argument, at the level of `=₀`. -/
private def mulQ_l_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.mul_Q s u) (Term.app2 Term.mul_Q t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.mul_Q (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- Congruence for `mul_Q` in its second argument, at the level of `=₀`. -/
private def mulQ_r_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.mul_Q u s) (Term.app2 Term.mul_Q u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.mul_Q u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- `=₀` implies `=_ℚ`. (`RationalNumbers.lean`'s `eq_Q_from_nat_eq` is private; this is the
same statement, one `prwby` away from `eq_Q_refl_inst`.) -/
private def eqQ_of_nat_eq {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (eq_Q s t) := by
  pmode
  pfrom hh := h
  prwby hh
  pthm (eq_Q_refl_inst t)

/-- `(f ·_ℝ g)(x) =_ℚ (g ·_ℝ f)(x)` — pointwise commutativity of the **raw** product
sequence. Not `=₀`: `mul_Q` does not commute on the nose, for the same encoding reason
`add_Q` does not (REALS_PLAN §0.2). -/
def mul_R_pointwise_comm (f g : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app (Term.app2 Term.mul_R f g) x) (.app (Term.app2 Term.mul_R g f) x)) :=
  let bfg : Term F Γ Ty.nat := Term.app2 Term.add
    (Term.app2 Term.add (.app f .zero) (.app g .zero)) (Term.ofNat 2)
  let bgf : Term F Γ Ty.nat := Term.app2 Term.add
    (Term.app2 Term.add (.app g .zero) (.app f .zero)) (Term.ofNat 2)
  let I : Term F Γ Ty.nat := Term.app2 Term.add x bfg
  let J : Term F Γ Ty.nat := Term.app2 Term.add x bgf
  -- `J =₀ I`: the two bounds differ only by the order of the two `·(0)` terms
  let hJI : Derivable F al Premises (Formula.eq0 J I) :=
    add_congr_r x (add_congr_l (add_comm (.app g .zero) (.app f .zero)) (Term.ofNat 2))
  -- `(g ·_ℝ f)(x) =₀ ĝ(I) ·_ℚ f̂(I)`
  let hgf : Derivable F al Premises
      (Formula.eq0 (.app (Term.app2 Term.mul_R g f) x)
        (Term.app2 Term.mul_Q (Term.app2 Term.cauchyfy g I)
          (Term.app2 Term.cauchyfy f I))) :=
    qtrans (mul_R_apply g f x)
      (qtrans (mulQ_l_nat _ (cauchyfy_idx_nat g hJI))
        (mulQ_r_nat _ (cauchyfy_idx_nat f hJI)))
  eqQtrans (eqQ_of_nat_eq (mul_R_apply f g x))
    (eqQtrans
      (mul_Q_comm_inst (Term.app2 Term.cauchyfy f I) (Term.app2 Term.cauchyfy g I))
      (eqQ_of_nat_eq (Derivable.mp hgf Derivable.sym0)))

/-- `f ·_ℝ g =_ℝ g ·_ℝ f`, at explicit reals. -/
def mul_comm_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.mul_R f g) (Term.app2 Term.mul_R g f)) :=
  eq_R_of_cauchyfy_eqQ _ _ (by
    rw [mul_R_app_weaken, mul_R_app_weaken]
    exact cauchyfy_congr
      (Term.app2 Term.mul_R f.weaken g.weaken)
      (Term.app2 Term.mul_R g.weaken f.weaken)
      (mul_R_pointwise_comm f.weaken g.weaken Term.zero)
      (fun x => by
        rw [mul_R_app_weaken, mul_R_app_weaken]
        exact mul_R_pointwise_comm f.weaken.weaken g.weaken.weaken x)
      (.app .succ (.var .vz)))

/-- ⊢ ∀f,g : ℝ. f ·_ℝ g =_ℝ g ·_ℝ f -/
def mul_comm_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.mul_R (.var .vz) (.var (.vs .vz)))))) :=
  univ_gen (univ_gen (mul_comm_R_core (.var (.vs .vz)) (.var .vz)))

-- ── `mul_one_R` ─────────────────────────────────────────────────────────────
--
-- Unlike `mul_comm_R`, this one *can* discharge the outer `cauchyfy`: `mul_R f 1ℝ` is
-- pointwise `=ℚ` to `f̂(· +ℕ b)`, which is Cauchy, and `lt_Q_dec`'s decision is `=ℚ`-invariant
-- (that is what `lt_Q_congr` supplies), so `cauchyfy_id` applies.  What is left is
--
--     |f̂(n+1+b) −ℚ f̂(n+1)|  <ℚ  2^{-n},        b = f(0) +ℕ 1ℚ-code +ℕ 2
--
-- with `b` **symbolic** — a telescope of symbolically many `cauchyfy` steps, which is exactly
-- `cauchyfy_shift_le`.  It is not a slack argument: `2^{-(n+1)} <ℚ 2^{-n}` is the only slack
-- there is, and it is spent on the last step.
--
-- `b` is spelled out at every occurrence rather than named: a named wrapper would hide it
-- from `prw` and from the `=₀` congruences (REALS_PLAN §0.1).

/-- `mul_Q_one` at an explicit term. -/
def mul_Q_one_inst (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q a Term.one_Q) a) := by
  have h := Derivable.mp (mul_Q_one (al := al) (Premises := Premises) (Γ := Γ)) (.forall_ax a)
  q_norm using h

/-- Congruence for `pow2neg_Q` in its index, at the level of `=₀`. -/
private def pow2neg_idx_nat {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.pow2neg_Q s) (.app Term.pow2neg_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.pow2neg_Q (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

private theorem one_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.one_R : Term F Δ (realTy ι)).weaken (σ := ρ) = Term.one_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_R_closed_subst _

private theorem mul_one_R_weaken {Δ : Ctx ι} {ρ : Ty ι} (f : Term F Δ (realTy ι)) :
    (Term.app2 Term.mul_R f Term.one_R).weaken (σ := ρ) =
      Term.app2 Term.mul_R f.weaken Term.one_R := by
  rw [mul_R_app_weaken, one_R_weaken']

/-- `(f ·_ℝ 1_ℝ)(x) =_ℚ f̂(x +ℕ b)`: multiplying by `1_ℝ` is a pure index shift.

Only `=_ℚ`, not `=₀` — `mul_Q q 1ℚ` is not `q` on the nose in the encoding. -/
def mul_one_R_apply (f : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app (Term.app2 Term.mul_R f Term.one_R) x)
        (Term.app2 Term.cauchyfy f
          (Term.app2 Term.add x (Term.app2 Term.add
            (Term.app2 Term.add (.app f .zero) (.app Term.one_R .zero))
            (Term.ofNat 2))))) :=
  let I : Term F Γ Ty.nat := Term.app2 Term.add x (Term.app2 Term.add
    (Term.app2 Term.add (.app f .zero) (.app Term.one_R .zero)) (Term.ofNat 2))
  eqQtrans
    (eqQ_of_nat_eq
      (qtrans (mul_R_apply f Term.one_R x)
        (mulQ_r_nat (Term.app2 Term.cauchyfy f I) (cauchyfy_one_R I))))
    (mul_Q_one_inst (Term.app2 Term.cauchyfy f I))

/-- The Cauchy check passes for `f ·_ℝ 1_ℝ` at every index: the raw sequence is `f̂` read
`b` places in, and `cauchyfy_cauchy` there costs `2^{-(k+b+1)} ≤ℚ 2^{-(k+1)}`. -/
def mul_one_R_check (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (Term.app2 Term.mul_R f.weaken Term.one_R) (.var .vz))
            (.app (Term.app2 Term.mul_R f.weaken Term.one_R) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  papplym (lt_Q_congr
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.app .succ (.var .vz)) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (.app (Term.app2 Term.mul_R f.weaken Term.one_R) (.var .vz))
      (.app (Term.app2 Term.mul_R f.weaken Term.one_R) (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (abs_Q_congr (sub_Q_congr
      (eqQsym (mul_one_R_apply f.weaken (.var .vz)))
      (eqQsym (mul_one_R_apply f.weaken (.app .succ (.var .vz))))))
    (eq_Q_refl_inst _))
  papplym (lt_le_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.app .succ (.var .vz)) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))))
    (.app Term.pow2neg_Q
      (Term.app2 Term.add (.app .succ (.var .vz)) (Term.app2 Term.add
        (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
        (Term.ofNat 2))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz))))
  psplit
  · -- `cauchyfy_cauchy` at `m := k +ℕ b`, with `succ m` renamed to `(succ k) +ℕ b`
    papplym (lt_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
            (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
            (Term.ofNat 2))))
        (Term.app2 Term.cauchyfy f.weaken
          (.app .succ (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
            (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
            (Term.ofNat 2)))))))
      (.app Term.pow2neg_Q
        (.app .succ (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2)))))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
            (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
            (Term.ofNat 2))))
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.app .succ (.var .vz)) (Term.app2 Term.add
            (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
            (Term.ofNat 2))))))
      (.app Term.pow2neg_Q
        (Term.app2 Term.add (.app .succ (.var .vz)) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))
      (abs_Q_congr (sub_Q_congr (eq_Q_refl_inst _)
        (eqQ_of_nat_eq (Derivable.mp
          (cauchyfy_idx_nat f.weaken
            (add_succ_l (.var .vz) (Term.app2 Term.add
              (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
              (Term.ofNat 2))))
          Derivable.sym0))))
      (eqQ_of_nat_eq (Derivable.mp
        (pow2neg_idx_nat (add_succ_l (.var .vz) (Term.app2 Term.add
          (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
          (Term.ofNat 2))))
        Derivable.sym0)))
    pthm (cauchyfy_cauchy f.weaken
      (Term.app2 Term.add (.var .vz) (Term.app2 Term.add
        (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
        (Term.ofNat 2))))
  · pthm (pow2neg_Q_le_add (.app .succ (.var .vz)) (Term.app2 Term.add
      (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
      (Term.ofNat 2)))

/-- `(f ·_ℝ 1_ℝ)^(s) =_ℚ f̂(s +ℕ b)`: `cauchyfy` is the identity on `f ·_ℝ 1_ℝ`. -/
def cauchyfy_mul_one_R (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.cauchyfy (Term.app2 Term.mul_R f Term.one_R) s)
        (Term.app2 Term.cauchyfy f
          (Term.app2 Term.add s (Term.app2 Term.add
            (Term.app2 Term.add (.app f .zero) (.app Term.one_R .zero))
            (Term.ofNat 2))))) :=
  eqQtrans
    (eqQ_of_nat_eq (cauchyfy_id (Term.app2 Term.mul_R f Term.one_R)
      (mul_one_R_weaken f ▸ mul_one_R_check f) s))
    (mul_one_R_apply f s)

/-- `u =_ℝ f` whenever `û` is `f̂` read a *symbolic* number `bw` of places in.

The shift is taken as a Lean-level parameter, and so is the composed real `u`: `prw` must not
be pointed at a goal containing `Term.mul_R`, exactly as for `Term.add_R`
(`add_eq_zero_R_gen`). -/
private def mul_one_R_gen (f u : Term F Γ (realTy ι)) (bw : Term F (Ty.nat :: Γ) Ty.nat)
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.app .succ (.var .vz)) bw)))) :
    Derivable F al Premises (eq_R u f) := by
  pmode
  pforall
  papplym (lt_Q_congr
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.app .succ (.var .vz)) bw))
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz))
    (abs_Q_congr (sub_Q_congr (eqQsym hu) (eq_Q_refl_inst _)))
    (eq_Q_refl_inst _))
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken
        (Term.app2 Term.add (.app .succ (.var .vz)) bw))
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · papplym (le_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.app .succ (.var .vz)) bw))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.app .succ (.var .vz)) bw))
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (abs_diff_Q_comm
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.cauchyfy f.weaken
          (Term.app2 Term.add (.app .succ (.var .vz)) bw)))
      (eq_Q_refl_inst _))
    pthm (cauchyfy_shift_le f.weaken (.app .succ (.var .vz)) bw)
  · pthm (pow2neg_Q_lt_succ (.var .vz))

/-- `f ·_ℝ 1_ℝ =_ℝ f`, at an explicit real. -/
def mul_one_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R (Term.app2 Term.mul_R f Term.one_R) f) :=
  mul_one_R_gen f (Term.app2 Term.mul_R f Term.one_R)
    (Term.app2 Term.add
      (Term.app2 Term.add (.app f.weaken .zero) (.app Term.one_R .zero))
      (Term.ofNat 2))
    ((mul_one_R_weaken f).symm ▸ cauchyfy_mul_one_R f.weaken (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. f ·_ℝ 1_ℝ =_ℝ f -/
def mul_one_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var .vz) Term.one_R)
              (.var .vz))) :=
  univ_gen (mul_one_R_core (.var .vz))

end OrderedFieldAxioms

end Metatheorems
