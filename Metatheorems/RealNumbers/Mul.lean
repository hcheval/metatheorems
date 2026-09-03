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

/-- ⊢ ∀f : ℝ. f ·_ℝ 1_ℝ =_ℝ f -/
def mul_one_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var .vz) Term.one_R)
              (.var .vz))) :=
  sorry

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

end OrderedFieldAxioms

end Metatheorems
