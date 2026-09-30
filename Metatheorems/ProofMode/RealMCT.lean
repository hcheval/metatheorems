/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealMCTStatement
import Metatheorems.RealNumbers
import Metatheorems.ProofMode.Arith

/-!
# ℝ-MCT, the dichotomy proof (P2ℝ) — `real_mct_p2`

`RealMCTStatement.lean` fixes the statement

    ∀ x^{(ℕ→ℝ) ×ₜ ((ℕ→ℕ) ×ₜ ℕ)} ( ∀u B(u,x) → ∃v C(v,x) )
                                  a := fst x, g := fst (snd x), k := snd (snd x)

    B(u,x) := ∀n ( a(n+1) ≤ℝ a n ∧ 0ℝ ≤ℝ a n ∧ a n ≤ℝ 1ℝ )      each read at Cauchy index u
    C(v,x) := leIdx |a v −ℝ a(v + g v)|ℝ ⟨2^{-(k+1)}⟩ℝ (k+2)     i.e. D̂(k+3) <ℚ 3·2^{-(k+2)}

and `docs/REAL_MCT.md` §3 plans its derivation as `mct_p2`'s budget descent over the reals. This
file is that derivation, at `Allowed.extended` (no `lem`, no `markov`: the only case split is
`qf_lem` on the quantifier-free conclusion matrix), and `real_mct_bound_p2` feeds it to the
metatheorem. The argument is Kohlenbach, *Applied Proof Theory*, §2.3 (Prop. 2.26–2.27), with
the counting done as a budget induction (`real_mct_window`, `real_mct_descent`,
`real_mct_body`) exactly as `ProofMode/MCT.lean` does it for ℕ-MCT.
-/

namespace Metatheorems
namespace ProofMode

open Formula RealMCT

variable {ι κ : Type} {F : κ → Ty ι}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

-- Normalisation: renames pushed to the leaves, `leIdx` and `le_R` kept folded

section Norm

/-- A weakening under a renaming commutes: `(t.weaken).rename (ext r) = (t.rename r).weaken`.
This is the rule that lets two renamings around an opaque leaf collapse to the coercion's
spelling `weaken (weaken a)`. -/
theorem rename_ext_weaken {Δ Δ' : Ctx ι} {τ ρ : Ty ι} (r : Term.Renaming Δ Δ')
    (t : Term F Δ τ) :
    (t.weaken (σ := ρ)).rename (Term.Renaming.ext r) = (t.rename r).weaken := by
  rw [Term.weaken, Term.weaken, Term.rename_rename, Term.rename_rename]
  rfl

/-- The `_rename'` family: a closed constant is fixed by every renaming. -/
theorem cauchyfy_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.cauchyfy : Term F Δ _).rename r = Term.cauchyfy := by
  rw [Term.rename_eq_subst]; exact cauchyfy_closed_subst _
theorem abs_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.abs_R : Term F Δ _).rename r = Term.abs_R := by
  rw [Term.rename_eq_subst]; exact abs_R_closed_subst _
theorem sub_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.sub_R : Term F Δ _).rename r = Term.sub_R := by
  rw [Term.rename_eq_subst]; exact sub_R_closed_subst _
theorem add_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.add_R : Term F Δ _).rename r = Term.add_R := by
  rw [Term.rename_eq_subst]; exact add_R_closed_subst _
theorem neg_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.neg_R : Term F Δ _).rename r = Term.neg_R := by
  rw [Term.rename_eq_subst]; exact neg_R_closed_subst _
theorem zero_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.zero_R : Term F Δ (realTy ι)).rename r = Term.zero_R := by
  rw [Term.rename_eq_subst]; exact zero_R_closed_subst _
theorem one_R_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.one_R : Term F Δ (realTy ι)).rename r = Term.one_R := by
  rw [Term.rename_eq_subst]; exact one_R_closed_subst _
theorem pow2neg_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.pow2neg_Q : Term F Δ _).rename r = Term.pow2neg_Q := by
  rw [Term.rename_eq_subst]; exact pow2neg_Q_closed_subst _
theorem le_Q_dec_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.le_Q_dec : Term F Δ _).rename r = Term.le_Q_dec := by
  rw [Term.rename_eq_subst]; exact le_Q_dec_closed_subst _
theorem lt_Q_dec_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.lt_Q_dec : Term F Δ _).rename r = Term.lt_Q_dec := by
  rw [Term.rename_eq_subst]; exact lt_Q_dec_closed_subst _
theorem sub_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.sub_Q : Term F Δ _).rename r = Term.sub_Q := by
  rw [Term.rename_eq_subst]; exact sub_Q_closed_subst _
theorem add_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.add_Q : Term F Δ _).rename r = Term.add_Q := by
  rw [Term.rename_eq_subst]; exact add_Q_closed_subst _
theorem mul_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.mul_Q : Term F Δ _).rename r = Term.mul_Q := by
  rw [Term.rename_eq_subst]; exact mul_Q_closed_subst _
theorem encode_nat_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.encode_nat_Q : Term F Δ _).rename r = Term.encode_nat_Q := by
  rw [Term.rename_eq_subst]; exact encode_nat_Q_closed_subst _
theorem exp2_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.exp2 : Term F Δ _).rename r = Term.exp2 := by
  rw [Term.rename_eq_subst]; exact exp2_closed_subst _
theorem add_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.add : Term F Δ _).rename r = Term.add := by
  rw [Term.rename_eq_subst]; exact add_closed_subst _
theorem zero_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.zero_Q : Term F Δ _).rename r = Term.zero_Q := by
  rw [Term.rename_eq_subst]; exact zero_Q_closed_subst _
theorem one_Q_rename' {Δ Δ' : Ctx ι} (r : Term.Renaming Δ Δ') :
    (Term.one_Q : Term F Δ _).rename r = Term.one_Q := by
  rw [Term.rename_eq_subst]; exact one_Q_closed_subst _

theorem const_R_rename {Δ Δ' : Ctx ι} (q : Term F Δ Ty.nat) (r : Term.Renaming Δ Δ') :
    (const_R q : Term F Δ (realTy ι)).rename r = const_R (q.rename r) := by
  rw [Term.rename_eq_subst, const_R_subst, ← Term.rename_eq_subst]

theorem le_R_renameF {Δ Δ' : Ctx ι} (f g : Term F Δ (realTy ι)) (r : Term.Renaming Δ Δ') :
    (le_R f g).renameF r = le_R (f.rename r) (g.rename r) := by
  rw [Formula.renameF_eq_substF, le_R_substF, ← Term.rename_eq_subst, ← Term.rename_eq_subst]

theorem le_Q_renameF {Δ Δ' : Ctx ι} (a b : Term F Δ Ty.nat) (r : Term.Renaming Δ Δ') :
    (le_Q a b).renameF r = le_Q (a.rename r) (b.rename r) := by
  simp only [le_Q, Formula.renameF, Term.rename, Term.app2, le_Q_dec_rename']

theorem lt_Q_renameF {Δ Δ' : Ctx ι} (a b : Term F Δ Ty.nat) (r : Term.Renaming Δ Δ') :
    (lt_Q a b).renameF r = lt_Q (a.rename r) (b.rename r) := by
  simp only [lt_Q, Formula.renameF, Term.rename, Term.app2, lt_Q_dec_rename']

/-- `leIdx` commutes with substitution — the matrix stays folded. -/
@[simp] theorem leIdx_substF {Δ : Ctx ι} (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat)
    (σ : Term.Subst F Γ Δ) :
    (leIdx f g m).substF σ = leIdx (f.subst σ) (g.subst σ) (m.subst σ) := by
  simp only [leIdx, Formula.substF, Term.subst, Term.app2, le_Q_dec_closed_subst,
    pow2neg_Q_closed_subst, sub_Q_closed_subst, cauchyfy_closed_subst]

theorem leIdx_renameF {Δ : Ctx ι} (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat)
    (r : Term.Renaming Γ Δ) :
    (leIdx f g m).renameF r = leIdx (f.rename r) (g.rename r) (m.rename r) := by
  simp only [leIdx, Formula.renameF, Term.rename, Term.app2, le_Q_dec_rename',
    pow2neg_Q_rename', sub_Q_rename', cauchyfy_rename']

theorem leIdx_weakenBy {ρ : Ty ι} (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    Formula.weakenBy ρ (leIdx f g m) = leIdx f.weaken g.weaken m.weaken := by
  rw [← Formula.substF_shift_eq_weakenBy, leIdx_substF, Term.subst_shift_eq_weaken,
    Term.subst_shift_eq_weaken, Term.subst_shift_eq_weaken]

theorem weakenBy_all {ρ τ : Ty ι} (A : Formula F (τ :: Γ)) :
    Formula.weakenBy ρ (Formula.all τ A)
      = Formula.all τ (A.renameF (Term.Renaming.ext Term.Renaming.shift)) := rfl

theorem weakenBy_ex {ρ τ : Ty ι} (A : Formula F (τ :: Γ)) :
    Formula.weakenBy ρ (Formula.ex τ A)
      = Formula.ex τ (A.renameF (Term.Renaming.ext Term.Renaming.shift)) := rfl

theorem weakenBy_or {ρ : Ty ι} (A B : Formula F Γ) :
    Formula.weakenBy ρ (A ∨ᶠ B) = (Formula.weakenBy ρ A ∨ᶠ Formula.weakenBy ρ B) := rfl

end Norm

/-- **The normalisation the ℝ-MCT scripts run after every `pinduction`/`pinst`/`pexists`
and every `pforall`.** `mnorm`'s rule set, plus: `weakenBy` pushed through *every* formula
former including `∀`/`∃` (so a weakened hypothesis is instantiated with `pinst h xₖ`, never
`pspecialize`), `renameF` pushed to the terms, `leIdx`/`le_R`/`le_Q`/`lt_Q`/`const_R` kept
folded, and every closed constant fixed under renaming. -/
macro "rmnorm" : tactic =>
  `(tactic| (try anorm_cons
             simp only [List.map_cons, List.map_nil, le_R_substF, const_R_subst, leIdx_substF,
               Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst, Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               Term.weaken_subst0, subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, ProofMode.succVar0, closed_subst, add_closed_subst,
               abs_R_closed_subst, sub_R_closed_subst, add_R_closed_subst, neg_R_closed_subst,
               zero_R_closed_subst, one_R_closed_subst, mul_R_closed_subst,
               Term.Renaming.ext, Term.Renaming.shift,
               weakenBy_eq0, weakenBy_and, weakenBy_bot, Formula.weakenBy_imp,
               weakenBy_all, weakenBy_ex, weakenBy_or,
               le_Q_weakenBy, lt_Q_weakenBy, le_R_weakenBy, leIdx_weakenBy,
               Formula.renameF, le_R_renameF, le_Q_renameF, lt_Q_renameF, leIdx_renameF,
               const_R_rename, rename_ext_weaken,
               Term.rename, Term.rename_shift, rename_vs_eq_weaken,
               cauchyfy_rename', abs_R_rename', sub_R_rename', add_R_rename', neg_R_rename',
               zero_R_rename', one_R_rename', pow2neg_Q_rename', le_Q_dec_rename',
               lt_Q_dec_rename', sub_Q_rename', add_Q_rename', mul_Q_rename',
               encode_nat_Q_rename', exp2_rename', add_rename', zero_Q_rename', one_Q_rename',
               weaken_app, weaken_succ, weaken_zero, cauchyfy_weaken', abs_R_weaken', sub_R_weaken,
               add_R_weaken', neg_R_weaken', pow2neg_Q_weaken', le_Q_dec_weaken',
               lt_Q_dec_weaken', sub_Q_weaken', add_Q_weaken', mul_Q_weaken',
               encode_nat_Q_weaken', exp2_weaken', add_weaken', zero_R_weaken, one_R_weaken',
               const_R_weaken, zero_Q_weaken', one_Q_weaken']
             try anorm_cons))

-- The conclusion matrix, negated: `¬C(m)` is a rational inequality

/-- `¬ leIdx f g m` is `¬¬(2^{-m} ≤ℚ f̂(m+1) −ℚ ĝ(m+1))`; the matrix is quantifier-free, so
`qf_double_neg_elim` returns the rational fact. No `Derivable.markov`, no `lem`. -/
def leIdx_dne (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (¬ᶠ (leIdx f g m) →ᶠ
        le_Q (.app Term.pow2neg_Q m)
          (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy f (.app .succ m))
            (Term.app2 Term.cauchyfy g (.app .succ m)))) :=
  qf_double_neg_elim rfl

-- The budget: `q_j := ⟨j ·ℚ 2^{-(k+1)}⟩ℝ`, three rational identities

section Budget

/-- `encode_nat_Q 0 =₀ 0ℚ`: `pair (2·0) 0` is `pair 0 0` on the nose. -/
def encode_zero_eq (Γ : Ctx ι) :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.encode_nat_Q Term.zero) Term.zero_Q) :=
  qtrans (encode_nat_Q_unfold Term.zero)
    (qfer_no_premise_nat_nf (mul_zero (Term.ofNat 2))
      (r := Term.app2 Term.pair (.var .vz) Term.zero) (by qb_nf; try rfl) (by qb_nf; try rfl))

/-- `0ℚ ·ℚ e =ℚ 0ℚ`, by `x =ℚ x +ℚ x` (distributivity over `0 +ℚ 0`) and cancellation. -/
def zero_mul_Q_eq (e : Term F Γ Ty.nat) :
    Derivable F al Premises (eq_Q (Term.app2 Term.mul_Q Term.zero_Q e) Term.zero_Q) :=
  let x : Term F Γ Ty.nat := Term.app2 Term.mul_Q Term.zero_Q e
  let hxx : Derivable F al Premises (eq_Q x (Term.app2 Term.add_Q x x)) :=
    eqQtrans (mulQl (eqQsym (add_Q_zero_inst Term.zero_Q)) e)
      (eqQtrans (mul_Q_comm_inst (Term.app2 Term.add_Q Term.zero_Q Term.zero_Q) e)
        (eqQtrans (distrib_Q_inst e Term.zero_Q Term.zero_Q)
          (eqQtrans (addQl (mul_Q_comm_inst e Term.zero_Q) (Term.app2 Term.mul_Q e Term.zero_Q))
            (addQr x (mul_Q_comm_inst e Term.zero_Q)))))
  eqQtrans (eqQsym (add_Q_sub_cancel_l x x))
    (eqQtrans (sub_Q_congr (eqQsym hxx) (eq_Q_refl_inst x)) (sub_Q_self x))

/-- `q_0 ≤ℚ 0ℚ`. -/
def budget_zero_Q (e : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q (.app Term.encode_nat_Q Term.zero) e) Term.zero_Q) :=
  le_Q_of_eq_Q (eqQtrans (mulQl (eqQ_of_nat_eq' (encode_zero_eq Γ)) e) (zero_mul_Q_eq e))

/-- `q_{j+1} ≤ℚ q_j +ℚ e`: `encode (S j) =ℚ encode j +ℚ 1`, distribute, `e ·ℚ 1 =ℚ e`. -/
def budget_succ_Q (j e : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app .succ j)) e)
        (Term.app2 Term.add_Q (Term.app2 Term.mul_Q (.app Term.encode_nat_Q j) e) e)) :=
  let ej : Term F Γ Ty.nat := .app Term.encode_nat_Q j
  le_Q_of_eq_Q
    (eqQtrans (mulQl (encode_succ j) e)
      (eqQtrans (mul_Q_comm_inst (Term.app2 Term.add_Q ej Term.one_Q) e)
        (eqQtrans (distrib_Q_inst e ej Term.one_Q)
          (eqQtrans (addQl (mul_Q_comm_inst e ej) (Term.app2 Term.mul_Q e Term.one_Q))
            (addQr (Term.app2 Term.mul_Q ej e) (mul_Q_one_inst e))))))

/-- `2^{-0} =₀ 1ℚ`: `pair 2 (pd (exp2 0)) =₀ pair 2 0`. -/
def pow2neg_zero_eq (Γ : Ctx ι) :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.pow2neg_Q Term.zero) Term.one_Q) :=
  let hpd : Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.pd (.app Term.exp2 Term.zero)) Term.zero) :=
    qtrans (qfer_no_premise_nat_nf exp2_zero (r := .app Term.pd (.var .vz))
        (by qb_nf; try rfl) (by qb_nf; try rfl))
      (pd_succ Term.zero)
  qtrans (pow2neg_Q_unfold Term.zero)
    (qfer_no_premise_nat_nf hpd (r := Term.app2 Term.pair (Term.ofNat 2) (.var .vz))
      (by qb_nf; try rfl) (by qb_nf; try rfl))

/-- `1ℚ ≤ℚ q_{2^{k+1}}`: `⟨2^{k+1}⟩ ·ℚ 2^{-(k+1)} =ℚ 2^{-0} =ℚ 1` (`encode_pow2_mul`). -/
def budget_top_Q (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q Term.one_Q
        (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app Term.exp2 (.app .succ k)))
          (.app Term.pow2neg_Q (.app .succ k)))) :=
  let sk : Term F Γ Ty.nat := .app .succ k
  let hidx : Derivable F al Premises
      (Formula.eq0 (.app Term.pow2neg_Q (Term.app2 Term.add sk Term.zero))
        (.app Term.pow2neg_Q sk)) :=
    qfer_no_premise_nat_nf (add_zero_r sk) (r := .app Term.pow2neg_Q (.var .vz))
      (by qb_nf) (by qb_nf)
  le_Q_of_eq_Q
    (eqQtrans (eqQ_of_nat_eq' (Derivable.mp (pow2neg_zero_eq Γ) Derivable.sym0))
      (eqQtrans (eqQsym (encode_pow2_mul sk Term.zero))
        (mulQr (.app Term.encode_nat_Q (.app Term.exp2 sk)) (eqQ_of_nat_eq' hidx))))

/-- `q_0 ≤ℝ 0ℝ`. -/
def budget_zero_R (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (const_R (Term.app2 Term.mul_Q (.app Term.encode_nat_Q Term.zero)
                (.app Term.pow2neg_Q (.app .succ k))))
            Term.zero_R) :=
  Eq.mpr (congrArg (fun z => Derivable F al Premises
      (le_R (const_R (Term.app2 Term.mul_Q (.app Term.encode_nat_Q Term.zero)
        (.app Term.pow2neg_Q (.app .succ k)))) z)) zero_R_eq_const)
    (Derivable.mp (budget_zero_Q _) (const_R_mono _ Term.zero_Q))

/-- `q_{j+1} ≤ℝ q_j +ℝ ε`. -/
def budget_succ_R (j k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (const_R (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app .succ j))
                (.app Term.pow2neg_Q (.app .succ k))))
            (Term.app2 Term.add_R
              (const_R (Term.app2 Term.mul_Q (.app Term.encode_nat_Q j)
                (.app Term.pow2neg_Q (.app .succ k))))
              (const_R (.app Term.pow2neg_Q (.app .succ k))))) :=
  Derivable.mp (budget_succ_Q j _) (const_R_le_add _ _ _)

/-- `1ℝ ≤ℝ q_{2^{k+1}}`. -/
def one_R_le_budget (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R Term.one_R
        (const_R (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app Term.exp2 (.app .succ k)))
          (.app Term.pow2neg_Q (.app .succ k))))) :=
  Eq.mpr (congrArg (fun z => Derivable F al Premises
      (le_R z (const_R (Term.app2 Term.mul_Q
        (.app Term.encode_nat_Q (.app Term.exp2 (.app .succ k)))
        (.app Term.pow2neg_Q (.app .succ k)))))) one_R_eq_const)
    (Derivable.mp (budget_top_Q k) (const_R_mono Term.one_Q _))

end Budget

-- The window lemma: every window is good, or it drops by the budget unit

/-- **The window lemma.** Under the premise `∀u B`, for every `m`: either `∃n C(n)` (with
`n := m`), or `0ℝ ≤ℝ a(m+gm)` and `a(m+gm) +ℝ ε ≤ℝ a m`. The book's single step. -/
def real_mct_window (a : Term F Γ (Ty.nat →ₜ realTy ι)) (g : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat                            -- u = x₀, n = x₁
          (leIdx (a ⬝ S x₁) (a ⬝ x₁) x₀ ∧ᶠ leIdx Term.zero_R (a ⬝ x₁) x₀
            ∧ᶠ leIdx (a ⬝ x₁) Term.one_R x₀))
       →ᶠ Formula.all Ty.nat                                             -- m = x₀
            (Formula.ex Ty.nat                                           -- n = x₁
               (leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₁) ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))))
                  (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k)))
             ∨ᶠ (le_R Term.zero_R (a ⬝ (x₀ +ᵗ g ⬝ x₀))
                 ∧ᶠ le_R (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
                         (a ⬝ x₀)))) := by
  pmode
  pintro H
  pforall                       -- m = x₀
  rmnorm
  -- one-step antitonicity, as a ∀ over `le_R`, from the premise's first conjunct
  phave hstep : Formula.all Ty.nat (le_R (a ⬝ S x₁) (a ⬝ x₁))
  · pforall                     -- n = x₁
    papply (le_R_of_le_R_pu (a ⬝ S x₁) (a ⬝ x₁))
    pforall                     -- u = x₂
    rmnorm
    pinst H x₂ with Hu
    rmnorm
    pinst Hu x₁ with Hn
    rmnorm
    pdestruct Hn with H12 H3
    pdestruct H12 with H1 H2
    pexact H1
  -- `0 ≤ a(m + g m)`, from the second conjunct
  phave h0 : le_R Term.zero_R (a ⬝ (x₀ +ᵗ g ⬝ x₀))
  · papply (le_R_of_le_R_pu Term.zero_R (a ⬝ (x₀ +ᵗ g ⬝ x₀)))
    pforall                     -- u = x₁
    rmnorm
    pinst H x₁ with Hu
    rmnorm
    pinst Hu (x₀ +ᵗ g ⬝ x₀) with Hn
    rmnorm
    pdestruct Hn with H12 H3
    pdestruct H12 with H1 H2
    pexact H2
  -- `a(m + g m) ≤ a m`: the antitone chain at `i := g m`
  pfrom ac := antitone_chain_R a
  pinst ac (g ⬝ x₀) with ac1
  rmnorm
  pinst ac1 x₀ with ac2
  rmnorm
  papply ac2 in hstep with hanti
  -- the dichotomy on the quantifier-free matrix
  phave hlem :
      leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
          (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k))
      ∨ᶠ ¬ᶠ (leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
          (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k)))
  · pthm (qf_lem rfl)
  pcases hlem with hgood | hbad
  · -- good: `m` is the witness
    pleft
    pexists x₀
    rmnorm
    pexact hgood
  · -- bad: the window drops by `ε`
    pright
    psplit
    · pexact h0
    · papplym (leIdx_dne (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
        (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k))) in hbad with hX
      prw (cauchyfy_const (Term.pow2neg_Q ⬝ (S k)) (S (S (S k)))) in hX with hX'
      papply (window_drop (a ⬝ x₀) (a ⬝ (x₀ +ᵗ g ⬝ x₀)) k)
      · pexact hanti
      · pexact hX'

-- The budget descent

/-- **The budget descent.** `∀j ((∀u B) → ∀m (a m ≤ℝ q_j → ∃n C(n)))`. -/
def real_mct_descent (a : Term F Γ (Ty.nat →ₜ realTy ι)) (g : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat                                                -- j = x₀
        (Formula.all Ty.nat (Formula.all Ty.nat                          -- u = x₁, n = x₂
            (leIdx (a ⬝ S x₂) (a ⬝ x₂) x₁ ∧ᶠ leIdx Term.zero_R (a ⬝ x₂) x₁
              ∧ᶠ leIdx (a ⬝ x₂) Term.one_R x₁))
         →ᶠ Formula.all Ty.nat                                           -- m = x₁
              (le_R (a ⬝ x₁)
                 (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
               →ᶠ Formula.ex Ty.nat                                      -- n = x₂
                    (leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₂) ⬝ (a ⬝ (x₂ +ᵗ g ⬝ x₂))))
                      (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k)))))) := by
  pmode
  pinduction
  · -- j = 0 : a bad window would put `ε` below `0`
    rmnorm
    pintro H
    papplym (real_mct_window a g k) in H with hw
    pforall                     -- m = x₀
    pintro hm
    rmnorm
    pinst hw x₀ with hwm
    rmnorm
    pcases hwm with hgood | hbad
    · pexact hgood
    · pdestruct hbad with h0 hd
      pexfalso
      phave hε0 : le_R (const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R
      · papply (le_R_trans_core (const_R (Term.pow2neg_Q ⬝ (S k)))
          (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R)
        psplit
        · pthm (le_R_zero_add (const_R (Term.pow2neg_Q ⬝ (S k))))
        · papply (le_R_trans_core (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
            (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R)
          psplit
          · papply (le_R_add_mono_r_core Term.zero_R (a ⬝ (x₀ +ᵗ g ⬝ x₀))
              (const_R (Term.pow2neg_Q ⬝ (S k))))
            pexact h0
          · papply (le_R_trans_core
              (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              (a ⬝ x₀) Term.zero_R)
            psplit
            · pexact hd
            · papply (le_R_trans_core (a ⬝ x₀)
                (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ Term.zero) ⬝ (Term.pow2neg_Q ⬝ (S k))))
                Term.zero_R)
              psplit
              · pexact hm
              · pthm (budget_zero_R k)
      papply hε0
      pthm (zero_lt_pow2neg_R (S k))
  · -- j → j+1 : a bad window pays one unit, and the induction hypothesis applies at m + g m
    pforall                     -- j = x₀
    pintro ih
    rmnorm
    pintro H
    papplym (real_mct_window a g k) in H with hw
    papply ih in H with ih1
    pforall                     -- m = x₁
    pintro hm
    rmnorm
    pinst hw x₁ with hwm
    rmnorm
    pcases hwm with hgood | hbad
    · pexact hgood
    · pdestruct hbad with h0 hd
      phave hle : le_R (a ⬝ (x₁ +ᵗ g ⬝ x₁))
          (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
      · papply (le_R_add_cancel_r_core (a ⬝ (x₁ +ᵗ g ⬝ x₁))
          (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
          (const_R (Term.pow2neg_Q ⬝ (S k))))
        papply (le_R_trans_core
          (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
          (a ⬝ x₁)
          (Term.add_R ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
            ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
        psplit
        · pexact hd
        · papply (le_R_trans_core (a ⬝ x₁)
            (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (S x₀)) ⬝ (Term.pow2neg_Q ⬝ (S k))))
            (Term.add_R ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
              ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
          psplit
          · pexact hm
          · pthm (budget_succ_R x₀ k)
      pinst ih1 (x₁ +ᵗ g ⬝ x₁) with ih2
      rmnorm
      papply ih2 in hle with hex
      pexact hex

-- Closing: `A(2^{k+1})` at `m := 0`, and the statement

/-- **The body of the statement** over separate `a`, `g`, `k`: `(∀u B) →ᶠ ∃n C(n)`. -/
def real_mct_body (a : Term F Γ (Ty.nat →ₜ realTy ι)) (g : Term F Γ (Ty.nat →ₜ Ty.nat))
    (k : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat                            -- u = x₀, n = x₁
          (leIdx (a ⬝ S x₁) (a ⬝ x₁) x₀ ∧ᶠ leIdx Term.zero_R (a ⬝ x₁) x₀
            ∧ᶠ leIdx (a ⬝ x₁) Term.one_R x₀))
       →ᶠ Formula.ex Ty.nat                                              -- n = x₀
            (leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
              (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k)))) := by
  pmode
  pintro H
  pfrom d := real_mct_descent a g k
  pinst d (Term.exp2 ⬝ (S k)) with d1
  rmnorm
  papply d1 in H with d2
  pinst d2 Term.zero with d3
  rmnorm
  papply d3
  -- a 0 ≤ 1 ≤ q_{2^{k+1}}
  papply (le_R_trans_core (a ⬝ Term.zero) Term.one_R
    (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k))) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
  psplit
  · papply (le_R_of_le_R_pu (a ⬝ Term.zero) Term.one_R)
    pforall                     -- u = x₀
    rmnorm
    pinst H x₀ with Hu
    rmnorm
    pinst Hu Term.zero with Hn
    rmnorm
    pdestruct Hn with H12 H3
    pexact H3
  · pthm (one_R_le_budget k)

/-- **ℝ-MCT, proof P2ℝ.** The dichotomy derivation of `RealMCT.rmStatement`, at any
`Allowed` — in particular at `Allowed.extended`. `a`, `g`, `k` are the three projections of the
single quantified `x`, exactly as `RealMCTStatement.lean` reads them. -/
def real_mct_p2 : Derivable F al Premises (Γ := []) RealMCT.rmStatement := by
  pmode
  pforall
  pthm (real_mct_body (Term.fst x₀) (Term.fst (Term.snd x₀)) (Term.snd (Term.snd x₀)))

/-! ## It goes through the metatheorem

`RealMCTStatement.lean` checked that the statement fits `syntactic_general_metatheorem_at_gen`
with the derivation as a hypothesis. That hypothesis is now discharged: the bound is data. -/

section Extraction

variable {X : ι → Type} {si : SpaceInterp X F}

/-- **The bound for P2ℝ.** `rmBound` at `real_mct_p2`; elaborating is the check that the
derivation has the shape the metatheorem wants. -/
def real_mct_bound_p2 (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am) :=
  RealMCT.rmBound eqxi spremise cm (real_mct_p2 (al := Allowed.extended))

end Extraction

#print axioms leIdx_dne
#print axioms budget_zero_Q
#print axioms budget_succ_Q
#print axioms budget_top_Q
#print axioms real_mct_window
#print axioms real_mct_descent
#print axioms real_mct_body
#print axioms real_mct_p2
#print axioms real_mct_bound_p2

end ProofMode
end Metatheorems
