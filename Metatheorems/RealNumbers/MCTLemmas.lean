/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.LeOrder

namespace Metatheorems

/-! **No `import Metatheorems.ProofMode.Arith` here.** That module declares the *global*
notations `S`, `+ᵗ`, `∸ᵗ`, `*ᵗ`, `pdᵗ`; importing it from a module below the `RealNumbers`
umbrella leaks them into every importer of the umbrella, and `MetricSpaces.lean` uses `S` as
an identifier (found 2026-09-05: the full build broke at `MetricSpaces.lean:717` with
"unexpected token 'S'"). So this file spells `S t` as `.app .succ t`, `s +ᵗ t` as
`Term.app2 Term.add s t`, and carries its own copy of `anorm_cons`'s rule list (`mcons`). -/

/-!
# The ℝ lemmas the ℝ-MCT derivation needs (`REAL_MCT.md` §5, revised)

`ProofMode/RealMCT.lean` derives the real-number monotone convergence theorem in metastable
form. Its descent runs entirely at the level of `≤_ℝ` — every estimate it needs is already
paid inside `LeOrder.lean`'s package — and what was missing was *assembly*: constants,
cancellation, absolute value, the antitone chain over the reals. This file is that assembly.

## Design rules, and where the plan (`REAL_MCT.md` §5) was revised

* **Everything with a rational side condition is an object implication.** There is no
  derivation-weakening combinator (`Derivable … A` in `Γ` does not give one in `ρ :: Γ`), so a
  lemma whose ℚ hypothesis arises *inside* a sequent — under the `∀n` of `le_R_of_all`, or in
  the bad branch of the dichotomy — cannot take it as a Lean-level argument. `const_R_mono`,
  `const_R_le_add`, `const_R_le_sub`, `zero_lt_const_R` and `const_le_R_of_sample` are all
  `… →ᶠ …`, and Lean-level uses go through `Derivable.mp`.
* **`≤` where the plan said `=`.** `const_R_add`/`const_R_sub`/`const_R_congr` were listed as
  `=ℝ` facts; the descent only ever needs one direction, and the `≤` versions are slack-free
  index-wise (`cauchyfy_const`, `cauchyfy_add_R`/`cauchyfy_sub_R`, then `p −ℚ q ≤ℚ 0 <ℚ 2^{-n}`).
  No `=ℝ` engine is touched.
* **`≤` where the plan said `<`.** `le_add_of_abs_sub_lt` became `le_add_of_abs_sub_le`,
  because `approx_le_R_core` already delivers `|f −ℝ ⟨f̂(n)⟩| ≤ℝ ⟨2^{-n}⟩` and the `≤` form is
  what chains; `approx_R`'s strict form is never used.
* **Algebra, not estimates.** `add_sub_cancel_le_R_core`, `le_add_sub_R`,
  `le_add_neg_cancel_R`, `le_R_add_cancel_r_core`, `sub_R_nonneg_of_le` are Lean-level chains
  of `le_R_of_eq_R_core` over the ring identities and the two monotonicity lemmas, exactly as
  `add_neg_cancel_le_R_core` is written. As the reverse-triangle note in CLAUDE.md predicts,
  each is tight as a direct estimate and free as algebra.
* **Transport along ℕ-equalities.** The antitone chain rewrites `a (m + S i)` to
  `a (S (m + i))` *inside* a `le_R`, which `prw` cannot do (the goal is not an equation).
  `le_R_app_congr_l` does it once: unpack the `¬∃`, and `prwby` the equation inside the
  quantifier-free witness. This lemma is the one genuinely new shape here.

## The two facts that carry the descent

* `window_drop`: a window that *fails* the conclusion matrix drops by the budget unit —
  `a(m+gm) ≤ℝ a m` and `2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ 2^{-(k+1)}` give
  `a(m+gm) +ℝ ⟨2^{-(k+1)}⟩ ≤ℝ a m`. The route is the plan's P3.2–P3.6: the sample bound
  lifts to `⟨2^{-(k+1)}⟩ ≤ℝ |a m −ℝ a(m+gm)|` through `approx_le_R_core`; antitonicity makes
  the difference nonnegative so `|w| ≤ℝ w`; monotonicity and `g +ℝ (f −ℝ g) ≤ℝ f` finish.
* `antitone_chain_R`: `∀i ∀m ((∀u a(Su) ≤ℝ a u) → a(m+i) ≤ℝ a m)`, the ℝ mirror of
  `ProofMode.antitone_chain`, by `pinduction` with `le_R_trans_core` and one transport per case.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section MCTLemmas

variable {Γ : Ctx ι}

-- ── Lean-level chaining combinators ─────────────────────────────────────────

/-- `≤ℝ`-transitivity as a Lean-level combinator. -/
def leRt {f g h : Term F Γ (realTy ι)}
    (h1 : Derivable F al Premises (le_R f g)) (h2 : Derivable F al Premises (le_R g h)) :
    Derivable F al Premises (le_R f h) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (le_R_trans_core f g h)

/-- `=ℝ` gives `≤ℝ`. -/
def leR_of_eq {f g : Term F Γ (realTy ι)} (h : Derivable F al Premises (eq_R f g)) :
    Derivable F al Premises (le_R f g) :=
  Derivable.mp h (le_R_of_eq_R_core f g)

def eqRsym {f g : Term F Γ (realTy ι)} (h : Derivable F al Premises (eq_R f g)) :
    Derivable F al Premises (eq_R g f) :=
  Derivable.mp h (eq_R_sym_core f g)

def eqRt {f g h : Term F Γ (realTy ι)}
    (h1 : Derivable F al Premises (eq_R f g)) (h2 : Derivable F al Premises (eq_R g h)) :
    Derivable F al Premises (eq_R f h) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (eq_R_trans_core f g h)

/-- Left additive monotonicity, Lean-level: `f ≤ℝ g → h +ℝ f ≤ℝ h +ℝ g`. -/
def leR_mono_l (h' : Term F Γ (realTy ι)) {f g : Term F Γ (realTy ι)}
    (h : Derivable F al Premises (le_R f g)) :
    Derivable F al Premises (le_R (Term.app2 Term.add_R h' f) (Term.app2 Term.add_R h' g)) :=
  Derivable.mp h (le_R_add_mono_l_core h' f g)

/-- Right additive monotonicity, Lean-level: `f ≤ℝ g → f +ℝ h ≤ℝ g +ℝ h`. -/
def leR_mono_r (h' : Term F Γ (realTy ι)) {f g : Term F Γ (realTy ι)}
    (h : Derivable F al Premises (le_R f g)) :
    Derivable F al Premises (le_R (Term.app2 Term.add_R f h') (Term.app2 Term.add_R g h')) :=
  Derivable.mp h (le_R_add_mono_r_core f g h')

-- ── Weakening of closed constants (the `_weaken'` family, for `mnorm`) ──────

theorem neg_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.neg_R : Term F Δ _).weaken (σ := ρ) = Term.neg_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact neg_R_closed_subst _

theorem neg_R_app_weaken'' {Δ : Ctx ι} {ρ : Ty ι} (g : Term F Δ (realTy ι)) :
    (Term.app Term.neg_R g).weaken (σ := ρ) = Term.app Term.neg_R g.weaken := by
  show Term.app ((Term.neg_R : Term F Δ _).weaken) g.weaken = _
  rw [neg_R_weaken']

theorem add_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.add_R : Term F Δ _).weaken (σ := ρ) = Term.add_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact add_R_closed_subst _

theorem one_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.one_R : Term F Δ (realTy ι)).weaken (σ := ρ) = Term.one_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_R_closed_subst _

theorem le_Q_dec_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.le_Q_dec : Term F Δ _).weaken (σ := ρ) = Term.le_Q_dec := by
  rw [Term.weaken, Term.rename_eq_subst]; exact le_Q_dec_closed_subst _

theorem lt_Q_dec_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.lt_Q_dec : Term F Δ _).weaken (σ := ρ) = Term.lt_Q_dec := by
  rw [Term.weaken, Term.rename_eq_subst]; exact lt_Q_dec_closed_subst _

theorem sub_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.sub_Q : Term F Δ _).weaken (σ := ρ) = Term.sub_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact sub_Q_closed_subst _

theorem add_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.add_Q : Term F Δ _).weaken (σ := ρ) = Term.add_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact add_Q_closed_subst _

theorem mul_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.mul_Q : Term F Δ _).weaken (σ := ρ) = Term.mul_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact mul_Q_closed_subst _

theorem encode_nat_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.encode_nat_Q : Term F Δ _).weaken (σ := ρ) = Term.encode_nat_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact encode_nat_Q_closed_subst _

theorem exp2_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.exp2 : Term F Δ _).weaken (σ := ρ) = Term.exp2 := by
  rw [Term.weaken, Term.rename_eq_subst]; exact exp2_closed_subst _

theorem add_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.add : Term F Δ _).weaken (σ := ρ) = Term.add := by
  rw [Term.weaken, Term.rename_eq_subst]; exact add_closed_subst _

theorem zero_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.zero_Q : Term F Δ _).weaken (σ := ρ) = Term.zero_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact zero_Q_closed_subst _

theorem one_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.one_Q : Term F Δ _).weaken (σ := ρ) = Term.one_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_Q_closed_subst _

theorem weaken_zero {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.zero : Term F Δ Ty.nat).weaken (σ := ρ) = Term.zero := rfl

/-- The eta-reduced spelling of `Renaming.shift` that `anorm_cons` leaves behind, folded back
to `Term.weaken` so that leaves match the coercion's spelling syntactically. -/
theorem rename_vs_eq_weaken {Δ : Ctx ι} {τ ρ : Ty ι} (t : Term F Δ τ) :
    t.rename (fun {τ'} (v : Var Δ τ') => Var.vs (σ := ρ) v) = t.weaken := rfl

-- ── `Formula.weakenBy` through the formula shapes a script `pexact`s ──────────
--
-- `pm_allI` wraps every hypothesis in `Formula.weakenBy`. For a `∀`-hypothesis that wrapper
-- is what `pspecialize`/`pinst` match on, so it is left alone; for a quantifier-free
-- hypothesis, or a `le_R`, it must become the *syntactic* weakening of the leaves, or the
-- final `pexact` unfolds a closed constant under a rename (the trap that killed the first
-- version of `const_R_mono`).

theorem weakenBy_eq0 {ρ : Ty ι} (s t : Term F Γ Ty.nat) :
    Formula.weakenBy ρ (Formula.eq0 s t) = Formula.eq0 s.weaken t.weaken := rfl

theorem weakenBy_and {ρ : Ty ι} (A B : Formula F Γ) :
    Formula.weakenBy ρ (A ∧ᶠ B) = (Formula.weakenBy ρ A ∧ᶠ Formula.weakenBy ρ B) := rfl

theorem weakenBy_bot {ρ : Ty ι} :
    Formula.weakenBy ρ (⊥ᶠ : Formula F Γ) = ⊥ᶠ := rfl

theorem le_Q_weakenBy {ρ : Ty ι} (a b : Term F Γ Ty.nat) :
    Formula.weakenBy ρ (le_Q a b) = le_Q a.weaken b.weaken := by
  rw [← Formula.substF_shift_eq_weakenBy]
  simp only [le_Q, Formula.substF, Term.subst, Term.app2, le_Q_dec_closed_subst,
    Term.subst_shift_eq_weaken]

theorem lt_Q_weakenBy {ρ : Ty ι} (a b : Term F Γ Ty.nat) :
    Formula.weakenBy ρ (lt_Q a b) = lt_Q a.weaken b.weaken := by
  rw [← Formula.substF_shift_eq_weakenBy]
  simp only [lt_Q, Formula.substF, Term.subst, Term.app2, lt_Q_dec_closed_subst,
    Term.subst_shift_eq_weaken]

theorem le_R_weakenBy {ρ : Ty ι} (f g : Term F Γ (realTy ι)) :
    Formula.weakenBy ρ (le_R f g) = le_R f.weaken g.weaken := by
  rw [← Formula.substF_shift_eq_weakenBy, le_R_substF, Term.subst_shift_eq_weaken,
    Term.subst_shift_eq_weaken]

/-- `0ℝ` is the constant real at `0ℚ`. -/
theorem zero_R_eq_const : (Term.zero_R : Term F Γ (realTy ι)) = const_R Term.zero_Q := by
  show Term.lam Term.zero_Q = Term.lam (Term.zero_Q.weaken)
  rw [Term.weaken, Term.rename_eq_subst, zero_Q_closed_subst]

/-- `1ℝ` is the constant real at `1ℚ`. -/
theorem one_R_eq_const : (Term.one_R : Term F Γ (realTy ι)) = const_R Term.one_Q := by
  show Term.lam Term.one_Q = Term.lam (Term.one_Q.weaken)
  rw [Term.weaken, Term.rename_eq_subst, one_Q_closed_subst]

/-- **The normalisation the ℝ-MCT scripts use.** `anorm`'s substitution rules, plus
`le_R_substF`/`const_R_subst` so `le_R` and constants stay folded, plus the `weakenBy` lemmas
above (a weakened QF or `le_R` hypothesis becomes the syntactic weakening of its leaves), a
rename push/fold pair, and a `_weaken'` cleanup for every closed constant the derivation
mentions. The goal is that a hypothesis weakened by `pforall` and a lemma instance elaborated
with the weakening *coercion* agree syntactically, so `pexact` never has to unfold a closed
constant under a rename (CLAUDE.md trap 12). `∀`-hypotheses keep their `weakenBy` wrapper,
which is what `pspecialize`/`pinst` match on.

`mcons` is `ProofMode.Arith`'s `anorm_cons`, copied verbatim (that module cannot be imported
here; see the note at the top of the file). -/
macro "mcons" : tactic =>
  `(tactic| simp only [
      Formula.subst0_renameF_ext, Formula.substF_subst0_map_renameF_ext,
      Formula.substF_cons_renameF_ext,
      Term.subst_subst0_map_rename_ext, Term.subst_cons_rename_ext,
      Term.subst_cons_weaken, Term.Subst.cons_vz, Term.Subst.cons_vs,
      Term.rename_comp, Term.rename_shift, Term.Renaming.comp_apply,
      Term.Renaming.shift])

macro "mnorm" : tactic =>
  `(tactic| (try mcons
             simp only [List.map_cons, List.map_nil, le_R_substF, const_R_subst,
               Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst, Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               Term.weaken_subst0, subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, ProofMode.succVar0, closed_subst, add_closed_subst,
               abs_R_closed_subst, sub_R_closed_subst, add_R_closed_subst, neg_R_closed_subst,
               zero_R_closed_subst, one_R_closed_subst, mul_R_closed_subst,
               weakenBy_eq0, weakenBy_and, weakenBy_bot, Formula.weakenBy_imp,
               le_Q_weakenBy, lt_Q_weakenBy, le_R_weakenBy,
               Term.rename, Term.rename_shift, rename_vs_eq_weaken,
               weaken_app, weaken_succ, weaken_zero, cauchyfy_weaken', abs_R_weaken', sub_R_weaken,
               add_R_weaken', neg_R_weaken', pow2neg_Q_weaken', le_Q_dec_weaken',
               lt_Q_dec_weaken', sub_Q_weaken', add_Q_weaken', mul_Q_weaken',
               encode_nat_Q_weaken', exp2_weaken', add_weaken', zero_R_weaken, one_R_weaken',
               const_R_weaken, zero_Q_weaken', one_Q_weaken']
             try mcons))

-- ── ℚ helpers ───────────────────────────────────────────────────────────────

/-- `x ≤ℚ y → x −ℚ y ≤ℚ 0`. -/
def sub_Q_nonpos_of_le (x y : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q x y →ᶠ le_Q (Term.app2 Term.sub_Q x y) Term.zero_Q) :=
  le_Q_of_eq_Q_diff x y (Term.app2 Term.sub_Q x y) Term.zero_Q
    (eqQtrans (eqQsym (neg_Q_sub_Q y x)) (eqQsym (sub_Q_zero_l (Term.app2 Term.sub_Q x y))))

/-- **The slack-free index step**: `x ≤ℚ y → x −ℚ y <ℚ 2^{-n}`. Every `≤ℝ` fact about
constants below reduces to this at each index. -/
def lt_pow2neg_of_le (x y n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q x y →ᶠ lt_Q (Term.app2 Term.sub_Q x y) (.app Term.pow2neg_Q n)) := by
  pmode
  pintro h
  papply (le_lt_Q_trans (Term.app2 Term.sub_Q x y) Term.zero_Q (.app Term.pow2neg_Q n))
  psplit
  · papply (sub_Q_nonpos_of_le x y)
    pexact h
  · pthm (zero_lt_pow2neg_Q n)

/-- `a ≤ℚ c −ℚ b → b +ℚ a ≤ℚ c`. -/
def le_Q_add_of_le_sub (a c b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a (Term.app2 Term.sub_Q c b) →ᶠ le_Q (Term.app2 Term.add_Q b a) c) :=
  le_Q_of_eq_Q_diff a (Term.app2 Term.sub_Q c b) (Term.app2 Term.add_Q b a) c
    (sub_Q_sub c b a)

/-- `=ℚ` gives `≤ℚ`. -/
def le_Q_of_eq_Q {x y : Term F Γ Ty.nat} (h : Derivable F al Premises (eq_Q x y)) :
    Derivable F al Premises (le_Q x y) :=
  Derivable.mp (le_Q_refl x) (le_Q_congr x x x y (eq_Q_refl_inst x) h)

-- ── Constants ───────────────────────────────────────────────────────────────

/-- **M1.** `p ≤ℚ q → ⟨p⟩ℝ ≤ℝ ⟨q⟩ℝ`. Slack-free: both cauchyfications are the constants. -/
def const_R_mono (p q : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q p q →ᶠ le_R (const_R p) (const_R q)) := by
  pmode
  pintro h
  papply (le_R_of_all (const_R p) (const_R q))
  simp only [const_R_weaken]
  pforall
  prw (cauchyfy_const p.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_const q.weaken (.app .succ (.var .vz)))
  papply (lt_pow2neg_of_le p.weaken q.weaken (.var .vz))
  mnorm
  pexact h

/-- **M2, `≤` form.** `p ≤ℚ q +ℚ r → ⟨p⟩ℝ ≤ℝ ⟨q⟩ℝ +ℝ ⟨r⟩ℝ`. `add_R`'s `+1` shift is
harmless: the summands are constants at every index. -/
def const_R_le_add (p q r : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q p (Term.app2 Term.add_Q q r) →ᶠ
        le_R (const_R p) (Term.app2 Term.add_R (const_R q) (const_R r))) := by
  pmode
  pintro h
  papply (le_R_of_all (const_R p) (Term.app2 Term.add_R (const_R q) (const_R r)))
  simp only [const_R_weaken, add_R_app_weaken]
  pforall
  prw (cauchyfy_const p.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_add_R (const_R q.weaken) (const_R r.weaken) (.app .succ (.var .vz)))
  prw (cauchyfy_const q.weaken (.app .succ (.app .succ (.var .vz))))
  prw (cauchyfy_const r.weaken (.app .succ (.app .succ (.var .vz))))
  papply (lt_pow2neg_of_le p.weaken (Term.app2 Term.add_Q q.weaken r.weaken) (.var .vz))
  mnorm
  pexact h

/-- **M2, subtraction.** `p +ℚ r ≤ℚ q → ⟨p⟩ℝ ≤ℝ ⟨q⟩ℝ −ℝ ⟨r⟩ℝ`. -/
def const_R_le_sub (p q r : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q p r) q →ᶠ
        le_R (const_R p) (Term.app2 Term.sub_R (const_R q) (const_R r))) := by
  pmode
  pintro h
  papply (le_R_of_all (const_R p) (Term.app2 Term.sub_R (const_R q) (const_R r)))
  simp only [const_R_weaken, sub_R_app_weaken]
  pforall
  prw (cauchyfy_const p.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_sub_R (const_R q.weaken) (const_R r.weaken) (.app .succ (.var .vz)))
  prw (cauchyfy_const q.weaken (.app .succ (.app .succ (.var .vz))))
  prw (cauchyfy_const r.weaken (.app .succ (.app .succ (.var .vz))))
  papply (lt_pow2neg_of_le p.weaken
    (Term.app2 Term.add_Q q.weaken (.app Term.neg_Q r.weaken)) (.var .vz))
  papply (le_Q_congr p.weaken (Term.app2 Term.sub_Q q.weaken r.weaken)
    p.weaken (Term.app2 Term.add_Q q.weaken (.app Term.neg_Q r.weaken))
    (eq_Q_refl_inst _) (sub_Q_eq_add_neg q.weaken r.weaken))
  papply (le_Q_sub_of_add_le r.weaken p.weaken q.weaken)
  papply (le_Q_congr (Term.app2 Term.add_Q p.weaken r.weaken) q.weaken
    (Term.app2 Term.add_Q r.weaken p.weaken) q.weaken
    (add_Q_comm_inst _ _) (eq_Q_refl_inst _))
  mnorm
  pexact h

/-- **M7, in the form the base case needs**: `2^{-n} ≤ℚ q → 0ℝ <ℝ ⟨q⟩ℝ`, with `n` the
witness. -/
def zero_lt_const_R (q n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.pow2neg_Q n) q →ᶠ lt_R Term.zero_R (const_R q)) := by
  pmode
  pintro h
  pexists n
  canorm
  prw (cauchyfy_const q (.app .succ n))
  prw (cauchyfy_zero_R (.app .succ n))
  papply (le_Q_congr (.app Term.pow2neg_Q n) q (.app Term.pow2neg_Q n)
    (Term.app2 Term.sub_Q q Term.zero_Q) (eq_Q_refl_inst _) (eqQsym (sub_Q_zero_Q q)))
  pexact h

/-- `0ℝ <ℝ ⟨2^{-n}⟩ℝ`. -/
def zero_lt_pow2neg_R (n : Term F Γ Ty.nat) :
    Derivable F al Premises (lt_R Term.zero_R (const_R (.app Term.pow2neg_Q n))) :=
  Derivable.mp (le_Q_refl _) (zero_lt_const_R (.app Term.pow2neg_Q n) n)

-- ── Absolute value and sign ─────────────────────────────────────────────────

/-- `w ≤ℝ |w|ℝ`. Slack-free: `le_Q_self_abs` at every index. -/
def le_abs_R (w : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R w (.app Term.abs_R w)) :=
  le_R_of_bound w (.app Term.abs_R w) (by
    rw [abs_R_app_weaken]
    pmode
    prw (cauchyfy_abs_R w.weaken (.app .succ (.var .vz)))
    papply (lt_pow2neg_of_le _ _ _)
    pthm (le_Q_self_abs (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))

/-- `−ℝ w ≤ℝ |w|ℝ`. -/
def neg_le_abs_R (w : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R (.app Term.neg_R w) (.app Term.abs_R w)) :=
  le_R_of_bound (.app Term.neg_R w) (.app Term.abs_R w) (by
    rw [abs_R_app_weaken, neg_R_app_weaken'']
    pmode
    prw (cauchyfy_abs_R w.weaken (.app .succ (.var .vz)))
    prw (cauchyfy_neg w.weaken (.app .succ (.var .vz)))
    papply (lt_pow2neg_of_le _ _ _)
    papply (le_Q_congr
      (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
      (.app Term.abs_Q (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))
      (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
      (.app Term.abs_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
      (eq_Q_refl_inst _)
      (abs_Q_neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))
    pthm (le_Q_self_abs (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))))

/-- **M4a.** `0ℝ ≤ℝ w → −ℝ w ≤ℝ 0ℝ`. Slack-free: the same index, `0 −ℚ ŵ` against
`−ℚ ŵ −ℚ 0`. -/
def neg_R_nonpos_of_nonneg (w : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R Term.zero_R w →ᶠ le_R (.app Term.neg_R w) Term.zero_R) := by
  pmode
  pintro h
  papplym (le_R_all Term.zero_R w) in h with hb
  papply (le_R_of_all (.app Term.neg_R w) Term.zero_R)
  simp only [neg_R_app_weaken'', zero_R_weaken]
  pforall
  pspecialize hb with hb1
  lnorm
  prw (cauchyfy_zero_R (.app .succ (.var .vz))) in hb1 with hb2
  prw (cauchyfy_neg w.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_zero_R (.app .succ (.var .vz)))
  papply (lt_Q_congr
    (Term.app2 Term.sub_Q Term.zero_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
    (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))) Term.zero_Q)
    (.app Term.pow2neg_Q (.var .vz))
    (eqQtrans (sub_Q_zero_l (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
      (eqQsym (sub_Q_zero_Q (.app Term.neg_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))))
    (eq_Q_refl_inst _))
  pexact hb2

/-- **M4.** `0ℝ ≤ℝ w → |w|ℝ ≤ℝ w`, through `abs_R_le_of_le_le_core` at `v := w`: the
two sides are `w ≤ℝ w` and `−ℝ w ≤ℝ 0ℝ ≤ℝ w`. Not via `|w| =ℝ w`, which is tight. -/
def abs_R_le_self_of_nonneg (w : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R Term.zero_R w →ᶠ le_R (.app Term.abs_R w) w) := by
  pmode
  pintro h
  papply (abs_R_le_of_le_le_core w w)
  psplit
  · pthm (le_R_refl_core w)
  · papply (le_R_trans_core (.app Term.neg_R w) Term.zero_R w)
    psplit
    · papply (neg_R_nonpos_of_nonneg w)
      pexact h
    · pexact h

-- ── Algebra: the ring identities as `≤ℝ` chains ────────────────────────────

/-- `f ≤ℝ 0ℝ +ℝ f`. -/
def le_R_zero_add (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f (Term.app2 Term.add_R Term.zero_R f)) :=
  leR_of_eq (eqRsym (eqRt (add_comm_R_core Term.zero_R f) (add_zero_R_core f)))

/-- `g ≤ℝ f +ℝ (g −ℝ f)` — the reverse of `add_sub_cancel_le_R_core`. -/
def le_add_sub_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R g (Term.app2 Term.add_R f (Term.app2 Term.sub_R g f))) :=
  let nf : Term F Γ (realTy ι) := .app Term.neg_R f
  leRt (leR_of_eq (eqRsym (add_zero_R_core g)))
    (leRt (leR_mono_l g (leR_of_eq (eqRsym (add_neg_R_core f))))
      (leRt (leR_of_eq (eqRsym (add_assoc_R_core g f nf)))
        (leRt (leR_mono_r nf (leR_of_eq (add_comm_R_core g f)))
          (leRt (leR_of_eq (add_assoc_R_core f g nf))
            (leR_mono_l f (leR_of_eq (eqRsym (sub_R_eq_add_neg_R_core g f))))))))

/-- **M5.** `g +ℝ (f −ℝ g) ≤ℝ f`. -/
def add_sub_cancel_le_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.add_R g (Term.app2 Term.sub_R f g)) f) :=
  let ng : Term F Γ (realTy ι) := .app Term.neg_R g
  leRt (leR_mono_l g (leR_of_eq (sub_R_eq_add_neg_R_core f g)))
    (leRt (leR_of_eq (eqRsym (add_assoc_R_core g f ng)))
      (leRt (leR_mono_r ng (leR_of_eq (add_comm_R_core g f)))
        (add_neg_cancel_le_R_core f g)))

/-- `f ≤ℝ (f +ℝ h) +ℝ (−ℝ h)` — the reverse of `add_neg_cancel_le_R_core`. -/
def le_add_neg_cancel_R (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f (Term.app2 Term.add_R (Term.app2 Term.add_R f h) (.app Term.neg_R h))) :=
  let nh : Term F Γ (realTy ι) := .app Term.neg_R h
  leRt (leR_of_eq (eqRsym (add_zero_R_core f)))
    (leRt (leR_mono_l f (leR_of_eq (eqRsym (add_neg_R_core h))))
      (leR_of_eq (eqRsym (add_assoc_R_core f h nh))))

/-- **M5'.** `f +ℝ h ≤ℝ g +ℝ h → f ≤ℝ g`, algebraically (a direct estimate is tight). -/
def le_R_add_cancel_r_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h) →ᶠ le_R f g) := by
  let nh : Term F Γ (realTy ι) := .app Term.neg_R h
  pmode
  pintro hyp
  papply (le_R_trans_core f (Term.app2 Term.add_R (Term.app2 Term.add_R f h) nh) g)
  psplit
  · pthm (le_add_neg_cancel_R f h)
  · papply (le_R_trans_core (Term.app2 Term.add_R (Term.app2 Term.add_R f h) nh)
      (Term.app2 Term.add_R (Term.app2 Term.add_R g h) nh) g)
    psplit
    · papply (le_R_add_mono_r_core (Term.app2 Term.add_R f h) (Term.app2 Term.add_R g h) nh)
      pexact hyp
    · pthm (add_neg_cancel_le_R_core g h)

/-- `g ≤ℝ f → 0ℝ ≤ℝ f −ℝ g`. -/
def sub_R_nonneg_of_le (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R g f →ᶠ le_R Term.zero_R (Term.app2 Term.sub_R f g)) := by
  let ng : Term F Γ (realTy ι) := .app Term.neg_R g
  pmode
  pintro h
  papply (le_R_trans_core Term.zero_R (Term.app2 Term.add_R g ng) (Term.app2 Term.sub_R f g))
  psplit
  · pthm (leR_of_eq (eqRsym (add_neg_R_core g)))
  · papply (le_R_trans_core (Term.app2 Term.add_R g ng) (Term.app2 Term.add_R f ng)
      (Term.app2 Term.sub_R f g))
    psplit
    · papply (le_R_add_mono_r_core g f ng)
      pexact h
    · pthm (leR_of_eq (eqRsym (sub_R_eq_add_neg_R_core f g)))

/-- `g −ℝ f ≤ℝ v → g ≤ℝ f +ℝ v`. -/
def le_add_of_sub_le (g f v : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.sub_R g f) v →ᶠ le_R g (Term.app2 Term.add_R f v)) := by
  pmode
  pintro h
  papply (le_R_trans_core g (Term.app2 Term.add_R f (Term.app2 Term.sub_R g f))
    (Term.app2 Term.add_R f v))
  psplit
  · pthm (le_add_sub_R f g)
  · papply (le_R_add_mono_l_core f (Term.app2 Term.sub_R g f) v)
    pexact h

/-- **M3, `≤` form.** `|f −ℝ g|ℝ ≤ℝ v → g ≤ℝ f +ℝ v`: `g −ℝ f =ℝ −ℝ(f −ℝ g) ≤ℝ |f −ℝ g|`. -/
def le_add_of_abs_sub_le (f g v : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R (.app Term.abs_R (Term.app2 Term.sub_R f g)) v →ᶠ
        le_R g (Term.app2 Term.add_R f v)) := by
  let d : Term F Γ (realTy ι) := Term.app2 Term.sub_R f g
  pmode
  pintro h
  papply (le_add_of_sub_le g f v)
  papply (le_R_trans_core (Term.app2 Term.sub_R g f) (.app Term.abs_R d) v)
  psplit
  · papply (le_R_trans_core (Term.app2 Term.sub_R g f) (.app Term.neg_R d) (.app Term.abs_R d))
    psplit
    · pthm (leR_of_eq (eqRsym (neg_sub_R_core f g)))
    · pthm (neg_le_abs_R d)
  · pexact h

-- ── The sample lower bound ──────────────────────────────────────────────────

/-- **A rational lower bound from one sample**: `q +ℚ 2^{-n} ≤ℚ f̂(n) → ⟨q⟩ℝ ≤ℝ f`.
Through `approx_le_R_core`: `⟨f̂(n)⟩ ≤ℝ f +ℝ ⟨2^{-n}⟩`, so `⟨f̂(n)⟩ −ℝ ⟨2^{-n}⟩ ≤ℝ f`, and
`⟨q⟩ ≤ℝ ⟨f̂(n)⟩ −ℝ ⟨2^{-n}⟩` is `const_R_le_sub`. The plan's P3.2–P3.3. -/
def const_le_R_of_sample (f : Term F Γ (realTy ι)) (n q : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q q (.app Term.pow2neg_Q n)) (Term.app2 Term.cauchyfy f n) →ᶠ
        le_R (const_R q) f) := by
  let c : Term F Γ (realTy ι) := const_R (Term.app2 Term.cauchyfy f n)
  let P : Term F Γ (realTy ι) := const_R (.app Term.pow2neg_Q n)
  pmode
  pintro h
  papply (le_R_trans_core (const_R q) (Term.app2 Term.sub_R c P) f)
  psplit
  · papply (const_R_le_sub q (Term.app2 Term.cauchyfy f n) (.app Term.pow2neg_Q n))
    pexact h
  · papply (le_sub_R_of_le_add_core c f P)
    papply (le_add_of_abs_sub_le f c P)
    pthm (approx_le_R_core f n)

-- ── The window drop ─────────────────────────────────────────────────────────

/-- **The bad window drops by the budget unit.** With `u := a m`, `v := a(m + g m)`,
`D := |u −ℝ v|ℝ` and `ε := ⟨2^{-(k+1)}⟩ℝ`:

    v ≤ℝ u  →  2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ 2^{-(k+1)}  →  v +ℝ ε ≤ℝ u.

The ℚ hypothesis is the negated conclusion matrix `¬C(m)` after `qf_double_neg_elim` and
`cauchyfy_const`. Accounting: `D̂(k+3) ≥ 2^{-(k+1)} + 2^{-(k+2)} ≥ 2^{-(k+1)} + 2^{-(k+3)}`, so
`const_le_R_of_sample` gives `ε ≤ℝ D`; antitonicity gives `0 ≤ℝ u −ℝ v`, so `D ≤ℝ u −ℝ v`;
then `v +ℝ ε ≤ℝ v +ℝ (u −ℝ v) ≤ℝ u`. -/
def window_drop (u v : Term F Γ (realTy ι)) (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R v u →ᶠ
       le_Q (.app Term.pow2neg_Q (.app .succ (.app .succ k)))
         (Term.app2 Term.sub_Q
           (Term.app2 Term.cauchyfy (.app Term.abs_R (Term.app2 Term.sub_R u v))
             (.app .succ (.app .succ (.app .succ k))))
           (.app Term.pow2neg_Q (.app .succ k))) →ᶠ
       le_R (Term.app2 Term.add_R v (const_R (.app Term.pow2neg_Q (.app .succ k)))) u) := by
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ k)
  let P2 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ k))
  let P3 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ (.app .succ k)))
  let w : Term F Γ (realTy ι) := Term.app2 Term.sub_R u v
  let D : Term F Γ (realTy ι) := .app Term.abs_R w
  let c : Term F Γ Ty.nat := Term.app2 Term.cauchyfy D (.app .succ (.app .succ (.app .succ k)))
  pmode
  pintro hanti hX
  phave hq : le_Q (Term.app2 Term.add_Q e P3) c
  · papply (le_Q_trans (Term.app2 Term.add_Q e P3) (Term.app2 Term.add_Q e P2) c)
    psplit
    · papply (le_Q_add_l e P3 P2)
      pthm (pow2neg_Q_le_succ (.app .succ (.app .succ k)))
    · papply (le_Q_add_of_le_sub P2 c e)
      pexact hX
  phave hlb : le_R (const_R e) D
  · papply (const_le_R_of_sample D (.app .succ (.app .succ (.app .succ k))) e)
    pexact hq
  phave hw0 : le_R Term.zero_R w
  · papply (sub_R_nonneg_of_le u v)
    pexact hanti
  phave hDw : le_R D w
  · papply (abs_R_le_self_of_nonneg w)
    pexact hw0
  papply (le_R_trans_core (Term.app2 Term.add_R v (const_R e)) (Term.app2 Term.add_R v w) u)
  psplit
  · papply (le_R_add_mono_l_core v (const_R e) w)
    papply (le_R_trans_core (const_R e) D w)
    psplit
    · pexact hlb
    · pexact hDw
  · pthm (add_sub_cancel_le_R_core u v)

end MCTLemmas

-- ── Transport and the antitone chain (proof-mode scripts) ───────────────────

namespace ProofMode

variable {Γ : Ctx ι}

/-- **Transport `≤ℝ` along an ℕ-equality in a function argument.**
`s =₀ t → a s ≤ℝ g → a t ≤ℝ g`. `le_R` is `¬∃n(qf)`, so unpack the witness against the
new statement, supply it against the old one, and `prwby` the equation inside the
quantifier-free matrix — the one place QF-ER applies. -/
def le_R_app_congr_l (a : Term F Γ (Ty.nat →ₜ realTy ι)) (s t : Term F Γ Ty.nat)
    (g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.eq0 s t →ᶠ le_R (Term.app a s) g →ᶠ le_R (Term.app a t) g) := by
  pmode
  pintro he hle
  pintro hex
  pobtain hex with hn
  mnorm
  papply hle
  pexists (.var .vz)
  mnorm
  prwby he
  pexact hn

/-- **The antitone chain over ℝ**: `∀i ∀m ((∀u. a(Su) ≤ℝ a u) → a(m+i) ≤ℝ a m)`.
The mirror of `ProofMode.antitone_chain`, with `le_R_trans_core` for `monus_trans` and a
transport (`le_R_app_congr_l`) where the ℕ proof could `prw`. -/
def antitone_chain_R (a : Term F Γ (Ty.nat →ₜ realTy ι)) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (Formula.all Ty.nat (le_R (a ⬝ (Term.app .succ x₂)) (a ⬝ x₂)) →ᶠ
         le_R (a ⬝ (Term.app2 Term.add x₁ x₀)) (a ⬝ x₁)))) := by
  pmode
  pinduction
  · -- i = 0 : a (m + 0) ≤ a m, by transport from a m ≤ a m
    mnorm
    pforall
    pintro hmono
    papply (le_R_app_congr_l a x₀ (Term.app2 Term.add x₀ Term.zero) (a ⬝ x₀))
    · psym
      pthm (add_zero_r x₀)
    · pthm (le_R_refl_core (a ⬝ x₀))
  · pforall
    pintro ih
    mnorm
    pforall
    pintro hmono
    -- a (m + S i) = a (S (m + i)) ≤ a (m + i) ≤ a m
    papply (le_R_app_congr_l a (Term.app .succ (Term.app2 Term.add x₁ x₀))
      (Term.app2 Term.add x₁ (Term.app .succ x₀)) (a ⬝ x₁))
    · psym
      pthm (add_succ x₁ x₀)
    · papply (le_R_trans_core (a ⬝ (Term.app .succ (Term.app2 Term.add x₁ x₀)))
        (a ⬝ (Term.app2 Term.add x₁ x₀)) (a ⬝ x₁))
      psplit
      · pinst hmono (Term.app2 Term.add x₁ x₀) with hm
        mnorm
        pexact hm
      · pspecialize ih with ihm
        papply ihm
        pexact hmono

end ProofMode

end Metatheorems
