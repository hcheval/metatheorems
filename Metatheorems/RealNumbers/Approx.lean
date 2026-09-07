/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Negation
import Metatheorems.RealNumbers.Bounds

namespace Metatheorems

/-!
# The approximation layer: `const_R`, `abs_R`/`sub_R` under `cauchyfy`, and the
`le_R (abs_R (sub_R u v)) (const_R q)` converters

Support for Kohlenbach §4.1's Lemma 4.2 (`approx_R`/`approx_le_R`) and Lemma 4.3
(`cauchy_complete_R`), which live in `Metric.lean`. Four layers:

1. ℚ-level moves that were still missing: `sub_Q` reassociation (`sub_Q_sub`), the
   `<`/`≤`-against-`sub_Q` conversions, the strict two-step dyadic decrease, and the
   **reverse triangle inequality** `| |a|ℚ −ℚ |b|ℚ |ℚ ≤ℚ |a −ℚ b|ℚ`.
2. `cauchyfy` evaluation for three new shapes: an arbitrary constant sequence
   (`cauchyfy_const`), `abs_R w` for an arbitrary `w` (`cauchyfy_abs_R` —
   the reverse triangle inequality is exactly what licenses this), and `sub_R f g`
   (`cauchyfy_sub_R`, via `add_R_check` on `f +ℝ (−ℝ g)`).
3. The two converters between `le_R (abs_R (sub_R u v)) (const_R q)` and its pointwise
   ℚ content `|û(m+2) −ℚ v̂(m+2)| <ℚ q +ℚ 2^{-m}` — one direction Lean-level
   (`abs_sub_le_const_R`), one an object implication (`bound_of_abs_sub_le_const`),
   because `cauchy_complete_R` must consume its hypothesis *inside* a sequent.
4. ℕ `monus` order facts for the completeness lemma's side conditions.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

section Approx

variable {Γ : Ctx ι}

-- ── Small Lean-level plumbing (private re-derivations of module-scoped helpers) ──

private theorem weaken_subst0' {τ ρ : Ty ι} (t : Term F Γ τ) (s : Term F Γ ρ) :
    t.weaken.subst0 s = t :=
  Term.weaken_subst0 t s

/-- `(app t.weaken (var vz)).subst0 u = app t u` (private in `Arithmetic.lean`). -/
private theorem app_weaken_vz_subst0' {ρ σ' : Ty ι} (t : Term F Γ (ρ →ₜ σ')) (u : Term F Γ ρ) :
    (Term.app t.weaken (.var .vz)).subst0 u = Term.app t u := by
  change Term.app (t.weaken.subst0 u) u = Term.app t u
  rw [weaken_subst0']

/-- `S`-congruence at `=₀` (the ones elsewhere are private). -/
def succ_congrA {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) (by qb_nf) (by qb_nf)

/-- `sub_Q` congruence in the second argument, at `=₀`. -/
def subQ_r_nat (c : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.sub_Q c s) (Term.app2 Term.sub_Q c t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.sub_Q c.weaken (.var .vz))
    (by qb_nf) (by qb_nf)

/-- `lt`/`le` transitivity with Lean-level premises, strict-first. -/
def ltleQt {a b c : Term F Γ Ty.nat}
    (h1 : Derivable F al Premises (lt_Q a b))
    (h2 : Derivable F al Premises (le_Q b c)) :
    Derivable F al Premises (lt_Q a c) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (lt_le_Q_trans a b c)

/-- …and strict-second. -/
def leltQt {a b c : Term F Γ Ty.nat}
    (h1 : Derivable F al Premises (le_Q a b))
    (h2 : Derivable F al Premises (lt_Q b c)) :
    Derivable F al Premises (lt_Q a c) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (le_lt_Q_trans a b c)

-- ── ℚ moves ────────────────────────────────────────────────────────────────

/-- `−ℚ (a −ℚ b) =ℚ (−ℚ a) +ℚ b`. -/
private def neg_Q_sub_add (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app Term.neg_Q (Term.app2 Term.sub_Q a b))
            (Term.app2 Term.add_Q (.app Term.neg_Q a) b)) :=
  eqQtrans (neg_Q_congr (sub_Q_eq_add_neg a b))
    (eqQtrans (neg_Q_add_Q a (.app Term.neg_Q b))
      (addQr (.app Term.neg_Q a) (neg_Q_neg_Q b)))

/-- `(b +ℚ c) −ℚ a =ℚ (c −ℚ a) +ℚ b`. -/
private def sub_Q_add_l (b c a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (Term.app2 Term.add_Q b c) a)
            (Term.app2 Term.add_Q (Term.app2 Term.sub_Q c a) b)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  eqQtrans (sub_Q_eq_add_neg (Term.app2 Term.add_Q b c) a)
    (eqQtrans (addQl (add_Q_comm_inst b c) na)
      (eqQtrans (add_Q_assoc_inst c b na)
        (eqQtrans (addQr c (add_Q_comm_inst b na))
          (eqQtrans (eqQsym (add_Q_assoc_inst c na b))
            (addQl (eqQsym (sub_Q_eq_add_neg c a)) b)))))

/-- `c −ℚ (a −ℚ b) =ℚ (c −ℚ a) +ℚ b`. -/
private def sub_Q_sub_r (c a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q c (Term.app2 Term.sub_Q a b))
            (Term.app2 Term.add_Q (Term.app2 Term.sub_Q c a) b)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  eqQtrans (sub_Q_eq_add_neg c (Term.app2 Term.sub_Q a b))
    (eqQtrans (addQr c (neg_Q_sub_add a b))
      (eqQtrans (eqQsym (add_Q_assoc_inst c na b))
        (addQl (eqQsym (sub_Q_eq_add_neg c a)) b)))

/-- `(a −ℚ b) −ℚ c =ℚ a −ℚ (b +ℚ c)` — `sub_Q` reassociation. -/
def sub_Q_sub (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (Term.app2 Term.sub_Q a b) c)
            (Term.app2 Term.sub_Q a (Term.app2 Term.add_Q b c))) :=
  let nb : Term F Γ Ty.nat := .app Term.neg_Q b
  let nc : Term F Γ Ty.nat := .app Term.neg_Q c
  eqQtrans (sub_Q_eq_add_neg (Term.app2 Term.sub_Q a b) c)
    (eqQtrans (addQl (sub_Q_eq_add_neg a b) nc)
      (eqQtrans (add_Q_assoc_inst a nb nc)
        (eqQtrans (addQr a (eqQsym (neg_Q_add_Q b c)))
          (eqQsym (sub_Q_eq_add_neg a (Term.app2 Term.add_Q b c))))))

/-- `a <ℚ b +ℚ c → a −ℚ b <ℚ c`. -/
def lt_Q_sub_of_lt_add (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q a (Term.app2 Term.add_Q b c) →ᶠ lt_Q (Term.app2 Term.sub_Q a b) c) :=
  lt_Q_of_eq_Q_diff a (Term.app2 Term.add_Q b c) (Term.app2 Term.sub_Q a b) c
    (eqQtrans (sub_Q_add_l b c a) (eqQsym (sub_Q_sub_r c a b)))

/-- `a −ℚ b <ℚ c → a <ℚ b +ℚ c`. -/
def lt_Q_add_of_sub_lt (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.sub_Q a b) c →ᶠ lt_Q a (Term.app2 Term.add_Q b c)) :=
  lt_Q_of_eq_Q_diff (Term.app2 Term.sub_Q a b) c a (Term.app2 Term.add_Q b c)
    (eqQtrans (sub_Q_sub_r c a b) (eqQsym (sub_Q_add_l b c a)))

/-- `a ≤ℚ b +ℚ c → a −ℚ b ≤ℚ c`. -/
def le_Q_sub_of_le_add_l (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q a (Term.app2 Term.add_Q b c) →ᶠ le_Q (Term.app2 Term.sub_Q a b) c) :=
  le_Q_of_eq_Q_diff a (Term.app2 Term.add_Q b c) (Term.app2 Term.sub_Q a b) c
    (eqQtrans (sub_Q_add_l b c a) (eqQsym (sub_Q_sub_r c a b)))

/-- `a +ℚ b ≤ℚ c → b ≤ℚ c −ℚ a`. -/
def le_Q_sub_of_add_le (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q a b) c →ᶠ le_Q b (Term.app2 Term.sub_Q c a)) :=
  le_Q_of_eq_Q_diff (Term.app2 Term.add_Q a b) c b (Term.app2 Term.sub_Q c a)
    (eqQsym (sub_Q_sub c a b))

/-- `2^{-(n+2)} <ℚ 2^{-n}` — the strict two-step decrease. -/
def pow2neg_Q_lt_two (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n))) (.app Term.pow2neg_Q n)) :=
  ltleQt (pow2neg_Q_lt_succ (.app .succ n)) (pow2neg_Q_le_succ n)

/-- **The reverse triangle inequality**: `| |a|ℚ −ℚ |b|ℚ |ℚ ≤ℚ |a −ℚ b|ℚ`.

Its three prerequisites — `z ≤ℚ |z|`, `−|z| ≤ℚ z` and the two-sided bound — are
`le_Q_self_abs`, `abs_Q_le_cases` and `abs_Q_le_add_diff`, and this is assembly on top of
them. It is what
makes `abs_R w` pass the Cauchy check for *any* `w` (`abs_R_check` below). -/
def abs_Q_rev_triangle (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q
              (Term.app2 Term.sub_Q (.app Term.abs_Q a) (.app Term.abs_Q b)))
            (.app Term.abs_Q (Term.app2 Term.sub_Q a b))) :=
  let A : Term F Γ Ty.nat := .app Term.abs_Q a
  let B : Term F Γ Ty.nat := .app Term.abs_Q b
  let D : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a b)
  let z : Term F Γ Ty.nat := Term.app2 Term.sub_Q A B
  -- `|a| ≤ |b| + |a − b|`, so `z = |a| − |b| ≤ |a − b|`
  let h1 : Derivable F al Premises (le_Q A (Term.app2 Term.add_Q B D)) :=
    Derivable.mp (abs_Q_le_add_diff a b)
      (le_Q_congr A (Term.app2 Term.add_Q B (.app Term.abs_Q (Term.app2 Term.sub_Q b a)))
        A (Term.app2 Term.add_Q B D)
        (eq_Q_refl_inst A) (addQr B (abs_diff_Q_comm b a)))
  let hz : Derivable F al Premises (le_Q z D) :=
    Derivable.mp h1 (le_Q_sub_of_le_add_l A B D)
  -- `|b| ≤ |a| + |a − b|`, so `−z = |b| − |a| ≤ |a − b|`
  let h2 : Derivable F al Premises (le_Q B (Term.app2 Term.add_Q A D)) :=
    abs_Q_le_add_diff b a
  let hz' : Derivable F al Premises (le_Q (Term.app2 Term.sub_Q B A) D) :=
    Derivable.mp h2 (le_Q_sub_of_le_add_l B A D)
  let hnz : Derivable F al Premises (le_Q (.app Term.neg_Q z) D) :=
    Derivable.mp hz'
      (le_Q_congr (Term.app2 Term.sub_Q B A) D (.app Term.neg_Q z) D
        (eqQsym (neg_Q_sub_Q B A)) (eq_Q_refl_inst D))
  by
  pmode
  pfrom hc := abs_Q_le_cases z
  pcases hc with hA | hB
  · papplym (le_Q_trans (.app Term.abs_Q z) z D)
    psplit
    · pexact hA
    · pthm hz
  · papplym (le_Q_trans (.app Term.abs_Q z) (.app Term.neg_Q z) D)
    psplit
    · pexact hB
    · pthm hnz

-- ── `const_R`: the constant real at an arbitrary rational code ─────────────
--
-- Lives here rather than in `Metric.lean` so its `cauchyfy` theory can sit beside it.

/-- The constant real sequence at a rational code — the book's `r ↦ λn.⟨r⟩` embedding
    of ℚ into ℝ (p. 80). `⟨2^{-k}⟩_ℝ` is `const_R (pow2neg_Q k)`. -/
def const_R {Γ : Ctx ι} (q : Term F Γ Ty.nat) : Term F Γ (realTy ι) :=
  Term.lam q.weaken

/-- Weakening commutes with `const_R`. -/
theorem const_R_weaken {Δ : Ctx ι} {ρ : Ty ι} (q : Term F Δ Ty.nat) :
    (const_R q : Term F Δ (realTy ι)).weaken (σ := ρ) = const_R q.weaken := by
  show Term.lam (Term.rename _ (Term.rename _ q)) = Term.lam (Term.rename _ (Term.rename _ q))
  rw [Term.rename_rename, Term.rename_rename]
  congr 1

/-- `const_R` commutes with substitution. -/
@[simp] theorem const_R_subst {Δ Δ' : Ctx ι} (q : Term F Δ Ty.nat)
    (σ : Term.Subst F Δ Δ') :
    (const_R q).subst σ = const_R (q.subst σ) := by
  show Term.lam (Term.subst _ q.weaken) = Term.lam (q.subst σ).weaken
  rw [Term.weaken_subst_ext]

/-- `le_R` commutes with substitution (the `le_R_pu_substF` of `Terms/ClosedSubst.lean`,
for the `¬∃` spelling). -/
theorem le_R_substF {Δ Δ' : Ctx ι} (f g : Term F Δ (realTy ι))
    (σ : Term.Subst F Δ Δ') :
    (le_R f g).substF σ = le_R (f.subst σ) (g.subst σ) := by
  simp only [le_R, lt_R, Formula.neg, Formula.substF, Term.subst, Term.Subst.ext,
    Term.app2, Term.weaken_subst_ext,
    le_Q_dec_closed_subst, sub_Q_closed_subst, cauchyfy_closed_subst,
    pow2neg_Q_closed_subst]

/-- `(const_R q)(x) =₀ q`. -/
def const_R_apply (q : Term F Γ Ty.nat) (x : Term F Γ Ty.nat) :
    Derivable F al Premises (Formula.eq0 (.app (const_R q) x) q) :=
  lam_correct_nf q.weaken x (weaken_subst0' q x)

/-- The Cauchy check passes for `const_R q` at every index. Spelled out rather than
written with `Term.cauchy_check_at`, for the usual `prw` reason. -/
def const_R_check (q : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (const_R q.weaken) (.var .vz))
            (.app (const_R q.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (const_R_apply q.weaken (.var .vz))
  prw (const_R_apply q.weaken (.app .succ (.var .vz)))
  pthm (lt_Q_abs_sub_self q.weaken (.app .succ (.var .vz)))

/-- `cauchyfy` is the identity on `const_R q`, and its value is `q` — `cauchyfy_const`
at an *arbitrary* constant, REALS_PLAN §0.8 item 3. -/
def cauchyfy_const (q : Term F Γ Ty.nat) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (const_R q) s) q) :=
  qtrans
    (cauchyfy_id (const_R q) (const_R_weaken q ▸ const_R_check q) s)
    (const_R_apply q s)

-- ── `abs_R w` is Cauchy for any `w` ────────────────────────────────────────

/-- The Cauchy check passes for `|w|_ℝ` at every index, for **any** `w`: `ŵ` is Cauchy by
`cauchyfy_cauchy`, and the reverse triangle inequality transfers its rate to `|ŵ(·)|ℚ`. -/
def abs_R_check (w : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (.app Term.abs_R w.weaken) (.var .vz))
            (.app (.app Term.abs_R w.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (abs_R_apply w.weaken (.var .vz))
  prw (abs_R_apply w.weaken (.app .succ (.var .vz)))
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (.app Term.abs_Q (Term.app2 Term.cauchyfy w.weaken (.var .vz)))
      (.app Term.abs_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy w.weaken (.var .vz))
      (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz))))
  psplit
  · pthm (abs_Q_rev_triangle
      (Term.app2 Term.cauchyfy w.weaken (.var .vz))
      (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
  · pthm (cauchyfy_cauchy w.weaken (.var .vz))

/-- `(|w|ℝ)^(s) =₀ |ŵ(s)|ℚ`: `cauchyfy` is the identity on `abs_R w`, for any `w`. -/
def cauchyfy_abs_R (w : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.abs_R w) s)
        (.app Term.abs_Q (Term.app2 Term.cauchyfy w s))) :=
  qtrans
    (cauchyfy_id (.app Term.abs_R w) (abs_R_app_weaken w ▸ abs_R_check w) s)
    (abs_R_apply w s)

-- ── `sub_R` beta and `cauchyfy` evaluation ─────────────────────────────────

private theorem neg_R_app_weaken' {Δ : Ctx ι} {ρ : Ty ι} (g : Term F Δ (realTy ι)) :
    (Term.app Term.neg_R g).weaken (σ := ρ) = Term.app Term.neg_R g.weaken := by
  show Term.app ((Term.neg_R : Term F Δ _).weaken) g.weaken = _
  rw [Term.weaken, Term.rename_eq_subst]
  rw [neg_R_closed_subst]

/-- The body `sub_R` compiles to, in the two-variable context `[g, f, …Γ]`. -/
private def sub_R_body : Term F (realTy ι :: realTy ι :: Γ) (realTy ι) :=
  Term.app2 Term.add_R (.var (.vs .vz)) (.app Term.neg_R (.var .vz))

/-- `sub_R f g =_{ℕ→ℕ} add_R f (neg_R g)` — the two beta steps, at function type. -/
private def sub_R_fun_eq (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqAtType (realTy ι) (Term.app2 Term.sub_R f g)
        (Term.app2 Term.add_R f (.app Term.neg_R g))) :=
  have body_eq : (Term.sub_R : Term F Γ _) = Term.lam (Term.lam sub_R_body) := rfl
  have nf : ((sub_R_body : Term F (realTy ι :: realTy ι :: Γ) _).subst0 g.weaken).subst0 f
      = Term.app2 Term.add_R f (.app Term.neg_R g) := by
    simp only [sub_R_body, Term.subst0, Term.subst, Term.subst0_map, Term.app2,
      subst_subst0_map_weaken, add_R_closed_subst, neg_R_closed_subst, closed_subst]
  body_eq ▸ lam2_correct_nf sub_R_body f g nf

/-- `(f −ℝ g)(x) =₀ (f +ℝ (−ℝ g))(x)` — `sub_R` beta-reduces pointwise. -/
def sub_R_apply (f g : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app (Term.app2 Term.sub_R f g) x)
        (.app (Term.app2 Term.add_R f (.app Term.neg_R g)) x)) :=
  let s : Term F Γ (realTy ι) := Term.app2 Term.sub_R f g
  let t : Term F Γ (realTy ι) := Term.app2 Term.add_R f (.app Term.neg_R g)
  let P : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))
  let inst : Derivable F al Premises (P.subst0 x) :=
    Derivable.mp (sub_R_fun_eq f g) (.forall_ax x)
  have heq : P.subst0 x = Formula.eq0 (Term.app s x) (Term.app t x) := by
    show Formula.eq0 ((Term.app s.weaken (.var .vz)).subst0 x)
        ((Term.app t.weaken (.var .vz)).subst0 x) = _
    rw [app_weaken_vz_subst0', app_weaken_vz_subst0']
  heq ▸ inst

theorem sub_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.sub_R : Term F Δ _).weaken (σ := ρ) = Term.sub_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact sub_R_closed_subst _

theorem sub_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f g : Term F Δ (realTy ι)) :
    (Term.app2 Term.sub_R f g).weaken (σ := ρ) =
      Term.app2 Term.sub_R f.weaken g.weaken := by
  show Term.app2 (Term.weaken Term.sub_R) f.weaken g.weaken = _
  rw [sub_R_weaken]

/-- The Cauchy check passes for `f −ℝ g` at every index: pointwise it *is*
`f +ℝ (−ℝ g)`, whose check is `add_R_check`. -/
def sub_R_check (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (Term.app2 Term.sub_R f.weaken g.weaken) (.var .vz))
            (.app (Term.app2 Term.sub_R f.weaken g.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (sub_R_apply f.weaken g.weaken (.var .vz))
  prw (sub_R_apply f.weaken g.weaken (.app .succ (.var .vz)))
  pthm (neg_R_app_weaken' g ▸ add_R_check f (.app Term.neg_R g))

/-- **`(f −ℝ g)^(s) =₀ f̂(s+1) +ℚ (−ℚ ĝ(s+1))`** — `cauchyfy` evaluates a difference. -/
def cauchyfy_sub_R (f g : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (Term.app2 Term.sub_R f g) s)
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f (.app .succ s))
          (.app Term.neg_Q (Term.app2 Term.cauchyfy g (.app .succ s))))) :=
  qtrans
    (cauchyfy_id (Term.app2 Term.sub_R f g)
      (sub_R_app_weaken f g ▸ sub_R_check f g) s)
    (qtrans (sub_R_apply f g s)
      (qtrans (add_R_apply f (.app Term.neg_R g) s)
        (addQ_r_nat (Term.app2 Term.cauchyfy f (.app .succ s))
          (cauchyfy_neg g (.app .succ s)))))

-- ── ℕ order facts in `monus` form, and small index arithmetic ──────────────

/-- `a ∸ (a + b) =₀ 0` — a number is below itself plus anything. -/
def monus_add_r (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus a (Term.app2 Term.add a b)) Term.zero) :=
  qtrans (monus_monus a a b)
    (qtrans (monus_congr_fst (monus_self a) b) (monus_zero_l b))

/-- `b ∸ (a + b) =₀ 0`. -/
def monus_add_l (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus b (Term.app2 Term.add a b)) Term.zero) :=
  qtrans (monus_congr_snd b (add_comm a b)) (monus_add_r b a)

/-- `p + 2 =₀ S (S p)`. -/
def add_two (p : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add p (Term.ofNat 2)) (.app .succ (.app .succ p))) :=
  qtrans (add_succ p (Term.ofNat 1))
    (succ_congrA (qtrans (add_succ p (Term.ofNat 0)) (succ_congrA (add_zero_r p))))

/-- `p + 3 =₀ S (S (S p))`. -/
def add_three (p : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add p (Term.ofNat 3))
        (.app .succ (.app .succ (.app .succ p)))) :=
  qtrans (add_succ p (Term.ofNat 2)) (succ_congrA (add_two p))

/-- `p + 5 =₀ S⁵ p`. -/
def add_five (p : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add p (Term.ofNat 5))
        (.app .succ (.app .succ (.app .succ (.app .succ (.app .succ p)))))) :=
  qtrans (add_succ p (Term.ofNat 4))
    (succ_congrA (qtrans (add_succ p (Term.ofNat 3)) (succ_congrA (add_three p))))

/-- `a ∸ S a =₀ 0`. -/
def monus_succ_self (a : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus a (.app .succ a)) Term.zero) :=
  let h1 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add a (Term.ofNat 1)) (.app .succ a)) :=
    qtrans (add_succ a (Term.ofNat 0)) (succ_congrA (add_zero_r a))
  qtrans (monus_congr_snd a (Derivable.mp h1 Derivable.sym0))
    (monus_add_r a (Term.ofNat 1))

-- ── The two `le_R`/pointwise-bound converters ──────────────────────────────

/-- **From the pointwise ℚ bound to `|u −ℝ v|ℝ ≤ℝ ⟨q⟩ℝ`** (Lean-level premise). The
hypothesis is the strict bound `|û(x₀+2) −ℚ v̂(x₀+2)|ℚ <ℚ q +ℚ 2^{-x₀}` at the bound
variable of `Ty.nat :: Γ`. -/
def abs_sub_le_const_R (u v : Term F Γ (realTy ι)) (q : Term F Γ Ty.nat)
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy u.weaken (.app .succ (.app .succ (.var .vz))))
              (Term.app2 Term.cauchyfy v.weaken (.app .succ (.app .succ (.var .vz))))))
            (Term.app2 Term.add_Q q.weaken (.app Term.pow2neg_Q (.var .vz))))) :
    Derivable F al Premises
      (le_R (.app Term.abs_R (Term.app2 Term.sub_R u v)) (const_R q)) :=
  le_R_of_bound (.app Term.abs_R (Term.app2 Term.sub_R u v)) (const_R q) (by
    rw [abs_R_app_weaken, sub_R_app_weaken, const_R_weaken]
    pmode
    prw (cauchyfy_abs_R (Term.app2 Term.sub_R u.weaken v.weaken) (.app .succ (.var .vz)))
    prw (cauchyfy_sub_R u.weaken v.weaken (.app .succ (.var .vz)))
    prw (cauchyfy_const q.weaken (.app .succ (.var .vz)))
    papplym (lt_Q_congr
      (Term.app2 Term.sub_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy u.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy v.weaken (.app .succ (.app .succ (.var .vz))))))
        q.weaken)
      (.app Term.pow2neg_Q (.var .vz))
      (Term.app2 Term.sub_Q
        (.app Term.abs_Q (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy u.weaken (.app .succ (.app .succ (.var .vz))))
          (.app Term.neg_Q
            (Term.app2 Term.cauchyfy v.weaken (.app .succ (.app .succ (.var .vz)))))))
        q.weaken)
      (.app Term.pow2neg_Q (.var .vz))
      (sub_Q_congr
        (abs_Q_congr (sub_Q_eq_add_neg
          (Term.app2 Term.cauchyfy u.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy v.weaken (.app .succ (.app .succ (.var .vz))))))
        (eq_Q_refl_inst q.weaken))
      (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
    papplym (lt_Q_sub_of_lt_add
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.app .succ (.var .vz))))))
      q.weaken
      (.app Term.pow2neg_Q (.var .vz)))
    pthm h)

/-- **From `|u −ℝ v|ℝ ≤ℝ ⟨q⟩ℝ` to the pointwise ℚ bound**, as an object implication —
`cauchy_complete_R` has to consume its hypothesis inside a sequent, so the Lean-level
converse above is not enough. At any index `m`:
`|û(m+2) −ℚ v̂(m+2)|ℚ <ℚ q +ℚ 2^{-m}`. -/
def bound_of_abs_sub_le_const (u v : Term F Γ (realTy ι)) (q m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (.app Term.abs_R (Term.app2 Term.sub_R u v)) (const_R q) →ᶠ
       lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
               (Term.app2 Term.cauchyfy u (.app .succ (.app .succ m)))
               (Term.app2 Term.cauchyfy v (.app .succ (.app .succ m)))))
            (Term.app2 Term.add_Q q (.app Term.pow2neg_Q m))) := by
  pmode
  pintro h
  papplym (le_R_all (.app Term.abs_R (Term.app2 Term.sub_R u v)) (const_R q)) in h with h2
  pinst h2 m with h3
  canorm
  prw (cauchyfy_abs_R (Term.app2 Term.sub_R u v) (.app .succ m)) in h3 with h4
  prw (cauchyfy_sub_R u v (.app .succ m)) in h4 with h5
  prw (cauchyfy_const q (.app .succ m)) in h5 with h6
  papplym (lt_Q_add_of_sub_lt
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy u (.app .succ (.app .succ m)))
      (Term.app2 Term.cauchyfy v (.app .succ (.app .succ m)))))
    q
    (.app Term.pow2neg_Q m))
  papplym (lt_Q_congr
    (Term.app2 Term.sub_Q
      (.app Term.abs_Q (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy u (.app .succ (.app .succ m)))
        (.app Term.neg_Q (Term.app2 Term.cauchyfy v (.app .succ (.app .succ m))))))
      q)
    (.app Term.pow2neg_Q m)
    (Term.app2 Term.sub_Q
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy u (.app .succ (.app .succ m)))
        (Term.app2 Term.cauchyfy v (.app .succ (.app .succ m)))))
      q)
    (.app Term.pow2neg_Q m)
    (sub_Q_congr
      (abs_Q_congr (eqQsym (sub_Q_eq_add_neg
        (Term.app2 Term.cauchyfy u (.app .succ (.app .succ m)))
        (Term.app2 Term.cauchyfy v (.app .succ (.app .succ m))))))
      (eq_Q_refl_inst q))
    (eq_Q_refl_inst (.app Term.pow2neg_Q m)))
  pexact h6

-- ── Weakening pushes through the closed constants involved ─────────────────

/-- Weakening distributes over application — definitional, but `canorm` has no rule for
it, and a folded `Term.weaken` around an application spine is invisible to `prw` and to
`pexact` alike (display-hiding family, CLAUDE.md note 12). -/
theorem weaken_app {Δ : Ctx ι} {ρ σ' τ' : Ty ι}
    (a : Term F Δ (ρ →ₜ σ')) (b : Term F Δ ρ) :
    (Term.app a b).weaken (σ := τ') = Term.app a.weaken b.weaken := rfl

theorem weaken_succ {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.succ : Term F Δ _).weaken (σ := ρ) = Term.succ := rfl

theorem cauchyfy_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.cauchyfy : Term F Δ _).weaken (σ := ρ) = Term.cauchyfy := by
  rw [Term.weaken, Term.rename_eq_subst]; exact cauchyfy_closed_subst _

theorem abs_R_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.abs_R : Term F Δ _).weaken (σ := ρ) = Term.abs_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact abs_R_closed_subst _

theorem cauchyfy_app2_weaken {Δ : Ctx ι} {ρ : Ty ι}
    (f : Term F Δ (realTy ι)) (k : Term F Δ Ty.nat) :
    (Term.app2 Term.cauchyfy f k).weaken (σ := ρ) =
      Term.app2 Term.cauchyfy f.weaken k.weaken := by
  show Term.app2 (Term.weaken Term.cauchyfy) f.weaken k.weaken = _
  rw [cauchyfy_weaken']

theorem pow2neg_Q_weaken' {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.pow2neg_Q : Term F Δ _).weaken (σ := ρ) = Term.pow2neg_Q := by
  rw [Term.weaken, Term.rename_eq_subst]; exact pow2neg_Q_closed_subst _

theorem pow2neg_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (k : Term F Δ Ty.nat) :
    (Term.app Term.pow2neg_Q k).weaken (σ := ρ) = .app Term.pow2neg_Q k.weaken := by
  show Term.app (Term.weaken Term.pow2neg_Q) k.weaken = _
  rw [pow2neg_Q_weaken']

-- ── Lemma 4.2 in `≤ℝ` form ─────────────────────────────────────────────────

/-- **`approx_le_R` at explicit `f`, `k`**: `|f −ℝ ⟨f̂(k)⟩ℝ|ℝ ≤ℝ ⟨2^{-k}⟩ℝ`.

The estimate is the crude telescope through the far point `(x₀+2) +ℕ k`, which dominates
both `x₀+2` and `k`, so no case split on `k ≤ x₀` and no Archimedean witness is needed —
that is REALS_PLAN §0.8's closing observation, realised: the `≤ℝ` form is Π₁⁰ and cheap.
The strictness the pointwise bound wants comes from `2^{-(x₀+2)} <ℚ 2^{-x₀}`, not from the
sequence. -/
def approx_le_R_core (f : Term F Γ (realTy ι)) (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (.app Term.abs_R
              (Term.app2 Term.sub_R f (const_R (Term.app2 Term.cauchyfy f k))))
            (const_R (.app Term.pow2neg_Q k))) :=
  abs_sub_le_const_R f (const_R (Term.app2 Term.cauchyfy f k)) (.app Term.pow2neg_Q k)
    (by
      rw [const_R_weaken, cauchyfy_app2_weaken, pow2neg_app_weaken]
      -- names for the pieces of the estimate
      let x2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.app .succ (.var .vz))
      let a : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken x2
      let b : Term F (Ty.nat :: Γ) Ty.nat :=
        Term.app2 Term.cauchyfy f.weaken (Term.app2 Term.add x2 k.weaken)
      let b' : Term F (Ty.nat :: Γ) Ty.nat :=
        Term.app2 Term.cauchyfy f.weaken (Term.app2 Term.add k.weaken x2)
      let c : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken k.weaken
      let X1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a b)
      let X2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q b c)
      let Pk : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q k.weaken
      let Px : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
      let hflip : Derivable F al Premises (Γ := Ty.nat :: Γ)
          (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q c b')) X2) :=
        eqQtrans
          (eqQ_of_nat_eq' (abs_Q_congr_nat
            (subQ_r_nat c (cauchyfy_idx_nat' f.weaken (add_comm k.weaken x2)))))
          (abs_diff_Q_comm c b)
      pmode
      prw (cauchyfy_const (Term.app2 Term.cauchyfy f.weaken k.weaken) x2)
      papplym (le_lt_Q_trans
        (.app Term.abs_Q (Term.app2 Term.sub_Q a c))
        (Term.app2 Term.add_Q X1 X2)
        (Term.app2 Term.add_Q Pk Px))
      psplit
      · pthm (abs_Q_sub_triangle a b c)
      · papplym (lt_Q_congr (Term.app2 Term.add_Q X1 X2) (Term.app2 Term.add_Q Px Pk)
          (Term.app2 Term.add_Q X1 X2) (Term.app2 Term.add_Q Pk Px)
          (eq_Q_refl_inst (Term.app2 Term.add_Q X1 X2)) (add_Q_comm_inst Px Pk))
        papplym (lt_le_Q_add X1 X2 Px Pk)
        psplit
        · papplym (le_lt_Q_trans X1 (.app Term.pow2neg_Q x2) Px)
          psplit
          · pthm (cauchyfy_shift_le f.weaken x2 k.weaken)
          · pthm (pow2neg_Q_lt_two (.var .vz))
        · papplym (le_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q c b')) Pk X2 Pk
            hflip (eq_Q_refl_inst Pk))
          pthm (cauchyfy_shift_le f.weaken k.weaken x2))

/-- **Lemma 4.2, `≤ℝ` form** (Kohlenbach p. 80): `f̂(k)` is a rational `2^{-k}`-approximation
of `f`, with the approximation read as `≤ℝ`:

    `WE-HA^ω↾ ⊢ ∀f,k. |f −ℝ λn.f̂(k)|ℝ ≤ℝ ⟨2^{-k}⟩ℝ`

This is the Π₁⁰ version of `approx_R` — no witness, no Archimedean modulus — and it is
all that `cauchy_complete_R` needs. The `<ℝ` version (`approx_R`, `Metric.lean`) carries
the additional Archimedean content. -/
def approx_le_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all Ty.nat
        (le_R
          (Term.app Term.abs_R
            (Term.app2 Term.sub_R
              (.var (.vs .vz))
              (const_R (Term.app (Term.app Term.cauchyfy (.var (.vs .vz))) (.var .vz)))))
          (const_R (.app Term.pow2neg_Q (.var .vz)))))) :=
  univ_gen (univ_gen (approx_le_R_core (.var (.vs .vz)) (.var .vz)))

-- ── The two diagonal estimates for `cauchy_complete_R` ─────────────────────

/-- **The Cauchy check of the diagonal**: from
`|u −ℝ v|ℝ ≤ℝ ⟨2^{-(x+3)}⟩ℝ`, conclude `|û(x+3) −ℚ v̂(x+4)|ℚ <ℚ 2^{-(x+1)}`.

With `u := Φ(x+3)`, `v := Φ(x+4)` this is exactly the Cauchy check the witness sequence
`k ↦ Φ̂(k+3)(k+3)` of `cauchy_complete_R` must pass at index `x`. Stated as an object
implication because the `le_R` hypothesis is only available inside a sequent there.

The estimate, through the far point `x+6`: `2^{-(x+3)}` (shift on `u`) + `2^{-(x+3)} +
2^{-(x+4)}` (the hypothesis, read at `m = x+4`) + `2^{-(x+4)}` (shift on `v`)
= `2^{-(x+2)} + 2^{-(x+3)} < 2^{-(x+1)}`. -/
def diag_check_bound (u v : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (.app Term.abs_R (Term.app2 Term.sub_R u v))
          (const_R (.app Term.pow2neg_Q (.app .succ (.app .succ (.app .succ x)))))
        →ᶠ
       lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
               (Term.app2 Term.cauchyfy u (.app .succ (.app .succ (.app .succ x))))
               (Term.app2 Term.cauchyfy v
                 (.app .succ (.app .succ (.app .succ (.app .succ x)))))))
            (.app Term.pow2neg_Q (.app .succ x))) :=
  let x3 : Term F Γ Ty.nat := .app .succ (.app .succ (.app .succ x))
  let x4 : Term F Γ Ty.nat := .app .succ x3
  let x6 : Term F Γ Ty.nat := .app .succ (.app .succ x4)
  let P1 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ x)
  let P2 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ x))
  let P3 : Term F Γ Ty.nat := .app Term.pow2neg_Q x3
  let P4 : Term F Γ Ty.nat := .app Term.pow2neg_Q x4
  let a : Term F Γ Ty.nat := Term.app2 Term.cauchyfy u x3
  let a6 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy u x6
  let b6 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy v x6
  let b : Term F Γ Ty.nat := Term.app2 Term.cauchyfy v x4
  let S1 : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a6)
  let M : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a6 b6)
  let T : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q b6 b)
  let D1 : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a6 b)
  let E : Term F Γ Ty.nat :=
    Term.app2 Term.add_Q P3 (Term.app2 Term.add_Q (Term.app2 Term.add_Q P3 P4) P4)
  -- `|û(x+3) −ℚ û(x+6)| ≤ℚ 2^{-(x+3)}` — the telescope, with the index normalised
  let hT1 : Derivable F al Premises (le_Q S1 P3) :=
    Derivable.mp (cauchyfy_shift_le u x3 (Term.ofNat 3))
      (le_Q_congr
        (.app Term.abs_Q (Term.app2 Term.sub_Q a
          (Term.app2 Term.cauchyfy u (Term.app2 Term.add x3 (Term.ofNat 3))))) P3 S1 P3
        (eqQ_of_nat_eq' (abs_Q_congr_nat
          (subQ_r_nat a (cauchyfy_idx_nat' u (add_three x3)))))
        (eq_Q_refl_inst P3))
  -- `|v̂(x+6) −ℚ v̂(x+4)| ≤ℚ 2^{-(x+4)}` — the same, flipped
  let hflip : Derivable F al Premises
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q b
        (Term.app2 Term.cauchyfy v (Term.app2 Term.add x4 (Term.ofNat 2))))) T) :=
    eqQtrans
      (eqQ_of_nat_eq' (abs_Q_congr_nat
        (subQ_r_nat b (cauchyfy_idx_nat' v (add_two x4)))))
      (abs_diff_Q_comm b b6)
  let hT3 : Derivable F al Premises (le_Q T P4) :=
    Derivable.mp (cauchyfy_shift_le v x4 (Term.ofNat 2))
      (le_Q_congr
        (.app Term.abs_Q (Term.app2 Term.sub_Q b
          (Term.app2 Term.cauchyfy v (Term.app2 Term.add x4 (Term.ofNat 2))))) P4 T P4
        hflip (eq_Q_refl_inst P4))
  -- `E =ℚ 2^{-(x+2)} +ℚ 2^{-(x+3)}`, and that is `≤ℚ 2^{-(x+1)}`
  let hE : Derivable F al Premises (eq_Q E (Term.app2 Term.add_Q P2 P3)) :=
    eqQtrans (addQr P3 (add_Q_assoc_inst P3 P4 P4))
      (eqQtrans (eqQsym (add_Q_assoc_inst P3 P3 (Term.app2 Term.add_Q P4 P4)))
        (eqQtrans
          (addQl ((pow2neg_Q_halve (.app .succ (.app .succ x))))
            (Term.app2 Term.add_Q P4 P4))
          (addQr P2 ((pow2neg_Q_halve x3)))))
  let hEP1 : Derivable F al Premises (le_Q E P1) :=
    Derivable.mp
      (Derivable.mp
        (Derivable.mp (pow2neg_Q_le_succ (.app .succ (.app .succ x)))
          (le_Q_add_l P2 P3 P2))
        (le_Q_congr (Term.app2 Term.add_Q P2 P3) (Term.app2 Term.add_Q P2 P2)
          (Term.app2 Term.add_Q P2 P3) P1
          (eq_Q_refl_inst (Term.app2 Term.add_Q P2 P3))
          ((pow2neg_Q_halve (.app .succ x)))))
      (le_Q_congr (Term.app2 Term.add_Q P2 P3) P1 E P1
        (eqQsym hE) (eq_Q_refl_inst P1))
  by
  pmode
  pintro h
  papplym (bound_of_abs_sub_le_const u v P3 x4) in h with hb
  papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q a b))
    (Term.app2 Term.add_Q S1 D1) P1)
  psplit
  · pthm (abs_Q_sub_triangle a a6 b)
  · papplym (le_lt_Q_trans (Term.app2 Term.add_Q S1 D1)
      (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M T)) P1)
    psplit
    · papplym (le_Q_add_l S1 D1 (Term.app2 Term.add_Q M T))
      pthm (abs_Q_sub_triangle a6 b6 b)
    · papplym (lt_le_Q_trans (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M T)) E P1)
      psplit
      · papplym (lt_Q_congr
          (Term.app2 Term.add_Q (Term.app2 Term.add_Q M T) S1)
          (Term.app2 Term.add_Q (Term.app2 Term.add_Q (Term.app2 Term.add_Q P3 P4) P4) P3)
          (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M T))
          E
          (add_Q_comm_inst (Term.app2 Term.add_Q M T) S1)
          (add_Q_comm_inst (Term.app2 Term.add_Q (Term.app2 Term.add_Q P3 P4) P4) P3))
        papplym (lt_le_Q_add (Term.app2 Term.add_Q M T) S1
          (Term.app2 Term.add_Q (Term.app2 Term.add_Q P3 P4) P4) P3)
        psplit
        · papplym (lt_le_Q_add M T (Term.app2 Term.add_Q P3 P4) P4)
          psplit
          · pexact hb
          · pthm hT3
        · pthm hT1
      · pthm hEP1

/-- **The goal estimate of `cauchy_complete_R`**: from
`|u −ℝ w|ℝ ≤ℝ ⟨2^{-n}⟩ℝ` and `|w −ℝ v|ℝ ≤ℝ ⟨2^{-(x+5)}⟩ℝ`, conclude

    `|û(x+2) −ℚ v̂(x+5)|ℚ −ℚ 2^{-n} <ℚ 2^{-x}`,

with the absolute value spelled in `add`/`neg_Q` form — exactly the shape the goal has
after `cauchyfy_sub_R`, so the caller applies this with no congruence step.

With `u := Φ n`, `w := Φ (n + (x+5))`, `v := Φ (x+5)` this is the pointwise bound behind
`|Φn −ℝ f|ℝ ≤ℝ ⟨2^{-n}⟩ℝ` for the diagonal witness `f`. The far point is `x+7`; the
budget is `2^{-(x+2)}` (shift on `u`) + `2^{-n} + 2^{-(x+5)}` (hypothesis 1 at `m = x+5`)
+ `2·2^{-(x+5)}` (hypothesis 2) + `2^{-(x+5)}` (shift on `v`)
= `2^{-n} + 2^{-(x+2)} + 2^{-(x+3)} < 2^{-n} + 2^{-x}`. -/
def diag_goal_bound (u w v : Term F Γ (realTy ι)) (n x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_R (.app Term.abs_R (Term.app2 Term.sub_R u w))
          (const_R (.app Term.pow2neg_Q n))
        →ᶠ
       le_R (.app Term.abs_R (Term.app2 Term.sub_R w v))
          (const_R (.app Term.pow2neg_Q
            (.app .succ (.app .succ (.app .succ (.app .succ (.app .succ x)))))))
        →ᶠ
       lt_Q
        (Term.app2 Term.sub_Q
          (.app Term.abs_Q (Term.app2 Term.add_Q
            (Term.app2 Term.cauchyfy u (.app .succ (.app .succ x)))
            (.app Term.neg_Q (Term.app2 Term.cauchyfy v
              (.app .succ (.app .succ (.app .succ (.app .succ (.app .succ x)))))))))
          (.app Term.pow2neg_Q n))
        (.app Term.pow2neg_Q x)) :=
  let x2 : Term F Γ Ty.nat := .app .succ (.app .succ x)
  let x5 : Term F Γ Ty.nat := .app .succ (.app .succ (.app .succ x2))
  let x7 : Term F Γ Ty.nat := .app .succ (.app .succ x5)
  let Pn : Term F Γ Ty.nat := .app Term.pow2neg_Q n
  let Px : Term F Γ Ty.nat := .app Term.pow2neg_Q x
  let P1 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ x)
  let P2 : Term F Γ Ty.nat := .app Term.pow2neg_Q x2
  let Q3 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ x2)
  let Q4 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ (.app .succ x2))
  let P5 : Term F Γ Ty.nat := .app Term.pow2neg_Q x5
  let a : Term F Γ Ty.nat := Term.app2 Term.cauchyfy u x2
  let a7 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy u x7
  let w7 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy w x7
  let e7 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy v x7
  let e : Term F Γ Ty.nat := Term.app2 Term.cauchyfy v x5
  let A : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a e)
  let S1 : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a7)
  let M1 : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a7 w7)
  let M2 : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q w7 e7)
  let T : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q e7 e)
  let Z : Term F Γ Ty.nat := Term.app2 Term.add_Q (Term.app2 Term.add_Q P5 P5) P5
  let W : Term F Γ Ty.nat := Term.app2 Term.add_Q (Term.app2 Term.add_Q Pn P5) Z
  let E : Term F Γ Ty.nat := Term.app2 Term.add_Q P2 W
  -- the two shifts
  let hS : Derivable F al Premises (le_Q S1 P2) :=
    Derivable.mp (cauchyfy_shift_le u x2 (Term.ofNat 5))
      (le_Q_congr
        (.app Term.abs_Q (Term.app2 Term.sub_Q a
          (Term.app2 Term.cauchyfy u (Term.app2 Term.add x2 (Term.ofNat 5))))) P2 S1 P2
        (eqQ_of_nat_eq' (abs_Q_congr_nat
          (subQ_r_nat a (cauchyfy_idx_nat' u (add_five x2)))))
        (eq_Q_refl_inst P2))
  let hflip : Derivable F al Premises
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q e
        (Term.app2 Term.cauchyfy v (Term.app2 Term.add x5 (Term.ofNat 2))))) T) :=
    eqQtrans
      (eqQ_of_nat_eq' (abs_Q_congr_nat
        (subQ_r_nat e (cauchyfy_idx_nat' v (add_two x5)))))
      (abs_diff_Q_comm e e7)
  let hT : Derivable F al Premises (le_Q T P5) :=
    Derivable.mp (cauchyfy_shift_le v x5 (Term.ofNat 2))
      (le_Q_congr
        (.app Term.abs_Q (Term.app2 Term.sub_Q e
          (Term.app2 Term.cauchyfy v (Term.app2 Term.add x5 (Term.ofNat 2))))) P5 T P5
        hflip (eq_Q_refl_inst P5))
  -- the dyadic bookkeeping: `E =ℚ 2^{-n} +ℚ (2^{-(x+2)} +ℚ 2^{-(x+3)})`
  let yAll : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q P5 Z) Q3) :=
    eqQtrans (addQr P5 (add_Q_comm_inst (Term.app2 Term.add_Q P5 P5) P5))
      (eqQtrans (eqQsym (add_Q_assoc_inst P5 P5 (Term.app2 Term.add_Q P5 P5)))
        (eqQtrans
          (addQl ((pow2neg_Q_halve (.app .succ (.app .succ x2))))
            (Term.app2 Term.add_Q P5 P5))
          (eqQtrans (addQr Q4 ((pow2neg_Q_halve (.app .succ (.app .succ x2)))))
            ((pow2neg_Q_halve (.app .succ x2))))))
  let wAll : Derivable F al Premises (eq_Q W (Term.app2 Term.add_Q Pn Q3)) :=
    eqQtrans (add_Q_assoc_inst Pn P5 Z) (addQr Pn yAll)
  let hE : Derivable F al Premises
      (eq_Q E (Term.app2 Term.add_Q Pn (Term.app2 Term.add_Q P2 Q3))) :=
    eqQtrans (addQr P2 wAll)
      (eqQtrans (eqQsym (add_Q_assoc_inst P2 Pn Q3))
        (eqQtrans (addQl (add_Q_comm_inst P2 Pn) Q3)
          (add_Q_assoc_inst Pn P2 Q3)))
  -- `2^{-(x+2)} +ℚ 2^{-(x+3)} <ℚ 2^{-(x+1)} ≤ℚ 2^{-x}`
  let hlt : Derivable F al Premises (lt_Q (Term.app2 Term.add_Q P2 Q3) P1) :=
    Derivable.mp
      (Derivable.mp (pow2neg_Q_lt_succ x2) (lt_Q_add_l P2 Q3 P2))
      (lt_Q_congr (Term.app2 Term.add_Q P2 Q3) (Term.app2 Term.add_Q P2 P2)
        (Term.app2 Term.add_Q P2 Q3) P1
        (eq_Q_refl_inst (Term.app2 Term.add_Q P2 Q3))
        ((pow2neg_Q_halve (.app .succ x))))
  let hltPx : Derivable F al Premises (lt_Q (Term.app2 Term.add_Q P2 Q3) Px) :=
    ltleQt hlt (pow2neg_Q_le_succ x)
  let hElt : Derivable F al Premises (lt_Q E (Term.app2 Term.add_Q Pn Px)) :=
    Derivable.mp
      (Derivable.mp hltPx (lt_Q_add_l Pn (Term.app2 Term.add_Q P2 Q3) Px))
      (lt_Q_congr (Term.app2 Term.add_Q Pn (Term.app2 Term.add_Q P2 Q3))
        (Term.app2 Term.add_Q Pn Px) E (Term.app2 Term.add_Q Pn Px)
        (eqQsym hE) (eq_Q_refl_inst (Term.app2 Term.add_Q Pn Px)))
  by
  pmode
  pintro h1
  pintro h2
  papplym (bound_of_abs_sub_le_const u w Pn x5) in h1 with hb1
  papplym (bound_of_abs_sub_le_const w v P5 x5) in h2 with hb2
  papplym (lt_Q_congr (Term.app2 Term.sub_Q A Pn) Px
    (Term.app2 Term.sub_Q
      (.app Term.abs_Q (Term.app2 Term.add_Q a (.app Term.neg_Q e))) Pn) Px
    (sub_Q_congr (abs_Q_congr (sub_Q_eq_add_neg a e)) (eq_Q_refl_inst Pn))
    (eq_Q_refl_inst Px))
  papplym (lt_Q_sub_of_lt_add A Pn Px)
  papplym (le_lt_Q_trans A
    (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T)))
    (Term.app2 Term.add_Q Pn Px))
  psplit
  · -- the three triangles
    papplym (le_Q_trans A
      (Term.app2 Term.add_Q S1 (.app Term.abs_Q (Term.app2 Term.sub_Q a7 e)))
      (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T))))
    psplit
    · pthm (abs_Q_sub_triangle a a7 e)
    · papplym (le_Q_add_l S1 (.app Term.abs_Q (Term.app2 Term.sub_Q a7 e))
        (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T)))
      papplym (le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q a7 e))
        (Term.app2 Term.add_Q M1 (.app Term.abs_Q (Term.app2 Term.sub_Q w7 e)))
        (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T)))
      psplit
      · pthm (abs_Q_sub_triangle a7 w7 e)
      · papplym (le_Q_add_l M1 (.app Term.abs_Q (Term.app2 Term.sub_Q w7 e))
          (Term.app2 Term.add_Q M2 T))
        pthm (abs_Q_sub_triangle w7 e7 e)
  · -- the sum against `E`, then `E <ℚ 2^{-n} +ℚ 2^{-x}` strictly
    papplym (le_lt_Q_trans
      (Term.app2 Term.add_Q S1 (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T)))
      E (Term.app2 Term.add_Q Pn Px))
    psplit
    · papplym (le_Q_add_both S1 (Term.app2 Term.add_Q M1 (Term.app2 Term.add_Q M2 T))
        P2 W)
      psplit
      · pthm hS
      · papplym (le_Q_add_both M1 (Term.app2 Term.add_Q M2 T)
          (Term.app2 Term.add_Q Pn P5) Z)
        psplit
        · papplym (lt_Q_imp_le_Q M1 (Term.app2 Term.add_Q Pn P5))
          pexact hb1
        · papplym (le_Q_add_both M2 T (Term.app2 Term.add_Q P5 P5) P5)
          psplit
          · papplym (lt_Q_imp_le_Q M2 (Term.app2 Term.add_Q P5 P5))
            pexact hb2
          · pthm hT
    · pthm hElt

-- ── The diagonal-witness combinator for `cauchy_complete_R` ────────────────
--
-- The completeness witness is `f := λk. Φ̂(k+3)(k+3)`. It is built as a **closed
-- combinator applied to `Φ`**, not as a bare `Term.lam` mentioning `Φ.weaken`: an
-- application spine weakens by one `diag_seq_app_weaken` rewrite and stays visible to
-- `prw`, while a literal λ-witness would accumulate `Term.weaken`s around a binder that
-- every proof-mode step then has to push through by hand.

/-- `diag_seq Φ = λk. Φ̂(k+3)(k+3)` — the diagonal of a sequence of reals, with the
`+3` offset Kohlenbach's Lemma 4.3 uses. -/
def Term.diag_seq {Γ : Ctx ι} : Term F Γ ((Ty.nat →ₜ realTy ι) →ₜ realTy ι) :=
  Term.lam (Term.lam (Term.app2 Term.cauchyfy
    (.app (.var (.vs .vz)) (.app .succ (.app .succ (.app .succ (.var .vz)))))
    (.app .succ (.app .succ (.app .succ (.var .vz))))))

@[simp] theorem diag_seq_closed_subst {Δ Δ' : Ctx ι} (σ : Term.Subst F Δ Δ') :
    (Term.diag_seq : Term F Δ _).subst σ = Term.diag_seq := by
  simp only [Term.diag_seq, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift, cauchyfy_closed_subst]

attribute [closed_subst] diag_seq_closed_subst

theorem diag_seq_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.diag_seq : Term F Δ _).weaken (σ := ρ) = Term.diag_seq := by
  rw [Term.weaken, Term.rename_eq_subst]; exact diag_seq_closed_subst _

theorem diag_seq_app_weaken {Δ : Ctx ι} {ρ : Ty ι}
    (Ψ : Term F Δ (Ty.nat →ₜ realTy ι)) :
    (Term.app Term.diag_seq Ψ).weaken (σ := ρ) = .app Term.diag_seq Ψ.weaken := by
  show Term.app (Term.weaken Term.diag_seq) Ψ.weaken = _
  rw [diag_seq_weaken]

/-- `(diag_seq Ψ)(t) =₀ Ψ̂(t+3)(t+3)` — the two beta steps. -/
def diag_seq_apply (Ψ : Term F Γ (Ty.nat →ₜ realTy ι)) (t : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app (.app Term.diag_seq Ψ) t)
        (Term.app2 Term.cauchyfy
          (.app Ψ (.app .succ (.app .succ (.app .succ t))))
          (.app .succ (.app .succ (.app .succ t))))) :=
  lam2_correct_nf
    (Term.app2 Term.cauchyfy
      (.app (.var (.vs .vz)) (.app .succ (.app .succ (.app .succ (.var .vz)))))
      (.app .succ (.app .succ (.app .succ (.var .vz))))
      : Term F (Ty.nat :: (Ty.nat →ₜ realTy ι) :: Γ) Ty.nat)
    Ψ t (by qb_nf)

/-- `c =₀ 0 → sg_bar c =₀ 1`, as an object implication — the sequent-level counterpart of
`qtrans (sg_bar_congr ·) sg_bar_zero`. -/
def sg_bar_of_zero (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 c Term.zero →ᶠ
       Formula.eq0 (.app Term.sg_bar c) (.app .succ .zero)) := by
  pmode
  pintro h
  prwby h
  pthm sg_bar_zero

end Approx

end Metatheorems
