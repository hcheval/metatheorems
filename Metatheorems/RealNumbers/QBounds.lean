/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RationalNumbers

namespace Metatheorems

/-!
# ℚ-code bounds: the code-dominates-magnitude toolkit

The ℕ and ℚ lemmas behind `abs_R_bound` (Kohlenbach p. 430: `|α|_ℝ ≤_ℝ (α(0)+1)_ℝ`) and
`mul_R_check` (that `mul_R f g` is provably Cauchy). The central fact is **a ℚ-code dominates
the magnitude it encodes** (`abs_Q_le_encode`): `|c|_ℚ ≤_ℚ ⟨c⟩_ℚ` for every code `c`, because
`rat_num c = div2(j₁ c + isOdd (j₁ c)) ≤ j₁ c ≤ c ≤ c · rat_den c`.

Everything here is pure ℕ/ℚ — no `cauchyfy`, no real operations — so the file sits beside
`RealNumbers/Defs.lean` rather than above it. Several small `private` computations from
`RationalNumbers.lean` (`isEven_zero`, `isEven_succ`, `two_mul_eq_add`, …) are re-derived
here because that file is another workstream's and its privates are module-scoped.
-/

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

/-- The substitution normal-form discharger for this file's `qfer`/beta side conditions.
`qnorm` with an empty lemma list does not parse outside `Arithmetic.lean`, so this file
carries its own; the set is `q_ord_norm`'s term-level half. -/
macro "qb_nf" : tactic =>
  `(tactic| simp only [Term.subst0, Term.subst,
      Term.subst0_map, Term.subst0_map_vz, Term.subst0_map_vs,
      Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var,
      Term.weaken_subst0, Term.weaken_subst0_eta, subst_subst0_map_weaken,
      Term.app2, Term.app3, Term.ofNat, closed_subst])

macro "qb_nf" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$ts,*, Term.subst0, Term.subst,
      Term.subst0_map, Term.subst0_map_vz, Term.subst0_map_vs,
      Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var,
      Term.weaken_subst0, Term.weaken_subst0_eta, subst_subst0_map_weaken,
      Term.app2, Term.app3, Term.ofNat, closed_subst])

/-- `canorm` (from `RealNumbers/Estimates.lean`) minus the `cauchyState` pieces — this file
sits below `Cauchyfy.lean`, so it carries its own copy of the normaliser. -/
macro "qb_canorm" : tactic =>
  `(tactic| (try q_cons_norm
             simp only [lt_Q, le_Q, eq_Q,
               Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst,
               Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               Term.weaken_subst0, subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, ProofMode.succVar0, closed_subst,
               ← Formula.substF_shift_eq_weakenBy, Term.subst_shift_eq_weaken]
             try q_cons_norm))

section QBounds

variable {Γ : Ctx ι}

-- ── Congruence helpers (via QF-ER, the standard pattern) ────────────────────

private def succ_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz))
    (by qb_nf) (by qb_nf)

private def isEven_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.isEven s) (.app Term.isEven t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.isEven (.var .vz))
    (by qb_nf) (by qb_nf)

private def isOdd_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.isOdd s) (.app Term.isOdd t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.isOdd (.var .vz))
    (by qb_nf) (by qb_nf)

private def div2_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.div2 s) (.app Term.div2 t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.div2 (.var .vz))
    (by qb_nf) (by qb_nf)

private def rat_num_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.rat_num s) (.app Term.rat_num t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_num (.var .vz))
    (by qb_nf) (by qb_nf)

private def pair_congr_l {s t : Term F Γ Ty.nat} (u : Term F Γ Ty.nat)
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.pair s u) (Term.app2 Term.pair t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.pair (.var .vz) u.weaken)
    (by qb_nf) (by qb_nf)

-- ── isEven / isOdd computations (re-derived; the originals are private) ─────

private def isEven_body : Term F (Ty.nat :: Γ) Ty.nat :=
  Term.app3 (.prec Ty.nat) (.app .succ .zero)
    (Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))) (.var .vz)

/-- `isEven 0 =₀ 1`. -/
def isEven_zero' :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isEven Term.zero) (.app .succ .zero)) :=
  let h1 := Term.lam_correct (isEven_body (Γ := Γ)) Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- `isEven (S n) =₀ sg_bar (isEven n)`. -/
def isEven_succ' (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.isEven (.app .succ n))
        (.app Term.sg_bar (.app Term.isEven n))) :=
  let z : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
    Term.lam (Term.lam (.app Term.sg_bar (.var (.vs .vz))))
  let recn : Term F Γ Ty.nat := Term.app3 (.prec Ty.nat) (.app .succ .zero) z n
  let h1 := lam_correct_nf (isEven_body (Γ := Γ)) (.app .succ n)
    (by qb_nf [isEven_body])
  let h2 : Derivable F al Premises
      (Formula.eq0 (Term.app2 z recn n) (.app Term.sg_bar recn)) :=
    lam2_correct_nf
      (.app Term.sg_bar (.var (.vs .vz)) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
      recn n (by qb_nf)
  let h3 : Derivable F al Premises (Formula.eq0 (.app Term.isEven n) recn) :=
    Term.lam_correct (isEven_body (Γ := Γ)) n
  let h4 := sg_bar_congr (Derivable.mp h3 Derivable.sym0)
  let c1 := .mp (.mp (.rec_succ (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) .trans0
  .mp (.mp h4 (.mp c2 and_intro)) .trans0

/-- `isEven 1 =₀ 0`. -/
def isEven_one' :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.isEven (.app .succ .zero)) Term.zero) :=
  qtrans (isEven_succ' .zero)
    (qtrans (sg_bar_congr isEven_zero') (sg_bar_succ .zero))

/-- `isOdd n =₀ 1 ∸ isEven n`. -/
def isOdd_unfold' (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.isOdd n)
        (Term.app2 Term.monus (.app .succ .zero) (.app Term.isEven n))) :=
  lam_correct_nf
    (Term.app2 Term.monus (.app .succ .zero) (.app Term.isEven (.var .vz))
      : Term F (Ty.nat :: Γ) Ty.nat) n (by qb_nf)

/-- `2 · n =₀ n + n`. -/
def two_mul_eq_add' (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.mul (Term.ofNat 2) n) (Term.app2 Term.add n n)) :=
  let h_ms := mul_succ_l (.app .succ .zero) n
  let h_m1 := qtrans (mul_comm (.app .succ .zero) n) (mul_one_r n)
  qtrans h_ms (add_congr_l h_m1 n)

/-- `isEven (n + n) =₀ 1` — a double is even. -/
def isEven_add_self (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.isEven (Term.app2 Term.add n n)) (.app .succ .zero)) :=
  let all_form : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (Formula.eq0 (.app Term.isEven (Term.app2 Term.add (.var .vz) (.var .vz)))
          (.app .succ .zero))) := by
    pmode
    pinduction
    · q_ord_norm
      prw (add_zero_r (Term.zero : Term F Γ Ty.nat))
      pthm isEven_zero'
    · pforall
      pintro ih
      q_ord_norm
      prw (add_succ (.app .succ (.var .vz)) (.var .vz))
      prw (add_succ_l (.var .vz) (.var .vz))
      prw (isEven_succ' (.app .succ (Term.app2 Term.add (.var .vz) (.var .vz))))
      prw (isEven_succ' (Term.app2 Term.add (.var .vz) (.var .vz)))
      prwby ih
      prw (sg_bar_succ (Term.zero : Term F (Ty.nat :: Γ) Ty.nat))
      pthm sg_bar_zero
  by
    have h := Derivable.mp all_form (.forall_ax n)
    q_norm using h

/-- `isOdd (n + n) =₀ 0`. -/
def isOdd_add_self (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.isOdd (Term.app2 Term.add n n)) Term.zero) :=
  qtrans (isOdd_unfold' (Term.app2 Term.add n n))
    (qtrans (monus_congr_snd (.app .succ .zero) (isEven_add_self n))
      (monus_self (.app .succ .zero)))

/-- `isOdd (S (n + n)) =₀ 1`. -/
def isOdd_succ_add_self (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.isOdd (.app .succ (Term.app2 Term.add n n)))
        (.app .succ .zero)) :=
  let hE : Derivable F al Premises
      (Formula.eq0 (.app Term.isEven (.app .succ (Term.app2 Term.add n n))) Term.zero) :=
    qtrans (isEven_succ' (Term.app2 Term.add n n))
      (qtrans (sg_bar_congr (isEven_add_self n)) (sg_bar_succ .zero))
  qtrans (isOdd_unfold' (.app .succ (Term.app2 Term.add n n)))
    (qtrans (monus_congr_snd (.app .succ .zero) hE) (monus_zero (.app .succ .zero)))

-- ── `2^(a+b) = 2^a · 2^b`, and `n + 2 ≤ 2^(n+1)` ─────────────────────────────

/-- `exp2 (a + b) =₀ exp2 a · exp2 b`. -/
def exp2_add (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.exp2 (Term.app2 Term.add a b))
        (Term.app2 Term.mul (.app Term.exp2 a) (.app Term.exp2 b))) :=
  let all_form : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (Formula.eq0 (.app Term.exp2 (Term.app2 Term.add a.weaken (.var .vz)))
          (Term.app2 Term.mul (.app Term.exp2 a.weaken) (.app Term.exp2 (.var .vz))))) := by
    pmode
    pinduction
    · q_ord_norm
      prw (add_zero_r a)
      prw (exp2_zero)
      pthm (Derivable.mp (mul_one_r (.app Term.exp2 a)) Derivable.sym0)
    · pforall
      pintro ih
      q_ord_norm
      prw (add_succ a.weaken (.var .vz))
      prw (exp2_succ (Term.app2 Term.add a.weaken (.var .vz)))
      prwby ih
      prw (exp2_succ (.var .vz))
      pthm (Derivable.mp
        (mul_add (.app Term.exp2 a.weaken) (.app Term.exp2 (.var .vz))
          (.app Term.exp2 (.var .vz)))
        Derivable.sym0)
  by
    have h := Derivable.mp all_form (.forall_ax b)
    q_norm using h

/-- `n + 2 ≤ 2^(n+1)`, in `monus` form: the strict version of `exp2_ge_self` one level up.
This is what makes an `encode_lt` between `⟨n+1⟩` and `⟨2^(n+1)⟩` available, which is where
the strictness of the multiplicative Cauchy estimates comes from. -/
def succ_succ_le_exp2_succ (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ n))
        (.app Term.exp2 (.app .succ n))) .zero) :=
  let all_form : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat
        (Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ (.var .vz)))
          (.app Term.exp2 (.app .succ (.var .vz)))) .zero)) := by
    pmode
    pinduction
    · q_ord_norm
      prw (exp2_succ (Term.zero : Term F Γ Ty.nat))
      prw (exp2_zero)
      -- SS0 ∸ (1+1): 1+1 =₀ SS0, then monus_self
      prw (add_succ (.app .succ .zero) (Term.zero : Term F Γ Ty.nat))
      prw (add_zero_r (.app .succ (.zero : Term F Γ Ty.nat)))
      pthm (monus_self (.app .succ (.app .succ (.zero : Term F Γ Ty.nat))))
    · pforall
      pintro ih
      q_ord_norm
      prw (exp2_succ (.app .succ (.var .vz)))
      -- SSSk =₀ SSk + 1, then add_le_mono with SSk ≤ 2^(k+1) and 1 ≤ 2^(k+1)
      phave hS : Formula.eq0
          (.app .succ (.app .succ (.app .succ (.var .vz : Term F (Ty.nat :: Γ) Ty.nat))))
          (Term.app2 Term.add (.app .succ (.app .succ (.var .vz))) (.app .succ .zero))
      · pthm (Derivable.mp
          (qtrans (add_succ (.app .succ (.app .succ (.var .vz))) .zero)
            (succ_congr' (add_zero_r (.app .succ (.app .succ (.var .vz))))))
          Derivable.sym0)
      prwby hS
      papplym (add_le_mono (.app .succ (.app .succ (.var .vz)))
        (.app Term.exp2 (.app .succ (.var .vz)))
        (.app .succ .zero)
        (.app Term.exp2 (.app .succ (.var .vz))))
      psplit
      · pexact ih
      · pthm (one_le_exp2 (.app .succ (.var .vz)))
  by
    have h := Derivable.mp all_form (.forall_ax n)
    q_norm using h

-- ── Unfolds for `rat_num`, `rat_encode`, `fst_pair`, `encode_nat_Q` ─────────

/-- `rat_num z =₀ div2 (j₁ z + isOdd (j₁ z))`. -/
def rat_num_unfold' (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_num z)
        (.app Term.div2 (Term.app2 Term.add
          (.app Term.fst_pair z) (.app Term.isOdd (.app Term.fst_pair z))))) :=
  lam_correct_nf
    (.app Term.div2 (Term.app2 Term.add
      (.app Term.fst_pair (.var .vz)) (.app Term.isOdd (.app Term.fst_pair (.var .vz))))
      : Term F (Ty.nat :: Γ) Ty.nat) z (by qb_nf)

/-- `rat_encode s n d =₀ pair (2·n ∸ isEven s) d`. -/
def rat_encode_unfold' (s n d : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app3 Term.rat_encode s n d)
        (Term.app2 Term.pair
          (Term.app2 Term.monus (Term.app2 Term.mul (Term.ofNat 2) n) (.app Term.isEven s))
          d)) :=
  lam3_correct_nf
    (Term.app2 Term.pair
      (Term.app2 Term.monus
        (Term.app2 Term.mul (Term.ofNat 2) (.var (.vs .vz)))
        (.app Term.isEven (.var (.vs (.vs .vz)))))
      (.var .vz)) s n d (by qb_nf)

/-- `fst_pair z =₀ z ∸ triag (inv_triag z)`. -/
def fst_pair_unfold' (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.fst_pair z)
        (Term.app2 Term.monus z (.app Term.triag (.app Term.inv_triag z)))) :=
  lam_correct_nf
    (Term.app2 Term.monus (.var .vz) (.app Term.triag (.app Term.inv_triag (.var .vz)))
      : Term F (Ty.nat :: Γ) Ty.nat) z (by qb_nf)

/-- `⟨c⟩_ℚ =₀ pair (2·c) 0`. -/
def encode_nat_Q_unfold (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.encode_nat_Q c)
        (Term.app2 Term.pair (Term.app2 Term.mul (Term.ofNat 2) c) Term.zero)) :=
  lam_correct_nf
    (Term.app2 Term.pair (Term.app2 Term.mul (Term.ofNat 2) (.var .vz)) Term.zero
      : Term F (Ty.nat :: Γ) Ty.nat) c (by qb_nf)

-- ── `div2` on doubles, via the public `rat_encode` roundtrip ────────────────

/-- `div2 (m + m) =₀ m`. Not proved by analysing `div2`'s state machine: the public
roundtrip `rat_num_rat_encode` already contains that analysis, and
`rat_num (pair (2m) 0) = div2 (2m + isOdd (2m))` unfolds to exactly this statement. -/
def div2_double' (m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.div2 (Term.app2 Term.add m m)) m) :=
  let twoM : Term F Γ Ty.nat := Term.app2 Term.mul (Term.ofNat 2) m
  let enc : Term F Γ Ty.nat := Term.app3 Term.rat_encode (.app .succ .zero) m Term.zero
  let pairT : Term F Γ Ty.nat := Term.app2 Term.pair twoM Term.zero
  let h_enc : Derivable F al Premises (Formula.eq0 enc pairT) :=
    qtrans (rat_encode_unfold' (.app .succ .zero) m Term.zero)
      (pair_congr_l Term.zero
        (qtrans (monus_congr_snd twoM isEven_one') (monus_zero twoM)))
  let h_rt : Derivable F al Premises (Formula.eq0 (.app Term.rat_num enc) m) :=
    rat_num_rat_encode (.app .succ .zero) m Term.zero (isEven_cases (.app .succ .zero))
  let j : Term F Γ Ty.nat := .app Term.fst_pair pairT
  let h_j' : Derivable F al Premises (Formula.eq0 j (Term.app2 Term.add m m)) :=
    qtrans (fst_pair_pair twoM Term.zero) (two_mul_eq_add' m)
  let h_num_pair : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_num pairT)
        (.app Term.div2 (Term.app2 Term.add j (.app Term.isOdd j)))) :=
    rat_num_unfold' pairT
  let h_arg : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add j (.app Term.isOdd j))
        (Term.app2 Term.add m m)) :=
    qtrans (add_congr_l h_j' (.app Term.isOdd j))
      (qtrans (add_congr_r (Term.app2 Term.add m m)
        (qtrans (isOdd_congr' h_j') (isOdd_add_self m)))
        (add_zero_r (Term.app2 Term.add m m)))
  qtrans
    (qtrans
      (Derivable.mp (div2_congr' h_arg) Derivable.sym0)
      (Derivable.mp h_num_pair Derivable.sym0))
    (qtrans (rat_num_congr' (Derivable.mp h_enc Derivable.sym0)) h_rt)

-- ── Every number is a double or a double plus one ───────────────────────────

/-- `∃m. j = m + m ∨ j = S (m + m)`. The parity existential `isEven_cases` cannot supply. -/
def double_or_succ (j : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.ex Ty.nat
        (Formula.eq0 j.weaken (Term.app2 Term.add (.var .vz) (.var .vz))
          ∨ᶠ Formula.eq0 j.weaken (.app .succ (Term.app2 Term.add (.var .vz) (.var .vz))))) :=
  let all_form : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.ex Ty.nat
        (Formula.eq0 (.var (.vs .vz)) (Term.app2 Term.add (.var .vz) (.var .vz))
          ∨ᶠ Formula.eq0 (.var (.vs .vz))
              (.app .succ (Term.app2 Term.add (.var .vz) (.var .vz)))))) := by
    pmode
    pinduction
    · qb_canorm
      pexists Term.zero
      qb_canorm
      pleft
      pthm (Derivable.mp (add_zero_r (Term.zero : Term F Γ Ty.nat)) Derivable.sym0)
    · pforall
      pintro ih
      qb_canorm
      pobtain ih with hm
      qb_canorm
      pcases hm with h1 | h2
      · pexists (.var .vz)
        qb_canorm
        pright
        prwby h1
        prefl
      · pexists (.app .succ (.var .vz))
        qb_canorm
        pleft
        prw (qtrans (add_succ (.app .succ (.var .vz)) (.var .vz))
          (succ_congr' (add_succ_l (.var .vz) (.var .vz))))
        prwby h2
        prefl
  by
    have h := Derivable.mp all_form (.forall_ax j)
    q_norm using h

-- ── The exact `div2` bound, and the code-dominates chain ────────────────────

/-- `div2 (j + isOdd j) ≤ j` — i.e. `rat_num`'s rounding never overshoots its input. -/
def div2_add_isOdd_le (j : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus
        (.app Term.div2 (Term.app2 Term.add j (.app Term.isOdd j))) j) .zero) := by
  pmode
  pfrom hex := double_or_succ j
  pobtain hex with hcase
  qb_canorm
  pcases hcase with h1 | h2
  · prwby h1
    prw (isOdd_add_self (.var .vz))
    prw (add_zero_r (Term.app2 Term.add (.var .vz) (.var .vz)))
    prw (div2_double' (.var .vz))
    pthm (monus_add_self (.var .vz) (.var .vz))
  · prwby h2
    prw (isOdd_succ_add_self (.var .vz))
    prw (add_succ (.app .succ (Term.app2 Term.add (.var .vz) (.var .vz))) Term.zero)
    prw (add_zero_r (.app .succ (Term.app2 Term.add (.var .vz) (.var .vz))))
    prw (Derivable.mp
      (qtrans (add_succ (.app .succ (.var .vz)) (.var .vz))
        (succ_congr' (add_succ_l (.var .vz) (.var .vz))))
      Derivable.sym0)
    prw (div2_double' (.app .succ (.var .vz)))
    prw (monus_succ_l (.var .vz) (Term.app2 Term.add (.var .vz) (.var .vz)))
    pthm (monus_add_self (.var .vz) (.var .vz))

/-- `j₁ z ≤ z`: a Cantor code dominates its first projection. -/
def fst_pair_le (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.fst_pair z) z) .zero) :=
  let t : Term F Γ Ty.nat := .app Term.triag (.app Term.inv_triag z)
  let h1 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.fst_pair z) z)
        (Term.app2 Term.monus (Term.app2 Term.monus z t) z)) :=
    monus_congr_fst (fst_pair_unfold' z) z
  -- (z ∸ t) ∸ z =₀ z ∸ (t + z) =₀ 0
  let h2 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.monus z t) z) .zero) :=
    qtrans (Derivable.mp (monus_monus z t z) Derivable.sym0) (monus_add_self z t)
  qtrans h1 h2

/-- **`rat_num z ≤ z`: a ℚ-code dominates its own (unsigned) numerator.** -/
def rat_num_le_self (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.rat_num z) z) .zero) :=
  let j : Term F Γ Ty.nat := .app Term.fst_pair z
  let d2 : Term F Γ Ty.nat := .app Term.div2 (Term.app2 Term.add j (.app Term.isOdd j))
  let h1 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.rat_num z) z)
        (Term.app2 Term.monus d2 z)) :=
    monus_congr_fst (rat_num_unfold' z) z
  let h2 : Derivable F al Premises (Formula.eq0 (Term.app2 Term.monus d2 z) .zero) :=
    Derivable.mp
      (Derivable.mp (Derivable.mp (fst_pair_le z)
        (Derivable.mp (div2_add_isOdd_le j) and_intro))
        (monus_le_trans d2 j z))
      I_comb
  qtrans h1 h2

-- ── More congruence helpers ─────────────────────────────────────────────────

private def snd_pair_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.snd_pair s) (.app Term.snd_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.snd_pair (.var .vz))
    (by qb_nf) (by qb_nf)

private def rat_den_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.rat_den s) (.app Term.rat_den t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_den (.var .vz))
    (by qb_nf) (by qb_nf)

private def rat_sign_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.rat_sign s) (.app Term.rat_sign t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.rat_sign (.var .vz))
    (by qb_nf) (by qb_nf)

private def fst_pair_congr'' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.fst_pair s) (.app Term.fst_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.fst_pair (.var .vz))
    (by qb_nf) (by qb_nf)

private def abs_diff_congr_fst' (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff s u) (Term.app2 Term.abs_diff t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.abs_diff (.var .vz) u.weaken)
    (by qb_nf) (by qb_nf)

private def abs_diff_congr_snd' (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff u s) (Term.app2 Term.abs_diff u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.abs_diff u.weaken (.var .vz))
    (by qb_nf) (by qb_nf)

-- ── Parts of `⟨c⟩_ℚ` ────────────────────────────────────────────────────────

/-- `rat_den z =₀ S (snd_pair z)`. -/
def rat_den_unfold' (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den z) (.app .succ (.app Term.snd_pair z))) :=
  lam_correct_nf
    (.app .succ (.app Term.snd_pair (.var .vz)) : Term F (Ty.nat :: Γ) Ty.nat) z
    (by qb_nf)

/-- `rat_sign z =₀ isEven (j₁ z)`. -/
def rat_sign_unfold' (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign z) (.app Term.isEven (.app Term.fst_pair z))) :=
  lam_correct_nf
    (.app Term.isEven (.app Term.fst_pair (.var .vz)) : Term F (Ty.nat :: Γ) Ty.nat) z
    (by qb_nf)

/-- `rat_num ⟨c⟩ =₀ c`. -/
def rat_num_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_num (.app Term.encode_nat_Q c)) c) :=
  let twoC : Term F Γ Ty.nat := Term.app2 Term.mul (Term.ofNat 2) c
  let enc : Term F Γ Ty.nat := Term.app3 Term.rat_encode (.app .succ .zero) c Term.zero
  let pairT : Term F Γ Ty.nat := Term.app2 Term.pair twoC Term.zero
  let h_enc : Derivable F al Premises (Formula.eq0 enc pairT) :=
    qtrans (rat_encode_unfold' (.app .succ .zero) c Term.zero)
      (pair_congr_l Term.zero
        (qtrans (monus_congr_snd twoC isEven_one') (monus_zero twoC)))
  let h_rt : Derivable F al Premises (Formula.eq0 (.app Term.rat_num enc) c) :=
    rat_num_rat_encode (.app .succ .zero) c Term.zero (isEven_cases (.app .succ .zero))
  qtrans (rat_num_congr' (encode_nat_Q_unfold c))
    (qtrans (rat_num_congr' (Derivable.mp h_enc Derivable.sym0)) h_rt)

/-- `rat_den ⟨c⟩ =₀ 1`. -/
def rat_den_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den (.app Term.encode_nat_Q c)) (.app .succ .zero)) :=
  let twoC : Term F Γ Ty.nat := Term.app2 Term.mul (Term.ofNat 2) c
  qtrans (rat_den_congr' (encode_nat_Q_unfold c))
    (qtrans (rat_den_unfold' (Term.app2 Term.pair twoC Term.zero))
      (succ_congr' (snd_pair_pair twoC Term.zero)))

/-- `rat_sign ⟨c⟩ =₀ 1`. -/
def rat_sign_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign (.app Term.encode_nat_Q c)) (.app .succ .zero)) :=
  let twoC : Term F Γ Ty.nat := Term.app2 Term.mul (Term.ofNat 2) c
  let pairT : Term F Γ Ty.nat := Term.app2 Term.pair twoC Term.zero
  qtrans (rat_sign_congr' (encode_nat_Q_unfold c))
    (qtrans (rat_sign_unfold' pairT)
      (qtrans (isEven_congr' (qtrans (fst_pair_pair twoC Term.zero) (two_mul_eq_add' c)))
        (isEven_add_self c)))

/-- `posN z =₀ rat_num z` for a positively-signed code. -/
def posN_of_sign_one (z : Term F Γ Ty.nat)
    (hs : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign z) (.app .succ .zero))) :
    Derivable F al Premises (Formula.eq0 (posN z) (.app Term.rat_num z)) :=
  qtrans (mul_congr_l hs (.app Term.rat_num z)) (mul_one_l (.app Term.rat_num z))

/-- `negN z =₀ 0` for a positively-signed code. -/
def negN_of_sign_one (z : Term F Γ Ty.nat)
    (hs : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign z) (.app .succ .zero))) :
    Derivable F al Premises (Formula.eq0 (negN z) .zero) :=
  qtrans (mul_congr_l
      (qtrans (monus_congr_snd (.app .succ .zero) hs) (monus_self (.app .succ .zero)))
      (.app Term.rat_num z))
    (mul_zero_l (.app Term.rat_num z))

/-- `posN ⟨c⟩ =₀ c`. -/
def posN_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises (Formula.eq0 (posN (.app Term.encode_nat_Q c)) c) :=
  qtrans (posN_of_sign_one _ (rat_sign_encode c)) (rat_num_encode c)

/-- `negN ⟨c⟩ =₀ 0`. -/
def negN_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises (Formula.eq0 (negN (.app Term.encode_nat_Q c)) .zero) :=
  negN_of_sign_one _ (rat_sign_encode c)

-- ── `≤_ℚ` between codes with denominator 1 ──────────────────────────────────

/-- `≤_ℚ` between two positively-signed, denominator-1 codes reduces to a plain ℕ
inequality between their numerators. -/
def le_Q_of_parts_le (x y : Term F Γ Ty.nat)
    (hnx : Derivable F al Premises (Formula.eq0 (negN x) .zero))
    (hny : Derivable F al Premises (Formula.eq0 (negN y) .zero))
    (hdx : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den x) (.app .succ .zero)))
    (hdy : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den y) (.app .succ .zero)))
    (h : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (posN x) (posN y)) .zero)) :
    Derivable F al Premises (le_Q x y) :=
  let dx : Term F Γ Ty.nat := .app Term.rat_den x
  let dy : Term F Γ Ty.nat := .app Term.rat_den y
  let L : Term F Γ Ty.nat :=
    Term.app2 Term.add (Term.app2 Term.mul (negN y) dx) (Term.app2 Term.mul (posN x) dy)
  let R : Term F Γ Ty.nat :=
    Term.app2 Term.add (Term.app2 Term.mul (posN y) dx) (Term.app2 Term.mul (negN x) dy)
  -- L =₀ posN x, R': posN y ≤ R
  let hL : Derivable F al Premises (Formula.eq0 L (posN x)) :=
    qtrans
      (add_congr_l (qtrans (mul_congr_l hny dx) (mul_zero_l dx))
        (Term.app2 Term.mul (posN x) dy))
    (qtrans (add_zero_l (Term.app2 Term.mul (posN x) dy))
      (qtrans (mul_congr_r (posN x) hdy) (mul_one_r (posN x))))
  let hR : Derivable F al Premises (Formula.eq0 R (posN y)) :=
    qtrans
      (add_congr_r (Term.app2 Term.mul (posN y) dx)
        (qtrans (mul_congr_l hnx dy) (mul_zero_l dy)))
    (qtrans (add_zero_r (Term.app2 Term.mul (posN y) dx))
      (qtrans (mul_congr_r (posN y) hdx) (mul_one_r (posN y))))
  let hcross : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus L R) .zero) :=
    qtrans (monus_congr_fst hL R) (qtrans (monus_congr_snd (posN x) hR) h)
  Derivable.mp hcross (le_Q_of_cross x y)

/-- `⟨c⟩ ≤_ℚ ⟨d⟩` from `c ≤ d` at ℕ. -/
def encode_le (c d : Term F Γ Ty.nat)
    (h : Derivable F al Premises (Formula.eq0 (Term.app2 Term.monus c d) .zero)) :
    Derivable F al Premises
      (le_Q (.app Term.encode_nat_Q c) (.app Term.encode_nat_Q d)) :=
  le_Q_of_parts_le _ _ (negN_encode c) (negN_encode d) (rat_den_encode c)
    (rat_den_encode d)
    (qtrans (monus_congr_fst (posN_encode c) (posN (.app Term.encode_nat_Q d)))
      (qtrans (monus_congr_snd c (posN_encode d)) h))

/-- **A ℚ-code dominates the magnitude it encodes**: `|c|_ℚ ≤_ℚ ⟨c⟩_ℚ`.
Kohlenbach p. 430's `rmrk:bound-on-real`, at the level of a single code:
`num c ≤ j₁ c ≤ c ≤ c · den c`, and the cross criterion does the rest. -/
def abs_le_encode (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q c) (.app Term.encode_nat_Q c)) :=
  let dabs : Term F Γ Ty.nat := .app Term.rat_den (.app Term.abs_Q c)
  let dc : Term F Γ Ty.nat := .app Term.rat_den c
  let dy : Term F Γ Ty.nat := .app Term.rat_den (.app Term.encode_nat_Q c)
  let L : Term F Γ Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.mul (negN (.app Term.encode_nat_Q c)) dabs)
      (Term.app2 Term.mul (posN (.app Term.abs_Q c)) dy)
  let R : Term F Γ Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.mul (posN (.app Term.encode_nat_Q c)) dabs)
      (Term.app2 Term.mul (negN (.app Term.abs_Q c)) dy)
  -- L =₀ num c
  let hL : Derivable F al Premises (Formula.eq0 L (.app Term.rat_num c)) :=
    qtrans
      (add_congr_l (qtrans (mul_congr_l (negN_encode c) dabs) (mul_zero_l dabs))
        (Term.app2 Term.mul (posN (.app Term.abs_Q c)) dy))
    (qtrans (add_zero_l (Term.app2 Term.mul (posN (.app Term.abs_Q c)) dy))
      (qtrans (mul_congr_l (posN_abs_Q c) dy)
        (qtrans (mul_congr_r (.app Term.rat_num c) (rat_den_encode c))
          (mul_one_r (.app Term.rat_num c)))))
  -- R =₀ c · den c
  let hR : Derivable F al Premises
      (Formula.eq0 R (Term.app2 Term.mul c dc)) :=
    qtrans
      (add_congr_r (Term.app2 Term.mul (posN (.app Term.encode_nat_Q c)) dabs)
        (qtrans (mul_congr_l (negN_abs_Q c) dy) (mul_zero_l dy)))
    (qtrans (add_zero_r (Term.app2 Term.mul (posN (.app Term.encode_nat_Q c)) dabs))
      (qtrans (mul_congr_l (posN_encode c) dabs)
        (mul_congr_r c (rat_den_abs_Q c))))
  -- num c ≤ c ≤ c·den c
  let h_c_le : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus c (Term.app2 Term.mul c dc)) .zero) :=
    let hdc : Derivable F al Premises
        (Formula.eq0 (Term.app2 Term.mul c dc)
          (Term.app2 Term.add (Term.app2 Term.mul c (.app Term.snd_pair c)) c)) :=
      qtrans (mul_congr_r c (rat_den_unfold' c)) (mul_succ c (.app Term.snd_pair c))
    qtrans (monus_congr_snd c hdc)
      (monus_add_self c (Term.app2 Term.mul c (.app Term.snd_pair c)))
  let h_num_le : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app Term.rat_num c)
        (Term.app2 Term.mul c dc)) .zero) :=
    Derivable.mp
      (Derivable.mp (Derivable.mp h_c_le
        (Derivable.mp (rat_num_le_self c) and_intro))
        (monus_le_trans (.app Term.rat_num c) c (Term.app2 Term.mul c dc)))
      I_comb
  let hcross : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus L R) .zero) :=
    qtrans (monus_congr_fst hL R)
      (qtrans (monus_congr_snd (.app Term.rat_num c) hR) h_num_le)
  Derivable.mp hcross (le_Q_of_cross (.app Term.abs_Q c) (.app Term.encode_nat_Q c))

-- ── Sums of positively-signed codes ─────────────────────────────────────────

/-- The same-sign bit is set when both signs are `1`. -/
def addQ_same_pos (x y : Term F Γ Ty.nat)
    (hsx : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign x) (.app .succ .zero)))
    (hsy : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign y) (.app .succ .zero))) :
    Derivable F al Premises (Formula.eq0 (addQ_same x y) (.app .succ .zero)) :=
  qtrans
    (sg_bar_congr
      (qtrans (abs_diff_congr_fst' (.app Term.rat_sign y) hsx)
        (qtrans (abs_diff_congr_snd' (.app .succ .zero) hsy)
          (abs_diff_self (.app .succ .zero)))))
    sg_bar_zero

/-- The sign read back from a same-positive-sign sum is `1` — unconditionally, numerator
zero included, because `isEven (2·N) =₀ 1` for every `N`. -/
def rat_sign_add_Q_pos (x y : Term F Γ Ty.nat)
    (hsx : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign x) (.app .succ .zero)))
    (hsy : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign y) (.app .succ .zero))) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app2 Term.add_Q x y)) (.app .succ .zero)) :=
  let N : Term F Γ Ty.nat := addQ_num x y
  let hE : Derivable F al Premises
      (Formula.eq0 (.app Term.isEven (addQ_sign x y)) .zero) :=
    qtrans (isEven_congr' (qtrans (addQ_sign_same x y (addQ_same_pos x y hsx hsy)) hsx))
      isEven_one'
  qtrans (rat_sign_add_Q x y)
    (qtrans (isEven_congr'
        (qtrans (monus_congr_snd (Term.app2 Term.mul (Term.ofNat 2) N) hE)
          (monus_zero (Term.app2 Term.mul (Term.ofNat 2) N))))
      (qtrans (isEven_congr' (two_mul_eq_add' N)) (isEven_add_self N)))

/-- The sign read back from a product of positively-signed codes is `1`. -/
def rat_sign_mul_Q_pos (x y : Term F Γ Ty.nat)
    (hsx : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign x) (.app .succ .zero)))
    (hsy : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign y) (.app .succ .zero))) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app2 Term.mul_Q x y)) (.app .succ .zero)) :=
  let N : Term F Γ Ty.nat :=
    Term.app2 Term.mul (.app Term.rat_num x) (.app Term.rat_num y)
  let hSame : Derivable F al Premises
      (Formula.eq0 (.app Term.sg_bar (Term.app2 Term.abs_diff
        (.app Term.rat_sign x) (.app Term.rat_sign y))) (.app .succ .zero)) :=
    addQ_same_pos x y hsx hsy
  let hE : Derivable F al Premises
      (Formula.eq0 (.app Term.isEven (.app Term.sg_bar (Term.app2 Term.abs_diff
        (.app Term.rat_sign x) (.app Term.rat_sign y)))) .zero) :=
    qtrans (isEven_congr' hSame) isEven_one'
  qtrans (rat_sign_mul_Q x y)
    (qtrans (isEven_congr'
        (qtrans (monus_congr_snd (Term.app2 Term.mul (Term.ofNat 2) N) hE)
          (monus_zero (Term.app2 Term.mul (Term.ofNat 2) N))))
      (qtrans (isEven_congr' (two_mul_eq_add' N)) (isEven_add_self N)))

/-- The parts of `1_ℚ`, once and for all. -/
def rat_sign_one_Q' :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_sign Term.one_Q) (.app .succ .zero)) :=
  rat_sign_pair_two .zero

def rat_num_one_Q' :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_num Term.one_Q) (.app .succ .zero)) :=
  rat_num_pair_two .zero

def rat_den_one_Q' :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.rat_den Term.one_Q) (.app .succ .zero)) :=
  qtrans (rat_den_unfold' Term.one_Q) (succ_congr' (snd_pair_pair (Term.ofNat 2) .zero))

/-- `⟨S m⟩ =_ℚ ⟨m⟩ +_ℚ 1_ℚ` — the additive step of the ℕ ↪ ℚ embedding. -/
def encode_succ (m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app Term.encode_nat_Q (.app .succ m))
        (Term.app2 Term.add_Q (.app Term.encode_nat_Q m) Term.one_Q)) :=
  let em : Term F Γ Ty.nat := .app Term.encode_nat_Q m
  let v : Term F Γ Ty.nat := Term.app2 Term.add_Q em Term.one_Q
  let sv : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign v) (.app .succ .zero)) :=
    rat_sign_add_Q_pos em Term.one_Q (rat_sign_encode m) rat_sign_one_Q'
  -- num v =₀ S m
  let hcross1 : Derivable F al Premises
      (Formula.eq0 (addQ_cross em Term.one_Q) m) :=
    qtrans (mul_congr_l (rat_num_encode m) (.app Term.rat_den Term.one_Q))
      (qtrans (mul_congr_r m rat_den_one_Q') (mul_one_r m))
  let hcross2 : Derivable F al Premises
      (Formula.eq0 (addQ_cross Term.one_Q em) (.app .succ .zero)) :=
    qtrans (mul_congr_l rat_num_one_Q' (.app Term.rat_den em))
      (qtrans (mul_congr_r (.app .succ .zero) (rat_den_encode m))
        (mul_one_r (.app .succ .zero)))
  let hnum_v : Derivable F al Premises (Formula.eq0 (.app Term.rat_num v) (.app .succ m)) :=
    qtrans (rat_num_add_Q em Term.one_Q)
      (qtrans (addQ_num_same em Term.one_Q
          (addQ_same_pos em Term.one_Q (rat_sign_encode m) rat_sign_one_Q'))
        (qtrans (add_congr_l hcross1 (addQ_cross Term.one_Q em))
          (qtrans (add_congr_r m hcross2)
            (qtrans (add_succ m .zero) (succ_congr' (add_zero_r m))))))
  let hd_v : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den v) (.app .succ .zero)) :=
    qtrans (rat_den_add_Q em Term.one_Q)
      (qtrans (mul_congr_l (rat_den_encode m) (.app Term.rat_den Term.one_Q))
        (qtrans (mul_congr_r (.app .succ .zero) rat_den_one_Q')
          (mul_one_r (.app .succ .zero))))
  eq_Q_of_pos_neg _ _
    (qtrans (posN_encode (.app .succ m))
      (Derivable.mp (qtrans (posN_of_sign_one v sv) hnum_v) Derivable.sym0))
    (qtrans (negN_encode (.app .succ m))
      (Derivable.mp (negN_of_sign_one v sv) Derivable.sym0))
    (qtrans (rat_den_encode (.app .succ m)) (Derivable.mp hd_v Derivable.sym0))

-- ── Order plumbing for the estimates ────────────────────────────────────────

/-- `x ≤_ℚ y` and `0 <_ℚ P` give `x −_ℚ y <_ℚ P` — the shape a `≤` between cauchyfied
values must take to refute a `lt_R` witness. -/
def sub_lt_of_le (x y P : Term F Γ Ty.nat)
    (hxy : Derivable F al Premises (le_Q x y))
    (hP : Derivable F al Premises (lt_Q Term.zero_Q P)) :
    Derivable F al Premises (lt_Q (Term.app2 Term.sub_Q x y) P) :=
  let d : Term F Γ Ty.nat := Term.app2 Term.sub_Q y x
  let h1 : Derivable F al Premises (le_Q Term.zero_Q d) :=
    Derivable.mp hxy (le_Q_to_zero_sub x y)
  let h2 : Derivable F al Premises (lt_Q Term.zero_Q (Term.app2 Term.add_Q P d)) :=
    Derivable.mp (Derivable.mp h1 (Derivable.mp hP and_intro)) (lt_Q_zero_add_le P d)
  let h3 : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q P d)
        (Term.app2 Term.sub_Q P (Term.app2 Term.sub_Q x y))) :=
    eqQsym (eqQtrans (sub_Q_eq_add_neg P (Term.app2 Term.sub_Q x y))
      (addQr P (neg_Q_sub_Q y x)))
  Derivable.mp (Derivable.mp h2 (lt_Q_zero_congr _ _ h3))
    (lt_Q_of_zero_sub (Term.app2 Term.sub_Q x y) P)

/-- `| |z| |_ℚ =_ℚ |z|_ℚ`. -/
def abs_Q_abs_Q (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app Term.abs_Q (.app Term.abs_Q z)) (.app Term.abs_Q z)) :=
  eq_Q_of_pos_neg _ _
    (qtrans (posN_abs_Q (.app Term.abs_Q z))
      (qtrans (rat_num_abs_Q z) (Derivable.mp (posN_abs_Q z) Derivable.sym0)))
    (qtrans (negN_abs_Q (.app Term.abs_Q z))
      (Derivable.mp (negN_abs_Q z) Derivable.sym0))
    (rat_den_abs_Q (.app Term.abs_Q z))

/-- `0 ≤_ℚ |z|_ℚ`. -/
def le_Q_zero_abs (z : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q Term.zero_Q (.app Term.abs_Q z)) :=
  Derivable.mp (negN_abs_Q z) (le_Q_zero_of_parts (.app Term.abs_Q z))

/-- `|x| ≤_ℚ |y| +_ℚ |y −_ℚ x|` — magnitude moves by at most the distance moved. -/
def abs_Q_le_add_diff (x y : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q x)
        (Term.app2 Term.add_Q (.app Term.abs_Q y)
          (.app Term.abs_Q (Term.app2 Term.sub_Q y x)))) :=
  let h := abs_Q_sub_triangle x y Term.zero_Q
  Derivable.mp h
    (le_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q x Term.zero_Q))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q x y))
        (.app Term.abs_Q (Term.app2 Term.sub_Q y Term.zero_Q)))
      (.app Term.abs_Q x)
      (Term.app2 Term.add_Q (.app Term.abs_Q y)
        (.app Term.abs_Q (Term.app2 Term.sub_Q y x)))
      (abs_Q_congr (sub_Q_zero_Q x))
      (eqQtrans
        (add_Q_comm_inst (.app Term.abs_Q (Term.app2 Term.sub_Q x y))
          (.app Term.abs_Q (Term.app2 Term.sub_Q y Term.zero_Q)))
        (eqQtrans
          (addQr (.app Term.abs_Q (Term.app2 Term.sub_Q y Term.zero_Q))
            (abs_diff_Q_comm x y))
          (addQl (abs_Q_congr (sub_Q_zero_Q y))
            (.app Term.abs_Q (Term.app2 Term.sub_Q y x))))))

private def pd_congr'' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app Term.pd s) (.app Term.pd t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.pd (.var .vz))
    (by qb_nf) (by qb_nf)

private def pair_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.pair u s) (Term.app2 Term.pair u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.pair u.weaken (.var .vz))
    (by qb_nf) (by qb_nf)

/-- `⟨2^{-0}⟩_ℚ =₀ 1_ℚ`. -/
def pow2neg_zero_eq_one :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.pow2neg_Q Term.zero) Term.one_Q) :=
  qtrans (pow2neg_Q_unfold Term.zero)
    (pair_congr_r (Term.ofNat 2)
      (qtrans (pd_congr'' exp2_zero) (pd_succ .zero)))

/-- `≤_ℚ` transitivity with Lean-level premises: the composition every chain below uses. -/
def leQt {a b c : Term F Γ Ty.nat}
    (h1 : Derivable F al Premises (le_Q a b))
    (h2 : Derivable F al Premises (le_Q b c)) :
    Derivable F al Premises (le_Q a c) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (le_Q_trans a b c)

-- ── `eq_Q` congruence for `mul_Q`, in usable form ───────────────────────────

/-- `mul_Q_congr` instantiated at four explicit terms. -/
def mul_Q_congr_inst (a b c d : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q a b ∧ᶠ eq_Q c d →ᶠ
        eq_Q (Term.app2 Term.mul_Q a c) (Term.app2 Term.mul_Q b d)) := by
  have h := Derivable.mp (Derivable.mp (Derivable.mp (Derivable.mp
    (mul_Q_congr (al := al) (Premises := Premises) (Γ := Γ))
    (.forall_ax a)) (.forall_ax b)) (.forall_ax c)) (.forall_ax d)
  q_norm using h

/-- `u =_ℚ v → u ·_ℚ w =_ℚ v ·_ℚ w`. -/
def mulQl {u v : Term F Γ Ty.nat}
    (h : Derivable F al Premises (eq_Q u v)) (w : Term F Γ Ty.nat) :
    Derivable F al Premises (eq_Q (Term.app2 Term.mul_Q u w) (Term.app2 Term.mul_Q v w)) :=
  Derivable.mp (Derivable.mp (eq_Q_refl_inst w) (Derivable.mp h and_intro))
    (mul_Q_congr_inst u v w w)

/-- `u =_ℚ v → w ·_ℚ u =_ℚ w ·_ℚ v`. -/
def mulQr (w : Term F Γ Ty.nat) {u v : Term F Γ Ty.nat}
    (h : Derivable F al Premises (eq_Q u v)) :
    Derivable F al Premises (eq_Q (Term.app2 Term.mul_Q w u) (Term.app2 Term.mul_Q w v)) :=
  Derivable.mp (Derivable.mp h (Derivable.mp (eq_Q_refl_inst w) and_intro))
    (mul_Q_congr_inst w w u v)

-- ── Ring identities: negation and subtraction against `mul_Q` ───────────────

/-- `(−_ℚ x) ·_ℚ y =_ℚ −_ℚ (x ·_ℚ y)`. -/
def mul_Q_neg_l (x y : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (.app Term.neg_Q x) y)
        (.app Term.neg_Q (Term.app2 Term.mul_Q x y))) :=
  let px := posN x
  let nx := negN x
  let py := posN y
  let ny := negN y
  eq_Q_of_pos_neg _ _
    -- posN((−x)·y) = negN x·posN y + posN x·negN y = posN(−(x·y)) (after a swap)
    (qtrans (posN_mul_Q (.app Term.neg_Q x) y)
      (qtrans
        (qtrans (add_congr_l (mul_congr_l (posN_neg_Q x) py) (Term.app2 Term.mul (negN (.app Term.neg_Q x)) ny))
          (add_congr_r (Term.app2 Term.mul nx py) (mul_congr_l (negN_neg_Q x) ny)))
        (qtrans (add_comm (Term.app2 Term.mul nx py) (Term.app2 Term.mul px ny))
          (Derivable.mp (qtrans (posN_neg_Q (Term.app2 Term.mul_Q x y)) (negN_mul_Q x y))
            Derivable.sym0))))
    (qtrans (negN_mul_Q (.app Term.neg_Q x) y)
      (qtrans
        (qtrans (add_congr_l (mul_congr_l (posN_neg_Q x) ny) (Term.app2 Term.mul (negN (.app Term.neg_Q x)) py))
          (add_congr_r (Term.app2 Term.mul nx ny) (mul_congr_l (negN_neg_Q x) py)))
        (qtrans (add_comm (Term.app2 Term.mul nx ny) (Term.app2 Term.mul px py))
          (Derivable.mp (qtrans (negN_neg_Q (Term.app2 Term.mul_Q x y)) (posN_mul_Q x y))
            Derivable.sym0))))
    (qtrans (rat_den_mul_Q (.app Term.neg_Q x) y)
      (qtrans (mul_congr_l (rat_den_neg_Q x) (.app Term.rat_den y))
        (Derivable.mp (qtrans (rat_den_neg_Q (Term.app2 Term.mul_Q x y)) (rat_den_mul_Q x y))
          Derivable.sym0)))

/-- `(x +_ℚ y) ·_ℚ z =_ℚ x·z +_ℚ y·z`. -/
def add_mul_Q (x y z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (Term.app2 Term.add_Q x y) z)
        (Term.app2 Term.add_Q (Term.app2 Term.mul_Q x z) (Term.app2 Term.mul_Q y z))) :=
  eqQtrans (mul_Q_comm_inst (Term.app2 Term.add_Q x y) z)
    (eqQtrans (distrib_Q_inst z x y)
      (eqQtrans (addQr (Term.app2 Term.mul_Q z x) (mul_Q_comm_inst z y))
        (addQl (mul_Q_comm_inst z x) (Term.app2 Term.mul_Q y z))))

/-- `(a −_ℚ b) ·_ℚ c =_ℚ a·c −_ℚ b·c`. -/
def sub_Q_mul_distrib (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (Term.app2 Term.sub_Q a b) c)
        (Term.app2 Term.sub_Q (Term.app2 Term.mul_Q a c) (Term.app2 Term.mul_Q b c))) :=
  eqQtrans (mulQl (sub_Q_eq_add_neg a b) c)
    (eqQtrans (add_mul_Q a (.app Term.neg_Q b) c)
      (eqQtrans (addQr (Term.app2 Term.mul_Q a c) (mul_Q_neg_l b c))
        (eqQsym (sub_Q_eq_add_neg (Term.app2 Term.mul_Q a c) (Term.app2 Term.mul_Q b c)))))

/-- `|x ·_ℚ y|_ℚ =_ℚ |x|_ℚ ·_ℚ |y|_ℚ`. -/
def abs_Q_mul (x y : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app Term.abs_Q (Term.app2 Term.mul_Q x y))
        (Term.app2 Term.mul_Q (.app Term.abs_Q x) (.app Term.abs_Q y))) :=
  let ax : Term F Γ Ty.nat := .app Term.abs_Q x
  let ay : Term F Γ Ty.nat := .app Term.abs_Q y
  let sR : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign (Term.app2 Term.mul_Q ax ay)) (.app .succ .zero)) :=
    rat_sign_mul_Q_pos ax ay (rat_sign_abs_Q x) (rat_sign_abs_Q y)
  eq_Q_of_pos_neg _ _
    (qtrans (posN_abs_Q (Term.app2 Term.mul_Q x y))
      (qtrans (rat_num_mul_Q x y)
        (Derivable.mp
          (qtrans (posN_of_sign_one _ sR)
            (qtrans (rat_num_mul_Q ax ay)
              (qtrans (mul_congr_l (rat_num_abs_Q x) (.app Term.rat_num ay))
                (mul_congr_r (.app Term.rat_num x) (rat_num_abs_Q y)))))
          Derivable.sym0)))
    (qtrans (negN_abs_Q (Term.app2 Term.mul_Q x y))
      (Derivable.mp (negN_of_sign_one _ sR) Derivable.sym0))
    (qtrans (rat_den_abs_Q (Term.app2 Term.mul_Q x y))
      (qtrans (rat_den_mul_Q x y)
        (Derivable.mp
          (qtrans (rat_den_mul_Q ax ay)
            (qtrans (mul_congr_l (rat_den_abs_Q x) (.app Term.rat_den ay))
              (mul_congr_r (.app Term.rat_den x) (rat_den_abs_Q y))))
          Derivable.sym0)))

-- ── `≤_ℚ`/`<_ℚ` multiplication monotonicity ─────────────────────────────────

/-- `0 ≤ x → 0 ≤ y → 0 ≤ x·y`. -/
def le_Q_zero_mul (x y : Term F Γ Ty.nat)
    (hx : Derivable F al Premises (le_Q Term.zero_Q x))
    (hy : Derivable F al Premises (le_Q Term.zero_Q y)) :
    Derivable F al Premises (le_Q Term.zero_Q (Term.app2 Term.mul_Q x y)) :=
  let hnx : Derivable F al Premises (Formula.eq0 (negN x) .zero) :=
    Derivable.mp hx (le_Q_zero_parts x)
  let hny : Derivable F al Premises (Formula.eq0 (negN y) .zero) :=
    Derivable.mp hy (le_Q_zero_parts y)
  Derivable.mp
    (qtrans (negN_mul_Q x y)
      (qtrans
        (qtrans (add_congr_l (mul_congr_r (posN x) hny) (Term.app2 Term.mul (negN x) (posN y)))
          (add_congr_r (Term.app2 Term.mul (posN x) .zero) (mul_congr_l hnx (posN y))))
        (qtrans (add_congr_l (mul_zero (posN x)) (Term.app2 Term.mul Term.zero (posN y)))
          (qtrans (add_congr_r Term.zero (mul_zero_l (posN y))) (add_zero_r Term.zero)))))
    (le_Q_zero_of_parts (Term.app2 Term.mul_Q x y))

/-- `x ≤ X`, `0 ≤ y` give `x·y ≤ X·y`. -/
def le_Q_mul_mono_l (x X y : Term F Γ Ty.nat)
    (hx : Derivable F al Premises (le_Q x X))
    (hy : Derivable F al Premises (le_Q Term.zero_Q y)) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y)) :=
  let hd : Derivable F al Premises
      (le_Q Term.zero_Q (Term.app2 Term.mul_Q (Term.app2 Term.sub_Q X x) y)) :=
    le_Q_zero_mul _ y (Derivable.mp hx (le_Q_to_zero_sub x X)) hy
  Derivable.mp
    (Derivable.mp hd
      (le_Q_zero_congr _ _ (sub_Q_mul_distrib X x y)))
    (le_Q_of_zero_sub (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y))

/-- `0 ≤ x`, `y ≤ Y` give `x·y ≤ x·Y`. -/
def le_Q_mul_mono_r (x y Y : Term F Γ Ty.nat)
    (hx : Derivable F al Premises (le_Q Term.zero_Q x))
    (hy : Derivable F al Premises (le_Q y Y)) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q x Y)) :=
  Derivable.mp (le_Q_mul_mono_l y Y x hy hx)
    (le_Q_congr _ _ _ _ (mul_Q_comm_inst y x) (mul_Q_comm_inst Y x))

/-- `lt_Q_mul_pos` at two explicit terms. -/
def lt_Q_mul_pos_inst (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q Term.zero_Q a ∧ᶠ lt_Q Term.zero_Q b →ᶠ
        lt_Q Term.zero_Q (Term.app2 Term.mul_Q a b)) := by
  have h := Derivable.mp (Derivable.mp
    (lt_Q_mul_pos (al := al) (Premises := Premises) (Γ := Γ))
    (.forall_ax a)) (.forall_ax b)
  q_norm_ord using h

/-- `x < X`, `0 < y` give `x·y < X·y` — the strict step of every check estimate. -/
def lt_Q_mul_mono_l (x X y : Term F Γ Ty.nat)
    (hx : Derivable F al Premises (lt_Q x X))
    (hy : Derivable F al Premises (lt_Q Term.zero_Q y)) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y)) :=
  let hd : Derivable F al Premises
      (lt_Q Term.zero_Q (Term.app2 Term.mul_Q (Term.app2 Term.sub_Q X x) y)) :=
    Derivable.mp
      (Derivable.mp hy
        (Derivable.mp (Derivable.mp hx (lt_Q_to_zero_sub x X)) and_intro))
      (lt_Q_mul_pos_inst (Term.app2 Term.sub_Q X x) y)
  Derivable.mp
    (Derivable.mp hd (lt_Q_zero_congr _ _ (sub_Q_mul_distrib X x y)))
    (lt_Q_of_zero_sub (Term.app2 Term.mul_Q x y) (Term.app2 Term.mul_Q X y))

-- ── The move lemma: one factor shifts, the other is bounded ─────────────────

/-- `|a·r −_ℚ a'·r| ≤_ℚ B ·_ℚ P` from `|a − a'| ≤ P` and `|r| ≤ B`. -/
def mul_move_le (a a' r P B : Term F Γ Ty.nat)
    (h1 : Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q a a')) P))
    (h2 : Derivable F al Premises (le_Q (.app Term.abs_Q r) B)) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.mul_Q a r) (Term.app2 Term.mul_Q a' r)))
        (Term.app2 Term.mul_Q B P)) :=
  let d : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a')
  let ar : Term F Γ Ty.nat := .app Term.abs_Q r
  -- |a·r − a'·r| =ℚ |a−a'|·|r|
  let s12 : Derivable F al Premises
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.mul_Q a r) (Term.app2 Term.mul_Q a' r)))
        (Term.app2 Term.mul_Q d ar)) :=
    eqQtrans (abs_Q_congr (eqQsym (sub_Q_mul_distrib a a' r)))
      (abs_Q_mul (Term.app2 Term.sub_Q a a') r)
  -- ≤ P·|r| ≤ P·B =ℚ B·P
  let s3 : Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q d ar) (Term.app2 Term.mul_Q P ar)) :=
    le_Q_mul_mono_l d P ar h1 (le_Q_zero_abs r)
  let s4 : Derivable F al Premises
      (le_Q (Term.app2 Term.mul_Q P ar) (Term.app2 Term.mul_Q P B)) :=
    le_Q_mul_mono_r P ar B (leQt (le_Q_zero_abs (Term.app2 Term.sub_Q a a')) h1) h2
  Derivable.mp (leQt s3 s4)
    (le_Q_congr _ _ _ _ (eqQsym s12) (mul_Q_comm_inst P B))

/-- The mirror: the bounded factor on the left. -/
def mul_move_le_l (l a a' P B : Term F Γ Ty.nat)
    (h1 : Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q a a')) P))
    (h2 : Derivable F al Premises (le_Q (.app Term.abs_Q l) B)) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.mul_Q l a) (Term.app2 Term.mul_Q l a')))
        (Term.app2 Term.mul_Q B P)) :=
  Derivable.mp (mul_move_le a a' l P B h1 h2)
    (le_Q_congr _ _ _ _
      (abs_Q_congr (sub_Q_congr
        (mul_Q_comm_inst a l) (mul_Q_comm_inst a' l)))
      (eq_Q_refl_inst _))

-- ── `<_ℚ` between encodes, and the dyadic collection ────────────────────────

/-- `(a +_ℚ b) −_ℚ a =_ℚ b`. -/
def add_Q_sub_cancel_l (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (Term.app2 Term.add_Q a b) a) b) :=
  eqQtrans (sub_Q_eq_add_neg (Term.app2 Term.add_Q a b) a)
    (eqQtrans (addQl (add_Q_comm_inst a b) (.app Term.neg_Q a))
      (eqQtrans (add_Q_assoc_inst b a (.app Term.neg_Q a))
        (eqQtrans (addQr b (add_Q_neg_inst a)) (add_Q_zero_inst b))))

/-- `⟨c⟩ <_ℚ ⟨S c⟩`. -/
def encode_lt_succ (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.encode_nat_Q c) (.app Term.encode_nat_Q (.app .succ c))) :=
  Derivable.mp (zero_lt_one_Q (al := al) (Premises := Premises) (Γ := Γ))
    (lt_Q_of_eq_Q_diff Term.zero_Q Term.one_Q _ _
      (eqQtrans (sub_Q_zero_Q Term.one_Q)
        (eqQsym
          (eqQtrans (sub_Q_congr (encode_succ c) (eq_Q_refl_inst _))
            (add_Q_sub_cancel_l (.app Term.encode_nat_Q c) Term.one_Q)))))

/-- `⟨c⟩ <_ℚ ⟨d⟩` from `S c ≤ d` at ℕ. -/
def encode_lt (c d : Term F Γ Ty.nat)
    (h : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ c) d) .zero)) :
    Derivable F al Premises
      (lt_Q (.app Term.encode_nat_Q c) (.app Term.encode_nat_Q d)) :=
  Derivable.mp
    (Derivable.mp (encode_le (.app .succ c) d h)
      (Derivable.mp (encode_lt_succ c) and_intro))
    (lt_le_Q_trans (.app Term.encode_nat_Q c)
      (.app Term.encode_nat_Q (.app .succ c)) (.app Term.encode_nat_Q d))

/-- `⟨p⟩ +_ℚ ⟨q⟩ =_ℚ ⟨p + q⟩`. -/
def encode_add (p q : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (.app Term.encode_nat_Q p) (.app Term.encode_nat_Q q))
        (.app Term.encode_nat_Q (Term.app2 Term.add p q))) :=
  let ep : Term F Γ Ty.nat := .app Term.encode_nat_Q p
  let eq' : Term F Γ Ty.nat := .app Term.encode_nat_Q q
  let v : Term F Γ Ty.nat := Term.app2 Term.add_Q ep eq'
  let sv : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign v) (.app .succ .zero)) :=
    rat_sign_add_Q_pos ep eq' (rat_sign_encode p) (rat_sign_encode q)
  let hnum_v : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_num v) (Term.app2 Term.add p q)) :=
    qtrans (rat_num_add_Q ep eq')
      (qtrans (addQ_num_same ep eq'
          (addQ_same_pos ep eq' (rat_sign_encode p) (rat_sign_encode q)))
        (qtrans
          (add_congr_l
            (qtrans (mul_congr_l (rat_num_encode p) (.app Term.rat_den eq'))
              (qtrans (mul_congr_r p (rat_den_encode q)) (mul_one_r p)))
            (addQ_cross eq' ep))
          (add_congr_r p
            (qtrans (mul_congr_l (rat_num_encode q) (.app Term.rat_den ep))
              (qtrans (mul_congr_r q (rat_den_encode p)) (mul_one_r q))))))
  let hd_v : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den v) (.app .succ .zero)) :=
    qtrans (rat_den_add_Q ep eq')
      (qtrans (mul_congr_l (rat_den_encode p) (.app Term.rat_den eq'))
        (qtrans (mul_congr_r (.app .succ .zero) (rat_den_encode q))
          (mul_one_r (.app .succ .zero))))
  eqQsym (eq_Q_of_pos_neg _ _
    (qtrans (posN_encode (Term.app2 Term.add p q))
      (Derivable.mp (qtrans (posN_of_sign_one v sv) hnum_v) Derivable.sym0))
    (qtrans (negN_encode (Term.app2 Term.add p q))
      (Derivable.mp (negN_of_sign_one v sv) Derivable.sym0))
    (qtrans (rat_den_encode (Term.app2 Term.add p q))
      (Derivable.mp hd_v Derivable.sym0)))

/-- `1_ℚ =_ℚ ⟨1⟩`. -/
def one_Q_eq_encode :
    Derivable F al Premises (Γ := Γ)
      (eq_Q Term.one_Q (.app Term.encode_nat_Q (.app .succ .zero))) :=
  eqQ_of_nat_eq'' (Derivable.mp
    (qtrans (encode_nat_Q_unfold (.app .succ .zero))
      (pair_congr_l Term.zero (mul_one_r (Term.ofNat 2))))
    Derivable.sym0)
where
  /-- local `=₀ → =_ℚ` (avoiding an import cycle with `Bounds.lean`). -/
  eqQ_of_nat_eq'' {s t : Term F Γ Ty.nat}
      (h : Derivable F al Premises (Formula.eq0 s t)) :
      Derivable F al Premises (eq_Q s t) :=
    qtrans
      (qfer_no_premise_nat_nf (Derivable.mp h Derivable.sym0)
        (r := Term.app2 Term.eq_Q_dec s.weaken (.var .vz))
        (by qb_nf) (by qb_nf))
      (eq_Q_refl_inst s)

/-- Congruence for `encode_nat_Q`, at the level of `=₀`. -/
def encode_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.encode_nat_Q s) (.app Term.encode_nat_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.encode_nat_Q (.var .vz))
    (by qb_nf) (by qb_nf)

/-- Congruence for `exp2`, at the level of `=₀`. -/
def exp2_congr' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.exp2 s) (.app Term.exp2 t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.exp2 (.var .vz))
    (by qb_nf) (by qb_nf)

/-- **The dyadic collection**: `⟨2^e⟩ ·_ℚ 2^{-(e+m)} =_ℚ 2^{-m}`. -/
def encode_pow2_mul (e m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app Term.exp2 e))
              (.app Term.pow2neg_Q (Term.app2 Term.add e m)))
        (.app Term.pow2neg_Q m)) :=
  let E : Term F Γ Ty.nat := .app Term.encode_nat_Q (.app Term.exp2 e)
  let Pem : Term F Γ Ty.nat := .app Term.pow2neg_Q (Term.app2 Term.add e m)
  let L : Term F Γ Ty.nat := Term.app2 Term.mul_Q E Pem
  let R : Term F Γ Ty.nat := .app Term.pow2neg_Q m
  let sL : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign L) (.app .succ .zero)) :=
    rat_sign_mul_Q_pos E Pem (rat_sign_encode (.app Term.exp2 e))
      (rat_sign_pow2neg_Q (Term.app2 Term.add e m))
  let hnumL : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_num L) (.app Term.exp2 e)) :=
    qtrans (rat_num_mul_Q E Pem)
      (qtrans (mul_congr_l (rat_num_encode (.app Term.exp2 e)) (.app Term.rat_num Pem))
        (qtrans (mul_congr_r (.app Term.exp2 e) (rat_num_pow2neg_Q (Term.app2 Term.add e m)))
          (mul_one_r (.app Term.exp2 e))))
  let hdenL : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_den L) (.app Term.exp2 (Term.app2 Term.add e m))) :=
    qtrans (rat_den_mul_Q E Pem)
      (qtrans (mul_congr_l (rat_den_encode (.app Term.exp2 e)) (.app Term.rat_den Pem))
        (qtrans (mul_congr_r (.app .succ .zero) (rat_den_pow2neg_Q (Term.app2 Term.add e m)))
          (mul_one_l (.app Term.exp2 (Term.app2 Term.add e m)))))
  let sR : Derivable F al Premises
      (Formula.eq0 (.app Term.rat_sign R) (.app .succ .zero)) :=
    rat_sign_pow2neg_Q m
  let dL : Term F Γ Ty.nat := .app Term.rat_den L
  let dR : Term F Γ Ty.nat := .app Term.rat_den R
  let A1 : Term F Γ Ty.nat := Term.app2 Term.mul (posN L) dR
  let A2 : Term F Γ Ty.nat := Term.app2 Term.mul (negN R) dL
  let B1 : Term F Γ Ty.nat := Term.app2 Term.mul (posN R) dL
  let B2 : Term F Γ Ty.nat := Term.app2 Term.mul (negN L) dR
  let ee : Term F Γ Ty.nat := .app Term.exp2 (Term.app2 Term.add e m)
  -- both cross sums are `2^(e+m)`
  let hA : Derivable F al Premises (Formula.eq0 (Term.app2 Term.add A1 A2) ee) :=
    qtrans
      (qtrans
        (add_congr_l
          (qtrans (mul_congr_l (qtrans (posN_of_sign_one L sL) hnumL) dR)
            (mul_congr_r (.app Term.exp2 e) (rat_den_pow2neg_Q m)))
          A2)
        (add_congr_r (Term.app2 Term.mul (.app Term.exp2 e) (.app Term.exp2 m))
          (qtrans (mul_congr_l (negN_of_sign_one R sR) dL) (mul_zero_l dL))))
      (qtrans (add_zero_r (Term.app2 Term.mul (.app Term.exp2 e) (.app Term.exp2 m)))
        (Derivable.mp (exp2_add e m) Derivable.sym0))
  let hB : Derivable F al Premises (Formula.eq0 (Term.app2 Term.add B1 B2) ee) :=
    qtrans
      (qtrans
        (add_congr_l
          (qtrans (mul_congr_l
              (qtrans (posN_of_sign_one R sR) (rat_num_pow2neg_Q m)) dL)
            (qtrans (mul_congr_r (.app .succ .zero) hdenL) (mul_one_l ee)))
          B2)
        (add_congr_r ee
          (qtrans (mul_congr_l (negN_of_sign_one L sL) dR) (mul_zero_l dR))))
      (add_zero_r ee)
  -- cross: posN L · den R + negN R · den L =₀ posN R · den L + negN L · den R
  eq_Q_of_signed_cross L R (qtrans hA (Derivable.mp hB Derivable.sym0))

end QBounds

end Metatheorems
