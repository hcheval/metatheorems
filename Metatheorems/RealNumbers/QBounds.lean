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

variable {ι : Type} {F : ι → Ty ι}
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
    · canorm
      pexists Term.zero
      canorm
      pleft
      pthm (Derivable.mp (add_zero_r (Term.zero : Term F Γ Ty.nat)) Derivable.sym0)
    · pforall
      pintro ih
      canorm
      pobtain ih with hm
      canorm
      pcases hm with h1 | h2
      · pexists (.var .vz)
        canorm
        pright
        prwby h1
        prefl
      · pexists (.app .succ (.var .vz))
        canorm
        pleft
        prw (Derivable.mp
          (qtrans (add_succ (.app .succ (.var .vz)) (.var .vz))
            (succ_congr' (add_succ_l (.var .vz) (.var .vz))))
          Derivable.sym0)
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
  canorm
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

end QBounds

end Metatheorems
