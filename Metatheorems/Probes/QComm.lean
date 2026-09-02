/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RationalNumbers
import Metatheorems.ProofMode.Rewrite

/-!
# Probe QComm: what does the proof mode actually save on `add_Q_comm`?

`RationalNumbers.add_Q_comm` is 486 lines of raw `Derivable` combinators, written before the
proof mode existed. It is already proved, so re-deriving it here can only produce a line
count, never a new theorem — which is the point. The number decides whether the rationals
(and then the reals) are blocked on *tooling* or on *mathematics*.

The mathematical skeleton is deliberately kept identical to the original: this measures the
cost of the encoding, not of finding a better proof.

Nothing here is imported by `Metatheorems.lean`.
-/

namespace Metatheorems
namespace Probes

open Formula ProofMode

variable {ι : Type} {F : ι → Ty ι}
  {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-! ## Chunk 1 — pure congruence plumbing (calibration)

The original `h_num` (RationalNumbers.lean:5024–5031) is 8 lines of `ite_nat_congr_x/y/b`
threaded by `and_intro`/`.trans0`. It says: three rewrites under a context.
-/

/-- Original: 8 lines. Here: 4. -/
example (b b' x y : Term F Γ Ty.nat)
    (h_same : Derivable F al Premises (Formula.eq0 b b')) :
    Derivable F al Premises
      (Formula.eq0 (Term.app3 Term.ite_nat b (Term.app2 Term.add x y)
                                             (Term.app2 Term.abs_diff x y))
                   (Term.app3 Term.ite_nat b' (Term.app2 Term.add y x)
                                              (Term.app2 Term.abs_diff y x))) := by
  pmode
  prw (add_comm x y)
  prw (abs_diff_comm x y)
  prw h_same
  prefl

/-! ## The retrofit

Setup is copied verbatim from the original (RationalNumbers.lean:4960–5022): the `let`
abbreviations, the two substitution normal forms `nf_ab`/`nf_ba`, and the `lam2_correct_nf`
unfoldings. The proof mode does not address any of that, and it is reproduced unchanged so
the comparison is only over the part it *does* address.
-/

def add_Q_comm_pm :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_Q (.var .vz) (.var (.vs .vz)))))) :=
  -- ══════════ setup, verbatim from the original ══════════
  let a : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var (.vs .vz)
  let b : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let sa := Term.app Term.rat_sign a
  let sb := Term.app Term.rat_sign b
  let pa := Term.app Term.rat_num a
  let pb := Term.app Term.rat_num b
  let da := Term.app Term.rat_den a
  let db := Term.app Term.rat_den b
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    let n₁ := Term.var (.vs .vz)
    let n₂ := Term.var .vz
    let s₁ := Term.app Term.rat_sign n₁
    let s₂ := Term.app Term.rat_sign n₂
    let p₁ := Term.app Term.rat_num n₁
    let p₂ := Term.app Term.rat_num n₂
    let d₁ := Term.app Term.rat_den n₁
    let d₂ := Term.app Term.rat_den n₂
    let ac := Term.app2 Term.mul p₁ d₂
    let bc := Term.app2 Term.mul p₂ d₁
    let same := Term.app Term.sg_bar (Term.app2 Term.abs_diff s₁ s₂)
    Term.app3 Term.rat_encode
      (Term.app3 Term.ite_nat same s₁
        (Term.app3 Term.ite_nat (Term.app2 Term.geq ac bc) s₁ s₂))
      (Term.app3 Term.ite_nat same (Term.app2 Term.add ac bc) (Term.app2 Term.abs_diff ac bc))
      (Term.app Term.pd (Term.app2 Term.mul d₁ d₂))
  have body_eq : (Term.add_Q : Term F (Ty.nat :: Ty.nat :: Γ) _) =
      Term.lam (Term.lam body) := by rfl
  let ac_ab := Term.app2 Term.mul pa db
  let bc_ab := Term.app2 Term.mul pb da
  let same_ab := Term.app Term.sg_bar (Term.app2 Term.abs_diff sa sb)
  let sign_ab := Term.app3 Term.ite_nat same_ab sa
    (Term.app3 Term.ite_nat (Term.app2 Term.geq ac_ab bc_ab) sa sb)
  let num_ab := Term.app3 Term.ite_nat same_ab
    (Term.app2 Term.add ac_ab bc_ab)
    (Term.app2 Term.abs_diff ac_ab bc_ab)
  let den_ab := Term.app Term.pd (Term.app2 Term.mul da db)
  let same_ba := Term.app Term.sg_bar (Term.app2 Term.abs_diff sb sa)
  let sign_ba := Term.app3 Term.ite_nat same_ba sb
    (Term.app3 Term.ite_nat (Term.app2 Term.geq bc_ab ac_ab) sb sa)
  let num_ba := Term.app3 Term.ite_nat same_ba
    (Term.app2 Term.add bc_ab ac_ab)
    (Term.app2 Term.abs_diff bc_ab ac_ab)
  let den_ba := Term.app Term.pd (Term.app2 Term.mul db da)
  have nf_ab : (body.subst0 (b.weaken)).subst0 a =
      Term.app3 Term.rat_encode sign_ab num_ab den_ab := by
    qnorm [body, a, b, sign_ab, num_ab, den_ab, same_ab, ac_ab, bc_ab,
      sa, sb, pa, pb, da, db]
  have nf_ba : (body.subst0 (a.weaken)).subst0 b =
      Term.app3 Term.rat_encode sign_ba num_ba den_ba := by
    qnorm [body, a, b, sign_ba, num_ba, den_ba, same_ba,
      sa, sb, pa, pb, da, db, ac_ab, bc_ab]
  let unfold_ab := body_eq ▸ lam2_correct_nf body a b nf_ab
  let unfold_ba := body_eq ▸ lam2_correct_nf body b a nf_ba
  -- ══════════ end of setup ══════════

  let result_ab := Term.app2 Term.add_Q a b
  let result_ba := Term.app2 Term.add_Q b a
  let rn_ab := Term.app Term.rat_num result_ab
  let rd_ab := Term.app Term.rat_den result_ab
  let rs_ab := Term.app Term.rat_sign result_ab
  let rn_ba := Term.app Term.rat_num result_ba
  let rd_ba := Term.app Term.rat_den result_ba
  let rs_ba := Term.app Term.rat_sign result_ba
  let abs_rs := Term.app2 Term.abs_diff rs_ab rs_ba
  let sg_nn := Term.app Term.sg (Term.app2 Term.add num_ab num_ab)

  -- ── the three component equalities (original: 11 lines) ──
  let h_same : Derivable F al Premises (Formula.eq0 same_ab same_ba) := by
    pmode; prw (abs_diff_comm sa sb); prefl
  let h_num : Derivable F al Premises (Formula.eq0 num_ab num_ba) := by
    pmode
    prw (add_comm ac_ab bc_ab)
    prw (abs_diff_comm ac_ab bc_ab)
    prw h_same
    prefl
  let h_den : Derivable F al Premises (Formula.eq0 den_ab den_ba) := by
    pmode; prw (mul_comm da db); prefl

  -- ── numerator / denominator extraction (original: ~45 lines) ──
  let h_rn_ab : Derivable F al Premises (Formula.eq0 rn_ab num_ab) := by
    pmode
    prw unfold_ab
    pthm (rat_num_rat_encode sign_ab num_ab den_ab (isEven_cases sign_ab))
  let h_rn_ba : Derivable F al Premises (Formula.eq0 rn_ba num_ab) := by
    pmode
    prw unfold_ba
    prw (rat_num_rat_encode sign_ba num_ba den_ba (isEven_cases sign_ba))
    prw h_num
    prefl
  let h_rd_eq : Derivable F al Premises (Formula.eq0 rd_ab rd_ba) := by
    pmode
    prw unfold_ab
    prw unfold_ba
    prw (rat_den_rat_encode sign_ab num_ab den_ab)
    prw (rat_den_rat_encode sign_ba num_ba den_ba)
    prw h_den
    prefl

  -- ── the cross-multiplication half of `eq_Q` (original: ~12 lines) ──
  let h_cross : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.abs_diff
        (Term.app2 Term.mul rn_ab rd_ba) (Term.app2 Term.mul rn_ba rd_ab)) .zero) := by
    pmode
    prw h_rn_ab
    prw h_rn_ba
    prw h_rd_eq
    pthm (abs_diff_self _)

  -- ── `sign_ab =₀ sign_ba` suffices for the sign half (original: 44 lines) ──
  let sign_to_mul : Derivable F al Premises
      (Formula.eq0 sign_ab sign_ba →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) := by
    pmode
    pintro hs
    phave habs : Formula.eq0 abs_rs .zero
    · papplym (Derivable.mp (abs_diff_eq_zero_iff rs_ab rs_ba)
        (.syllogism .and_perm .and_weak))
      prw unfold_ab
      prw unfold_ba
      prwby hs
      prw h_num
      prw h_den
      prefl
    prwby habs
    pthm (mul_zero_l sg_nn)

  -- ── `num_ab =₀ 0` also suffices (original: 33 lines) ──
  let num_zero_to_mul : Derivable F al Premises
      (Formula.eq0 num_ab .zero →ᶠ
       Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) := by
    pmode
    pintro hn
    prwby hn
    prw (add_zero_r Term.zero)
    prw sg_zero
    pthm (mul_zero abs_rs)

  -- ── the sign case analysis (original: ~260 lines) ──
  let inner_ab := Term.app3 Term.ite_nat (Term.app2 Term.geq ac_ab bc_ab) sa sb
  let inner_ba := Term.app3 Term.ite_nat (Term.app2 Term.geq bc_ab ac_ab) sb sa
  let h_cases : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs sg_nn) .zero) := by
    pmode
    pfrom hsplit := sg_bar_cases (Term.app2 Term.abs_diff sa sb)
    pcases hsplit with hone | hzero
    · -- Case A: the signs agree, so both results take the `sa`/`sb` branch.
      papplym sign_to_mul
      phave hsa : Formula.eq0 sign_ab sa
      · prwby hone
        pthm (ite_nat_one sa inner_ab)
      phave hsb : Formula.eq0 sign_ba sb
      · phave hone' : Formula.eq0 same_ba (.app .succ .zero)
        · prw (Derivable.mp h_same Derivable.sym0)
          pexact hone
        prwby hone'
        pthm (ite_nat_one sb inner_ba)
      phave hab : Formula.eq0 sa sb
      · papplym (Derivable.mp (abs_diff_eq_zero_iff sa sb) Derivable.and_weak)
        papplym (sg_bar_eq_S0_implies_zero (Term.app2 Term.abs_diff sa sb))
        pexact hone
      prwby hsa
      prwby hsb
      pexact hab
    · -- Case B: the signs differ; both results take the `geq` branch.
      phave hsi : Formula.eq0 sign_ab inner_ab
      · prwby hzero
        pthm (ite_nat_zero sa inner_ab)
      phave hzero' : Formula.eq0 same_ba .zero
      · prw (Derivable.mp h_same Derivable.sym0)
        pexact hzero
      phave hsi' : Formula.eq0 sign_ba inner_ba
      · prwby hzero'
        pthm (ite_nat_zero sb inner_ba)
      phave hnd : Formula.eq0 num_ab (Term.app2 Term.abs_diff ac_ab bc_ab)
      · prwby hzero
        pthm (ite_nat_zero (Term.app2 Term.add ac_ab bc_ab)
          (Term.app2 Term.abs_diff ac_ab bc_ab))
      pfrom hmon := monus_disjunct ac_ab bc_ab
      pcases hmon with hm1 | hm2
      · -- ac ∸ bc =₀ 0
        pfrom hsg := sg_bar_cases (Term.app2 Term.monus bc_ab ac_ab)
        pcases hsg with hs1 | hs0
        · -- both differences vanish: ac =₀ bc, so the numerator is 0
          papplym num_zero_to_mul
          prwby hnd
          papplym (Derivable.mp (abs_diff_eq_zero_iff ac_ab bc_ab)
            (.syllogism .and_perm .and_weak))
          papplym (monus_eq_zero_antisym ac_ab bc_ab)
          psplit
          · pexact hm1
          · papplym (sg_bar_eq_S0_implies_zero (Term.app2 Term.monus bc_ab ac_ab))
            pexact hs1
        · -- the two `geq` tests pick out the same sign, `sb`
          papplym sign_to_mul
          prwby hsi
          prwby hsi'
          prw (geq_unfold ac_ab bc_ab)
          prw (geq_unfold bc_ab ac_ab)
          prwby hs0
          phave hs1' : Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus ac_ab bc_ab))
              (.app .succ .zero)
          · prwby hm1
            pthm sg_bar_zero
          prwby hs1'
          prw (ite_nat_zero sa sb)
          prw (ite_nat_one sb sa)
          prefl
      · -- bc ∸ ac =₀ 0, the mirror image
        pfrom hsg := sg_bar_cases (Term.app2 Term.monus ac_ab bc_ab)
        pcases hsg with hs1 | hs0
        · papplym num_zero_to_mul
          prwby hnd
          papplym (Derivable.mp (abs_diff_eq_zero_iff ac_ab bc_ab)
            (.syllogism .and_perm .and_weak))
          papplym (monus_eq_zero_antisym ac_ab bc_ab)
          psplit
          · papplym (sg_bar_eq_S0_implies_zero (Term.app2 Term.monus ac_ab bc_ab))
            pexact hs1
          · pexact hm2
        · papplym sign_to_mul
          prwby hsi
          prwby hsi'
          prw (geq_unfold ac_ab bc_ab)
          prw (geq_unfold bc_ab ac_ab)
          prwby hs0
          phave hs1' : Formula.eq0 (.app Term.sg_bar (Term.app2 Term.monus bc_ab ac_ab))
              (.app .succ .zero)
          · prwby hm2
            pthm sg_bar_zero
          prwby hs1'
          prw (ite_nat_one sa sb)
          prw (ite_nat_zero sb sa)
          prefl

  -- ── final assembly (original: 10 lines) ──
  let h_sign_zero : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.mul abs_rs
        (Term.app Term.sg (Term.app2 Term.add rn_ab rn_ba))) .zero) := by
    pmode
    prw h_rn_ab
    prw h_rn_ba
    pthm h_cases
  univ_gen (univ_gen (eq_Q_from_components h_cross h_sign_zero))

/-- The retrofit inhabits exactly the original's type — stated independently so a drift in
either would fail here rather than pass silently. -/
example : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_Q (.var .vz) (.var (.vs .vz)))))) :=
  add_Q_comm

/-- …and so does the original, from the same statement. -/
example : Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (eq_Q (Term.app2 Term.add_Q (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_Q (.var .vz) (.var (.vs .vz)))))) :=
  add_Q_comm_pm

#print axioms add_Q_comm_pm

end Probes
end Metatheorems
