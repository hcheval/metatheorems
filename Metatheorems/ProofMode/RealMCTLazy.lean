/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.RealMCT

/-!
# ℝ-MCT, the lazy proof (P1ℝ) — `real_mct_p1`

The same statement `RealMCT.rmStatement` that `real_mct_p2` proves, derived the way one
proves it on paper — the ℝ mirror of `ProofMode/MCTLazy.lean`'s `mct_p1`:

* assume no window is good (`pby_contra N`, so `N : ¬∃n C(n)`);
* a bad window drops by the budget unit: `¬C(m)` is, by `leIdx_dne` and `cauchyfy_const`,
  the rational fact `window_drop` consumes, and antitonicity (`antitone_chain_R`) supplies its
  other hypothesis — exactly the bad branch of `real_mct_window`, without the dichotomy;
* the descent `∀j ∃m (a m +ℝ q_j ≤ℝ a 0)`, `q_j := ⟨j ·ℚ 2^{-(k+1)}⟩ℝ`, by `pinduction`
  carrying the context: the witness is `m ↦ m + g m` once per step, and the step is
  `budget_succ_R` plus `≤ℝ`-monotonicity;
* at `j = 2^{k+1}` one more drop puts `(0 +ℝ ε) +ℝ q_j ≤ℝ 1ℝ ≤ℝ 0ℝ +ℝ q_j`
  (`one_R_le_budget`), cancel (`le_R_add_cancel_r_core`), so `ε ≤ℝ 0ℝ` against
  `zero_lt_pow2neg_R`.

**Markov, not excluded middle.** The reductio is applied only at the headline `∃n C(n)`,
whose matrix `rmC` is quantifier-free and ∨-free (`rmC_qf`, `rmC_vf`), so the classical
content is exactly `¬¬∃n(qf) → ∃n(qf)`, i.e. `Derivable.markov` — `pby_contra` refuses any
other shape (ARCHITECTURE.md §12, D-1/D-4). Hence `(hmk : al.markov = true)` where `p2`
needs nothing; the derivation lives at `Allowed.extended`, and `#print axioms` is
`[propext, Quot.sound]`, the same list as `real_mct_p2`.

`real_mct_bound_p1` is the metatheorem applied.
-/

namespace Metatheorems
namespace ProofMode

open Formula RealMCT

variable {ι κ : Type} {F : κ → Ty ι}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **The body of the statement**, proved lazily: `(∀u B) →ᶠ ∃n C(n)` over separate `a`, `g`,
`k`. `hmk` is what makes the reductio legal — `pby_contra` is the Markov rule and says so. -/
def real_mct_lazy_body (hmk : al.markov = true)
    (a : Term F Γ (Ty.nat →ₜ realTy ι)) (g : Term F Γ (Ty.nat →ₜ Ty.nat))
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
  pby_contra N
  -- every window is bad, so every window drops by ε
  phave hdrop : Formula.all Ty.nat                                       -- m = x₀
      (le_R (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
            (a ⬝ x₀))
  · pforall                     -- m = x₀
    rmnorm
    -- one-step antitonicity, from the premise's first conjunct
    phave hstep : Formula.all Ty.nat (le_R (a ⬝ S x₁) (a ⬝ x₁))
    · pforall                   -- n = x₁
      papply (le_R_of_le_R_pu (a ⬝ S x₁) (a ⬝ x₁))
      pforall                   -- u = x₂
      rmnorm
      pinst H x₂ with Hu
      rmnorm
      pinst Hu x₁ with Hn
      rmnorm
      pdestruct Hn with H12 H3
      pdestruct H12 with H1 H2
      pexact H1
    -- `a(m + g m) ≤ a m`: the antitone chain at `i := g m`
    pfrom ac := antitone_chain_R a
    pinst ac (g ⬝ x₀) with ac1
    rmnorm
    pinst ac1 x₀ with ac2
    rmnorm
    papply ac2 in hstep with hanti
    -- `¬C(m)`, from `N`
    phave hne : ¬ᶠ (leIdx (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
        (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k)))
    · pintro heq
      papply N
      pexists x₀
      rmnorm
      pexact heq
    -- …which is the rational fact the window drop consumes
    papplym (leIdx_dne (Term.abs_R ⬝ (Term.sub_R ⬝ (a ⬝ x₀) ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀))))
      (const_R (Term.pow2neg_Q ⬝ (S k))) (S (S k))) in hne with hX
    prw (cauchyfy_const (Term.pow2neg_Q ⬝ (S k)) (S (S (S k)))) in hX with hX'
    papply (window_drop (a ⬝ x₀) (a ⬝ (x₀ +ᵗ g ⬝ x₀)) k)
    · pexact hanti
    · pexact hX'
  -- the descent: j drops fit under a 0
  phave hQ : Formula.all Ty.nat (Formula.ex Ty.nat                       -- j = x₀, m = x₁
      (le_R (Term.add_R ⬝ (a ⬝ x₁)
               ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
            (a ⬝ Term.zero)))
  · pinduction
    · -- j = 0 : m := 0, `a 0 +ℝ q_0 ≤ℝ a 0 +ℝ 0ℝ =ℝ a 0`
      rmnorm
      pexists Term.zero
      rmnorm
      papply (le_R_trans_core
        (Term.add_R ⬝ (a ⬝ Term.zero)
          ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ Term.zero) ⬝ (Term.pow2neg_Q ⬝ (S k))))
        (Term.add_R ⬝ (a ⬝ Term.zero) ⬝ Term.zero_R)
        (a ⬝ Term.zero))
      psplit
      · papply (le_R_add_mono_l_core (a ⬝ Term.zero)
          (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ Term.zero) ⬝ (Term.pow2neg_Q ⬝ (S k))))
          Term.zero_R)
        pthm (budget_zero_R k)
      · pthm (leR_of_eq (add_zero_R_core (a ⬝ Term.zero)))
    · -- j → j+1 : m ↦ m + g m
      pforall                   -- j = x₀
      pintro ih
      rmnorm
      pobtain ih with him       -- m = x₁
      try rmnorm
      pexists (x₁ +ᵗ g ⬝ x₁)
      rmnorm
      pinst hdrop x₁ with hd
      rmnorm
      -- a(m+gm) + q_{j+1} ≤ a(m+gm) + (q_j + ε) ≤ (a(m+gm) + ε) + q_j ≤ a m + q_j ≤ a 0
      papply (le_R_trans_core
        (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
          ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (S x₀)) ⬝ (Term.pow2neg_Q ⬝ (S k))))
        (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
          ⬝ (Term.add_R
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
              ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
        (a ⬝ Term.zero))
      psplit
      · papply (le_R_add_mono_l_core (a ⬝ (x₁ +ᵗ g ⬝ x₁))
          (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (S x₀)) ⬝ (Term.pow2neg_Q ⬝ (S k))))
          (Term.add_R
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
              ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
        pthm (budget_succ_R x₀ k)
      · papply (le_R_trans_core
          (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
            ⬝ (Term.add_R
                ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
                ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
          (Term.add_R
            ⬝ (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
            ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
          (a ⬝ Term.zero))
        psplit
        · -- x + (q + ε) ≤ x + (ε + q) =ℝ (x + ε) + q
          papply (le_R_trans_core
            (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
              ⬝ (Term.add_R
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k))))
            (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
              ⬝ (Term.add_R
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k))
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            (Term.add_R
              ⬝ (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
          psplit
          · papply (le_R_add_mono_l_core (a ⬝ (x₁ +ᵗ g ⬝ x₁))
              (Term.add_R
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              (Term.add_R
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k))
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            papply (le_R_of_eq_R_core
              (Term.add_R
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              (Term.add_R
                  ⬝ const_R (Term.pow2neg_Q ⬝ (S k))
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            pthm (add_comm_R_core
              (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
              (const_R (Term.pow2neg_Q ⬝ (S k))))
          · papply (le_R_of_eq_R_core
              (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
                ⬝ (Term.add_R
                    ⬝ const_R (Term.pow2neg_Q ⬝ (S k))
                    ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
              (Term.add_R
                ⬝ (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
                ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            papply (eq_R_sym_core
              (Term.add_R
                ⬝ (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
                ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
              (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁))
                ⬝ (Term.add_R
                    ⬝ const_R (Term.pow2neg_Q ⬝ (S k))
                    ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))))
            pthm (add_assoc_R_core (a ⬝ (x₁ +ᵗ g ⬝ x₁))
              (const_R (Term.pow2neg_Q ⬝ (S k)))
              (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
        · papply (le_R_trans_core
            (Term.add_R
              ⬝ (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
            (Term.add_R ⬝ (a ⬝ x₁)
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k))))
            (a ⬝ Term.zero))
          psplit
          · papply (le_R_add_mono_r_core
              (Term.add_R ⬝ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
              (a ⬝ x₁)
              (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ x₀) ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            pexact hd
          · pexact him
  -- 2^{k+1} drops, then one more, do not fit under a 0 ≤ 1
  pinst hQ (Term.exp2 ⬝ (S k)) with hQ1
  rmnorm
  pobtain hQ1 with hm           -- m = x₀
  try rmnorm
  pinst hdrop x₀ with hd
  rmnorm
  -- `0 ≤ a(m + g m)` and `a 0 ≤ 1`, from the premise
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
  phave hb1 : le_R (a ⬝ Term.zero) Term.one_R
  · papply (le_R_of_le_R_pu (a ⬝ Term.zero) Term.one_R)
    pforall                     -- u = x₁
    rmnorm
    pinst H x₁ with Hu
    rmnorm
    pinst Hu Term.zero with Hn
    rmnorm
    pdestruct Hn with H12 H3
    pexact H3
  -- ε ≤ 0 + ε ≤ 0, the latter by cancelling q_N from
  -- (0 + ε) + q_N ≤ (a(m+gm) + ε) + q_N ≤ a m + q_N ≤ a 0 ≤ 1 ≤ q_N ≤ 0 + q_N
  phave hε0 : le_R (const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R
  · papply (le_R_trans_core (const_R (Term.pow2neg_Q ⬝ (S k)))
      (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R)
    psplit
    · pthm (le_R_zero_add (const_R (Term.pow2neg_Q ⬝ (S k))))
    · papply (le_R_add_cancel_r_core
        (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k))) Term.zero_R
        (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
          ⬝ (Term.pow2neg_Q ⬝ (S k)))))
      papply (le_R_trans_core
        (Term.add_R ⬝ (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
          ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
              ⬝ (Term.pow2neg_Q ⬝ (S k))))
        (Term.add_R ⬝ (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
          ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
              ⬝ (Term.pow2neg_Q ⬝ (S k))))
        (Term.add_R ⬝ Term.zero_R
          ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
              ⬝ (Term.pow2neg_Q ⬝ (S k)))))
      psplit
      · papply (le_R_add_mono_r_core
          (Term.add_R ⬝ Term.zero_R ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
          (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
          (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
              ⬝ (Term.pow2neg_Q ⬝ (S k)))))
        papply (le_R_add_mono_r_core Term.zero_R (a ⬝ (x₀ +ᵗ g ⬝ x₀))
          (const_R (Term.pow2neg_Q ⬝ (S k))))
        pexact h0
      · papply (le_R_trans_core
          (Term.add_R ⬝ (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
            ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                ⬝ (Term.pow2neg_Q ⬝ (S k))))
          (Term.add_R ⬝ (a ⬝ x₀)
            ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                ⬝ (Term.pow2neg_Q ⬝ (S k))))
          (Term.add_R ⬝ Term.zero_R
            ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                ⬝ (Term.pow2neg_Q ⬝ (S k)))))
        psplit
        · papply (le_R_add_mono_r_core
            (Term.add_R ⬝ (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ⬝ const_R (Term.pow2neg_Q ⬝ (S k)))
            (a ⬝ x₀)
            (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                ⬝ (Term.pow2neg_Q ⬝ (S k)))))
          pexact hd
        · papply (le_R_trans_core
            (Term.add_R ⬝ (a ⬝ x₀)
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                  ⬝ (Term.pow2neg_Q ⬝ (S k))))
            (a ⬝ Term.zero)
            (Term.add_R ⬝ Term.zero_R
              ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                  ⬝ (Term.pow2neg_Q ⬝ (S k)))))
          psplit
          · pexact hm
          · papply (le_R_trans_core (a ⬝ Term.zero) Term.one_R
              (Term.add_R ⬝ Term.zero_R
                ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                    ⬝ (Term.pow2neg_Q ⬝ (S k)))))
            psplit
            · pexact hb1
            · papply (le_R_trans_core Term.one_R
                (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                    ⬝ (Term.pow2neg_Q ⬝ (S k))))
                (Term.add_R ⬝ Term.zero_R
                  ⬝ const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                      ⬝ (Term.pow2neg_Q ⬝ (S k)))))
              psplit
              · pthm (one_R_le_budget k)
              · pthm (le_R_zero_add
                  (const_R (Term.mul_Q ⬝ (Term.encode_nat_Q ⬝ (Term.exp2 ⬝ (S k)))
                      ⬝ (Term.pow2neg_Q ⬝ (S k)))))
  papply hε0
  pthm (zero_lt_pow2neg_R (S k))

/-- **ℝ-MCT, proof P1ℝ.** The lazy derivation of `RealMCT.rmStatement`; needs Markov's
principle (`hmk`) and nothing else classical. Same statement, same encoding, same shared
lemmas as `real_mct_p2`; a different tree. -/
def real_mct_p1 (hmk : al.markov = true) :
    Derivable F al Premises (Γ := []) RealMCT.rmStatement := by
  pmode
  pforall
  pthm (real_mct_lazy_body hmk (Term.fst x₀) (Term.fst (Term.snd x₀)) (Term.snd (Term.snd x₀)))

section Extraction

variable {X : ι → Type} {si : SpaceInterp X F}

/-- **The bound for P1ℝ**: `rmBound` at `real_mct_p1`, exactly as `real_mct_bound_p2`.
Named and type-checked, not evaluated. -/
def real_mct_bound_p1 (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am) :=
  RealMCT.rmBound eqxi spremise cm (real_mct_p1 (al := Allowed.extended) rfl)

end Extraction

#print axioms real_mct_lazy_body
#print axioms real_mct_p1
#print axioms real_mct_bound_p1

end ProofMode
end Metatheorems
