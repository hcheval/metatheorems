/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MCTStatement
import Metatheorems.ProofMode.Arith

/-!
# Rung 7 — ℕ-MCT, the dichotomy proof (p₂)

`HANDOFF.md` A2. The statement is `MCTStatement.lean`'s `mctStatement`; what is built here is
the derivation of it, as a script.

## The proof

A bounded nonincreasing `a : ℕ → ℕ` has a flat window: `∃n, a n = a (n + g n)`. Classically
one takes the infimum; here the budget does the work. `a` takes values in ℕ and is bounded by
`K`, so it can strictly decrease at most `K` times. Formally, by induction on `k`:

    A(k)  ≡  (∀u B₀(u))  →  ∀m (a m ≤ k → ∃n (a n = a (n + g n)))

At `k = 0` boundedness pins `a m = 0`, and antitonicity pins `a (m + g m) = 0` as well, so
`m` is itself a flat point. At `k+1`, either the window at `m` is already flat — take `n := m`
— or it is not, and then `a (m + g m) < a m ≤ k+1`, so `a (m + g m) ≤ k` and the induction
hypothesis applies at `m + g m`. The statement follows by instantiating `A` at `k := K` and
`m := 0`.

Nothing here is classical beyond `qf_lem`, which is derivable in the base system: the
dichotomy is a decidable comparison of two natural numbers, not an appeal to LEM. That is the
whole point of p₂ — it goes through `general_metatheorem` at `Allowed.extended` with no
translation step, and its derivation tree contains no node where `g`-iteration could be
manufactured.

## What it is built from

Rungs 5, 6a and 6b, exactly as `HANDOFF.md` §3 A0 predicted: `antitone_chain` supplies
`a (m + i) ≤ a m`, and `strict_drop` turns "`a (m + g m) ≤ a m` and they differ" into
"`a (m + g m) ≤ k`". The marginal cost of the derivation is the skeleton only.
-/

namespace Metatheorems
namespace ProofMode

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **The budget descent.** `∀k ((∀u B₀ u) → ∀m (a m ≤ k → ∃n (a n = a (n + g n))))`.

`a`, `g` and `K` are separate parameters here; the fusion into the single functional `h` that
`mctStatement` quantifies over happens only at the end, in `mct_p2`. -/
def mct_descent 
    (a g : Term F Γ (Ty.nat →ₜ Ty.nat)) (K : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat                                        -- k = x₀
        (Formula.all Ty.nat                                      -- u = x₁
            ((a ⬝ S x₁ ∸ᵗ a ⬝ x₁ =₀ Term.zero) ∧ᶠ
             (a ⬝ x₁ ∸ᵗ K =₀ Term.zero))
          →ᶠ
          Formula.all Ty.nat                                     -- m = x₁
            ((a ⬝ x₁ ∸ᵗ x₀ =₀ Term.zero) →ᶠ
              Formula.ex Ty.nat                                  -- n = x₂
                (a ⬝ x₂ =₀ a ⬝ (x₂ +ᵗ g ⬝ x₂))))) := by
  pmode
  pinduction
  · -- k = 0 : `a m ≤ 0` forces `a m = 0`, and antitonicity forces `a (m + g m) = 0` too
    anorm
    pintro H
    pforall
    pintro hm
    pexists x₀
    prw (monus_zero (a ⬝ x₀)) in hm with hm0
    phave hstep : Formula.all Ty.nat (a ⬝ S x₁ ∸ᵗ a ⬝ x₁ =₀ Term.zero)
    · pforall
      pspecialize H with Hu
      anorm_ren
      pand_left
      pexact Hu
    pfrom ac := antitone_chain a
    pinst ac (g ⬝ x₀) with ac1
    anorm
    pinst ac1 x₀ with ac2
    anorm
    papply ac2 in hstep with hanti
    prwby hm0 in hanti with hanti'
    prw (monus_zero (a ⬝ (x₀ +ᵗ g ⬝ x₀))) in hanti' with hz
    ptrans Term.zero
    · pexact hm0
    · psym
      pexact hz
  · pforall
    pintro ih
    anorm
    pintro H
    pforall
    pintro hm
    -- one-step antitonicity, projected out of the premise
    phave hstep : Formula.all Ty.nat (a ⬝ S x₂ ∸ᵗ a ⬝ x₂ =₀ Term.zero)
    · pforall
      pspecialize H with Hu
      anorm_ren
      pand_left
      pexact Hu
    pfrom ac := antitone_chain a
    pinst ac (g ⬝ x₁) with ac1
    anorm
    pinst ac1 x₁ with ac2
    anorm
    papply ac2 in hstep with hanti
    -- is the window at m already flat?
    phave hlem :
      (a ⬝ x₁ =₀ a ⬝ (x₁ +ᵗ g ⬝ x₁)) ∨ᶠ ¬ᶠ(a ⬝ x₁ =₀ a ⬝ (x₁ +ᵗ g ⬝ x₁))
    · pthm (qf_lem rfl)
    pcases hlem with heq | hne
    · -- flat: m is the witness
      pexists x₁
      anorm
      pexact heq
    · -- not flat: the budget drops, and the induction hypothesis applies at m + g m
      pfrom sd := strict_drop
      pinst sd x₀ with sd1
      anorm
      pinst sd1 (a ⬝ (x₁ +ᵗ g ⬝ x₁)) with sd2
      anorm
      pinst sd2 (a ⬝ x₁) with sd3
      anorm
      papply sd3 in hm with sd4
      papply sd4 in hanti with sd5
      papply sd5 in hne with hle
      papply ih in H with ih1
      pinst ih1 (x₁ +ᵗ g ⬝ x₁) with ih2
      anorm
      papply ih2 in hle with hex
      pexact hex

/-- **The body of the statement**, over separate `a`, `g`, `K`: `(∀u B₀ u) → ∃n (a n = a (n + g n))`.

The descent at `k := K` and `m := 0`; the side condition `a 0 ≤ K` is the premise's second
conjunct at `u := 0`. -/
def mct_body 
    (a g : Term F Γ (Ty.nat →ₜ Ty.nat)) (K : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat
          ((a ⬝ S x₀ ∸ᵗ a ⬝ x₀ =₀ Term.zero) ∧ᶠ (a ⬝ x₀ ∸ᵗ K =₀ Term.zero))
        →ᶠ Formula.ex Ty.nat (a ⬝ x₀ =₀ a ⬝ (x₀ +ᵗ g ⬝ x₀))) := by
  pmode
  pintro H
  pfrom d := mct_descent a g K
  pinst d K with d1
  anorm
  papply d1 in H with d2
  pinst d2 Term.zero with d3
  anorm
  papply d3
  pinst H Term.zero with H0
  anorm
  pand_right
  pexact H0

/-- **Rung 7 — ℕ-MCT, proof p₂.** The dichotomy derivation of `mctStatement`.

`a`, `g` and `K` are the three components of the single quantified functional `h`, exactly as
`MCTStatement.lean` encodes them: `a := h 0`, `g := h 1`, `K := h 2 0`. Fusing them into one
parameter is what lets a single majorant cover all three; the proof above never needed to know
that, which is why it was done over three separate parameters and specialised only here. -/
def mct_p2 :
    Derivable F al Premises (Γ := []) mctStatement := by
  pmode
  pforall
  pthm (mct_body (x₀ ⬝ (Term.ofNat 0)) (x₀ ⬝ (Term.ofNat 1))
          ((x₀ ⬝ (Term.ofNat 2)) ⬝ (Term.ofNat 0)))

/-! ## It goes through the metatheorem

`MCTStatement.lean` checked that the *statement* fits `general_metatheorem` and that the
extraction/bounding split composes for it, both with the derivation left as a hypothesis.
That hypothesis is now discharged. -/

section Extraction

variable {X : ι → Type}

/-- **A4, first half.** The two functionals p₂ yields: `U` says where to test the premise,
`V` is the witness. Both compute — nothing here is `noncomputable`. -/
def mct_extract_p2 (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env) :=
  mctExtract si eqxi premise_realizer (mct_p2 (al := Allowed.extended))

/-- **A4, second half.** The bound, from that extraction plus majorants for `U` and `V`. -/
theorem mct_bound_p2 (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    (mj : MajorizabilityRel si)
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (U_star V_star : Ty.interpret X (mctTy ι →ₜ Ty.nat).hat)
    (hU : mj.maj (mctTy ι →ₜ Ty.nat) U_star
      (mct_extract_p2 si eqxi premise_realizer).val.1)
    (hV : mj.maj (mctTy ι →ₜ Ty.nat) V_star
      (mct_extract_p2 si eqxi premise_realizer).val.2) :
    ∃ Φ : Ty.interpret X (mctTy ι).hat → Nat,
      ∀ (x : Ty.interpret X (mctTy ι)) (x_star : Ty.interpret X (mctTy ι).hat),
        mj.maj (mctTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si mctB₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si mctC₀ (v, (x, ())) :=
  mct_bound si eqxi mj premise_realizer (mct_p2 (al := Allowed.extended))
    U_star V_star hU hV

end Extraction

#print axioms mct_p2

end ProofMode
end Metatheorems
