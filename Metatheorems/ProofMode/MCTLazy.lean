/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.MCT

/-!
# ℕ-MCT, the lazy proof (p₁)

The *same statement* as `ProofMode/MCT.lean`, proved the way one actually
proves it on paper — and the point of the exercise is that the two derivations differ where it
matters.

## The proof

Suppose there is no flat window. Then at every `m` the value drops strictly: `a (m + g m) < a m`,
since `a (m + g m) ≤ a m` by antitonicity and the two are not equal. Feeding that back into
itself gives, for every `k`, some `m` with `a m + k ≤ a 0`. Take `k := K + 1`: with `a 0 ≤ K`
that forces `K + 1 ≤ K`, and `S K ∸ K = 1`, so `1 = 0`.

## Where it differs from p₂

The descent `∀k ∃m (a m + k ≤ a 0)` is an induction whose *witness* is built by applying
`m ↦ m + g m` once per step. That is where `g`-iteration is manufactured: the extracted
witness functional for this induction node is an iterate. p₂'s induction carries no
existential in its conclusion — its `∃` is discharged inside each branch — so its tree has no
such node. `A5`'s tracer is meant to make exactly this visible.

## The translation (D-1)

The reductio is applied **only** to the headline `∃n (a n =₀ a (n + g n))`, whose matrix is
quantifier-free and ∨-free. So its classical content is exactly `¬¬∃n(qf) → ∃n(qf)`, which is
Markov — `pby_contra`, which refuses any other shape. Nothing else in the proof is classical;
`Allowed.extended` has `lem := false`, and this derivation lives there.

The hand-translation is D-1's shortcut, and `pby_contra`'s refusal message is the discipline
made mechanical: a proof that needs `by_contra` anywhere else has not been translated.
-/

namespace Metatheorems
namespace ProofMode

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **The body of the statement**, proved lazily: `(∀u B₀ u) → ∃n (a n = a (n + g n))`.

`hmk` is what makes the reductio legal — `pby_contra` is the Markov rule and says so. -/
def mct_lazy_body (hmk : al.markov = true)
    (a g : Term F Γ (Ty.nat →ₜ Ty.nat)) (K : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat
          ((a ⬝ S x₀ ∸ᵗ a ⬝ x₀ =₀ Term.zero) ∧ᶠ (a ⬝ x₀ ∸ᵗ K =₀ Term.zero))
        →ᶠ Formula.ex Ty.nat (a ⬝ x₀ =₀ a ⬝ (x₀ +ᵗ g ⬝ x₀))) := by
  pmode
  pintro H
  pby_contra N
  -- no flat window, so the value differs at every m …
  phave hne : Formula.all Ty.nat (¬ᶠ(a ⬝ x₀ =₀ a ⬝ (x₀ +ᵗ g ⬝ x₀)))
  · pforall
    pintro heq
    papply N
    pexists x₀
    anorm
    pexact heq
  -- … and since it never rises, it drops strictly
  phave hdrop :
    Formula.all Ty.nat (S (a ⬝ (x₀ +ᵗ g ⬝ x₀)) ∸ᵗ a ⬝ x₀ =₀ Term.zero)
  · pforall
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
    pspecialize hne with hne0
    pfrom sn := monus_succ_of_ne
    pinst sn (a ⬝ (x₀ +ᵗ g ⬝ x₀)) with sn1
    anorm
    pinst sn1 (a ⬝ x₀) with sn2
    anorm
    papply sn2 in hanti with sn3
    papply sn3 in hne0 with sd
    pexact sd
  -- the descent: k strict drops fit under a 0
  phave hQ :
    Formula.all Ty.nat (Formula.ex Ty.nat
      (((a ⬝ x₁) +ᵗ x₀) ∸ᵗ a ⬝ Term.zero =₀ Term.zero))
  · pinduction
    · anorm
      pexists Term.zero
      anorm
      prw (add_zero_r (a ⬝ Term.zero))
      pthm (monus_self (a ⬝ Term.zero))
    · pforall
      pintro ih
      anorm
      pobtain ih with him
      pexists (x₁ +ᵗ g ⬝ x₁)
      anorm
      pinst hdrop x₁ with hd
      anorm
      pfrom ama := add_monus_add
      pinst ama x₀ with ama1
      anorm
      pinst ama1 (S (a ⬝ (x₁ +ᵗ g ⬝ x₁))) with ama2
      anorm
      pinst ama2 (a ⬝ x₁) with ama3
      anorm
      prwby hd in ama3 with ama4
      pfrom mt := monus_trans
      pinst mt ((S (a ⬝ (x₁ +ᵗ g ⬝ x₁))) +ᵗ x₀) with mt1
      anorm
      pinst mt1 ((a ⬝ x₁) +ᵗ x₀) with mt2
      anorm
      pinst mt2 (a ⬝ Term.zero) with mt3
      anorm
      papply mt3 in ama4 with mt4
      papply mt4 in him with hfin
      prw (add_succ (a ⬝ (x₁ +ᵗ g ⬝ x₁)) x₀)
      prw (add_succ_l (a ⬝ (x₁ +ᵗ g ⬝ x₁)) x₀) in hfin with hfin'
      pexact hfin'
  -- K + 1 drops do not fit under a 0 ≤ K
  pinst hQ (S K) with hQ1
  anorm
  pobtain hQ1 with hm
  pinst H Term.zero with H0
  anorm
  pdestruct H0 with _hmono hb
  pfrom mt := monus_trans
  pinst mt ((a ⬝ x₀) +ᵗ S K) with mt1
  anorm
  pinst mt1 (a ⬝ Term.zero) with mt2
  anorm
  pinst mt2 K with mt3
  anorm
  papply mt3 in hm with mt4
  papply mt4 in hb with hle
  pfrom mas := monus_add_self_l
  pinst mas (a ⬝ x₀) with mas1
  anorm
  pinst mas1 (S K) with mas2
  anorm
  pinst mt (S K) with n1
  anorm
  pinst n1 ((a ⬝ x₀) +ᵗ S K) with n2
  anorm
  pinst n2 K with n3
  anorm
  papply n3 in mas2 with n4
  papply n4 in hle with hSK
  -- but S K ∸ K = 1
  pfrom sms := succ_monus_self
  pinst sms K with sms1
  anorm
  pfrom snz := Derivable.succ_ne_zero
  pinst snz Term.zero with snz1
  anorm
  papply snz1
  ptrans (S K ∸ᵗ K)
  · psym
    pexact sms1
  · pexact hSK

/-- **A3 — ℕ-MCT, proof p₁.** The lazy derivation of `mctStatement`.

Same statement, same encoding, same shared lemmas as `mct_p2`; a different tree. -/
def mct_p1 (hmk : al.markov = true) :
    Derivable F al Premises (Γ := []) mctStatement := by
  pmode
  pforall
  pthm (mct_lazy_body hmk (x₀ ⬝ (Term.ofNat 0)) (x₀ ⬝ (Term.ofNat 1))
          ((x₀ ⬝ (Term.ofNat 2)) ⬝ (Term.ofNat 0)))

/-! ## The other extraction

`mct_extract_p2` and this one are the two halves of A4: the same statement, the same
extraction, two derivations. What is *not* claimed here is that the extracted terms differ —
that is a computation, and it needs a concrete interpretation to run in. What is established
is that both derivations exist, are accepted at `Allowed.extended`, and feed the same
functional. -/

section Extraction

variable {X : ι → Type}

/-- **A4, p₁'s half.** The functionals the lazy derivation yields.

The result type is written out rather than inferred: inferring it means normalising the
Dialectica interpretation of the whole derivation, and this one is large enough that the
elaborator does not get there. -/
def mct_extract_p1 (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env) :
    { UV : (Ty.interpret X (mctTy ι) → Nat) × (Ty.interpret X (mctTy ι) → Nat) //
      ∀ x : Ty.interpret X (mctTy ι),
        Formula.interpret si mctB₀ (UV.1 x, (x, ())) →
        Formula.interpret si mctC₀ (UV.2 x, (x, ())) } :=
  mctExtract si eqxi premise_realizer (mct_p1 (al := Allowed.extended) rfl)

/-- The bound p₁ gives, **via the syntactic metatheorem**. See the note at `mct_bound_p2` for
why the `MajorizabilityRel` and the two majorant hypotheses are gone. -/
theorem mct_bound_p1 (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    (am : AbstractMajorizability si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B) :
    ∃ Φ : Ty.interpret X (mctTy ι).hat → Nat,
      ∀ (x : Ty.interpret X (mctTy ι)) (x_star : Ty.interpret X (mctTy ι).hat),
        am.toRel.maj (mctTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si mctB₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si mctC₀ (v, (x, ())) :=
  syntactic_general_metatheorem eqxi spremise am rfl rfl rfl rfl
    (mct_p1 (al := Allowed.extended) rfl)

end Extraction

#print axioms mct_p1

end ProofMode
end Metatheorems
