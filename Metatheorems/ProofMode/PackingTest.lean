/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Packing

namespace Metatheorems
namespace ProofMode

/-!
# Acceptance test for the packaging kit

Every proof here goes through kit lemmas only — no kernel constructor is applied directly,
which is the discipline the tactic layer will inherit.
-/

variable {ι κ : Type} {F : κ → Ty ι}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B C : Formula F Γ}

open Formula

/-! ## The handoff's smoke test -/

example : Seq F a Premises [A, B] (A ∧ᶠ B) :=
  seq_andI (seq_id .hz) (seq_id (.hs .hz))

/-! ## `intro` and `revert` really are the identity

This is the payoff of folding the context so the head is the innermost antecedent. -/

example : @seq_intro ι κ F a Premises Γ [B] A C = id := rfl
example : @seq_revert ι κ F a Premises Γ [B] A C = id := rfl

/-- …and they are mutually inverse, definitionally. -/
example (h : Seq F a Premises (A :: [B]) C) : seq_revert (seq_intro h) = h := rfl

/-! ## Propositional glue -/

/-- Commutativity of conjunction, written the way a tactic script would build it. -/
example : Seq F a Premises [] ((A ∧ᶠ B) →ᶠ (B ∧ᶠ A)) :=
  seq_intro (seq_andI (seq_andE₂ (seq_id .hz)) (seq_andE₁ (seq_id .hz)))

/-- Case analysis, and the two `∨`-introductions. -/
example : Seq F a Premises [] ((A ∨ᶠ B) →ᶠ (B ∨ᶠ A)) :=
  seq_intro (seq_orE (seq_id .hz) (seq_orI₂ (seq_id .hz)) (seq_orI₁ (seq_id .hz)))

/-- Cut, and hypothesis lookup at depth. -/
example (hA : Seq F a Premises [] A) :
    Seq F a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) :=
  seq_intro (seq_intro (seq_andI (seq_id (.hs .hz)) (seq_id .hz)))

/-- Exchange and contraction. -/
example (h : Seq F a Premises [A, B] C) : Seq F a Premises [B, A] C :=
  seq_exchange h

example (h : Seq F a Premises [A, A] C) : Seq F a Premises [A] C :=
  seq_contract h

/-- `⊥` eliminates to anything. -/
example : Seq F a Premises [⊥ᶠ] A :=
  seq_exfalso (seq_id .hz)

/-! ## Quantifiers

These are the ones where the hypothesis context has to weaken into `ρ :: Γ`, and where
off-by-one errors would live. -/

section Quantifiers
variable {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}

/-- `∀`-introduction with a *non-empty* context: the context weakens, and the eigenvariable
condition holds because nothing in `Δ.map (weakenBy ρ)` can mention variable 0. -/
example (h : Seq F a Premises [Formula.weakenBy ρ A] P) :
    Seq F a Premises [A] (Formula.all ρ P) :=
  seq_allI h

/-- `∀`-elimination at a term. -/
example (t : Term F Γ ρ) (h : Seq F a Premises [] (Formula.all ρ P)) :
    Seq F a Premises [] (P.subst0 t) :=
  seq_allE h t

/-- Instantiate then re-generalize. The hypothesis arrives weakened, so it is *used* via
`seq_allE_here`, not looked up. -/
example : Seq F a Premises [] (Formula.all ρ P →ᶠ Formula.all ρ P) :=
  seq_intro (seq_allI (seq_allE_here (seq_id .hz)))

/-- `∃`-introduction at a witness. -/
example (t : Term F Γ ρ) (h : Seq F a Premises [] (P.subst0 t)) :
    Seq F a Premises [] (Formula.ex ρ P) :=
  seq_exI t h

/-- `∃`-elimination: consume the witness and put it straight back. Exercises the
`Δ.map (weakenBy ρ)` bookkeeping in both `seq_exE` and `seq_id`. -/
example : Seq F a Premises [] (Formula.ex ρ P →ᶠ Formula.ex ρ P) :=
  seq_intro (seq_exE (seq_id .hz) (seq_id (.hs .hz)))

/-- `∀` distributes over `∧`, one direction — a proof that actually uses several moves
under a binder. -/
example : Seq F a Premises []
    (Formula.all ρ (P ∧ᶠ Q) →ᶠ Formula.all ρ P ∧ᶠ Formula.all ρ Q) :=
  seq_intro (seq_andI
    (seq_allI (seq_andE₁ (seq_allE_here (seq_id .hz))))
    (seq_allI (seq_andE₂ (seq_allE_here (seq_id .hz)))))

end Quantifiers

end ProofMode
end Metatheorems
