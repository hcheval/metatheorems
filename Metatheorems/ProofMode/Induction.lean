/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Packing

/-!
# Induction in a hypothesis context

The kernel's `induction` is a *rule*: it concludes `∀n A(n)` from `A(0)` and
`∀n (A(n) → A(n+1))`, with no side formula. A proof mode needs it with a hypothesis context
present, and that is not a matter of bookkeeping — the hypotheses have to be carried through
the induction, so the formula actually inducted on is

    A' := Δ↑ →ᶠ A

one hypothesis at a time. This file does that peeling, and pays for it with the two
substitution lemmas that say a weakening survives a substitution for the variable it
introduced.

Those two lemmas are the entire cost of the general rule, and they are the reason this is a
separate file from `Packing.lean`: everything there is pure combinator plumbing, whereas
this needs facts about de Bruijn substitution.
-/

namespace Metatheorems

namespace Formula

variable {ι : Type} {F : ι → Ty ι}

/-- Substituting for the variable a weakening just introduced undoes the weakening. -/
theorem subst0_weakenBy {Γ : Ctx ι} {ρ : Ty ι} (B : Formula F Γ) (t : Term F Γ ρ) :
    (Formula.weakenBy ρ B).subst0 t = B :=
  Formula.substF_renameF_id Term.Renaming.shift (Term.subst0_map t) (fun _ => rfl) B

/-- The in-place version: a weakened formula does not mention variable 0, so substituting
for it changes nothing. -/
theorem substVar0_weakenBy {Γ : Ctx ι} {ρ : Ty ι} (B : Formula F Γ) (t : Term F (ρ :: Γ) ρ) :
    Formula.substVar0 (Formula.weakenBy ρ B) t = Formula.weakenBy ρ B := by
  show Formula.substF (Term.substVar0_map t) (Formula.renameF Term.Renaming.shift B)
      = Formula.renameF Term.Renaming.shift B
  rw [Formula.renameF_substF, Formula.renameF_eq_substF]
  rfl

/-- Weakening *under* a binder, then substituting the bound variable back, is the identity.

This is what you need to re-introduce an `∃` at a witness you have just obtained: after
`seq_exE` the goal is `(∃x A)↑` in the extended context, and supplying `x` itself for the
witness lands on this. -/
theorem subst0_weakenUnder {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) :
    Formula.subst0 (Formula.renameF (Term.Renaming.ext (Term.Renaming.shift (σ := ρ))) A)
      (Term.var .vz) = A :=
  Formula.substF_renameF_id _ _ (fun v => by cases v <;> rfl) A

end Formula

namespace ProofMode

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

open Formula

-- ============================================================================
-- Kernel combinators the peeling needs
-- ============================================================================

/-- Weaken the consequent of an implication. -/
def imp_mono_right {Γ : Ctx ι} {W Y Z : Formula F Γ}
    (h : Derivable F EqX a Premises (Y →ᶠ Z)) :
    Derivable F EqX a Premises ((W →ᶠ Y) →ᶠ (W →ᶠ Z)) :=
  .exportation (.syllogism (.importation mp_form) h)

/-- `∀` is monotone. -/
def forall_mono {Γ : Ctx ι} {ρ : Ty ι} {X Y : Formula F (ρ :: Γ)}
    (h : Derivable F EqX a Premises (X →ᶠ Y)) :
    Derivable F EqX a Premises (Formula.all ρ X →ᶠ Formula.all ρ Y) :=
  .forall_rule (.syllogism (forall_ax_vz (ρ := ρ) (A := X)) h)

/-- Push a hypothesis under a `∀` it does not mention. Converse of `forall_imp_pull`. -/
def forall_imp_push {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {X : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises
      ((B →ᶠ Formula.all ρ X) →ᶠ Formula.all ρ (Formula.weakenBy ρ B →ᶠ X)) :=
  .forall_rule (imp_mono_right (forall_ax_vz (ρ := ρ) (A := X)))

/-- Transport a sequent along an equality of goals. -/
def seq_cast {Δ : HCtx F Γ} {X Y : Formula F Γ} (h : X = Y)
    (d : Seq F EqX a Premises Δ X) : Seq F EqX a Premises Δ Y :=
  h ▸ d

-- ============================================================================
-- Induction
-- ============================================================================

/-- The successor of the variable a `∀ n` binder just introduced. -/
abbrev succVar0 {Γ : Ctx ι} : Term F (Ty.nat :: Γ) Ty.nat :=
  Term.app Term.succ (.var .vz)

/-- **Induction with a hypothesis context.**

At each hypothesis the formula inducted on gains that hypothesis as an antecedent, which is
the usual "strengthen the induction hypothesis by the context" step written out. The user of
the tactic never sees it: `Δ` and the names come back unchanged. -/
def seq_induction : {Δ : HCtx F Γ} → {A : Formula F (Ty.nat :: Γ)} →
    Seq F EqX a Premises Δ (A.subst0 Term.zero) →
    Seq F EqX a Premises Δ (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0)) →
    Seq F EqX a Premises Δ (Formula.all Ty.nat A)
  | [],      _, base, step => .induction base step
  | A₀ :: Δ, A, base, step =>
      -- The formula actually inducted on.
      let A' : Formula F (Ty.nat :: Γ) := Formula.weakenBy Ty.nat A₀ →ᶠ A
      let base' : Seq F EqX a Premises Δ (A'.subst0 Term.zero) :=
        seq_cast (congrArg (· →ᶠ A.subst0 Term.zero)
          (Formula.subst0_weakenBy A₀ Term.zero).symm) base
      let step' : Seq F EqX a Premises Δ
          (Formula.all Ty.nat (A' →ᶠ Formula.substVar0 A' succVar0)) :=
        seq_cast
          (congrArg (Formula.all Ty.nat)
            (congrArg (fun Z => A' →ᶠ (Z →ᶠ Formula.substVar0 A succVar0))
              (Formula.substVar0_weakenBy A₀ succVar0).symm))
          (seq_mono (Δ := Δ) (forall_mono S_comb)
            (seq_mono (Δ := Δ) forall_imp_push step))
      seq_mono (Δ := Δ) forall_imp_pull
        (seq_induction (Δ := Δ) (A := A') base' step')

end ProofMode
end Metatheorems
