/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Tactics

namespace Metatheorems
namespace ProofMode

/-!
# Worked examples

Ordinary logic, written as scripts. Nothing here mentions `Derivable`, `pack`, a de Bruijn
index, or a substitution lemma — which is the whole claim.

Everything below is in the *base* system: no LEM, no Markov, no choice. `a` is an arbitrary
`Allowed`, so these are intuitionistic derivations valid in every system we have.
-/

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B C : Formula F Γ}

open Formula

/-! ## Propositional -/

/-- Currying. -/
example : SeqD [] F EqX a Premises [] ((A ∧ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C)) := by
  pintro h ha hb
  papply h
  psplit
  · pexact ha
  · pexact hb

/-- Uncurrying, the other way. -/
example : SeqD [] F EqX a Premises [] ((A →ᶠ B →ᶠ C) →ᶠ (A ∧ᶠ B →ᶠ C)) := by
  pintro h hab
  pdestruct hab with ha hb
  papply h        -- two antecedents, two subgoals
  · pexact ha
  · pexact hb

/-- Contraposition. Note `¬ᶠA` is `A →ᶠ ⊥ᶠ`, so `pintro` and `papply` handle it with no
special support. -/
example : SeqD [] F EqX a Premises [] ((A →ᶠ B) →ᶠ (¬ᶠB →ᶠ ¬ᶠA)) := by
  pintro hab hnb ha
  papply hnb
  papply hab
  pexact ha

/-- Disjunctive syllogism. -/
example : SeqD [] F EqX a Premises [] ((A ∨ᶠ B) →ᶠ ¬ᶠA →ᶠ B) := by
  pintro hab hna
  pcases hab with hl | hr
  · pexfalso
    papply hna
    pexact hl
  · pexact hr

/-- Distribution of `∧` over `∨`, the direction that needs the case split. -/
example : SeqD [] F EqX a Premises [] (A ∧ᶠ (B ∨ᶠ C) →ᶠ (A ∧ᶠ B) ∨ᶠ (A ∧ᶠ C)) := by
  pintro h
  pdestruct h with ha hbc
  pcases hbc with hb | hc
  · pleft
    psplit
    · pexact ha
    · pexact hb
  · pright
    psplit
    · pexact ha
    · pexact hc

/-- Double negation introduction. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ ¬ᶠ¬ᶠA) := by
  pintro ha hna
  papply hna
  pexact ha

/-! ## Quantifiers -/

section Quantifiers
variable {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}

/-- `∀` distributes over `→`. This is the one that made the missing move obvious: after
`pforall` the hypotheses are weakened, so `himp` is *used* by `pspecialize … with …`. -/
example : SeqD [] F EqX a Premises []
    (Formula.all ρ (P →ᶠ Q) →ᶠ Formula.all ρ P →ᶠ Formula.all ρ Q) := by
  pintro himp hp
  pforall
  pspecialize himp with hpq
  pspecialize hp with hp'
  papply hpq
  pexact hp'

/-- `∀` distributes over `∧`, both conjuncts. -/
example : SeqD [] F EqX a Premises []
    (Formula.all ρ (P ∧ᶠ Q) →ᶠ Formula.all ρ P ∧ᶠ Formula.all ρ Q) := by
  pintro h
  psplit
  · pforall
    pspecialize h with hpq
    pdestruct hpq with hp _hq
    pexact hp
  · pforall
    pspecialize h with hpq
    pdestruct hpq with _hp hq
    pexact hq

/-- `∃` out of a conjunction. The witness obtained by `pobtain` is handed straight back, and
`pnorm` clears the weakening/substitution bookkeeping that produces. -/
example : SeqD [] F EqX a Premises []
    (Formula.ex ρ (P ∧ᶠ Q) →ᶠ Formula.ex ρ P) := by
  pintro h
  pobtain h with x
  pdestruct x with hp _hq
  pexists (Term.var .vz)
  pnorm
  pexact hp

/-- `∀` implies `∃` is *not* provable — the object logic has no non-emptiness assumption —
but `∀x P → P[t]` is, for any term you can write. -/
example (t : Term F Γ ρ) : SeqD [] F EqX a Premises []
    (Formula.all ρ P →ᶠ P.subst0 t) := by
  pintro h
  pinst h t with k
  pexact k

end Quantifiers

/-! ## Arithmetic

`refl0` and the induction rule are kernel-level; everything around them is script. -/

/-- Reflexivity at every natural, by induction. Trivial mathematically — the point is that
the induction *rule* is usable from a script with hypotheses in scope. -/
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.all Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pinduction
  · pthm .refl0
  · pforall
    pintro _ih
    pthm .refl0

/-- Transitivity of `=₀` as a script: the kernel gives it in `∧`-form, the script turns that
into the curried form. -/
example {s t u : Term F Γ Ty.nat} : SeqD [] F EqX a Premises []
    (Formula.eq0 s t →ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u) := by
  pintro hst htu
  pfrom htrans := Derivable.trans0 (s := s) (t := t) (u := u)
  papply htrans
  psplit
  · pexact hst
  · pexact htu

end ProofMode
end Metatheorems
