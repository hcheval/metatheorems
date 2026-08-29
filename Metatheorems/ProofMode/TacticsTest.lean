/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Tactics

namespace Metatheorems
namespace ProofMode

/-!
# Acceptance test for the tactic layer

The same theorems `PackingTest.lean` proves by hand, proved instead by script. Read the two
files side by side: that is the whole case for the proof mode.

Nothing here mentions `Derivable`, `pack`, `HVar`, or a de Bruijn index.
-/

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B : Formula F Γ}

open Formula

/-! ## Propositional -/

example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  psplit
  · pexact ha
  · pexact hb

example : SeqD [] F EqX a Premises [] ((A ∧ᶠ B) →ᶠ (B ∧ᶠ A)) := by
  pintro h
  pdestruct h with ha hb
  psplit
  · pexact hb
  · pexact ha

example : SeqD [] F EqX a Premises [] ((A ∨ᶠ B) →ᶠ (B ∨ᶠ A)) := by
  pintro h
  pcases h with hl | hr
  · pright
    pexact hl
  · pleft
    pexact hr

example : SeqD [] F EqX a Premises [] (⊥ᶠ →ᶠ A) := by
  pintro h
  pexfalso
  pexact h

/-- A kernel theorem, used from inside a script. This is the escape hatch: everything the
kernel already proves stays available. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ A) := by
  pthm I_comb

/-! ## Quantifiers

These are the scripts where the hypothesis context weakens under the binder. Note that the
script does not mention the weakening at all — `pexact h` still finds `h`, because `pforall`
leaves the *names* alone. -/

section Quantifiers
variable {ρ : Ty ι} {P Q : Formula F (ρ :: Γ)}

example : SeqD [] F EqX a Premises [] (Formula.all ρ P →ᶠ Formula.all ρ P) := by
  pintro h
  pforall
  pspecialize
  pexact h

example : SeqD [] F EqX a Premises []
    (Formula.all ρ (P ∧ᶠ Q) →ᶠ Formula.all ρ P ∧ᶠ Formula.all ρ Q) := by
  pintro h
  psplit
  · pforall
    pand_left
    pspecialize
    pexact h
  · pforall
    pand_right
    pspecialize
    pexact h

example : SeqD [] F EqX a Premises [] (Formula.ex ρ P →ᶠ Formula.ex ρ P) := by
  pintro h
  pobtain h with x
  pexact h

example (t : Term F Γ ρ) (h : SeqD [] F EqX a Premises [] (P.subst0 t)) :
    SeqD [] F EqX a Premises [] (Formula.ex ρ P) := by
  pexists t
  exact h

end Quantifiers

/-! ## Forward reasoning -/

example : SeqD [] F EqX a Premises [] (A →ᶠ (A ∧ᶠ A)) := by
  pintro h
  phave k : A
  · pexact h
  · psplit
    · pexact k
    · pexact k

example : SeqD [] F EqX a Premises [] ((A →ᶠ B) →ᶠ A →ᶠ B) := by
  pintro himp ha
  papply himp
  pexact ha

example {ρ : Ty ι} {P : Formula F (ρ :: Γ)} (t : Term F Γ ρ) :
    SeqD ["h"] F EqX a Premises [Formula.all ρ P] (P.subst0 t) := by
  pinst h t as k
  pexact k

/-! ## Induction

The hypothesis context is carried through the induction by `Packing`'s peeling; the script
does not mention it. Both of these prove `∀n (n =₀ n)`, the second with a hypothesis in
scope so that the peeling actually runs. -/

example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.all Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pinduction
  · pthm .refl0
  · pforall
    pintro hn
    pthm .refl0

example {C : Formula F Γ} : SeqD ["c"] F EqX a Premises [C]
    (Formula.all Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pinduction
  · pthm .refl0
  · pforall
    pintro hn
    pthm .refl0

/-! ## Principles of the extended system

`pside` discharges the `allowed` flags and the `isQF` / `isVFree` checks by computation. -/

section Extended
variable {Prem : PremiseSet F}

/-- Markov: the `∃` is proved by contradiction, then the contradiction is produced by
actually supplying the witness. -/
example : SeqD [] F EqX Allowed.extended Prem (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) Term.zero)) := by
  pby_contra h
  papply h
  pexists Term.zero
  pthm .refl0

/-- QF-AC, forwards: the choice function appears as a new hypothesis. -/
example : SeqD ["h"] F EqX Allowed.extended Prem (Γ := Γ)
    [Formula.all Ty.nat (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz)))]
    (Formula.ex (Ty.nat →ₜ Ty.nat) (Formula.all Ty.nat
      (Formula.substF Formula.acSubst (Formula.eq0 (Term.var .vz) (Term.var .vz))))) := by
  pqfac h as k
  pexact k

end Extended

/-! ## Error reporting

`pexact` is the only tactic that can fail on a *name*, and it says what names are in scope.
-/

/-- error: pexact: no hypothesis named `nope` (have: [h]) -/
#guard_msgs in
example : SeqD [] F EqX a Premises [] (A →ᶠ A) := by
  pintro h
  pexact nope

end ProofMode
end Metatheorems
