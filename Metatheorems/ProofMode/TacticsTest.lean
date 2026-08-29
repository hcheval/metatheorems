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

/-- `R_nat 0 (λx n. x) 0` — extensionally `0`, but computed by recursion. The witness the
surface-recursor ban exists to refuse.

A `macro`, not a `def`, so that it elaborates to the term the user would have typed. A `def`
would be a *constant* and the check would not look inside it — see `wrapped_iteration`
below, which records that limitation. -/
macro "iterating_zero" : term =>
  `(Term.app (Term.app (Term.app (Term.prec Ty.nat) Term.zero)
      (Term.lam (Term.lam (Term.var (.vs .vz))))) Term.zero)

/-- The same term behind a name. The surface check does not unfold constants — it must not,
since `Term.add` is also built from `Term.prec` — so this gets through. Recorded, not fixed:
the principled version is a whitelist of surface constants. -/
def wrapped_iteration : Term F Γ Ty.nat := iterating_zero

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
  pinst h t with k
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
  pqfac h with k
  pexact k

/-! ### The Markov shape check

`HANDOFF` D-4 asks that `by_contra` be the Markov rule *named as such*, and that it refuse
anything else with a message pointing at the translation discipline. Each way of getting it
wrong has its own message. Each goal below is separately provable, so the only message is
the refusal — the tactic declines to *start*, it does not leave a broken state. -/

-- Not an `∃` at all.
/--
error: pby_contra: the goal is not an ∃ — not a Markov shape.
Is this proof translated? (HANDOFF D-1: the classical content of a hand-translated proof is
exactly `¬¬∃n(qf) → ∃n(qf)`.)
-/
#guard_msgs in
example : SeqD [] F EqX Allowed.extended Prem (Γ := Γ) [] (A →ᶠ A) := by
  pby_contra h
  pthm I_comb

-- An `∃`, but the matrix has a quantifier in it.
/--
error: pby_contra: the matrix is not quantifier-free — not a Markov shape.
Is this proof translated?
-/
#guard_msgs in
example : SeqD [] F EqX Allowed.extended Prem (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.all Ty.nat
      (Formula.eq0 (Term.var (.vs .vz)) (Term.var (.vs .vz))))) := by
  pby_contra h
  pexists Term.zero
  pforall
  pthm .refl0

-- Quantifier-free, but with a `∨`: outside what our Dialectica interprets.
/--
error: pby_contra: the matrix contains ∨ — not a Markov shape.
Is this proof translated?
-/
#guard_msgs in
example : SeqD [] F EqX Allowed.extended Prem (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) Term.zero ∨ᶠ
      Formula.eq0 (Term.var .vz) Term.zero)) := by
  pby_contra h
  pexists Term.zero
  pleft
  pthm .refl0

-- The right shape, but Markov is not in the system.
/-- error: pby_contra: Markov is not available here — `allowed.markov` is not `true`. -/
#guard_msgs in
example : SeqD [] F EqX Allowed.base Prem (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) Term.zero)) := by
  pby_contra h
  pexists Term.zero
  pthm .refl0

end Extended

/-! ## `bound` v0 — the certificate checker

`pbound` is the headline `∃`-introduction. It takes the witness from the user and checks the
surface-recursor ban: iteration is what extraction is supposed to *produce*, so a
hand-written iterating witness would make the extraction vacuous.

Per HANDOFF D-2 the ban is on the *surface language*, so `pexists` and `pinst` carry it too;
`pexists!` is the named escape hatch. -/

/-- An honest witness passes. -/
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) Term.zero)) := by
  pbound Term.zero
  pthm .refl0

-- An iterating witness — `R_nat 0 (λx n. x) 0`, which is `0` but computed by recursion —
-- is rejected, with the reason.
/--
error: pbound: the term applies the primitive recursor directly.
Iteration is what extraction produces, so a hand-written iterating term makes the
extraction vacuous (HANDOFF D-2, surface-recursor ban). If this really is auxiliary, say so
explicitly with `pexists!`.
-/
#guard_msgs in
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pbound iterating_zero
  pthm .refl0

-- `pexists` carries the same ban — the surface language loses the recursor, not just the
-- headline position.
/--
error: pexists: the term applies the primitive recursor directly.
Iteration is what extraction produces, so a hand-written iterating term makes the
extraction vacuous (HANDOFF D-2, surface-recursor ban). If this really is auxiliary, say so
explicitly with `pexists!`.
-/
#guard_msgs in
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pexists iterating_zero
  pthm .refl0

/-- `pexists!` is the escape hatch: a bypass has to be written down. -/
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pexists! iterating_zero
  pthm .refl0

-- **R4 attempt C**: the smuggle that reaches the extracted term through an
-- *instantiation*, never touching an `∃`. Refused.
/--
error: pinst: the term applies the primitive recursor directly.
Iteration is what extraction produces, so a hand-written iterating term makes the
extraction vacuous (HANDOFF D-2, surface-recursor ban). If this really is auxiliary, say so
explicitly with `pexists!`.
-/
#guard_msgs in
example {P : Formula F (Ty.nat :: Γ)} :
    SeqD ["h"] F EqX a Premises [Formula.all Ty.nat P] (P.subst0 Term.zero) := by
  pinst h iterating_zero with k
  pinst h Term.zero with k'
  pexact k'

-- A route D-2's list does not name: the *formula* of a cut is user-written too, and its
-- terms reach the extracted content the same way an instantiation's do.
/--
error: phave: the formula applies the primitive recursor directly.
Iteration is what extraction produces, so writing it by hand makes the extraction
vacuous (HANDOFF D-2, surface-recursor ban).
-/
#guard_msgs in
example : SeqD [] F EqX a Premises (Γ := Γ) [] (A →ᶠ A) := by
  phave k : Formula.eq0 iterating_zero iterating_zero
  pthm I_comb

/-- **The recorded limitation.** The same iteration behind a `def` is accepted, because the
check must not unfold constants — `Term.add` is built from `Term.prec` too, and `x + y` is
not a smuggled bound. A whitelist of surface constants is the fix; a blacklist of one cannot
distinguish these. -/
example : SeqD [] F EqX a Premises (Γ := Γ) []
    (Formula.ex Ty.nat (Formula.eq0 (Term.var .vz) (Term.var .vz))) := by
  pbound wrapped_iteration
  pthm .refl0

/-! ## Parity with an established proof mode

The tactic set is being brought up to what the matching-logic proof mode
(`AML-Formalization/matching-logic/src/ProofMode`) offers, restricted to the moves that make
sense here. One test per move. -/

section Parity

/-- `mlIntro`+`mlAssumption`: close by *whichever* hypothesis fits, without naming it. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ A) := by
  pintro ha hb
  passumption

/-- `toMLGoal`: a theorem stated as an ordinary kernel derivation, proved as a script. This
is what makes the mode usable — every other test states its goal as a `SeqD` already. -/
example : Derivable F EqX a Premises (Γ := Γ) (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pmode
  pintro ha hb
  psplit
  · pexact ha
  · pexact hb

/-- `mlApply "H" in "H0"`: forward application into a hypothesis. -/
example : SeqD [] F EqX a Premises [] ((A →ᶠ B) →ᶠ A →ᶠ B) := by
  pintro himp ha
  papply himp in ha with hb
  pexact hb

/-- `mlApplyMeta`: apply a *kernel theorem* to the goal, leaving its antecedents. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  papplym and_intro
  · pexact ha
  · pexact hb

/-- `mlConj`: conjoin two hypotheses. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  pconj ha hb with hab
  pexact hab

/-- `mlDestructBot`. -/
example : SeqD [] F EqX a Premises [] (⊥ᶠ →ᶠ A) := by
  pintro hbot
  pcontradiction hbot

/-- `mlRename`. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ A) := by
  pintro h
  prename h into k
  pexact k

/-- `mlClassic`: case split on `A ∨ᶠ ¬ᶠA`, available only where LEM is. -/
example {Prem : PremiseSet F} :
    SeqD [] F EqX Allowed.classical Prem (Γ := Γ) [] (A →ᶠ A) := by
  pintro h
  pclassic A with hpos hneg
  · pexact h
  · pexact h

-- …and refused where it is not.
/--
error: pclassic: excluded middle is not available here — `allowed.lem` is not `true`.
-/
#guard_msgs in
example {Prem : PremiseSet F} :
    SeqD [] F EqX Allowed.base Prem (Γ := Γ) [] (A →ᶠ A) := by
  pintro h
  pclassic A with hpos hneg
  pexact h

/-- `mlApplyMeta … in "H"`. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  -- `and_intro` applied to `ha` alone leaves its second conjunct open, so it is given here;
  -- the same ambiguity Lean's own `apply … at` has.
  papplym (and_intro (B := B)) in ha with hstep
  papply hstep
  pexact hb

/-- `mlDestructImp`: prove the antecedent, keep the conclusion. -/
example : SeqD [] F EqX a Premises [] ((A →ᶠ B) →ᶠ A →ᶠ B) := by
  pintro himp ha
  pdestruct_imp himp with hb
  · pexact ha
  · pexact hb

/-- `mlTransitivity` for `→ᶠ`. The kit lemma it needs is itself proved as a script — the
mode is now strong enough to build its own furniture. -/
example : SeqD [] F EqX a Premises [] ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := by
  pintro hab hbc ha
  papply hbc
  papply hab
  pexact ha

/-- `mlClear`: drop a hypothesis from the *middle* of the context, not just the top. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ B) := by
  pintro ha hb
  pclear ha
  pexact hb

/-- `mlSwap`: exchange two adjacent hypotheses; the names move with them. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  pswap hb with ha
  psplit
  · pexact ha
  · pexact hb

/-- `mlRevertLast`. -/
example : SeqD [] F EqX a Premises [] (A →ᶠ A) := by
  pintro h
  prevert
  pthm I_comb

/-- `mlSymmetry in "H"`. -/
example {s t : Term F Γ Ty.nat} :
    SeqD [] F EqX a Premises [] (Formula.eq0 s t →ᶠ Formula.eq0 t s) := by
  pintro h
  psym in h with h'
  pexact h'

end Parity

/-! ## Named variables

An open formula prints applied to the variables it may mention, so a binder reads as a
binder. These two pin the cases where the naming is easy to get wrong. -/

section Naming
variable {ρ σ : Ty ι} {P Q : Formula F (ρ :: Γ)}

-- A *structured* weakened hypothesis. Its own binder is fresh, so it must not be named `x₀`
-- like the ambient variable; `↑ᶜ` marks where the renumbering applies.
/--
trace: ι : Type
F : ι → Ty ι
EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ X[i] → Term F Γ X[i] → Formula F Γ
a : Allowed
Premises : PremiseSet F
Γ : Ctx ι
A B : Formula F Γ
ρ σ : Ty ι
P Q : Formula F (ρ :: Γ)
⊢ ⟪Γ, x₀ : ρ⟫
      h : ↑ᶜ(∀ᶠ x₁ : ρ, P x₁ ∧ᶠ Q x₁)
      ────────────────────
      P x₀
-/
#guard_msgs in
example : SeqD ["h"] F EqX a Premises (Γ := ρ :: Γ)
    [Formula.weakenBy ρ (Formula.all ρ (P ∧ᶠ Q))] P := by
  trace_state
  pspecialize h with hpq
  pdestruct hpq with hp _hq
  pexact hp

-- An *atom* under a weakening. Its free variable is shared with the ambient context, so it
-- keeps the ambient name and the weakening prints invisibly.
/--
trace: ι : Type
F : ι → Ty ι
EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ X[i] → Term F Γ X[i] → Formula F Γ
a : Allowed
Premises : PremiseSet F
Γ : Ctx ι
A B : Formula F Γ
ρ σ : Ty ι
P Q : Formula F (ρ :: Γ)
⊢ ⟪Γ, x₀ : ρ, x₁ : σ⟫
      p : P x₀
      ────────────────────
      P x₀
-/
#guard_msgs in
example : SeqD ["p"] F EqX a Premises (Γ := σ :: ρ :: Γ)
    [Formula.weakenBy σ P] (Formula.weakenBy σ P) := by
  trace_state
  pexact p

end Naming

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
