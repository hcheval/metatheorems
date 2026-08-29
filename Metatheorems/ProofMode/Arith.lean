/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Arithmetic
import Metatheorems.ProofMode.Tactics

/-!
# Arithmetic in the proof mode

`Arithmetic.lean` proves these facts with raw constructors. This file proves one of them
again as a script, so the two can be compared directly.

## What the mode does and does not buy

The *logic* — induction, the induction hypothesis as a named assumption, chaining equalities
— becomes a script. What does not go away is the substitution bookkeeping: `induction` leaves
goals of the form `A.subst0 0` and `∀n (A → A[Sn])`, and those have to be normalised before
they are recognisable. `anorm` below does that with the same rewrite set the hand-built
proofs spell out one `_nf` lemma at a time.

There is no rewriting tactic, and there cannot be a general one: the system is *weakly*
extensional, so equals may be substituted for equals only through QF-ER, at quantifier-free
∨-free formulas. `ptrans` is the closest thing — a `calc` step, named midpoint and all.
-/

namespace Metatheorems
namespace ProofMode

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- Congruence for the successor, as an internal implication so a script can `papply` it.

This is QF-ER at `r := S(·)`: the only form of "substituting equals for equals" the system
has. -/
def succ_congr_imp {s t : Term F Γ Ty.nat} :
    Derivable F EqX al Premises
      (Formula.eq0 s t →ᶠ Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_nat_nf (A₀ := Formula.eq0 s t) (by rfl) (by rfl) I_comb
    (r := .app .succ (.var .vz)) rfl rfl

/-- Normalise the substitutions `pinduction` leaves behind.

The counterpart of the `base_nf` / `step_nf` / `inst_nf` lemmas that the hand-built proofs in
`Arithmetic.lean` write out separately for each theorem. -/
macro "anorm" : tactic =>
  `(tactic| simp only [Formula.subst0, Formula.substVar0, Formula.substF, Term.subst,
      Term.subst0_map, Term.substVar0_map, Term.app2, add_closed_subst,
      Term.weaken_subst0, Term.subst_subst0_map_weaken, weaken_substVar0, succVar0])

section AddComm
variable (adm : AdmissibleEqX EqX)

/-- **Commutativity of addition**, as a script. Compare `Metatheorems.add_comm`, which proves
the same thing with raw constructors.

The shape is the textbook one: induct on the second argument; the base case is
`x + 0 = x = 0 + x`; the step chains `x + Sy = S(x + y) = S(y + x) = Sy + x`, using the
induction hypothesis in the middle through successor-congruence. -/
example (x : Term F Γ Ty.nat) :
    SeqD [] F EqX al Premises []
      (Formula.all Ty.nat (Formula.eq0
        (Term.app2 Term.add (x.weaken (σ := Ty.nat)) (.var .vz))
        (Term.app2 Term.add (.var .vz) (x.weaken (σ := Ty.nat))))) := by
  pinduction
  · -- x + 0 = 0 + x
    anorm
    ptrans x
    · pthm (add_zero_r adm x)
    · psym
      pthm (add_zero_l adm x)
  · pforall
    pintro ih
    anorm
    -- x + Sy = S(x + y)
    ptrans (.app .succ (Term.app2 Term.add (x.weaken (σ := Ty.nat)) (.var .vz)))
    · pthm (add_succ adm (x.weaken (σ := Ty.nat)) (.var .vz))
    -- S(x + y) = S(y + x) = Sy + x
    · ptrans (.app .succ (Term.app2 Term.add (.var .vz) (x.weaken (σ := Ty.nat))))
      · pfrom sc := succ_congr_imp
          (s := Term.app2 Term.add (x.weaken (σ := Ty.nat)) (.var .vz))
          (t := Term.app2 Term.add (.var .vz) (x.weaken (σ := Ty.nat)))
        papply sc
        pexact ih
      · psym
        pthm (add_succ_l adm (.var .vz) (x.weaken (σ := Ty.nat)))

end AddComm

end ProofMode
end Metatheorems
