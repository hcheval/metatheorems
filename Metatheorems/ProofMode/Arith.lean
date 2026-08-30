/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Arithmetic
import Metatheorems.ProofMode.Tactics
import Metatheorems.ProofMode.Rewrite

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

/-! ## Printing arithmetic

A second delaborator for `Term.app`, registered after the generic one in `Pretty.lean` and
tried first. It recognises the binary arithmetic constants and falls through to juxtaposition
for everything else. -/

namespace Pretty
open Lean Lean.PrettyPrinter.Delaborator

/-- Infix for the object-level arithmetic operations. These *parse* as well as print, so a
script writes terms the way the goal shows them. -/
syntax:65 term:65 " +ᵗ " term:66 : term
syntax:70 term:70 " *ᵗ " term:71 : term
syntax:65 term:65 " ∸ᵗ " term:66 : term
syntax:max "S " term:max : term

macro_rules
  | `($a +ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.add $a $b)
  | `($a *ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.mul $a $b)
  | `($a ∸ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.monus $a $b)
  | `(S $t)     => `(Metatheorems.Term.app Metatheorems.Term.succ $t)

def delabArith : Delab := do
  let e ← SubExpr.getExpr
  guard (isSpine e)
  let (hd, xs) := termSpine e
  let hd? := hd.getAppFn.constName?
  if xs.size == 1 && hd? == some ``Term.succ then
    let a ← (Lean.PrettyPrinter.delab xs[0]! : MetaM _)
    return ← `(S $a)
  guard (xs.size == 2)
  let a ← (Lean.PrettyPrinter.delab xs[0]! : MetaM _)
  let b ← (Lean.PrettyPrinter.delab xs[1]! : MetaM _)
  match hd? with
  | some ``Term.add   => `($a +ᵗ $b)
  | some ``Term.mul   => `($a *ᵗ $b)
  | some ``Term.monus => `($a ∸ᵗ $b)
  | _ => failure

@[app_delab Metatheorems.Term.app]  def delabArithApp : Delab := delabArith
@[app_delab Metatheorems.Term.app2] def delabArithApp2 : Delab := delabArith

end Pretty

namespace ProofMode

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- Congruence for the successor, as an internal implication so a script can `papply` it.

This is QF-ER at `r := S(·)`: the only form of "substituting equals for equals" the system
has. -/
def succ_congr_imp {s t : Term F Γ Ty.nat} :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 s t →ᶠ Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_nat_nf (A₀ := Formula.eq0 s t) (by rfl) (by rfl) I_comb
    (r := .app .succ (.var .vz)) rfl rfl

/-- Normalise the substitutions `pinduction` leaves behind.

The counterpart of the `base_nf` / `step_nf` / `inst_nf` lemmas that the hand-built proofs in
`Arithmetic.lean` write out separately for each theorem. -/
macro "anorm" : tactic =>
  `(tactic| simp only [Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
      Term.subst,
      Term.subst0_map_vz, Term.subst0_map_vs,
      Term.substVar0_map_vz, Term.substVar0_map_vs,
      Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
      add_closed_subst, mul_closed_subst, monus_closed_subst, abs_diff_closed_subst,
      pd_closed_subst, sg_bar_closed_subst,
      Term.weaken_subst0, Term.subst_subst0_map_weaken, weaken_substVar0, succVar0])

namespace ByScript

/-!
These are theorems `Arithmetic.lean` already proves with raw constructors, proved again as
scripts so the two can be read side by side. They live in `ByScript` because they are the
*same* statements — the point is the proof, not the theorem.

Each is stated as a `Derivable`, not as a `SeqD`: that is how a theorem is written, and it is
what lets a later proof feed it to `prw` or `pthm`. `pmode` enters the mode.
-/

/-- **Commutativity of addition.** Compare `Metatheorems.add_comm`.

The shape is the textbook one, and with `prw` the script is the textbook script: induct on
the second argument, rewrite by the defining equations, use the induction hypothesis.

Compare `Nat.add_comm` in mathlib — `induction`, then `rw [Nat.add_succ, ih, Nat.succ_add]`.
The remaining differences are `anorm`, which pays for the substitutions `induction` leaves in
the goal, and the split between `prw` (closed equation) and `prwby` (hypothesis), which is
forced by QF-ER carrying a premise. -/
def add_comm (adm : AdmissibleEqX EqX) (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (x +ᵗ x₀) (x₀ +ᵗ x))) := by
  pmode
  pinduction
  · -- x + 0 = 0 + x
    anorm
    prw (add_zero_r adm x)
    prw (add_zero_l adm x)
    prefl
  · pforall
    pintro ih
    anorm
    -- x + Sy = S(x + y) = S(y + x) = Sy + x
    prw (add_succ adm _ _)
    prw (add_succ_l adm _ _)
    prwby ih
    prefl

/-- Occurrence selection. `x + 0` occurs twice here — once inside the left side, once as the
whole right side — and they are numbered left to right across the goal. -/
def add_zero_twice (adm : AdmissibleEqX EqX) (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.eq0 ((x +ᵗ Term.zero) +ᵗ Term.zero) (x +ᵗ Term.zero)) := by
  pmode
  prw (add_zero_r adm x) at 2   -- the right side:      (x + 0) + 0 =₀ x
  prw (add_zero_r adm x)        -- the one that is left: x + 0      =₀ x
  prw (add_zero_r adm x)        --                       x          =₀ x
  prefl

/-- **Rung 2** — associativity. Three variables and a nested context, so the rewrite rules
mention both an outer term and the bound variable in the same argument list.
Compare `Metatheorems.add_assoc`. -/
def add_assoc (adm : AdmissibleEqX EqX) (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 ((x +ᵗ y) +ᵗ x₀) (x +ᵗ (y +ᵗ x₀)))) := by
  pmode
  pinduction
  · anorm
    prw (add_zero_r adm (x +ᵗ y))
    prw (add_zero_r adm y)
    prefl
  · pforall
    pintro ih
    anorm
    prw (add_succ adm (x +ᵗ y) x₀)
    prw (add_succ adm y x₀)
    prw (add_succ adm x (y +ᵗ x₀))
    prwby ih
    prefl

/-- **Rung 3** — the first monus fact, `0 ∸ y = 0`. Compare `Metatheorems.monus_zero_l`. -/
def monus_zero_l (adm : AdmissibleEqX EqX) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (Term.zero ∸ᵗ x₀) Term.zero)) := by
  pmode
  pinduction
  · anorm
    prw (monus_zero adm Term.zero)
    prefl
  · pforall
    pintro ih
    anorm
    prw (monus_succ adm Term.zero x₀)
    prwby ih
    pthm pd_zero

end ByScript

end ProofMode
end Metatheorems
