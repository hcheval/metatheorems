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
syntax:max "pdᵗ " term:max : term

macro_rules
  | `($a +ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.add $a $b)
  | `($a *ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.mul $a $b)
  | `($a ∸ᵗ $b) => `(Metatheorems.Term.app2 Metatheorems.Term.monus $a $b)
  | `(S $t)     => `(Metatheorems.Term.app Metatheorems.Term.succ $t)
  | `(pdᵗ $t)   => `(Metatheorems.Term.app Metatheorems.Term.pd $t)

def delabArith : Delab := do
  let e ← SubExpr.getExpr
  guard (isSpine e)
  let (hd, xs) := termSpine e
  let hd? := hd.getAppFn.constName?
  if xs.size == 1 then
    if hd? == some ``Term.succ then
      let a ← (Lean.PrettyPrinter.delab xs[0]! : MetaM _)
      return ← `(S $a)
    if hd? == some ``Term.pd then
      let a ← (Lean.PrettyPrinter.delab xs[0]! : MetaM _)
      return ← `(pdᵗ $a)
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
      Term.weaken_subst0, Term.subst_subst0_map_weaken, Term.weaken_subst_ext,
      weaken_substVar0, succVar0])

/-- `anorm`, plus pushing *renamings* down to the variables.

Kept separate because it is not always an improvement: on a term built only from variables and
constants it finishes the job, but on an opaque parameter it turns a tidy `weakenBy` into a
stuck `Term.rename`. Use it when instantiating a weakened `∀`-hypothesis at a compound term,
and only then. -/
macro "anorm_deep" : tactic =>
  `(tactic| (anorm
             simp only [Formula.weakenBy, Formula.weaken, Formula.renameF, Term.rename,
               Term.Renaming.ext_vz, Term.Renaming.ext_vs, Term.Renaming.shift,
               Formula.substF, Term.subst, Term.subst0_map_vz, Term.subst0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Formula.subst0, Term.app2]))

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

/-- **Rung 4 — transitivity of `≤`, written with monus.**

`Arithmetic.lean` does *not* have this one: it is new, and it is the first of the shared
lemmas `HANDOFF.md` §3 A0 asks for, so proving it here is Track A work rather than a
re-proof.

It is also the first proof whose shape is not "induct and rewrite". It needs a case split on
whether each of `y` and `z` is zero — the zero cases contradict `S x ∸ y = 0` — and in the
successor cases it rewrites *inside* the premises, to expose the successors that
`monus_succ_l` strips and the induction hypothesis then consumes. -/
def monus_trans (adm : AdmissibleEqX EqX) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        ((x₀ ∸ᵗ x₁ =₀ Term.zero) →ᶠ (x₁ ∸ᵗ x₂ =₀ Term.zero) →ᶠ
         (x₀ ∸ᵗ x₂ =₀ Term.zero))))) := by
  pmode
  pinduction
  · -- x = 0, so x ∸ z = 0 outright
    anorm
    pforall
    pforall
    pintro h1 h2
    pthm (monus_zero_l adm x₁)
  · pforall
    pintro ih
    anorm
    pforall
    pforall
    pintro h1 h2
    -- is y zero?
    pfrom hdec := eq0_decidable'
    pinst hdec x₁ with hy
    anorm
    pcases hy with hy0 | hyn
    · -- y = 0 contradicts `S x ∸ y = 0`
      pexfalso
      pfrom hsnz := Derivable.succ_ne_zero
      pinst hsnz x₀ with hsnz'
      anorm
      papply hsnz'
      ptrans (S x₀ ∸ᵗ x₁)
      · psym
        ptrans (S x₀ ∸ᵗ Term.zero)
        · prwby hy0
          prefl
        · pthm (monus_zero adm (S x₀))
      · pexact h1
    · -- y = S(pd y): strip the successor off the first premise
      papplym (ne_zero_eq_succ_pd adm x₁) in hyn with hy1
      prwby hy1 in h1 with h1'
      prw (monus_succ_l adm x₀ (pdᵗ x₁)) in h1' with h1''
      prwby hy1 in h2 with h2'
      -- is z zero?
      pinst hdec x₂ with hz
      anorm
      pcases hz with hz0 | hzn
      · pexfalso
        pfrom hsnz := Derivable.succ_ne_zero
        pinst hsnz (pdᵗ x₁) with hsnz'
        anorm
        papply hsnz'
        ptrans (S (pdᵗ x₁) ∸ᵗ x₂)
        · psym
          ptrans (S (pdᵗ x₁) ∸ᵗ Term.zero)
          · prwby hz0
            prefl
          · pthm (monus_zero adm (S (pdᵗ x₁)))
        · pexact h2'
      · -- z = S(pd z): now both premises are at the predecessors
        papplym (ne_zero_eq_succ_pd adm x₂) in hzn with hz1
        prwby hz1 in h2' with h2''
        prw (monus_succ_l adm (pdᵗ x₁) (pdᵗ x₂)) in h2'' with h2'''
        -- feed the induction hypothesis at (pd y, pd z)
        pinst ih (pdᵗ x₁) with ihA
        anorm
        pinst ihA (pdᵗ x₂) with ihB
        anorm
        prwby hz1
        prw (monus_succ_l adm x₀ (pdᵗ x₂))
        papply ihB
        · pexact h1''
        · pexact h2'''

/-- **Rung 5 — the antitone chain.** A nonincreasing sequence never comes back up:
`a (m + i) ≤ a m`, by induction on `i`. The second of `HANDOFF.md` §3 A0's shared lemmas,
and the first proof with a hypothesis that survives the induction and a *function* parameter
rather than a variable.

The premise sits **inside** the quantifiers on purpose. Put outside, it would be weakened by
each `pforall`, and instantiating a weakened `∀`-hypothesis at a compound term leaves a
substitution `anorm` cannot normalise — see `LADDER.md`. Inside, every use is either at the
bound variable, where `pspecialize` applies and no substitution appears, or on an unweakened
hypothesis, where `pinst` does. -/
def antitone_chain (adm : AdmissibleEqX EqX) (a : Term F Γ (Ty.nat →ₜ Ty.nat)) :
    Derivable F EqX al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (Formula.all Ty.nat (Formula.eq0 (a ⬝ (S x₂) ∸ᵗ a ⬝ x₂) Term.zero) →ᶠ
         Formula.eq0 (a ⬝ (x₁ +ᵗ x₀) ∸ᵗ a ⬝ x₁) Term.zero))) := by
  pmode
  pinduction
  · -- i = 0 : a (m + 0) ∸ a m = a m ∸ a m = 0
    anorm
    pforall
    pintro hmono
    prw (add_zero_r adm x₀)
    pthm (monus_self adm (a ⬝ x₀))
  · pforall
    pintro ih
    anorm
    pforall
    pintro hmono
    -- a (m + S i) = a (S (m + i)), then chain through a (m + i)
    prw (add_succ adm x₁ x₀)
    pfrom mt := monus_trans adm
    pinst mt (a ⬝ (S (x₁ +ᵗ x₀))) with mt1
    anorm
    pinst mt1 (a ⬝ (x₁ +ᵗ x₀)) with mt2
    anorm
    pinst mt2 (a ⬝ x₁) with mt3
    anorm
    papply mt3
    · -- the sequence steps down at u := m + i
      pinst hmono (x₁ +ᵗ x₀) with hm
      anorm
      pexact hm
    · -- the induction hypothesis, at the bound variable and then at the premise
      pspecialize ih with ihm
      papply ihm
      pexact hmono

end ProofMode
end Metatheorems
