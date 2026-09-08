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

variable {ι κ : Type} {F : κ → Ty ι}
    {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- Congruence for the successor, as an internal implication so a script can `papply` it.

This is QF-ER at `r := S(·)`: the only form of "substituting equals for equals" the system
has. -/
def succ_congr_imp {s t : Term F Γ Ty.nat} :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 s t →ᶠ Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_nat_nf (A₀ := Formula.eq0 s t) (by rfl) (by rfl) I_comb
    (r := .app .succ (.var .vz)) rfl rfl

/-- Put a substitute-after-rename composite into `Term.Subst.cons` normal form.

Instantiating a *weakened* `∀`-hypothesis composes a renaming with a substitution. Left as an
anonymous `fun v => s (r v)` the composite matches no rewrite rule and gets stuck at any leaf
that is not a variable. `Term.Subst.cons` names the shape; see the comment block in
`Subst.lean`. Run before *and* after the main normalisation: before, so the composite is
recognised while `Formula.subst0` is still folded; after, so the leaves `weaken_subst_ext`
exposes under binders get the same treatment. -/
macro "anorm_cons" : tactic =>
  `(tactic| simp only [
      Formula.subst0_renameF_ext, Formula.substF_subst0_map_renameF_ext,
      Formula.substF_cons_renameF_ext,
      Term.subst_subst0_map_rename_ext, Term.subst_cons_rename_ext,
      Term.subst_cons_weaken, Term.Subst.cons_vz, Term.Subst.cons_vs,
      Term.rename_comp, Term.rename_shift, Term.Renaming.comp_apply,
      Term.Renaming.shift])

/-- Normalise the substitutions `pinduction` and `pinst` leave behind.

The counterpart of the `base_nf` / `step_nf` / `inst_nf` lemmas that the hand-built proofs in
`Arithmetic.lean` write out separately for each theorem. -/
macro "anorm" : tactic =>
  `(tactic| (try anorm_cons
             simp only [Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst,
               Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               add_closed_subst, mul_closed_subst, monus_closed_subst, abs_diff_closed_subst,
               pd_closed_subst, sg_bar_closed_subst,
               Term.weaken_subst0, Term.subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, succVar0]
             try anorm_cons))

/-- `anorm`, for a goal carrying a bare *renaming* under a binder rather than a substitution.

That is what `pspecialize` leaves: instantiating a weakened `∀` at the bound variable performs
no substitution at all, only a weakening under the binder. A renaming under a binder is a
`Term.Subst.cons` too — it keeps variable 0 and renames the rest — so one rewrite brings it
into the same normal form and `anorm` finishes.

Kept separate from `anorm` because the two rules compete: turning a renaming into a `cons`
*before* an enclosing `subst0` has absorbed it produces a substitution-after-substitution,
which is outside the vocabulary. Use this only when the renaming stands alone. -/
macro "anorm_ren" : tactic =>
  `(tactic| (try simp only [Formula.renameF_ext_eq_substF_cons, Term.rename_ext_eq_subst_cons]
             anorm))

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
def add_comm (x : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (x +ᵗ x₀) (x₀ +ᵗ x))) := by
  pmode
  pinduction
  · -- x + 0 = 0 + x
    anorm
    prw (add_zero_r x)
    prw (add_zero_l x)
    prefl
  · pforall
    pintro ih
    anorm
    -- x + Sy = S(x + y) = S(y + x) = Sy + x
    prw (add_succ _ _)
    prw (add_succ_l _ _)
    prwby ih
    prefl

/-- Occurrence selection. `x + 0` occurs twice here — once inside the left side, once as the
whole right side — and they are numbered left to right across the goal. -/
def add_zero_twice (x : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 ((x +ᵗ Term.zero) +ᵗ Term.zero) (x +ᵗ Term.zero)) := by
  pmode
  prw (add_zero_r x) at 2   -- the right side:      (x + 0) + 0 =₀ x
  prw (add_zero_r x)        -- the one that is left: x + 0      =₀ x
  prw (add_zero_r x)        --                       x          =₀ x
  prefl

/-- **Rung 2** — associativity. Three variables and a nested context, so the rewrite rules
mention both an outer term and the bound variable in the same argument list.
Compare `Metatheorems.add_assoc`. -/
def add_assoc (x y : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 ((x +ᵗ y) +ᵗ x₀) (x +ᵗ (y +ᵗ x₀)))) := by
  pmode
  pinduction
  · anorm
    prw (add_zero_r (x +ᵗ y))
    prw (add_zero_r y)
    prefl
  · pforall
    pintro ih
    anorm
    prw (add_succ (x +ᵗ y) x₀)
    prw (add_succ y x₀)
    prw (add_succ x (y +ᵗ x₀))
    prwby ih
    prefl

/-- **Rung 3** — the first monus fact, `0 ∸ y = 0`. Compare `Metatheorems.monus_zero_l`. -/
def monus_zero_l :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (Term.zero ∸ᵗ x₀) Term.zero)) := by
  pmode
  pinduction
  · anorm
    prw (monus_zero Term.zero)
    prefl
  · pforall
    pintro ih
    anorm
    prw (monus_succ Term.zero x₀)
    prwby ih
    pthm pd_zero

end ByScript

/-- **Rung 4 — transitivity of `≤`, written with monus.**

`Arithmetic.lean` does *not* have this one: it is new, and it is the first of the arithmetic
lemmas the MCT derivations share, so proving it here is real work rather than a re-proof.

It is also the first proof whose shape is not "induct and rewrite". It needs a case split on
whether each of `y` and `z` is zero — the zero cases contradict `S x ∸ y = 0` — and in the
successor cases it rewrites *inside* the premises, to expose the successors that
`monus_succ_l` strips and the induction hypothesis then consumes. -/
def monus_trans :
    Derivable F al Premises (Γ := Γ)
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
    pthm (monus_zero_l x₁)
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
        · pthm (monus_zero (S x₀))
      · pexact h1
    · -- y = S(pd y): strip the successor off the first premise
      papplym (ne_zero_eq_succ_pd x₁) in hyn with hy1
      prwby hy1 in h1 with h1'
      prw (monus_succ_l x₀ (pdᵗ x₁)) in h1' with h1''
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
          · pthm (monus_zero (S (pdᵗ x₁)))
        · pexact h2'
      · -- z = S(pd z): now both premises are at the predecessors
        papplym (ne_zero_eq_succ_pd x₂) in hzn with hz1
        prwby hz1 in h2' with h2''
        prw (monus_succ_l (pdᵗ x₁) (pdᵗ x₂)) in h2'' with h2'''
        -- feed the induction hypothesis at (pd y, pd z)
        pinst ih (pdᵗ x₁) with ihA
        anorm
        pinst ihA (pdᵗ x₂) with ihB
        anorm
        prwby hz1
        prw (monus_succ_l x₀ (pdᵗ x₂))
        papply ihB
        · pexact h1''
        · pexact h2'''

/-- **Rung 5 — the antitone chain.** A nonincreasing sequence never comes back up:
`a (m + i) ≤ a m`, by induction on `i`. The second of the shared lemmas,
and the first proof with a hypothesis that survives the induction and a *function* parameter
rather than a variable.

The premise sits **inside** the quantifiers on purpose. Put outside, it would be weakened by
each `pforall`, and instantiating a weakened `∀`-hypothesis at a compound term leaves a
substitution `anorm` cannot normalise — see `LADDER.md`. Inside, every use is either at the
bound variable, where `pspecialize` applies and no substitution appears, or on an unweakened
hypothesis, where `pinst` does. -/
def antitone_chain (a : Term F Γ (Ty.nat →ₜ Ty.nat)) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (Formula.all Ty.nat (Formula.eq0 (a ⬝ (S x₂) ∸ᵗ a ⬝ x₂) Term.zero) →ᶠ
         Formula.eq0 (a ⬝ (x₁ +ᵗ x₀) ∸ᵗ a ⬝ x₁) Term.zero))) := by
  pmode
  pinduction
  · -- i = 0 : a (m + 0) ∸ a m = a m ∸ a m = 0
    anorm
    pforall
    pintro hmono
    prw (add_zero_r x₀)
    pthm (monus_self (a ⬝ x₀))
  · pforall
    pintro ih
    anorm
    pforall
    pintro hmono
    -- a (m + S i) = a (S (m + i)), then chain through a (m + i)
    prw (add_succ x₁ x₀)
    pfrom mt := monus_trans
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

/-- The same theorem with the monotonicity premise **outside** the quantifiers.

This is the shape `antitone_chain` was written to avoid: `hmono` is weakened once by the
induction and again by each `pforall`, and it is then instantiated at the compound term
`m + i` — a substitute-after-rename composite over an *opaque* parameter `a`. Before
`Term.Subst.cons` this could not be normalised at all. -/
def antitone_chain_premise_outside
    (a : Term F Γ (Ty.nat →ₜ Ty.nat)) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (a ⬝ (S x₀) ∸ᵗ a ⬝ x₀) Term.zero) →ᶠ
       Formula.all Ty.nat (Formula.all Ty.nat
         (Formula.eq0 (a ⬝ (x₁ +ᵗ x₀) ∸ᵗ a ⬝ x₁) Term.zero))) := by
  pmode
  pintro hmono
  pinduction
  · anorm
    pforall
    prw (add_zero_r x₀)
    pthm (monus_self (a ⬝ x₀))
  · pforall
    pintro ih
    anorm
    pforall
    prw (add_succ x₁ x₀)
    pfrom mt := monus_trans
    pinst mt (a ⬝ (S (x₁ +ᵗ x₀))) with mt1
    anorm
    pinst mt1 (a ⬝ (x₁ +ᵗ x₀)) with mt2
    anorm
    pinst mt2 (a ⬝ x₁) with mt3
    anorm
    papply mt3
    · pinst hmono (x₁ +ᵗ x₀) with hm
      anorm
      pexact hm
    · pspecialize ih with ihm
      pexact ihm

/-- **Rung 6a — strictness.** `y ≤ x` and `y ≠ x` give `y < x`, written in monus form:
`y ∸ x = 0 → ¬(x = y) → S y ∸ x = 0`.

Not in `Arithmetic.lean` and not a consequence of what is: `monus_disjunct` at `(S y, x)`
leaves the branch `x ∸ S y = 0`, which is consistent with the premises — the case `x = S y`,
where the goal happens to hold anyway. So it needs its own induction, on `y`.

The shape is rung 4's: split on whether `x` is zero, kill the zero branch with
`succ_ne_zero`, and in the other branch replace `x` by `S (pd x)` so `monus_succ_l` strips a
successor off both the premise and the goal. What is new is that the *disequality* has to be
transported down to the predecessor as well, which is what the `phave` below does. -/
def monus_succ_of_ne :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        ((x₀ ∸ᵗ x₁ =₀ Term.zero) →ᶠ ¬ᶠ(x₁ =₀ x₀) →ᶠ
         (S x₀ ∸ᵗ x₁ =₀ Term.zero)))) := by
  pmode
  pinduction
  · -- y = 0 : x ≠ 0, so x = S(pd x) and S 0 ∸ S(pd x) = 0 ∸ pd x = 0
    anorm
    pforall
    pintro h1 hne
    papplym (ne_zero_eq_succ_pd x₀) in hne with hx
    prwby hx
    prw (monus_succ_l Term.zero (pdᵗ x₀))
    pthm (monus_zero_l (pdᵗ x₀))
  · pforall
    pintro ih
    anorm
    pforall
    pintro h1 hne
    -- is x zero?
    pfrom hdec := eq0_decidable'
    pinst hdec x₁ with hx
    anorm
    pcases hx with hx0 | hxn
    · -- x = 0 contradicts `S y ∸ x = 0`
      pexfalso
      pfrom hsnz := Derivable.succ_ne_zero
      pinst hsnz x₀ with hsnz'
      anorm
      papply hsnz'
      ptrans (S x₀ ∸ᵗ x₁)
      · psym
        ptrans (S x₀ ∸ᵗ Term.zero)
        · prwby hx0
          prefl
        · pthm (monus_zero (S x₀))
      · pexact h1
    · -- x = S(pd x): strip a successor off the premise, and off the disequality
      papplym (ne_zero_eq_succ_pd x₁) in hxn with hx1
      prwby hx1 in h1 with h1'
      prw (monus_succ_l x₀ (pdᵗ x₁)) in h1' with h1''
      -- the induction hypothesis at pd x
      pinst ih (pdᵗ x₁) with ihA
      anorm
      papply ihA in h1'' with ihB
      prwby hx1
      prw (monus_succ_l (S x₀) (pdᵗ x₁))
      papply ihB
      -- what is left: the disequality, transported down to the predecessor
      pintro hpd
      papply hne
      prwby hx1
      prwby hpd
      prefl

/-- **Rung 6b — the strict-drop step.** From `x ≤ K+1`, `y ≤ x` and `x ≠ y`, conclude
`y ≤ K`: the budget descent MCT's dichotomy proof runs on.

With rung 6a in hand this is two moves — strictness turns `y ≤ x` plus `x ≠ y` into
`S y ≤ x`, transitivity chains that against `x ≤ S K`, and `monus_succ_l` cancels the
successors. It is the first rung that is *composed* rather than proved: no induction, no
rewriting of its own beyond the last cancellation. -/
def strict_drop :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        ((x₂ ∸ᵗ S x₀ =₀ Term.zero) →ᶠ (x₁ ∸ᵗ x₂ =₀ Term.zero) →ᶠ ¬ᶠ(x₂ =₀ x₁) →ᶠ
         (x₁ ∸ᵗ x₀ =₀ Term.zero))))) := by
  pmode
  pforall
  pforall
  pforall
  pintro hK hyx hne
  -- y ≤ x and x ≠ y give S y ≤ x
  pfrom sne := monus_succ_of_ne
  pinst sne x₁ with sne1
  anorm
  pinst sne1 x₂ with sne2
  anorm
  papply sne2 in hyx with sne3
  papply sne3 in hne with hsy
  -- chain S y ≤ x ≤ S K
  pfrom mt := monus_trans
  pinst mt (S x₁) with mt1
  anorm
  pinst mt1 x₂ with mt2
  anorm
  pinst mt2 (S x₀) with mt3
  anorm
  papply mt3 in hsy with mt4
  papply mt4 in hK with hfin
  -- S y ∸ S K = y ∸ K
  prw (monus_succ_l x₁ x₀) in hfin with hfin'
  pexact hfin'

/-! ## Three more monus facts

Wanted by the *lazy* MCT proof rather than the dichotomy one: it counts strict drops against
a budget, so it needs `≤` to survive a common addend, `y ≤ x + y`, and the one arithmetic
fact that turns "`S K ≤ K`" into a contradiction. All three are short inductions. -/

/-- `S x ∸ x = 1`. The contradiction the lazy proof bottoms out in. -/
def succ_monus_self :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (S x₀ ∸ᵗ x₀ =₀ S Term.zero)) := by
  pmode
  pinduction
  · anorm
    pthm (monus_zero (S Term.zero))
  · pforall
    pintro ih
    anorm
    prw (monus_succ_l (S x₀) x₀)
    pexact ih

/-- `y ≤ x + y`. -/
def monus_add_self_l :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        (x₁ ∸ᵗ (x₀ +ᵗ x₁) =₀ Term.zero))) := by
  pmode
  pinduction
  · anorm
    pforall
    prw (add_zero_l x₀)
    pthm (monus_self x₀)
  · pforall
    pintro ih
    anorm
    pforall
    prw (add_succ_l x₀ x₁)
    prw (monus_succ x₁ (x₀ +ᵗ x₁))
    pspecialize ih with ihy
    anorm_ren
    prwby ihy
    pthm pd_zero

/-- `(x + k) ∸ (y + k) = x ∸ y`: a common addend cancels, so `≤` survives it. -/
def add_monus_add :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
        ((x₁ +ᵗ x₀) ∸ᵗ (x₂ +ᵗ x₀) =₀ x₁ ∸ᵗ x₂)))) := by
  pmode
  pinduction
  · anorm
    pforall
    pforall
    prw (add_zero_r x₀)
    prw (add_zero_r x₁)
    prefl
  · pforall
    pintro ih
    anorm
    pforall
    pforall
    prw (add_succ x₁ x₀)
    prw (add_succ x₂ x₀)
    prw (monus_succ_l (x₁ +ᵗ x₀) (x₂ +ᵗ x₀))
    pinst ih x₁ with ih1
    anorm
    pinst ih1 x₂ with ih2
    anorm
    pexact ih2

end ProofMode
end Metatheorems
