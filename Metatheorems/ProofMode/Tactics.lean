/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Display

/-!
# The tactic layer

Each move is a *lemma* stated on `SeqD` — the name-carrying wrapper — and a *macro* that
applies it. Splitting it that way is the point of this file: the lemma is where the name
list is kept in step with `Δ`, so the bookkeeping is checked by the elaborator rather than
by tactic code manipulating `Expr`s.

Consequently there is exactly one tactic here that inspects the goal at all, `pexact`, and
it does so only to turn a *name* into a de Bruijn index. Everything else is a macro.

## Naming

Tactics are prefixed `p`, since they operate on the object logic and must not be confused
with Lean's own `intro`, `cases`, … . A tactic never touches the kernel: it emits a `refine`
against a lemma from this file, which is built from `Packing.lean`, which is built from
`Derivable`.
-/

namespace Metatheorems
namespace ProofMode

open Lean Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {ns : List String}

-- ============================================================================
-- The moves, as name-aware lemmas
-- ============================================================================

/-- Introduce an implication, naming the new hypothesis. -/
def pm_intro (n : String) {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD (n :: ns) F EqX a Premises (A :: Δ) B) :
    SeqD ns F EqX a Premises Δ (A →ᶠ B) :=
  seq_intro h

/-- Split a conjunctive goal. -/
def pm_split {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h₁ : SeqD ns F EqX a Premises Δ A) (h₂ : SeqD ns F EqX a Premises Δ B) :
    SeqD ns F EqX a Premises Δ (A ∧ᶠ B) :=
  seq_andI h₁ h₂

/-- Take the left disjunct. -/
def pm_left {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ A) : SeqD ns F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_orI₁ h

/-- Take the right disjunct. -/
def pm_right {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ B) : SeqD ns F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_orI₂ h

/-- Case analysis on a disjunction, naming the hypothesis in each branch. -/
def pm_cases (n m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F EqX a Premises Δ (A ∨ᶠ B))
    (h₁ : SeqD (n :: ns) F EqX a Premises (A :: Δ) C)
    (h₂ : SeqD (m :: ns) F EqX a Premises (B :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_orE hAB h₁ h₂

/-- Project out of a conjunctive hypothesis-shaped goal (left). -/
def pm_andE₁ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A ∧ᶠ B)) : SeqD ns F EqX a Premises Δ A :=
  seq_andE₁ h

/-- Project out of a conjunctive hypothesis-shaped goal (right). -/
def pm_andE₂ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A ∧ᶠ B)) : SeqD ns F EqX a Premises Δ B :=
  seq_andE₂ h

/-- Destructure a conjunction into two named hypotheses.

Stated as a *cut* rather than as an in-place rewrite of one position, so it does not care
where the conjunction sits in `Δ`: the caller proves `A ∧ᶠ B` however it likes (typically
`pexact`), and the two components arrive on top of the context. -/
def pm_andcut (n m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F EqX a Premises Δ (A ∧ᶠ B))
    (k : SeqD (n :: m :: ns) F EqX a Premises (A :: B :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_andE₂ hAB) (seq_cut (seq_andE₁ (seq_weaken hAB)) k)

/-- `⊥` eliminates to anything. -/
def pm_exfalso {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ ⊥ᶠ) : SeqD ns F EqX a Premises Δ A :=
  seq_exfalso h

/-- Introduce a `∀`. The whole hypothesis context weakens; the *names* do not change, which
is why the name list can be reused verbatim. -/
def pm_allI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F EqX a Premises (Δ.map (Formula.weakenBy ρ)) A) :
    SeqD ns F EqX a Premises Δ (Formula.all ρ A) :=
  seq_allI h

/-- Instantiate a weakened `∀`-hypothesis at the bound variable. -/
def pm_allE_here {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F EqX a Premises Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    SeqD ns F EqX a Premises Δ A :=
  seq_allE_here h

/-- Supply a witness for an `∃` goal. -/
def pm_exI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F EqX a Premises Δ (A.subst0 t)) :
    SeqD ns F EqX a Premises Δ (Formula.ex ρ A) :=
  seq_exI t h

/-- Consume an `∃`, naming the body. -/
def pm_exE (n : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} {B : Formula F Γ}
    (hex : SeqD ns F EqX a Premises Δ (Formula.ex ρ A))
    (hbody : SeqD (n :: ns) F EqX a Premises
      (A :: Δ.map (Formula.weakenBy ρ)) (Formula.weakenBy ρ B)) :
    SeqD ns F EqX a Premises Δ B :=
  seq_exE hex hbody

/-- Use a theorem of the kernel — the escape hatch into `Derivable`. -/
def pm_have {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : Derivable F EqX a Premises A) : SeqD ns F EqX a Premises Δ A :=
  seq_of_thm h

-- ============================================================================
-- Tactics
-- ============================================================================

section Tactics
open Lean.Elab.Tactic Lean.Meta

/-- `pexact h` closes the goal with the hypothesis named `h`.

This is the only tactic that reads the goal: it turns the *name* `h` into the de Bruijn
index that `HVar` wants. Names and `Δ` are aligned positionally, so the index is just the
position of `h` in the name list. It comes first because the elimination tactics below
discharge their major premise with `by pexact …`. -/
elab "pexact " h:ident : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let args := ty.getAppArgs
  unless ty.isAppOf ``SeqD && args.size == 9 do
    throwError "pexact: the goal is not a proof-mode sequent{indentExpr ty}"
  let some namesE := listLit? args[1]! |
    throwError "pexact: the hypothesis names are not a literal list"
  let names := namesE.filterMap strLit?
  let n := h.getId.toString
  let some i := names.findIdx? (· == n) |
    throwError "pexact: no hypothesis named `{n}` (have: {names})"
  let mut v ← `(HVar.hz)
  for _ in [0:i] do v ← `(HVar.hs $v)
  evalTactic (← `(tactic| exact seq_id $v))

/-- `pintro h k …` introduces implications, naming the hypotheses. -/
syntax (name := pintro) "pintro" (ppSpace colGt ident)+ : tactic

macro_rules
  | `(tactic| pintro $h:ident $hs:ident*) =>
      let n := Lean.quote h.getId.toString
      if hs.isEmpty then
        `(tactic| refine pm_intro $n ?_)
      else
        `(tactic| (refine pm_intro $n ?_; pintro $hs*))

/-- `psplit` splits a conjunctive goal into two. -/
macro "psplit" : tactic => `(tactic| refine pm_split ?_ ?_)

/-- `pleft` / `pright` choose a disjunct. -/
macro "pleft" : tactic => `(tactic| refine pm_left ?_)
macro "pright" : tactic => `(tactic| refine pm_right ?_)

/-- `pcases h with hl | hr` does case analysis on the disjunction proved by hypothesis `h`. -/
macro "pcases " h:ident " with " l:ident " | " r:ident : tactic =>
  `(tactic| refine pm_cases $(Lean.quote l.getId.toString) $(Lean.quote r.getId.toString)
      (by pexact $h) ?_ ?_)

/-- `pand_left` / `pand_right` weaken the goal to a conjunction containing it. The other
conjunct is left as a metavariable, to be fixed by whatever closes the branch. -/
macro "pand_left" : tactic => `(tactic| apply pm_andE₁)
macro "pand_right" : tactic => `(tactic| apply pm_andE₂)

/-- `pexfalso` replaces the goal by `⊥ᶠ`. -/
macro "pexfalso" : tactic => `(tactic| refine pm_exfalso ?_)

/-- `pforall` introduces a `∀`, weakening the hypothesis context. -/
macro "pforall" : tactic => `(tactic| refine pm_allI ?_)

/-- `pspecialize` instantiates a weakened `∀`-goal at the bound variable. -/
macro "pspecialize" : tactic => `(tactic| refine pm_allE_here ?_)

/-- `pexists t` supplies a witness. -/
macro "pexists " t:term : tactic => `(tactic| refine pm_exI $t ?_)

/-- `pobtain h with x` consumes the `∃` proved by hypothesis `h`, naming the body `x`. -/
macro "pobtain " h:ident " with " x:ident : tactic =>
  `(tactic| refine pm_exE $(Lean.quote x.getId.toString) (by pexact $h) ?_)

/-- `pdestruct h with x y` splits the conjunction proved by hypothesis `h`. -/
macro "pdestruct " h:ident " with " x:ident ppSpace y:ident : tactic =>
  `(tactic| refine pm_andcut $(Lean.quote x.getId.toString) $(Lean.quote y.getId.toString)
      (by pexact $h) ?_)

/-- `pthm e` discharges the goal with a kernel theorem. -/
macro "pthm " e:term : tactic => `(tactic| exact pm_have $e)

end Tactics

end ProofMode
end Metatheorems
