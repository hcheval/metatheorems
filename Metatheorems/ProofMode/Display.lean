/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean
import Metatheorems.ProofMode.Packing
import Metatheorems.ProofMode.Pretty

/-!
# Rendering a proof-mode goal

`Seq F a Premises Δ B` is legible only if you can read `Δ` as a *list of named
hypotheses* rather than as a `List (Formula F Γ)` printed inline. This file adds the display
layer: a name-carrying wrapper `SeqD` and a delaborator that renders it as a box.

Names are display data, carried by a separate *reducible* wrapper:

    SeqD names F a Premises Δ B  :=  Seq F a Premises Δ B

so every kit lemma applies through it by unification, and `names` never affects the proof term.

## Rendering

    ⊢ ⟪[nat]⟫
        k : A
        h : B
        ────────────────────
        A ∧ᶠ B

where `[nat]` is the *term-variable* context `Γ`. Hypotheses are listed most-recent-*last*.

An unnamed position — `names` shorter than `Δ`, or not a literal list — prints as `_`, so
the renderer never fails on a goal a tactic has not yet labelled.
-/

namespace Metatheorems
namespace ProofMode

open Lean

variable {ι κ : Type} {F : κ → Ty ι}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- `Seq` together with display names for the hypothesis positions.

Reducible, hence interchangeable with `Seq` for every purpose except printing. -/
@[reducible] def SeqD (_names : List String) (F : κ → Ty ι)
    (a : Allowed) (Premises : PremiseSet F) {Γ : Ctx ι}
    (Δ : HCtx F Γ) (B : Formula F Γ) : Type :=
  Seq F a Premises Δ B

/-- Forget the names. Definitionally the identity. -/
def SeqD.toSeq {names : List String} {Δ : HCtx F Γ} {B : Formula F Γ} :
    SeqD names F a Premises Δ B → Seq F a Premises Δ B := id

/-- Attach names. Definitionally the identity. -/
def SeqD.ofSeq {names : List String} {Δ : HCtx F Γ} {B : Formula F Γ} :
    Seq F a Premises Δ B → SeqD names F a Premises Δ B := id

-- Syntax

/-- A rendered proof-mode goal. Display only — this never elaborates. -/
syntax (name := pmGoal)
  "⟪" term ("," ppSpace term " : " term)* "⟫"
    ppIndent((ppLine ident " : " term)* ppLine "────────────────────" ppLine term) : term

-- Delaborator

section Delab
open Lean.PrettyPrinter.Delaborator

/-- Weakening a formula, under the rule in `Pretty.delabWeakening`. (It lives here rather
than in `Pretty.lean` because `Formula.weakenBy` is declared in `Derivable.lean`.) -/
@[app_delab Metatheorems.Formula.weakenBy]
def delabFormulaWeakenBy : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 6)
  Pretty.delabWeakening args[5]!

/-- Split an expression that is a literal `List` spine into its elements. -/
partial def listLit? (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, x, xs]) => (listLit? xs).map (x :: ·)
  | _ => none

/-- Split a `List` spine, reducing as it goes. -/
partial def whnfListLit? (e : Expr) : MetaM (Option (List Expr)) := do
  match (← Lean.Meta.whnf e).getAppFnArgs with
  | (``List.nil, _) => return some []
  | (``List.cons, #[_, x, xs]) =>
      match ← whnfListLit? xs with
      | some r => return some (x :: r)
      | none => return none
  | _ => return none

/-- The `String` behind a string-literal expression. -/
def strLit? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Render `SeqD names F a Premises Δ B` as a proof-mode box.

Fails (falling back to the default application delaborator) only when `Δ` is not a literal
list — there is nothing sensible to draw in that case. -/
@[app_delab Metatheorems.ProofMode.SeqD]
def delabSeqD : Delab := do
  let e ← SubExpr.getExpr
  let args := e.getAppArgs
  -- ι, κ, names, F, a, Premises, Γ, Δ, B
  guard (args.size == 9)
  -- `∀`-introduction leaves `Δ` as `Δ.map (weakenBy ρ)`, so the spine has to be reduced
  -- rather than matched syntactically.
  let some hyps ← whnfListLit? args[7]! | failure
  let names : List String :=
    (listLit? args[2]!).map (·.filterMap strLit?) |>.getD []
  -- The term context: its explicit prefix is shown as named binders, under the same naming
  -- scheme the term printer uses, and its (usually abstract) tail as itself.
  let (tail, tys) := Pretty.ctxSplit args[6]!
  let tailStx ← Lean.PrettyPrinter.delab tail
  -- Outermost-first, under the same naming the term printer uses.
  let tvs : Array (TSyntax `term) := Pretty.ctxVarIdents 0 0 args[6]!
  let tts ← tys.toArray.reverse.mapM fun t => (Lean.PrettyPrinter.delab t : MetaM _)
  let goalStx ← Lean.PrettyPrinter.delab args[8]!
  -- `Δ`'s head is the most recent hypothesis; display oldest-first.
  let hyps := hyps.reverse
  let names := (names ++ List.replicate hyps.length "_").take hyps.length |>.reverse
  let ns : Array Ident := (names.map (mkIdent <| Name.mkSimple ·)).toArray
  let hs ← hyps.toArray.mapM fun h => Lean.PrettyPrinter.delab h
  `(⟪$tailStx $[, $tvs : $tts]*⟫ $[$ns:ident : $hs]* ──────────────────── $goalStx)

end Delab

end ProofMode
end Metatheorems
