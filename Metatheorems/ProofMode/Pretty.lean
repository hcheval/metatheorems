/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean
import Metatheorems.Language

/-!
# Printing the object language

Object-level terms and formulas are de Bruijn syntax trees, and printing them as such is
unreadable:

    (Term.add.app x.weaken).app (Term.var Var.vz)

This file makes them print like what they are:

    x₀ + x₁

## Named variables without a name environment

The usual way to print de Bruijn syntax with names is to thread a name stack through the
printer. That is awkward here, because delaborators are dispatched per-constant by Lean and
there is no natural place to keep the stack.

It is also unnecessary. The syntax is *intrinsically typed*: a variable's expression carries
its context, `Var Γ τ`, so the printer can read the context off the term itself. Naming a
variable by its **distance from the end of the context** rather than by its de Bruijn index
then gives names that do not shift when you go under a binder — which is the entire problem
with printing indices.

Concretely, in `ρ₂ :: ρ₁ :: ρ₀ :: Γ` the innermost variable (index 0) prints as `x₂`, and
under one more binder it still prints as `x₂` while the new one becomes `x₃`. Variables
reaching into an abstract tail `Γ` print as `y₀, y₁, …`, indexed from the top of the tail,
which is stable for the same reason.

## Open formulas print applied

A Lean variable `P : Formula F (ρ :: Γ)` is an object-level formula with a free object
variable — a predicate. Printing it as bare `P` hides that, and makes `∀ᶠ x₀ : ρ, P` look as
though the binder were vacuous. It prints as `P x₀`, and `P.subst0 t` prints as `P t`, so a
substitution reads as the application it is.

## Weakening

Weakening an *atom* is invisible: an atom binds nothing, so all its variables are shared with
the ambient context and already carry the ambient names. Weakening a structured formula is
marked `↑ᶜ`, because its own binders are fresh and must be kept clear of the ambient names —
see the two counters below.

These are *generated* names. Names the user chose — `pforall n` — would be better, and would
mean threading a second name list through `SeqD` beside the hypothesis names. That is a
separate change; this one costs no API.
-/

namespace Metatheorems
namespace Pretty

open Lean Lean.PrettyPrinter.Delaborator

/-- How many explicit `::` are on the front of a context expression. The tail may be an
opaque variable, which is exactly the situation inside a proof-mode goal. -/
partial def ctxPrefixLen (e : Expr) : Nat :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, _, t]) => 1 + ctxPrefixLen t
  | _ => 0

private def subscript (n : Nat) : String :=
  if n < 10 then
    String.ofList [Char.ofNat (0x2080 + n)]
  else
    subscript (n / 10) ++ subscript (n % 10)

/-! ### Printing under a weakening

A *weakened* formula was written in a smaller context than the one it is being read in, and
that splits its variables in two:

* its **free** variables are shared with the ambient context — weakening embeds them — so
  they must print with the *same* names they have outside;
* its **bound** variables are fresh, and must not collide with ambient ones.

Distance-from-the-tail alone cannot tell these apart: a binder inside the weakened formula
and an ambient variable introduced *by* the weakening both sit at the same distance from the
shared tail. So two counters are carried: how many weakenings have been crossed (`shift`,
which offsets fresh names out of the way) and how many binders have been crossed since the
last one (`inner`, which says which indices are the fresh ones).

With no weakening in sight both are zero and the whole thing collapses to the plain scheme.
-/

register_option pp.metatheorems.shift : Nat := {
  defValue := 0
  descr := "internal: weakenings crossed while printing object-level syntax"
}

register_option pp.metatheorems.inner : Nat := {
  defValue := 0
  descr := "internal: binders crossed since the last weakening"
}

/-- The current (shift, inner) pair. -/
def getDepths : DelabM (Nat × Nat) := do
  let o ← getOptions
  return (pp.metatheorems.shift.get o, pp.metatheorems.inner.get o)

/-- Print `x` one weakening deeper: fresh names move up, and no binder has been crossed
inside this weakening yet. -/
def withShift (x : DelabM α) : DelabM α := do
  let (s, _) ← getDepths
  withOptions (fun o => (pp.metatheorems.inner.set (pp.metatheorems.shift.set o (s + 1)) 0)) x

/-- Print `x` under one more object-level binder. -/
def withBinder (x : DelabM α) : DelabM α := do
  let (_, i) ← getDepths
  withOptions (pp.metatheorems.inner.set · (i + 1)) x

/-- The display name of the variable at de Bruijn index `i` in context `Γ`.

`i < inner` marks a variable bound *inside* the current weakening: fresh, so offset by
`shift`. Anything else is shared with the ambient context and keeps the ambient name. -/
def varName (shift inner : Nat) (Γ : Expr) (i : Nat) : String :=
  let n := ctxPrefixLen Γ
  if i < n then
    "x" ++ subscript ((if i < inner then shift else 0) + n - 1 - i)
  else
    "y" ++ subscript (i - n)

/-- The de Bruijn index of a `Var` expression. -/
partial def varIndex (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``Var.vz, _) => some 0
  | (``Var.vs, #[_, _, _, _, v]) => (varIndex v).map (· + 1)
  | _ => none

/-- The name a binder over `Γ` should introduce: the variable it binds is index 0 in
`ρ :: Γ`, so its name is fixed by `Γ`'s length. -/
def binderName (shift : Nat) (Γ : Expr) : String :=
  "x" ++ subscript (shift + ctxPrefixLen Γ)

/-- The name of the term variable standing at distance `k` from the end of the explicit
prefix — the same scheme `varName` uses, addressed from the other side. -/
def tvarName (k : Nat) : String := "x" ++ subscript k

/-- Split a context expression into its opaque tail and its explicit prefix,
innermost-first. -/
partial def ctxSplit (e : Expr) : Expr × List Expr :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, x, t]) =>
      let (tail, xs) := ctxSplit t
      (tail, x :: xs)
  | _ => (e, [])

end Pretty

-- ============================================================================
-- Notation for what already has a natural one
-- ============================================================================

namespace Formula

/-- Equality at type `0`. -/
scoped infix:50 " =₀ " => Formula.eq0

end Formula

-- ============================================================================
-- Delaborators
-- ============================================================================

namespace Pretty

open Lean Lean.PrettyPrinter.Delaborator

/-- Object-level binders, `λ`, and quantifiers. Display only. -/
syntax:lead "∀ᶠ " ident " : " term ", " term : term
syntax:lead "∃ᶠ " ident " : " term ", " term : term
syntax:lead "λᶠ " ident " : " term ", " term : term
syntax:max "S" : term
syntax:max "R[" term "]" : term
syntax:max "X[" term "]" : term
syntax:max "↑ᶜ" term:max : term

/-- Types: `nat` and `X i`; the arrow already has notation. -/
@[app_delab Metatheorems.Ty.nat]
def delabTyNat : Delab := do
  guard ((← SubExpr.getExpr).getAppNumArgs == 1)
  return mkIdent `nat

@[app_delab Metatheorems.Ty.base]
def delabTyBase : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 2)
  let i ← Lean.PrettyPrinter.delab args[1]!
  `(X[$i])

/-- The context of an expression that is an object-level formula or term, if it is one. -/
def objCtx? (ty : Expr) : Option Expr :=
  match ty.getAppFnArgs with
  | (``Formula, #[_, _, Γ]) => some Γ
  | (``Term, #[_, _, Γ, _]) => some Γ
  | _ => none

/-- The names of the explicit prefix of a context, outermost-first — under the same
free/bound split `varName` makes: entry `k` is de Bruijn index `n - 1 - k`. -/
def ctxVarIdents (shift inner : Nat) (Γ : Expr) : Array Ident :=
  let n := ctxPrefixLen Γ
  (List.range n).toArray.map fun k =>
    mkIdent (Name.mkSimple (varName shift inner Γ (n - 1 - k)))

/-- **An open formula prints applied to the variables it may mention.**

A Lean variable `P : Formula F (ρ :: Γ)` is an object-level formula with a free object
variable — a *predicate*. Printing it as bare `P` hides that, and makes `∀ᶠ x₀ : ρ, P` look
as though the binder were vacuous. It prints as `P x₀` instead.

This is the one place where the printer looks at an expression's *type* rather than at the
expression: an atom carries no structure to read the dependency off, only its context does.
An atom over a context with no explicit prefix — `x : Term F Γ nat` — is closed as far as
the displayed binders go, and prints bare. -/
@[delab fvar]
def delabOpenAtom : Delab := do
  let e ← SubExpr.getExpr
  let some Γ := objCtx? (← instantiateMVars (← Lean.Meta.inferType e)) | failure
  let (s, i) ← getDepths
  let xs := ctxVarIdents s i Γ
  guard (xs.size > 0)
  let base := mkIdent (← e.fvarId!.getUserName)
  `($base $xs*)

/-- Substituting into an open atom is application: `P.subst0 t` prints as `P t`. -/
@[app_delab Metatheorems.Formula.subst0]
def delabFormulaSubst0 : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  guard args[3]!.isFVar
  let p := mkIdent (← args[3]!.fvarId!.getUserName)
  let t ← Lean.PrettyPrinter.delab args[4]!
  `($p $t)

/-- Likewise in place: `P.substVar0 t` prints as `P t`. This is what makes the induction step
readable — `P x₀ →ᶠ P (S x₀)`. -/
@[app_delab Metatheorems.Formula.substVar0]
def delabFormulaSubstVar0 : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  guard args[3]!.isFVar
  let p := mkIdent (← args[3]!.fvarId!.getUserName)
  let t ← Lean.PrettyPrinter.delab args[4]!
  `($p $t)

/-- Weakening an atom is invisible; weakening anything else is marked `↑ᶜ`, and everything
inside it is named one level deeper.

An atom over a prefix-free context genuinely does not mention the displayed binders, so
dropping the weakening loses nothing. Structured formulas are different: their variables were
written in the *smaller* context, so naming them at the ambient depth would collide them with
the ambient variables. `withShift` moves them out of the way, and `↑ᶜ` says why. -/
def delabWeakening (inner : Expr) : Delab := do
  -- An atom binds nothing, so every variable it mentions is shared with the ambient context
  -- and already prints with the ambient name. Nothing to mark, and nothing to move.
  if inner.isFVar then
    if (objCtx? (← instantiateMVars (← Lean.Meta.inferType inner))).isSome then
      return ← Lean.PrettyPrinter.delab inner
  let i ← withShift (Lean.PrettyPrinter.delab inner : DelabM _)
  `(↑ᶜ$i)

/-- Variables print by name. -/
@[app_delab Metatheorems.Term.var]
def delabTermVar : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let some i := varIndex args[4]! | failure
  let (s, inner) ← getDepths
  return mkIdent (Name.mkSimple (varName s inner args[2]! i))

/-- Flatten an application spine, so `((f a) b) c` and `app2 f a b` both print as `f a b`.

`Term.app2` / `Term.app3` are abbreviations for iterated `Term.app`, but they survive in
elaborated terms, so the printer has to know all three. -/
partial def termSpine (e : Expr) : Expr × Array Expr :=
  match e.getAppFnArgs with
  | (``Term.app, args) =>
      if h : args.size = 7 then
        let (hd, as) := termSpine args[5]
        (hd, as.push args[6])
      else (e, #[])
  | (``Term.app2, args) =>
      if h : args.size = 9 then
        let (hd, as) := termSpine args[6]
        (hd, (as.push args[7]).push args[8])
      else (e, #[])
  | (``Term.app3, args) =>
      if h : args.size = 11 then
        let (hd, as) := termSpine args[7]
        (hd, ((as.push args[8]).push args[9]).push args[10])
      else (e, #[])
  | _ => (e, #[])

/-- Is this expression an application spine the printer knows how to flatten? -/
def isSpine (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``Term.app, args)  => args.size == 7
  | (``Term.app2, args) => args.size == 9
  | (``Term.app3, args) => args.size == 11
  | _ => false

/-- Application prints as juxtaposition. -/
def delabSpine : Delab := do
  let e ← SubExpr.getExpr
  guard (isSpine e)
  let (hd, as) := termSpine e
  let hdS ← Lean.PrettyPrinter.delab hd
  let asS ← as.mapM fun x => (Lean.PrettyPrinter.delab x : MetaM _)
  `($hdS $asS*)

@[app_delab Metatheorems.Term.app]  def delabTermApp : Delab := delabSpine
@[app_delab Metatheorems.Term.app2] def delabTermApp2 : Delab := delabSpine
@[app_delab Metatheorems.Term.app3] def delabTermApp3 : Delab := delabSpine

/-- The numeral, the successor, and the recursor. -/
@[app_delab Metatheorems.Term.zero]
def delabTermZero : Delab := do `(0)

@[app_delab Metatheorems.Term.succ]
def delabTermSucc : Delab := do `(S)

@[app_delab Metatheorems.Term.prec]
def delabTermPrec : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 4)
  let ρ ← Lean.PrettyPrinter.delab args[3]!
  `(R[$ρ])

/-- Weakening, under the rule in `delabWeakening`. -/
@[app_delab Metatheorems.Term.weaken]
def delabTermWeaken : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 6)
  delabWeakening args[5]!

/-- The name a binder over `Γ` introduces, and its body printed one binder deeper. -/
private def delabBinder (Γ ρ body : Expr) :
    DelabM (Ident × TSyntax `term × TSyntax `term) := do
  let (s, _) ← getDepths
  let x := mkIdent (Name.mkSimple (binderName s Γ))
  let ρS ← (Lean.PrettyPrinter.delab ρ : DelabM _)
  let bS ← withBinder (Lean.PrettyPrinter.delab body : DelabM _)
  return (x, ρS, bS)

@[app_delab Metatheorems.Term.lam]
def delabTermLam : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 6)
  let (x, ρ, b) ← delabBinder args[3]! args[2]! args[5]!
  `(λᶠ $x : $ρ, $b)

@[app_delab Metatheorems.Formula.all]
def delabFormulaAll : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let (x, ρ, b) ← delabBinder args[2]! args[3]! args[4]!
  `(∀ᶠ $x : $ρ, $b)

@[app_delab Metatheorems.Formula.ex]
def delabFormulaEx : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let (x, ρ, b) ← delabBinder args[2]! args[3]! args[4]!
  `(∃ᶠ $x : $ρ, $b)

end Pretty
end Metatheorems
