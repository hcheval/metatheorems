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

/-- The display name of the variable at de Bruijn index `i` in context `Γ`. -/
def varName (Γ : Expr) (i : Nat) : String :=
  let n := ctxPrefixLen Γ
  if i < n then "x" ++ subscript (n - 1 - i) else "y" ++ subscript (i - n)

/-- The de Bruijn index of a `Var` expression. -/
partial def varIndex (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``Var.vz, _) => some 0
  | (``Var.vs, #[_, _, _, _, v]) => (varIndex v).map (· + 1)
  | _ => none

/-- The name a binder over `Γ` should introduce: the variable it binds is index 0 in
`ρ :: Γ`, so its name is fixed by `Γ`'s length. -/
def binderName (Γ : Expr) : String := "x" ++ subscript (ctxPrefixLen Γ)

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

/-- Variables print by name. -/
@[app_delab Metatheorems.Term.var]
def delabTermVar : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let some i := varIndex args[4]! | failure
  return mkIdent (Name.mkSimple (varName args[2]! i))

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

/-- Weakening is invisible: it is the same term, read in a larger context. -/
@[app_delab Metatheorems.Term.weaken]
def delabTermWeaken : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 6)
  Lean.PrettyPrinter.delab args[5]!

@[app_delab Metatheorems.Term.lam]
def delabTermLam : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 6)
  let x := mkIdent (Name.mkSimple (binderName args[3]!))
  let ρ ← Lean.PrettyPrinter.delab args[2]!
  let b ← Lean.PrettyPrinter.delab args[5]!
  `(λᶠ $x : $ρ, $b)

@[app_delab Metatheorems.Formula.all]
def delabFormulaAll : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let x := mkIdent (Name.mkSimple (binderName args[2]!))
  let ρ ← Lean.PrettyPrinter.delab args[3]!
  let b ← Lean.PrettyPrinter.delab args[4]!
  `(∀ᶠ $x : $ρ, $b)

@[app_delab Metatheorems.Formula.ex]
def delabFormulaEx : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  guard (args.size == 5)
  let x := mkIdent (Name.mkSimple (binderName args[2]!))
  let ρ ← Lean.PrettyPrinter.delab args[3]!
  let b ← Lean.PrettyPrinter.delab args[4]!
  `(∃ᶠ $x : $ρ, $b)

end Pretty
end Metatheorems
