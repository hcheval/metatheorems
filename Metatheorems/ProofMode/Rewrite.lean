/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Arithmetic
import Metatheorems.ProofMode.Tactics

/-!
# Rewriting

There is no `rw` for the object logic in general, and there cannot be: the system is *weakly*
extensional, so equals may not be substituted for equals inside an arbitrary formula. What
there is instead is QF-ER, which says exactly

    from `s =₀ t` conclude `r[s] =₀ r[t]`   for any term abstraction `r`

— congruence for *terms*, which is all an equational rewrite needs. `prw` is built on that.

## How the abstraction is found

`Derivable.qfer` takes the abstraction `r : Term F (nat :: Γ) σ` as an argument, so the work
is finding it: given the goal's side `L` and the pattern `s`, produce `r` with the
occurrences of `s` replaced by the bound variable and every other leaf weakened. One
traversal computes that and the rewritten side `L[s := t]` at once.

The `subst0` round-trip proofs are not `rfl` — a weakened leaf only comes back by
`Term.subst_subst0_map_weaken` — but they need exactly that one lemma plus the structural
unfolding of `Term.subst`, with nothing theory-specific. `prw_norm` is that simp call.

## The two cases

Rewriting by a **closed** equation goes through `qfer_no_premise` and works in any hypothesis
context. Rewriting by a **hypothesis** needs the premise form of QF-ER, whose premise must be
quantifier-free and ∨-free — so it is available only when the hypothesis context *is* that
premise, i.e. holds one formula. This is the same split the matching-logic proof mode makes
between `mlRewrite` and `mlRewriteBy`, arrived at from a different restriction.
-/

namespace Metatheorems
namespace ProofMode

open Lean Lean.Elab.Tactic Lean.Meta Formula

/-- Normalise a `subst0` round-trip. Theory-independent: the only non-structural step is
undoing a weakening. -/
macro "prw_norm" : tactic =>
  `(tactic| simp only [Formula.subst0, Term.subst0, Term.subst, Term.subst0_map_vz,
      Term.subst0_map_vs, Term.subst_subst0_map_weaken, Term.app2, Term.app3])

section Build
variable {ι : Type}

/-- The result of scanning a term for a pattern: the abstraction to hand to QF-ER, the term
with the pattern replaced, and whether the pattern occurred at all. -/
structure Scan where
  /-- `r`, living in the extended context. -/
  abs : Expr
  /-- the original term with `s` replaced by `t`. -/
  rep : Expr
  /-- did the pattern occur? -/
  hit : Bool

/-- Scan `e` for `s`, abstracting it to the bound variable of `ρ :: Γ` and replacing it
by `t`.

The comparison is `isDefEq`, not syntactic equality, for two reasons. `Term.app2 add x 0` and
`Term.app (Term.app add x) 0` are the same term written two ways, and a rule applied at `_`
arrives with metavariables that the match has to *solve*. Matching outermost-first and
committing to the first success is what `rw` does. -/
partial def scanTerm (ι F Γ ρ s t : Expr) (e : Expr) : MetaM Scan := do
  let ctx' := mkApp3 (.const ``List.cons [0]) (mkApp (.const ``Ty []) ι) ρ Γ
  if ← isDefEq e s then
    return { abs := mkAppN (.const ``Term.var []) #[ι, F, ctx', ρ,
               mkAppN (.const ``Var.vz []) #[ι, ρ, Γ]]
             rep := ← instantiateMVars t, hit := true }
  match e.getAppFnArgs with
  | (``Term.app, args) =>
      if h : args.size = 7 then
        let f ← scanTerm ι F Γ ρ s t args[5]
        let x ← scanTerm ι F Γ ρ s t args[6]
        if f.hit || x.hit then
          return { abs := mkAppN (.const ``Term.app [])
                     #[ι, F, ctx', args[3], args[4], f.abs, x.abs]
                   rep := mkAppN (.const ``Term.app [])
                     #[ι, F, Γ, args[3], args[4], f.rep, x.rep]
                   hit := true }
        else leaf ι F Γ ρ e
      else leaf ι F Γ ρ e
  | _ => leaf ι F Γ ρ e
where
  /-- A leaf the pattern does not reach: weaken it, and leave it alone in the replacement. -/
  leaf (ι F Γ ρ e : Expr) : MetaM Scan := do
    let τ := (← instantiateMVars (← inferType e)).getAppArgs[3]!
    return { abs := mkAppN (.const ``Term.weaken []) #[ι, F, Γ, τ, ρ, e]
             rep := e, hit := false }

end Build

/-- The two sides of an equational goal. -/
private def eqGoalSides (who : String) : TacticM (Array Expr × Array Expr) := do
  let args ← seqDGoalArgs who
  let target ← whnfD args[8]!
  let targs := target.getAppArgs
  unless target.isAppOf ``Formula.eq0 && targs.size == 5 do
    throwError "{who}: the goal is not an equation{indentExpr args[8]!}"
  return (args, targs)

/-- Rewrite `s` to `t` throughout an equational goal, given a way to build the QF-ER
congruence proof from the abstraction. Shared by `prw` and `prwby`. -/
private def prwCore (who : String) (s t : Expr)
    (mkProof : TSyntax `term → TacticM (TSyntax `term)) : TacticM Unit := do
  let (args, targs) ← eqGoalSides who
  let (ι, F, Γ) := (args[0]!, args[2]!, args[6]!)
  let ρ := mkApp (.const ``Ty.nat []) ι
  let L ← scanTerm ι F Γ ρ s t targs[3]!
  let R ← scanTerm ι F Γ ρ s t targs[4]!
  unless L.hit || R.hit do
    throwError "{who}: the pattern does not occur in the goal.\n\
      Rewriting{indentExpr s}\nbut the goal is{indentExpr args[8]!}"
  -- `qfer` gives `L =₀ L[s:=t]` and `R =₀ R[s:=t]`; transitivity glues them to the goal.
  -- The abstraction is built, not written, so it goes back as an `Expr` rather than through
  -- the pretty printer: the display layer prints `Term.weaken` as `↑ᶜ`, which does not
  -- elaborate — deliberately, it is display-only.
  let hL ← mkProof (← Lean.Elab.Term.exprToSyntax L.abs)
  let hR ← mkProof (← Lean.Elab.Term.exprToSyntax R.abs)
  let repL ← Lean.Elab.Term.exprToSyntax L.rep
  let repR ← Lean.Elab.Term.exprToSyntax R.rep
  evalTactic (← `(tactic|
    refine pm_trans $repL $hL (pm_trans $repR ?_ (pm_sym $hR))))

/-- The two sides of an equation `s =₀ t`, from the formula expression. -/
private def eqSides (who : String) (what : MessageData) (f : Expr) :
    TacticM (Expr × Expr) := do
  let eq ← whnfD f
  let eqArgs := eq.getAppArgs
  unless eq.isAppOf ``Formula.eq0 && eqArgs.size == 5 do
    throwError "{who}: {what} is not an equation{indentExpr f}"
  return (eqArgs[3]!, eqArgs[4]!)

/-- `prw e` rewrites the goal with the closed equation `e : s =₀ t`, on both sides, the way
`rw` does. Available in any hypothesis context, since a closed equation needs no premise. -/
elab "prw " eStx:term : tactic => do
  let e ← elabTerm eStx none
  let ety ← instantiateMVars (← inferType e)
  let etyArgs := ety.getAppArgs
  unless ety.isAppOf ``Derivable && etyArgs.size == 7 do
    throwError "prw: not a kernel derivation{indentExpr ety}"
  let (s, t) ← eqSides "prw" m!"`{eStx}`" etyArgs[6]!
  -- The rule goes back as an `Expr`: matching may have solved metavariables in it, and
  -- re-elaborating the source would lose those solutions.
  prwCore "prw" s t fun r => do
    let eS ← Lean.Elab.Term.exprToSyntax (← instantiateMVars e)
    `(pm_have (qfer_no_premise_nat_nf $eS (r := $r) (by prw_norm) (by prw_norm)))

/-- `prwby h` rewrites the goal with a *hypothesis* `h : s =₀ t`.

QF-ER carries its premise, and that premise must be quantifier-free and ∨-free — so this is
available exactly when the hypothesis context *is* the premise, that is, when it holds the
one equation. (The matching-logic proof mode draws the same line, from its own side: its
`mlRewriteBy` needs the definedness theory and unrestricted reasoning, where `mlRewrite` does
not.) -/
elab "prwby " h:ident : tactic => do
  let args ← seqDGoalArgs "prwby"
  let some hyps ← whnfListLit? args[7]! |
    throwError "prwby: the hypothesis context is not a literal list"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  let n := h.getId.toString
  unless names == [n] do
    throwError "prwby: rewriting by a hypothesis needs the hypothesis context to be exactly \
      `{n}`,\nbecause QF-ER carries its premise and that premise is the context. \
      Here it is {names}.\nClear the others, or use a closed equation with `prw`."
  let (s, t) ← eqSides "prwby" m!"`{h.getId}`" hyps[0]!
  -- `s` and `t` have to be given: they are fixed by the *premise*, and the premise proof is
  -- just "the hypothesis is itself", which says nothing about its shape.
  let sS ← Lean.Elab.Term.exprToSyntax s
  let tS ← Lean.Elab.Term.exprToSyntax t
  -- The premise proof is `A₀ →ᶠ A₀`, since the premise *is* the equation being rewritten by.
  prwCore "prwby" s t fun r =>
    `(qfer_nat_nf (by rfl) (by rfl) (s := $sS) (t := $tS) I_comb
        (r := $r) (by prw_norm) (by prw_norm))

end ProofMode
end Metatheorems
