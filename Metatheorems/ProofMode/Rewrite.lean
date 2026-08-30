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
with the pattern replaced, and how many occurrences were rewritten. -/
structure Scan where
  /-- `r`, living in the extended context. -/
  abs : Expr
  /-- the original term with `s` replaced by `t`. -/
  rep : Expr
  /-- did the pattern occur? -/
  hit : Bool

/-- Which occurrences to rewrite: all of them, or the `n`-th, counting from 1 across the
whole goal, left to right. -/
inductive Occ
  | all
  | at (n : Nat)
  deriving Inhabited

/-- Scan `e` for `s`, abstracting it to the bound variable of `ρ :: Γ` and replacing it
by `t`.

The comparison is `isDefEq`, not syntactic equality, for two reasons. `Term.app2 add x 0` and
`Term.app (Term.app add x) 0` are the same term written two ways, and a rule applied at `_`
arrives with metavariables that the match has to *solve*. Matching outermost-first and
committing to the first success is what `rw` does. -/
partial def scanTerm (occ : Occ) (seen : IO.Ref Nat) (ι F Γ ρ s t : Expr) (e : Expr) :
    MetaM Scan := do
  let ctx' := mkApp3 (.const ``List.cons [0]) (mkApp (.const ``Ty []) ι) ρ Γ
  if ← isDefEq e s then
    seen.modify (· + 1)
    let count ← seen.get
    let take : Bool := match occ with
      | .all => true
      | .at n => count == n
    if take then
      return { abs := mkAppN (.const ``Term.var []) #[ι, F, ctx', ρ,
                 mkAppN (.const ``Var.vz []) #[ι, ρ, Γ]]
               rep := ← instantiateMVars t, hit := true }
    else
      return ← leaf ι F Γ ρ e
  -- All three application forms have to be descended through. `Term.app2` and `Term.app3`
  -- are abbreviations, but they survive elaboration, and the arithmetic notation produces
  -- them: treating them as leaves silently makes a whole subterm unreachable.
  match e.getAppFnArgs with
  | (``Term.app, args) =>
      if args.size == 7 then
        rebuild ``Term.app args #[3, 4] #[5, 6] ι F Γ ρ s t ctx' e
      else leaf ι F Γ ρ e
  | (``Term.app2, args) =>
      if args.size == 9 then
        rebuild ``Term.app2 args #[3, 4, 5] #[6, 7, 8] ι F Γ ρ s t ctx' e
      else leaf ι F Γ ρ e
  | (``Term.app3, args) =>
      if args.size == 11 then
        rebuild ``Term.app3 args #[3, 4, 5, 6] #[7, 8, 9, 10] ι F Γ ρ s t ctx' e
      else leaf ι F Γ ρ e
  | _ => leaf ι F Γ ρ e
where
  /-- A leaf the pattern does not reach: weaken it, and leave it alone in the replacement. -/
  leaf (ι F Γ ρ e : Expr) : MetaM Scan := do
    let τ := (← instantiateMVars (← inferType e)).getAppArgs[3]!
    return { abs := mkAppN (.const ``Term.weaken []) #[ι, F, Γ, τ, ρ, e]
             rep := e, hit := false }
  /-- Scan the arguments at `argIdx` and rebuild the node, or fall back to a leaf if the
  pattern is nowhere inside. `tyIdx` are the type arguments, which are copied through. -/
  rebuild (c : Name) (args : Array Expr) (tyIdx argIdx : Array Nat)
      (ι F Γ ρ s t ctx' e : Expr) : MetaM Scan := do
    let scans ← argIdx.mapM fun i => scanTerm occ seen ι F Γ ρ s t args[i]!
    if scans.any (·.hit) then
      let tys := tyIdx.map (args[·]!)
      return { abs := mkAppN (.const c []) (#[ι, F, ctx'] ++ tys ++ scans.map (·.abs))
               rep := mkAppN (.const c []) (#[ι, F, Γ] ++ tys ++ scans.map (·.rep))
               hit := true }
    else leaf ι F Γ ρ e

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
private def prwCore (who : String) (occ : Occ) (s t : Expr)
    (mkProof : TSyntax `term → TacticM (TSyntax `term)) : TacticM Unit := do
  let (args, targs) ← eqGoalSides who
  let (ι, F, Γ) := (args[0]!, args[2]!, args[6]!)
  let ρ := mkApp (.const ``Ty.nat []) ι
  -- One counter across both sides, so `at n` numbers occurrences left to right in the goal
  -- as displayed rather than per side.
  let seen ← IO.mkRef 0
  let L ← scanTerm occ seen ι F Γ ρ s t targs[3]!
  let R ← scanTerm occ seen ι F Γ ρ s t targs[4]!
  unless L.hit || R.hit do
    match occ, ← seen.get with
    | .at n, found =>
        throwError "{who}: asked for occurrence {n}, but the pattern occurs {found} time(s) \
          in the goal.\nRewriting{indentExpr s}"
    | .all, _ =>
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

/-- Elaborate a rewrite rule with its context pinned to the goal's.

Pinning by the *expected type* alone does not work: Lean fixes a rule's `Γ` from its first
explicit argument, before unifying the result type. So the context is injected as a named
argument at the head of the application — which is what lets a rule mention `x₀` next to a
term from the outer context, the latter then weakening by coercion.

Rules that are not applications, or whose context implicit is not called `Γ`, fall back to
plain elaboration against the expected type. -/
private partial def unparen (s : Syntax) : Syntax :=
  if s.getKind == ``Lean.Parser.Term.paren then unparen s[1] else s

private def elabRuleInCtx (eStx : TSyntax `term) (Γ expected : Expr) : TacticM Expr := do
  let bare := unparen eStx.raw
  if bare.getKind == ``Lean.Parser.Term.app then
    let ΓStx ← Lean.Elab.Term.exprToSyntax Γ
    let named ← `(Lean.Parser.Term.namedArgument| (Γ := $ΓStx))
    let pinned : TSyntax `term := ⟨Syntax.node2 .none ``Lean.Parser.Term.app bare[0]
      (Syntax.node .none `null (#[named.raw] ++ bare[1].getArgs))⟩
    try
      return ← Lean.Elab.Term.withoutErrToSorry (elabTerm pinned (some expected))
    catch _ => pure ()
  Lean.Elab.Term.withoutErrToSorry (elabTerm eStx (some expected))

/-- The two sides of an equation `s =₀ t`, from the formula expression. -/
private def eqSides (who : String) (what : MessageData) (f : Expr) :
    TacticM (Expr × Expr) := do
  let eq ← whnfD f
  let eqArgs := eq.getAppArgs
  unless eq.isAppOf ``Formula.eq0 && eqArgs.size == 5 do
    throwError "{who}: {what} is not an equation{indentExpr f}"
  return (eqArgs[3]!, eqArgs[4]!)

/-- The optional occurrence selector shared by `prw` and `prwby`. -/
syntax occSel := " at " num

private def readOcc : Option (TSyntax ``occSel) → Occ
  | none => .all
  | some s => .at s.raw[1].toNat

/-- `prw e` rewrites the goal with the closed equation `e : s =₀ t`, on both sides, the way
`rw` does; `prw e at n` rewrites only the `n`-th occurrence, numbered left to right across
the goal. Available in any hypothesis context, since a closed equation needs no premise. -/
elab "prw " eStx:term occ:(occSel)? : tactic => do
  -- The rule is elaborated against the *goal's* context, not in a vacuum. Without that,
  -- nothing pins the rule's `Γ`, and a variable like `x₀` in its arguments has no context to
  -- resolve against — while a term from the outer context needs the weakening coercion.
  let args ← seqDGoalArgs "prw"
  let A ← mkFreshExprMVar (mkAppN (.const ``Formula []) #[args[0]!, args[2]!, args[6]!])
  let expected := mkAppN (.const ``Derivable [])
    #[args[0]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, A]
  -- Pinning `Γ` by the *expected type* is not enough: Lean fixes a rule's `Γ` from its first
  -- explicit argument, before the result type is unified. So the goal's context is supplied
  -- as a named argument, which is what lets a rule mention `x₀` alongside a term from the
  -- outer context — the latter then weakens by coercion. Rules that do not take `Γ` by that
  -- name fall back to plain elaboration.
  let e ← elabRuleInCtx eStx args[6]! expected
  let ety ← instantiateMVars (← inferType e)
  let etyArgs := ety.getAppArgs
  unless ety.isAppOf ``Derivable && etyArgs.size == 7 do
    throwError "prw: not a kernel derivation{indentExpr ety}"
  let (s, t) ← eqSides "prw" m!"`{eStx}`" etyArgs[6]!
  -- The rule goes back as an `Expr`: matching may have solved metavariables in it, and
  -- re-elaborating the source would lose those solutions.
  prwCore "prw" (readOcc occ) s t fun r => do
    let eS ← Lean.Elab.Term.exprToSyntax (← instantiateMVars e)
    `(pm_have (qfer_no_premise_nat_nf $eS (r := $r) (by prw_norm) (by prw_norm)))

/-- `prwby h` rewrites the goal with a *hypothesis* `h : s =₀ t`.

QF-ER carries its premise, and that premise must be quantifier-free and ∨-free — so this is
available exactly when the hypothesis context *is* the premise, that is, when it holds the
one equation. (The matching-logic proof mode draws the same line, from its own side: its
`mlRewriteBy` needs the definedness theory and unrestricted reasoning, where `mlRewrite` does
not.) -/
elab "prwby " h:ident occ:(occSel)? : tactic => do
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
  prwCore "prwby" (readOcc occ) s t fun r =>
    `(qfer_nat_nf (by rfl) (by rfl) (s := $sS) (t := $tS) I_comb
        (r := $r) (by prw_norm) (by prw_norm))

end ProofMode
end Metatheorems
