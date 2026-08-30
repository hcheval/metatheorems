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

section QferGeneral
open Formula

variable {ι : Type} {F : ι → Ty ι}
  {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
  {al : Allowed} {Premises : PremiseSet F}

/-- QF-ER at an arbitrary pair of types, with the two `subst0` round-trips given explicitly.

`qfer_nat_nf` is this at `ρ = σ = nat`. The constructor was always general — `Derivable.qfer`
is stated for `eqAtType EqX ρ`/`eqAtType EqX σ` — so nothing here is new metatheory; only the
`_nf` wrappers were specialised. -/
def qfer_at_nf {Γ : Ctx ι} {A₀ : Formula F Γ} {ρ σ : Ty ι}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    {s t : Term F Γ ρ}
    (h : Derivable F EqX al Premises (A₀ →ᶠ eqAtType EqX ρ s t))
    {r : Term F (ρ :: Γ) σ} {rs rt : Term F Γ σ}
    (hs : r.subst0 s = rs) (ht : r.subst0 t = rt) :
    Derivable F EqX al Premises (A₀ →ᶠ eqAtType EqX σ rs rt) :=
  Eq.mp (congrArg (Derivable F EqX al Premises ·)
    (by rw [show r.subst0 s = rs from hs, show r.subst0 t = rt from ht]))
    (Derivable.qfer hqf hvf h)

/-- QF-ER without a premise, at an arbitrary pair of types. -/
def qfer_no_premise_at_nf {Γ : Ctx ι} {ρ σ : Ty ι}
    {s t : Term F Γ ρ} (h : Derivable F EqX al Premises (eqAtType EqX ρ s t))
    {r : Term F (ρ :: Γ) σ} {rs rt : Term F Γ σ}
    (hs : r.subst0 s = rs) (ht : r.subst0 t = rt) :
    Derivable F EqX al Premises (eqAtType EqX σ rs rt) :=
  Eq.mp (congrArg (Derivable F EqX al Premises ·)
    (by rw [show r.subst0 s = rs from hs, show r.subst0 t = rt from ht]))
    (qfer_no_premise h)

end QferGeneral

namespace ProofMode

open Lean Lean.Elab.Tactic Lean.Meta Formula

/-- Normalise a `subst0` round-trip. Theory-independent: the only non-structural step is
undoing a weakening. -/
macro "prw_norm" : tactic =>
  `(tactic| simp only [Formula.subst0, Term.subst0, Term.subst, Term.subst0_map_vz,
      Term.subst0_map_vs, Term.subst_subst0_map_weaken, Term.app2, Term.app3] <;> try rfl)

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
  -- A local abbreviation — `let same_ab := sg_bar (abs_diff sa sb)` in the surrounding term —
  -- is an fvar, not an application, so the structural descent below would call it a leaf and
  -- never look inside. Scan its value instead, and keep the unfolding only if the pattern was
  -- actually in there; otherwise put the abbreviation back, so goals stay readable.
  if e.isFVar then
    if let some v := ((← getLCtx).find? e.fvarId!).bind (·.value?) then
      let before ← seen.get
      let inner ← scanTerm occ seen ι F Γ ρ s t v
      if inner.hit then return inner
      seen.set before
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

/-- An equation, independent of how it was spelled: the type it is at, and its two sides. -/
structure EqShape where
  /-- the `Ty ι` the equation is at -/
  ty : Expr
  lhs : Expr
  rhs : Expr

/-- Recognise an equation in any spelling this development uses.

`eqAtType` is a `def` by recursion on the type, so its normal form differs per type — at
`nat` a `Formula.eq0`, at a base type whatever `EqX` says, at an arrow a `∀`. Only the
*folded* presentation has the sides in fixed positions, so this matches on that first and
only falls back to `whnfD` for the definitions that genuinely unfold to an equation
(`eq_Q`, `eq_R`, `Formula.neg`-style wrappers). -/
private def eqView? (ι eqx : Expr) (f : Expr) : MetaM (Option EqShape) := do
  let check (e : Expr) : MetaM (Option EqShape) := do
    let a := e.getAppArgs
    if e.isAppOf ``Formula.eq0 && a.size == 5 then
      return some ⟨mkApp (.const ``Ty.nat []) ι, a[3]!, a[4]!⟩
    if e.isAppOf ``eqAtType && a.size == 7 then
      return some ⟨a[4]!, a[5]!, a[6]!⟩
    -- `EqX i s t` at a base type: the head is the goal's own `EqX` parameter, which is an
    -- fvar, so there is nothing to unfold and only this comparison can identify it.
    if a.size == 4 && (← isDefEq e.getAppFn eqx) then
      return some ⟨mkApp2 (.const ``Ty.base []) ι a[0]!, a[2]!, a[3]!⟩
    return none
  if let some v ← check f then return some v
  check (← whnfD f)

/-- The goal as an equation. -/
private def eqGoalSides (who : String) : TacticM (Array Expr × EqShape) := do
  let args ← seqDGoalArgs who
  let some v ← eqView? args[0]! args[3]! args[8]! |
    throwError "{who}: the goal is not an equation{indentExpr args[8]!}"
  return (args, v)

/-- Rewrite `s` to `t` throughout an equational goal, given a way to build the QF-ER
congruence proof from the abstraction. Shared by `prw` and `prwby`. -/
private def prwCore (who : String) (occ : Occ) (ρ s t : Expr)
    (mkProof : TSyntax `term → TacticM (TSyntax `term)) : TacticM Unit := do
  let (args, goal) ← eqGoalSides who
  let (ι, F, Γ) := (args[0]!, args[2]!, args[6]!)
  -- The *goal's* type must stay `nat`: the gluing below is `pm_trans`/`pm_sym`, and the
  -- kernel's `.trans0`/`.sym0` are nat-only. At other types transitivity comes from
  -- `eqAtType_trans`, which needs an `AdmissibleEqX` this tactic is not given.
  -- The *pattern's* type `ρ` is unrestricted — QF-ER always was.
  unless goal.ty.isAppOf ``Ty.nat do
    throwError "{who}: the goal is an equation at{indentExpr goal.ty}\nbut rewriting is \
      currently glued by `pm_trans`/`pm_sym`, which the kernel provides only at `nat`. \
      Rewriting a pattern of any type inside a `nat`-valued goal does work."
  -- One counter across both sides, so `at n` numbers occurrences left to right in the goal
  -- as displayed rather than per side.
  let seen ← IO.mkRef 0
  let L ← scanTerm occ seen ι F Γ ρ s t goal.lhs
  let R ← scanTerm occ seen ι F Γ ρ s t goal.rhs
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

/-- The type and two sides of an equation, from the formula expression. Same view as the
goal uses, so a rule may be stated in any of the accepted spellings. -/
private def eqSides (who : String) (what : MessageData) (ι eqx f : Expr) :
    TacticM EqShape := do
  let some v ← eqView? ι eqx f |
    throwError "{who}: {what} is not an equation{indentExpr f}"
  return v

/-- The optional occurrence selector shared by `prw` and `prwby`. -/
syntax occSel := " at " num

private def readOcc : Option (TSyntax ``occSel) → Occ
  | none => .all
  | some s => .at s.raw[1].toNat

/-- Rewrite `s` to `t` inside an equational *hypothesis*, adding the result under `n`.

The same congruence, applied forwards: the hypothesis is threaded between the two sides'
congruences by transitivity. -/
private def prwAtCore (who : String) (occ : Occ) (ρ s t : Expr) (h : Ident) (n : Ident)
    (mkProof : TSyntax `term → TacticM (TSyntax `term)) : TacticM Unit := do
  let args ← seqDGoalArgs who
  let some hyps ← whnfListLit? args[7]! |
    throwError "{who}: the hypothesis context is not a literal list"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  let some i := names.findIdx? (· == h.getId.toString) |
    throwError "{who}: no hypothesis named `{h.getId}` (have: {names})"
  let target ← eqSides who m!"`{h.getId}`" args[0]! args[3]! hyps[i]!
  let (P, Q) := (target.lhs, target.rhs)
  let (ι, F, Γ) := (args[0]!, args[2]!, args[6]!)
  unless target.ty.isAppOf ``Ty.nat do
    throwError "{who}: `{h.getId}` is an equation at{indentExpr target.ty}\nbut the \
      forward form is glued by `pm_rw_at`, which is stated at `nat`."
  let seen ← IO.mkRef 0
  let sP ← scanTerm occ seen ι F Γ ρ s t P
  let sQ ← scanTerm occ seen ι F Γ ρ s t Q
  unless sP.hit || sQ.hit do
    throwError "{who}: the pattern does not occur in `{h.getId}`.\n\
      Rewriting{indentExpr s}\nbut `{h.getId}` is{indentExpr hyps[i]!}"
  let cP ← mkProof (← Lean.Elab.Term.exprToSyntax sP.abs)
  let cQ ← mkProof (← Lean.Elab.Term.exprToSyntax sQ.abs)
  -- The rewritten sides are passed explicitly: they are what the congruences *conclude*, so
  -- leaving them implicit would ask the elaborator to read them back out of the proofs.
  let repP ← Lean.Elab.Term.exprToSyntax sP.rep
  let repQ ← Lean.Elab.Term.exprToSyntax sQ.rep
  let origP ← Lean.Elab.Term.exprToSyntax P
  let origQ ← Lean.Elab.Term.exprToSyntax Q
  evalTactic (← `(tactic|
    refine pm_rw_at $(Lean.quote n.getId.toString)
      (P := $origP) (P' := $repP) (Q := $origQ) (Q' := $repQ)
      $cP $cQ (by pexact $h) ?_))

/-- `prw e` rewrites the goal with the closed equation `e : s =₀ t`, on both sides, the way
`rw` does; `prw e at n` rewrites only the `n`-th occurrence, numbered left to right across
the goal. Available in any hypothesis context, since a closed equation needs no premise. -/
elab "prw " eStx:term occ:(occSel)? : tactic => do
  -- The rule is elaborated against the *goal's* context, not in a vacuum. Without that,
  -- nothing pins the rule's `Γ`, and a variable like `x₀` in its arguments has no context to
  -- resolve against — while a term from the outer context needs the weakening coercion.
  let args ← seqDGoalArgs "prw"
  let e ← elabRuleInCtx eStx args[6]! (← derivableInGoal args)
  let ety ← instantiateMVars (← inferType e)
  let etyArgs := ety.getAppArgs
  unless ety.isAppOf ``Derivable && etyArgs.size == 7 do
    throwError "prw: not a kernel derivation{indentExpr ety}"
  let rule ← eqSides "prw" m!"`{eStx}`" etyArgs[0]! etyArgs[2]! etyArgs[6]!
  -- The rule goes back as an `Expr`: matching may have solved metavariables in it, and
  -- re-elaborating the source would lose those solutions.
  prwCore "prw" (readOcc occ) rule.ty rule.lhs rule.rhs fun r => do
    let eS ← Lean.Elab.Term.exprToSyntax (← instantiateMVars e)
    -- `σ := Ty.nat` has to be given. `eqAtType` matches on its type argument, so with `σ` a
    -- metavariable the conclusion cannot be unified against the goal's `Formula.eq0`.
    `(pm_have (qfer_no_premise_at_nf (σ := Ty.nat) $eS (r := $r) (by prw_norm) (by prw_norm)))

/-- `prwby h` rewrites the goal with a *hypothesis* `h : s =₀ t`.

QF-ER carries a premise, and that premise must be quantifier-free and ∨-free. The premise is
not the hypothesis *context* though — it is the equation itself. So the congruence

    (s =₀ t) →ᶠ (L =₀ L[s := t])

is a **closed** derivation, obtained from QF-ER at `I_comb`, and rewriting by a hypothesis is
that theorem applied to it. The rest of the context can be anything at all, including
non-quantifier-free hypotheses like an induction hypothesis. The only requirement is that
`h`'s own formula is quantifier-free and ∨-free, which is exactly what QF-ER asks. -/
elab "prwby " h:ident occ:(occSel)? : tactic => do
  let args ← seqDGoalArgs "prwby"
  let some hyps ← whnfListLit? args[7]! |
    throwError "prwby: the hypothesis context is not a literal list"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  let n := h.getId.toString
  let some i := names.findIdx? (· == n) |
    throwError "prwby: no hypothesis named `{n}` (have: {names})"
  let rule ← eqSides "prwby" m!"`{h.getId}`" args[0]! args[3]! hyps[i]!
  -- `s` and `t` have to be given: they are fixed by the premise, and the premise proof is
  -- just "the equation implies itself", which says nothing about its shape.
  let sS ← Lean.Elab.Term.exprToSyntax rule.lhs
  let tS ← Lean.Elab.Term.exprToSyntax rule.rhs
  prwCore "prwby" (readOcc occ) rule.ty rule.lhs rule.rhs fun r =>
    `(pm_mp (pm_have (qfer_at_nf (σ := Ty.nat) (by rfl) (by rfl) (s := $sS) (t := $tS) I_comb
        (r := $r) (by prw_norm) (by prw_norm))) (by pexact $h))

/-- `prw e in h with k` rewrites *inside* the equational hypothesis `h`, naming the result
`k`. The goal-directed `prw` proves `L =₀ L[s:=t]` and chains it onto the goal; this proves
the same congruence and threads the hypothesis between the two sides' copies of it. -/
elab "prw " eStx:term " in " h:ident " with " n:ident occ:(occSel)? : tactic => do
  let args ← seqDGoalArgs "prw"
  let e ← elabRuleInCtx eStx args[6]! (← derivableInGoal args)
  let ety ← instantiateMVars (← inferType e)
  let etyArgs := ety.getAppArgs
  unless ety.isAppOf ``Derivable && etyArgs.size == 7 do
    throwError "prw: not a kernel derivation{indentExpr ety}"
  let rule ← eqSides "prw" m!"`{eStx}`" etyArgs[0]! etyArgs[2]! etyArgs[6]!
  prwAtCore "prw" (readOcc occ) rule.ty rule.lhs rule.rhs h n fun r => do
    let eS ← Lean.Elab.Term.exprToSyntax (← instantiateMVars e)
    `(pm_have (qfer_no_premise_at_nf (σ := Ty.nat) $eS (r := $r) (by prw_norm) (by prw_norm)))

/-- `prwby h in k with m` rewrites inside the hypothesis `k` using the equation `h`. -/
elab "prwby " h:ident " in " k:ident " with " n:ident occ:(occSel)? : tactic => do
  let args ← seqDGoalArgs "prwby"
  let some hyps ← whnfListLit? args[7]! |
    throwError "prwby: the hypothesis context is not a literal list"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  let some i := names.findIdx? (· == h.getId.toString) |
    throwError "prwby: no hypothesis named `{h.getId}` (have: {names})"
  let rule ← eqSides "prwby" m!"`{h.getId}`" args[0]! args[3]! hyps[i]!
  let sS ← Lean.Elab.Term.exprToSyntax rule.lhs
  let tS ← Lean.Elab.Term.exprToSyntax rule.rhs
  prwAtCore "prwby" (readOcc occ) rule.ty rule.lhs rule.rhs k n fun r =>
    `(pm_mp (pm_have (qfer_at_nf (σ := Ty.nat) (by rfl) (by rfl) (s := $sS) (t := $tS) I_comb
        (r := $r) (by prw_norm) (by prw_norm))) (by pexact $h))

end ProofMode
end Metatheorems
