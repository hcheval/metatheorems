/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo

/-!
# Hand-written monotone realizers of the `¬¬`-combinators (MFI Lane C, "hand-write what dominates")

The fused recursion `monotone_nd_soundness` (`MonotoneND.lean`) applies a handful of closed
propositional combinators at every node of a classical derivation. On the gate derivation
(`LemBoundDemo.lFinalNoLem` prenexified, 363 constructors) the profile is: 134 `syllogism`
(each `neg_neg_mp` ×2, `K_comb`, `S_comb`, `neg_neg_imp_rev2`), 34 `exportation`, 30
`importation`, 11 `forall_rule` (each `neg_neg_mp`, `dnn_intro` ×2, `neg_neg_imp_rev`), 4
`expansion`, 2 `lem`, plus ~120 propositional axioms each wrapped in `dnn_intro`. Realizing
those combinators as leaves — `ofSRealizer ∘ syntactic_soundness`, i.e. the TERM route on a
fixed ~100-node Hilbert derivation, several times per node — is what made the classical
bound's kernel reduction a 12 GB `std::bad_alloc`. This module replaces them.

Each combinator is an `MRealizer cm <its formula>` whose **data** is an explicit λ-term at
the hat types and whose existential **realizer** is the same λ-term at the witness types —
written once, polymorphically in the four Lean types `WA CA WB CB` (`Ty.interpret` of a `wTy`
is definitionally the product/function type the clauses of `wTy` say), so the two coincide
syntactically and the majorization proof is purely structural. `maj_auto` below discharges
those: a *syntactic dispatcher* on the goal (`Prod.mk` → `prod_intro`, projection →
`prod_fst/snd`, `fun` → `arrow_intro` + intro, application → `app_compat`, `()` → `unit_maj`,
`maxT` → `maxT_selfMaj`), no search, no `isDefEq` beyond `assumption` at the leaves. The
`if`-realizers (`nnImpRevF`, `dnnLemF`) are the two combinators whose Hilbert proof uses a
hypothesis twice (contraction): the realizer branches on the decidable matrix, the majorant is
the `maxT` of the two branches — `MRealizer.andContract`'s pattern.

| combinator | here | case split |
|---|---|---|
| `dnn_intro : A → ¬¬A` | `dnnIntroF` | no |
| `neg_neg_mp : ¬¬(A→B) → ¬¬A → ¬¬B` | `nnMpF` | no |
| `neg_neg_imp_rev : (A → ¬¬B) → ¬¬(A→B)` | `nnImpRevF` | yes (`maxT`) |
| `neg_neg_imp_rev2`, `K_comb`, `S_comb` | eliminated: `syllogism` composes `MRealizer.syllogism`, `dnnIntroF`, `nnImpRevF` |
| `exp_form : (A∧B→C) → (A→B→C)` | `expF` | no |
| `imp_form : (A→B→C) → (A∧B→C)` | `impF` | no |
| `expansion_form : (A→B) → (C∨A→C∨B)` | `expansionF` | no (flag copied) |
| `dnn_lem : ¬¬(A ∨ ¬A)` | `dnnLemF` | yes (`maxT`, flag by `flagM`-style `maxT`) |
| `nn_all_nn : ¬¬∀x¬¬Q → ∀x¬¬Q` | assembled in `MonotoneND.lean` from the above |
-/

namespace Metatheorems

open Formula

-- ============================================================================
-- Field aliases with all arguments implicit (Monotone.lean's are module-private)
-- ============================================================================

section Helpers

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

theorem ndl_mapp {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)} {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (hf : am.maj (ρ →ₜ τ) f_star f) (hx : am.maj ρ x_star x) :
    am.maj τ (f_star x_star) (f x) :=
  am.app_compat _ _ _ _ hf hx

theorem ndl_mfst {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj ρ p_star.1 p.1 :=
  am.prod_fst _ _ h

theorem ndl_msnd {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj τ p_star.2 p.2 :=
  am.prod_snd _ _ h

theorem ndl_mpair {ρ τ : Ty ι} {a_star : Ty.interpret X ρ.hat} {a : Ty.interpret X ρ}
    {b_star : Ty.interpret X τ.hat} {b : Ty.interpret X τ}
    (ha : am.maj ρ a_star a) (hb : am.maj τ b_star b) :
    am.maj (ρ ×ₜ τ) (a_star, b_star) (a, b) :=
  am.prod_intro _ _ ha hb

theorem ndl_marr {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)}
    (h₁ : ∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
      am.maj ρ x_star x → am.maj τ (f_star x_star) (f x))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat),
      am.selfMaj ρ x y → am.selfMaj τ (f_star x) (f_star y)) :
    am.maj (ρ →ₜ τ) f_star f :=
  am.arrow_intro _ _ h₁ h₂

theorem ndl_sapp {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    {x y : Ty.interpret X ρ.hat} (hf : am.selfMaj (ρ →ₜ τ) f g) (hx : am.selfMaj ρ x y) :
    am.selfMaj τ (f x) (g y) :=
  am.selfMaj_app hf hx

theorem ndl_sfst {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj ρ p.1 q.1 :=
  am.selfMaj_prod_fst _ _ h

theorem ndl_ssnd {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj τ p.2 q.2 :=
  am.selfMaj_prod_snd _ _ h

theorem ndl_spair {ρ τ : Ty ι} {a b : Ty.interpret X ρ.hat} {c d : Ty.interpret X τ.hat}
    (h₁ : am.selfMaj ρ a b) (h₂ : am.selfMaj τ c d) :
    am.selfMaj (ρ ×ₜ τ) (a, c) (b, d) :=
  am.selfMaj_prod_intro _ _ h₁ h₂

theorem ndl_sarr {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    (h₁ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (g y))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (f y)) :
    am.selfMaj (ρ →ₜ τ) f g :=
  am.selfMaj_arrow_intro _ _ h₁ h₂

theorem ndl_mself {ρ : Ty ι} {a : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (h : am.maj ρ a x) : am.selfMaj ρ a a :=
  am.maj_selfMaj h

theorem ndl_sself {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} (h : am.selfMaj ρ a b) :
    am.selfMaj ρ a a :=
  am.selfMaj_self h

theorem ndl_munit : am.maj Ty.unit () () := am.unit_maj

theorem ndl_sunit : am.selfMaj Ty.unit () () := am.maj_selfMaj am.unit_maj

theorem ndl_smax {ρ : Ty ι} {a b c d : Ty.interpret X ρ.hat}
    (h₁ : am.selfMaj ρ a b) (h₂ : am.selfMaj ρ c d) :
    am.selfMaj ρ (maxT ρ a c) (maxT ρ b d) :=
  am.maxT_selfMaj h₁ h₂

end Helpers

-- ============================================================================
-- `maj_auto`: a syntactic dispatcher for structural majorization goals
-- ============================================================================

/-- `maj_auto`: see `majStep`. Declared before the dispatcher so the `maxT`/`ite` step can
recurse into it. -/
syntax (name := majAutoStx) "maj_auto" : tactic

open Lean Meta Elab Tactic in
/-- The object type `σ` of a hat-side expression: its inferred type is `Ty.interpret X σ.hat`
(the wrapper survives projections and applications, since `Ty.interpret`/`Ty.hat` unfold
structurally), and `whnf σ` exposes the `prod`/`arr` the dispatcher needs — Lean's unifier
cannot invert `Ty.hat` on its own, which is why `refine ndl_mfst ?_` alone stalls. -/
private partial def tyOfLean (ι : Expr) (t : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  match t.getAppFnArgs with
  | (``Ty.interpret, #[_, _, σh]) =>
    match σh.getAppFnArgs with
    | (``Ty.hat, #[_, σ]) => return some σ
    | _ => return none
  | (``Unit, #[]) => return some (mkApp (mkConst ``Ty.unit) ι)
  | (``PUnit, #[_]) => return some (mkApp (mkConst ``Ty.unit) ι)
  | (``Nat, #[]) => return some (mkApp (mkConst ``Ty.nat) ι)
  | (``Prod, #[l, r]) =>
    let some σl ← tyOfLean ι l | return none
    let some σr ← tyOfLean ι r | return none
    return some (mkApp3 (mkConst ``Ty.prod) ι σl σr)
  | _ =>
    match t with
    | .forallE _ d c _ =>
      if c.hasLooseBVars then return none
      let some σd ← tyOfLean ι d | return none
      let some σc ← tyOfLean ι c | return none
      return some (mkApp3 (mkConst ``Ty.arr) ι σd σc)
    | _ =>
      -- an abbreviation (`NW`, `IW`, …): unfold one reducible step and retry
      if fuel == 0 then return none
      let t' ← whnfR t
      if t' == t then return none
      tyOfLean ι t' (fuel - 1)

open Lean Meta Elab Tactic in
private def hatTyOf (ι : Expr) (e : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars (← inferType e)
  match ← tyOfLean ι t with
  | some σ => return some (← whnf σ)
  | none => return none

open Lean Meta Elab Tactic in
/-- One dispatch step on the main goal. Returns `false` when the goal is not one it handles. -/
private partial def majStep : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    if t.isForall then
      evalTactic (← `(tactic| intro _)); return true
    -- an `if` on the realizer side against a `maxT` majorant: split, then `maxT_maj_left/right`
    let t' := t.consumeMData
    let fn := t'.getAppFn
    let args := t'.getAppArgs
    unless fn.isConst && args.size == 9 do return false
    let isMaj := fn.constName! == ``AbstractMajorizability.maj
    let isSelf := fn.constName! == ``AbstractMajorizability.selfMaj
    unless isMaj || isSelf do return false
    let a := (args[7]!).headBeta
    let b := (args[8]!).headBeta
    let run (tac : TSyntax `tactic) : TacticM Bool := do
      try evalTactic tac; return true catch _ => return false
    -- hypotheses the leaf rules need: `hn : n ≥ am.N`, `henv : MajEnv …`, `he : SelfMajEnv …`
    let findHyp (hd : Name) : TacticM (Option Expr) := do
      for h in ← getLCtx do
        if h.isImplementationDetail then continue
        if (← instantiateMVars h.type).isAppOf hd then return some (mkFVar h.fvarId)
      return none
    -- the majorant of a closed default term: `termMajorizer_maj`
    if a.isAppOf ``termMajorizer then
      let some hn ← findHyp ``GE.ge | return false
      let hnS ← Term.exprToSyntax hn
      if isMaj then
        let some henv ← findHyp ``MajEnv | return false
        let heS ← Term.exprToSyntax henv
        return ← run (← `(tactic| exact (termMajorizer_maj _ _ _ $hnS).1 _ _ $heS))
      else
        if let some he ← findHyp ``SelfMajEnv then
          let heS ← Term.exprToSyntax he
          if ← run (← `(tactic| exact (termMajorizer_maj _ _ _ $hnS).2 _ _ $heS)) then return true
          if ← run (← `(tactic| exact (termMajorizer_maj _ _ _ $hnS).2 _ _
              (SelfMajEnv.self _ $heS))) then return true
        if let some henv ← findHyp ``MajEnv then
          let heS ← Term.exprToSyntax henv
          return ← run (← `(tactic| exact (termMajorizer_maj _ _ _ $hnS).2 _ _
              (MajEnv.toSelfMajEnv _ $heS)))
        return false
    -- the flag majorants `zeroM n` (of `0`) and `succM n (zeroM n)` (of `1`)
    if a.isAppOf ``ConstMajorants.zeroM || a.isAppOf ``ConstMajorants.succM then
      let some hn ← findHyp ``GE.ge | return false
      let hnS ← Term.exprToSyntax hn
      let isZ := a.isAppOf ``ConstMajorants.zeroM
      return ← run (← match isMaj, isZ with
        | true, true => `(tactic| exact ConstMajorants.zeroM_maj _ _ $hnS)
        | true, false => `(tactic| exact ndl_mapp (ConstMajorants.succM_maj _ _ $hnS)
            (ConstMajorants.zeroM_maj _ _ $hnS))
        | false, true => `(tactic| exact ndl_mself (ConstMajorants.zeroM_maj _ _ $hnS))
        | false, false => `(tactic| exact ndl_mself (ndl_mapp (ConstMajorants.succM_maj _ _ $hnS)
            (ConstMajorants.zeroM_maj _ _ $hnS))))
    -- the opaque realizer helpers, each with its own majorization / self-majorization lemma
    let helpers : List (Name × Name × Name × Nat) :=
      [(`Metatheorems.chiA, `Metatheorems.chiA_maj, `Metatheorems.chiA_self, 3),
       (`Metatheorems.chiAT, `Metatheorems.chiA_maj, `Metatheorems.chiA_self, 3),
       (`Metatheorems.phiI, `Metatheorems.phiI_maj, `Metatheorems.phiI_self, 2),
       (`Metatheorems.phiIT, `Metatheorems.phiI_maj, `Metatheorems.phiI_self, 2),
       (`Metatheorems.constNB, `Metatheorems.constNB_maj, `Metatheorems.constNB_self, 1),
       (`Metatheorems.qB, `Metatheorems.qB_maj, `Metatheorems.qB_self, 2),
       (`Metatheorems.psiA, `Metatheorems.psiA_maj, `Metatheorems.psiA_self, 2),
       (`Metatheorems.pPrime, `Metatheorems.pPrime_maj, `Metatheorems.pPrime_self, 3),
       (`Metatheorems.lemNa, `Metatheorems.lemNa_maj, `Metatheorems.lemNa_self, 3),
       (`Metatheorems.lemW1, `Metatheorems.lemW1_maj, `Metatheorems.lemW1_self, 5),
       (`Metatheorems.lemA1, `Metatheorems.lemA1_maj, `Metatheorems.lemA1_self, 5),
       (`Metatheorems.lemW2, `Metatheorems.lemW2_maj, `Metatheorems.lemW2_self, 5)]
    if let .const c _ := a.getAppFn then
      if let some (_, lm, ls, n) := helpers.find? (·.1 == c) then
        let id := mkIdent (if isMaj then lm else ls)
        let tac ← match n with
          | 1 => `(tactic| refine $id ?_)
          | 2 => `(tactic| refine $id ?_ ?_)
          | 3 => `(tactic| refine $id ?_ ?_ ?_)
          | _ => `(tactic| refine $id ?_ ?_ ?_ ?_ ?_)
        return ← run tac
    -- realizer-side `if` against a `maxT` majorant
    if isMaj && a.isAppOfArity ``maxT 5 && b.isAppOfArity ``ite 5 then
      return ← run (← `(tactic| split))
    if isMaj && a.isAppOfArity ``maxT 5 then
      -- after the `split`: `maj (maxT p q) x` with `x` one of the two branches — pick the
      -- side whose head symbol matches (a nested `by maj_auto` inside `first` would not
      -- backtrack: an unsolved nested `by` logs and inserts `sorry` instead of throwing)
      let p := (a.getAppArgs)[3]!
      let sameHead := p.getAppFn == b.getAppFn
      return ← run (← if sameHead
        then `(tactic| refine AbstractMajorizability.maxT_maj_left _ ?_ ?_)
        else `(tactic| refine AbstractMajorizability.maxT_maj_right _ ?_ ?_))
    if a.isLambda then
      return ← run (← if isMaj then `(tactic| refine ndl_marr ?_ ?_)
                               else `(tactic| refine ndl_sarr ?_ ?_))
    if a.isAppOfArity ``Prod.mk 4 then
      return ← run (← if isMaj then `(tactic| refine ndl_mpair ?_ ?_)
                               else `(tactic| refine ndl_spair ?_ ?_))
    let ιe := args[0]!
    -- projections come both as `Prod.fst p` applications and as primitive `Expr.proj` nodes
    let projOf (e : Expr) : Option (Bool × Expr) :=
      if e.isAppOfArity ``Prod.fst 3 then some (true, e.appArg!)
      else if e.isAppOfArity ``Prod.snd 3 then some (false, e.appArg!)
      else match e with
        | .proj ``Prod 0 p => some (true, p)
        | .proj ``Prod 1 p => some (false, p)
        | _ => none
    if let some (isFst, p) := projOf a then
      let some σ ← hatTyOf ιe p | return false
      let (``Ty.prod, #[_, ρ', τ']) := σ.getAppFnArgs | return false
      let ρs ← Term.exprToSyntax ρ'
      let τs ← Term.exprToSyntax τ'
      if isFst then
        return ← run (← if isMaj then `(tactic| refine ndl_mfst (ρ := $ρs) (τ := $τs) ?_)
                                 else `(tactic| refine ndl_sfst (ρ := $ρs) (τ := $τs) ?_))
      else
        return ← run (← if isMaj then `(tactic| refine ndl_msnd (ρ := $ρs) (τ := $τs) ?_)
                                 else `(tactic| refine ndl_ssnd (ρ := $ρs) (τ := $τs) ?_))
    if isSelf && a.isAppOfArity ``maxT 5 then
      return ← run (← `(tactic| refine ndl_smax ?_ ?_))
    if a.isConstOf ``Unit.unit || a.isConstOf ``PUnit.unit then
      return ← run (← if isMaj then `(tactic| exact ndl_munit)
                               else `(tactic| exact ndl_sunit))
    -- leaves: hypotheses. Find the one whose two SIDES match syntactically, then check its
    -- `Ty` index against the goal's by one defeq (`cTy (¬¬A)` vs `wTy (¬A) ×ₜ cTy ⊥`, a small
    -- structural unfolding). A plain `assumption` runs that defeq against every hypothesis,
    -- unfolding every big `wTy` type with no `whnf` cache (the formulas are free variables).
    let sidesOf (e : Expr) : Option (Bool × Expr × Expr) :=
      let e := e.consumeMData
      let fn := e.getAppFn
      let as := e.getAppArgs
      if fn.isConst && as.size == 9 then
        if fn.constName! == ``AbstractMajorizability.maj then some (true, as[7]!, as[8]!)
        else if fn.constName! == ``AbstractMajorizability.selfMaj then some (false, as[7]!, as[8]!)
        else none
      else none
    for h in ← getLCtx do
      if h.isImplementationDetail then continue
      let ht ← instantiateMVars h.type
      match sidesOf ht with
      | some (hm, ha, hb) =>
        if hm == isMaj && ha == a && hb == b then
          if ← isDefEq ht t' then g.assign (mkFVar h.fvarId); return true
      | none => pure ()
    if isSelf && a == b then
      -- `selfMaj a a` from a `maj a x` or a `selfMaj a b` hypothesis with the same left side
      for h in ← getLCtx do
        if h.isImplementationDetail then continue
        let ht ← instantiateMVars h.type
        match sidesOf ht with
        | some (hm, ha, _) =>
          if ha == a then
            let hs ← Term.exprToSyntax (mkFVar h.fvarId)
            let ok ← run (← if hm then `(tactic| exact ndl_mself $hs)
                                  else `(tactic| exact ndl_sself $hs))
            if ok then return true
        | none => pure ()
    if a.isApp && !(a.isAppOf ``maxT) then
      -- an application: split off the last argument, with the function's `arr` type given
      let some σ ← hatTyOf ιe a.appFn! | return false
      let (``Ty.arr, #[_, ρ', τ']) := σ.getAppFnArgs | return false
      let ρs ← Term.exprToSyntax ρ'
      let τs ← Term.exprToSyntax τ'
      return ← run (← if isMaj then `(tactic| refine ndl_mapp (ρ := $ρs) (τ := $τs) ?_ ?_)
                               else `(tactic| refine ndl_sapp (ρ := $ρs) (τ := $τs) ?_ ?_))
    return false

open Lean Meta Elab Tactic in
/-- Repeatedly dispatch on every goal until no goal moves. Stuck goals are left for the caller. -/
private partial def majGo : TacticM Unit := do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then return
  let mut moved := false
  let mut acc : List MVarId := []
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    let ok ← majStep
    if ok then moved := true
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc
  if moved then majGo

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| maj_auto) => majGo

-- ============================================================================
-- The realizer functions, polymorphic in the witness/counter types
-- ============================================================================

/-! `Ty.interpret X (wTy P)` is definitionally the type built from `Unit`, `×` and `→` by the
clauses of `wTy`, and `Ty.interpret X (wTy P).hat` is the same shape at the hat types. The
functions below are written once at Lean-type parameters and are used at both. -/

section RealizerFunctions

/-- `W(¬A)` for `W A = WA`, `C A = CA`. -/
abbrev NW (WA CA : Type) : Type := (WA → Unit) × (WA → Unit → CA)
/-- `C(¬A)`. -/
abbrev NC (WA : Type) : Type := WA × Unit
/-- `W(¬¬A)`. -/
abbrev NNW (WA CA : Type) : Type := NW (NW WA CA) (NC WA)
/-- `C(¬¬A)`. -/
abbrev NNC (WA CA : Type) : Type := NC (NW WA CA)
/-- `W(A → B)`. -/
abbrev IW (WA CA WB CB : Type) : Type := (WA → WB) × (WA → CB → CA)
/-- `C(A → B)`. -/
abbrev IC (WA CB : Type) : Type := WA × CB

/-- The realizer of `A → ¬¬A`: a witness `a` answers every `¬A`-challenge with `a`; the
counter for `A` is what the challenge asks of `a`. -/
def dnnFun {WA CA : Type} : IW WA CA (NNW WA CA) (NNC WA CA) :=
  (fun a => (fun _ => (), fun _ _ => (a, ())), fun a c => c.1.2 a ())

/-- `χ`: the `¬A`-challenge built from an `A → B` witness `(f, g)` and a `¬B`-challenge `ψ`. -/
def chiA {WA CA WB CB : Type} (f : WA → WB) (g : WA → CB → CA) (ψ : NW WB CB) : NW WA CA :=
  (fun _ => (), fun a _ => g a (ψ.2 (f a) ()))

/-- `φ`: the `¬(A→B)`-challenge built from a `¬¬A`-witness `Ψ` and a `¬B`-challenge `ψ`. -/
def phiI {WA CA WB CB : Type} (Ψ : NNW WA CA) (ψ : NW WB CB) :
    NW (IW WA CA WB CB) (IC WA CB) :=
  (fun _ => (),
   fun p _ => ((Ψ.2 (chiA p.1 p.2 ψ) ()).1, ψ.2 (p.1 ((Ψ.2 (chiA p.1 p.2 ψ) ()).1)) ()))

/-- The realizer of `¬¬(A → B) → (¬¬A → ¬¬B)` (`neg_neg_mp`). -/
def nnMpFun {WA CA WB CB : Type} :
    IW (NNW (IW WA CA WB CB) (IC WA CB)) (NNC (IW WA CA WB CB) (IC WA CB))
       (IW (NNW WA CA) (NNC WA CA) (NNW WB CB) (NNC WB CB))
       (IC (NNW WA CA) (NNC WB CB)) :=
  (fun Φ =>
    (fun Ψ =>
      (fun _ => (),
       fun ψ _ =>
        ((Φ.2 (phiI Ψ ψ) ()).1.1
          ((Ψ.2 (chiA (Φ.2 (phiI Ψ ψ) ()).1.1 (Φ.2 (phiI Ψ ψ) ()).1.2 ψ) ()).1), ())),
     fun Ψ c =>
      (chiA (Φ.2 (phiI Ψ c.1) ()).1.1 (Φ.2 (phiI Ψ c.1) ()).1.2 c.1, ())),
   fun Φ c => (phiI c.1 c.2.1, ()))

/-- `ψ_y`: the constant `¬B`-challenge answering with the counter `y`. -/
def constNB {WB CB : Type} (y : CB) : NW WB CB := (fun _ => (), fun _ _ => y)

/-- `q_b`: the `A → B`-witness answering every `A`-witness with the fixed `b`. -/
def qB {WA CA WB CB : Type} (g : WA → NNC WB CB → CA) (b : WB) : IW WA CA WB CB :=
  (fun _ => b, fun a y => g a (constNB y, ()))

/-- `ψ_φ`: the `¬B`-challenge answering `b` with the counter `φ` gives to `q_b`. -/
def psiA {WA CA WB CB : Type} (g : WA → NNC WB CB → CA)
    (φ : NW (IW WA CA WB CB) (IC WA CB)) : NW WB CB :=
  (fun _ => (), fun b _ => (φ.2 (qB g b) ()).2)

/-- `p'`: the `A → B`-witness obtained from an `A → ¬¬B`-witness `(f, g)` by feeding `f a` the
challenge `ψ_φ`. -/
def pPrime {WA CA WB CB : Type} (f : WA → NNW WB CB) (g : WA → NNC WB CB → CA)
    (φ : NW (IW WA CA WB CB) (IC WA CB)) : IW WA CA WB CB :=
  (fun a => ((f a).2 (psiA g φ) ()).1, fun a _ => g a (psiA g φ, ()))

/-! The pieces of `¬¬(A ∨ ¬A)`'s realizer. `W(A ∨ ¬A) = ℕ × (WA × W¬A)`, `C(A ∨ ¬A) =
CA × (WA × Unit)`, and the `¬(A ∨ ¬A)`-challenge is `φ : NW (ℕ × (WA × NW WA CA)) (CA × (WA × Unit))`.
The flags are parameters (`z` for the left disjunct, `o` for the right), because the majorant
must carry `cm.zeroM n` / `cm.succM n (cm.zeroM n)` where the realizer carries `0` / `1`. -/

/-- `na`: the `¬A`-witness that answers `a` with the counter `φ` gives to the LEFT disjunct
at `a` (with the default `¬A`-witness `dna` in the unused slot). -/
def lemNa {WA CA : Type} (φ : NW (ℕ × (WA × NW WA CA)) (CA × (WA × Unit))) (dna : NW WA CA)
    (z : ℕ) : NW WA CA :=
  (fun _ => (), fun a _ => (φ.2 (z, (a, dna)) ()).1)

/-- `w₁`: the RIGHT-disjunct witness, `na` with the default `A`-witness `da` in the unused slot. -/
def lemW1 {WA CA : Type} (φ : NW (ℕ × (WA × NW WA CA)) (CA × (WA × Unit))) (dna : NW WA CA)
    (da : WA) (o z : ℕ) : ℕ × (WA × NW WA CA) :=
  (o, (da, lemNa φ dna z))

/-- `a₁`: the `A`-witness `φ` challenges `w₁` with. -/
def lemA1 {WA CA : Type} (φ : NW (ℕ × (WA × NW WA CA)) (CA × (WA × Unit))) (dna : NW WA CA)
    (da : WA) (o z : ℕ) : WA :=
  (φ.2 (lemW1 φ dna da o z) ()).2.1

/-- `w₂`: the LEFT-disjunct witness at `a₁`. -/
def lemW2 {WA CA : Type} (φ : NW (ℕ × (WA × NW WA CA)) (CA × (WA × Unit))) (dna : NW WA CA)
    (da : WA) (o z : ℕ) : ℕ × (WA × NW WA CA) :=
  (z, (lemA1 φ dna da o z, dna))

/-- The realizer of exportation `(A ∧ B → C) → (A → B → C)`. -/
def expFun {WA CA WB CB WC CC : Type} :
    IW (IW (WA × WB) (CA × CB) WC CC) (IC (WA × WB) CC)
       (IW WA CA (IW WB CB WC CC) (IC WB CC)) (IC WA (IC WB CC)) :=
  (fun h => (fun a => (fun b => h.1 (a, b), fun b c => (h.2 (a, b) c).2),
             fun a p => (h.2 (a, p.1) p.2).1),
   fun _ c => ((c.1, c.2.1), c.2.2))

/-- The realizer of importation `(A → B → C) → (A ∧ B → C)`. -/
def impFun {WA CA WB CB WC CC : Type} :
    IW (IW WA CA (IW WB CB WC CC) (IC WB CC)) (IC WA (IC WB CC))
       (IW (WA × WB) (CA × CB) WC CC) (IC (WA × WB) CC) :=
  (fun h => (fun p => (h.1 p.1).1 p.2,
             fun p c => (h.2 p.1 (p.2, c), (h.1 p.1).2 p.2 c)),
   fun _ c => (c.1.1, (c.1.2, c.2)))

/-- The realizer of expansion `(A → B) → (C ∨ A → C ∨ B)`; the flag is copied. -/
def expansionFun {WA CA WB CB WC CC : Type} :
    IW (IW WA CA WB CB) (IC WA CB)
       (IW (ℕ × (WC × WA)) (CC × CA) (ℕ × (WC × WB)) (CC × CB)) (IC (ℕ × (WC × WA)) (CC × CB)) :=
  (fun h => (fun x => (x.1, (x.2.1, h.1 x.2.2)),
             fun x y => (y.1, h.2 x.2.2 y.2)),
   fun _ c => (c.1.2.2, c.2.2))

end RealizerFunctions

-- ============================================================================
-- Majorization of the helpers, once each, so the combinators need not unfold them
-- ============================================================================

/-! The object-level types of the helpers' arguments, at `Ty`. `Ty.interpret X (nwT α γ).hat`
is definitionally `NW (Ty.interpret X α.hat) (Ty.interpret X γ.hat)`, so each lemma below is
stated at these `Ty`s and applies verbatim to `wTy`/`cTy` instances after `whnf`. -/

/-- `wTy (¬A)` for `wTy A = α`, `cTy A = γ`. -/
abbrev nwT {ι : Type} (α γ : Ty ι) : Ty ι := (α →ₜ Ty.unit) ×ₜ (α →ₜ Ty.unit →ₜ γ)
/-- `cTy (¬A)`. -/
abbrev ncT {ι : Type} (α : Ty ι) : Ty ι := α ×ₜ Ty.unit
/-- `wTy (¬¬A)`. -/
abbrev nnwT {ι : Type} (α γ : Ty ι) : Ty ι := nwT (nwT α γ) (ncT α)
/-- `cTy (¬¬A)`. -/
abbrev nncT {ι : Type} (α γ : Ty ι) : Ty ι := ncT (nwT α γ)
/-- `wTy (A → B)`. -/
abbrev iwT {ι : Type} (α γ β δ : Ty ι) : Ty ι := (α →ₜ β) ×ₜ (α →ₜ δ →ₜ γ)
/-- `cTy (A → B)`. -/
abbrev icT {ι : Type} (α δ : Ty ι) : Ty ι := α ×ₜ δ

section TyWrappers

variable {ι : Type} {X : ι → Type}

/-! `Ty`-indexed wrappers of `chiA`/`phiI`. Writing `chiAT (wTy A) (cTy A) (wTy B) (cTy B) …`
in a combinator's data makes the elaborator check `nwT (wTy A) (cTy A) ≟ wTy (¬ᶠA)` at the
`Ty` level — a small structural unfolding — instead of inferring `chiA`'s four Lean-type
arguments by unifying `NW (IW ?WA ?CA ?WB ?CB) …` against `Ty.interpret X (wTy …).hat`, which
with `A B` free re-unfolds `wTy`'s duplicated subterms exponentially (no `whnf` cache). The
wrappers unfold to the polymorphic functions, so the helper lemmas apply to them unchanged. -/

/-- `chiA` at the hat types of `α γ β δ`. -/
abbrev chiAT (α γ β δ : Ty ι) (f : Ty.interpret X (α →ₜ β).hat)
    (g : Ty.interpret X (α →ₜ δ →ₜ γ).hat) (ψ : Ty.interpret X (nwT β δ).hat) :
    Ty.interpret X (nwT α γ).hat := chiA f g ψ

/-- `chiA` at the witness types of `α γ β δ`. -/
abbrev chiAW (α γ β δ : Ty ι) (f : Ty.interpret X (α →ₜ β))
    (g : Ty.interpret X (α →ₜ δ →ₜ γ)) (ψ : Ty.interpret X (nwT β δ)) :
    Ty.interpret X (nwT α γ) := chiA f g ψ

/-- `phiI` at the hat types of `α γ β δ`. -/
abbrev phiIT (α γ β δ : Ty ι) (Ψ : Ty.interpret X (nnwT α γ).hat)
    (ψ : Ty.interpret X (nwT β δ).hat) :
    Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)).hat := phiI Ψ ψ

/-- `phiI` at the witness types of `α γ β δ`. -/
abbrev phiIW (α γ β δ : Ty ι) (Ψ : Ty.interpret X (nnwT α γ))
    (ψ : Ty.interpret X (nwT β δ)) :
    Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)) := phiI Ψ ψ

end TyWrappers

section HelperMaj

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {α γ β δ : Ty ι}

theorem chiA_maj {f_star : Ty.interpret X (α →ₜ β).hat} {f : Ty.interpret X (α →ₜ β)}
    {g_star : Ty.interpret X (α →ₜ δ →ₜ γ).hat} {g : Ty.interpret X (α →ₜ δ →ₜ γ)}
    {ψ_star : Ty.interpret X (nwT β δ).hat} {ψ : Ty.interpret X (nwT β δ)}
    (hf : am.maj (α →ₜ β) f_star f) (hg : am.maj (α →ₜ δ →ₜ γ) g_star g)
    (hψ : am.maj (nwT β δ) ψ_star ψ) :
    am.maj (nwT α γ) (chiA f_star g_star ψ_star) (chiA f g ψ) := by
  dsimp only [chiA]; maj_auto

theorem chiA_self {f g : Ty.interpret X (α →ₜ β).hat}
    {g₁ g₂ : Ty.interpret X (α →ₜ δ →ₜ γ).hat} {ψ₁ ψ₂ : Ty.interpret X (nwT β δ).hat}
    (hf : am.selfMaj (α →ₜ β) f g) (hg : am.selfMaj (α →ₜ δ →ₜ γ) g₁ g₂)
    (hψ : am.selfMaj (nwT β δ) ψ₁ ψ₂) :
    am.selfMaj (nwT α γ) (chiA f g₁ ψ₁) (chiA g g₂ ψ₂) := by
  dsimp only [chiA]; maj_auto

theorem phiI_maj {Ψ_star : Ty.interpret X (nnwT α γ).hat} {Ψ : Ty.interpret X (nnwT α γ)}
    {ψ_star : Ty.interpret X (nwT β δ).hat} {ψ : Ty.interpret X (nwT β δ)}
    (hΨ : am.maj (nnwT α γ) Ψ_star Ψ) (hψ : am.maj (nwT β δ) ψ_star ψ) :
    am.maj (nwT (iwT α γ β δ) (icT α δ)) (phiI Ψ_star ψ_star) (phiI Ψ ψ) := by
  dsimp only [phiI]; maj_auto

theorem phiI_self {Ψ₁ Ψ₂ : Ty.interpret X (nnwT α γ).hat} {ψ₁ ψ₂ : Ty.interpret X (nwT β δ).hat}
    (hΨ : am.selfMaj (nnwT α γ) Ψ₁ Ψ₂) (hψ : am.selfMaj (nwT β δ) ψ₁ ψ₂) :
    am.selfMaj (nwT (iwT α γ β δ) (icT α δ)) (phiI Ψ₁ ψ₁) (phiI Ψ₂ ψ₂) := by
  dsimp only [phiI]; maj_auto

theorem constNB_maj {y_star : Ty.interpret X δ.hat} {y : Ty.interpret X δ}
    (hy : am.maj δ y_star y) :
    am.maj (nwT β δ) (constNB y_star) (constNB y) := by
  dsimp only [constNB]; maj_auto

theorem constNB_self {y₁ y₂ : Ty.interpret X δ.hat} (hy : am.selfMaj δ y₁ y₂) :
    am.selfMaj (nwT β δ) (constNB y₁) (constNB y₂) := by
  dsimp only [constNB]; maj_auto

theorem qB_maj {g_star : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat}
    {g : Ty.interpret X (α →ₜ nncT β δ →ₜ γ)} {b_star : Ty.interpret X β.hat}
    {b : Ty.interpret X β}
    (hg : am.maj (α →ₜ nncT β δ →ₜ γ) g_star g) (hb : am.maj β b_star b) :
    am.maj (iwT α γ β δ) (qB g_star b_star) (qB g b) := by
  dsimp only [qB]; maj_auto

theorem qB_self {g₁ g₂ : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat} {b₁ b₂ : Ty.interpret X β.hat}
    (hg : am.selfMaj (α →ₜ nncT β δ →ₜ γ) g₁ g₂) (hb : am.selfMaj β b₁ b₂) :
    am.selfMaj (iwT α γ β δ) (qB g₁ b₁) (qB g₂ b₂) := by
  dsimp only [qB]; maj_auto

theorem psiA_maj {g_star : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat}
    {g : Ty.interpret X (α →ₜ nncT β δ →ₜ γ)}
    {φ_star : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)).hat}
    {φ : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ))}
    (hg : am.maj (α →ₜ nncT β δ →ₜ γ) g_star g)
    (hφ : am.maj (nwT (iwT α γ β δ) (icT α δ)) φ_star φ) :
    am.maj (nwT β δ) (psiA g_star φ_star) (psiA g φ) := by
  dsimp only [psiA]; maj_auto

theorem psiA_self {g₁ g₂ : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat}
    {φ₁ φ₂ : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)).hat}
    (hg : am.selfMaj (α →ₜ nncT β δ →ₜ γ) g₁ g₂)
    (hφ : am.selfMaj (nwT (iwT α γ β δ) (icT α δ)) φ₁ φ₂) :
    am.selfMaj (nwT β δ) (psiA g₁ φ₁) (psiA g₂ φ₂) := by
  dsimp only [psiA]; maj_auto

theorem pPrime_maj {f_star : Ty.interpret X (α →ₜ nnwT β δ).hat}
    {f : Ty.interpret X (α →ₜ nnwT β δ)}
    {g_star : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat}
    {g : Ty.interpret X (α →ₜ nncT β δ →ₜ γ)}
    {φ_star : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)).hat}
    {φ : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ))}
    (hf : am.maj (α →ₜ nnwT β δ) f_star f) (hg : am.maj (α →ₜ nncT β δ →ₜ γ) g_star g)
    (hφ : am.maj (nwT (iwT α γ β δ) (icT α δ)) φ_star φ) :
    am.maj (iwT α γ β δ) (pPrime f_star g_star φ_star) (pPrime f g φ) := by
  dsimp only [pPrime]; maj_auto

theorem pPrime_self {f₁ f₂ : Ty.interpret X (α →ₜ nnwT β δ).hat}
    {g₁ g₂ : Ty.interpret X (α →ₜ nncT β δ →ₜ γ).hat}
    {φ₁ φ₂ : Ty.interpret X (nwT (iwT α γ β δ) (icT α δ)).hat}
    (hf : am.selfMaj (α →ₜ nnwT β δ) f₁ f₂) (hg : am.selfMaj (α →ₜ nncT β δ →ₜ γ) g₁ g₂)
    (hφ : am.selfMaj (nwT (iwT α γ β δ) (icT α δ)) φ₁ φ₂) :
    am.selfMaj (iwT α γ β δ) (pPrime f₁ g₁ φ₁) (pPrime f₂ g₂ φ₂) := by
  dsimp only [pPrime]; maj_auto

/-- `wTy (A ∨ ¬A)` for `wTy A = α`, `cTy A = γ`. -/
abbrev orNegW {ι : Type} (α γ : Ty ι) : Ty ι := Ty.nat ×ₜ (α ×ₜ nwT α γ)
/-- `cTy (A ∨ ¬A)`. -/
abbrev orNegC {ι : Type} (α γ : Ty ι) : Ty ι := γ ×ₜ (α ×ₜ Ty.unit)

theorem lemNa_maj {φ_star : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {φ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ))}
    {dna_star : Ty.interpret X (nwT α γ).hat} {dna : Ty.interpret X (nwT α γ)}
    {z_star : Ty.interpret X Ty.nat.hat} {z : Ty.interpret X Ty.nat}
    (hφ : am.maj (nwT (orNegW α γ) (orNegC α γ)) φ_star φ) (hdna : am.maj (nwT α γ) dna_star dna)
    (hz : am.maj Ty.nat z_star z) :
    am.maj (nwT α γ) (lemNa φ_star dna_star z_star) (lemNa φ dna z) := by
  dsimp only [lemNa]; maj_auto

theorem lemNa_self {φ₁ φ₂ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {d₁ d₂ : Ty.interpret X (nwT α γ).hat} {z₁ z₂ : Ty.interpret X Ty.nat.hat}
    (hφ : am.selfMaj (nwT (orNegW α γ) (orNegC α γ)) φ₁ φ₂) (hdna : am.selfMaj (nwT α γ) d₁ d₂)
    (hz : am.selfMaj Ty.nat z₁ z₂) :
    am.selfMaj (nwT α γ) (lemNa φ₁ d₁ z₁) (lemNa φ₂ d₂ z₂) := by
  dsimp only [lemNa]; maj_auto

theorem lemW1_maj {φ_star : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {φ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ))}
    {dna_star : Ty.interpret X (nwT α γ).hat} {dna : Ty.interpret X (nwT α γ)}
    {da_star : Ty.interpret X α.hat} {da : Ty.interpret X α}
    {o_star z_star : Ty.interpret X Ty.nat.hat} {o z : Ty.interpret X Ty.nat}
    (hφ : am.maj (nwT (orNegW α γ) (orNegC α γ)) φ_star φ) (hdna : am.maj (nwT α γ) dna_star dna)
    (hda : am.maj α da_star da) (ho : am.maj Ty.nat o_star o) (hz : am.maj Ty.nat z_star z) :
    am.maj (orNegW α γ) (lemW1 φ_star dna_star da_star o_star z_star) (lemW1 φ dna da o z) := by
  dsimp only [lemW1]; maj_auto

theorem lemW1_self {φ₁ φ₂ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {d₁ d₂ : Ty.interpret X (nwT α γ).hat} {a₁ a₂ : Ty.interpret X α.hat}
    {o₁ o₂ z₁ z₂ : Ty.interpret X Ty.nat.hat}
    (hφ : am.selfMaj (nwT (orNegW α γ) (orNegC α γ)) φ₁ φ₂) (hdna : am.selfMaj (nwT α γ) d₁ d₂)
    (hda : am.selfMaj α a₁ a₂) (ho : am.selfMaj Ty.nat o₁ o₂) (hz : am.selfMaj Ty.nat z₁ z₂) :
    am.selfMaj (orNegW α γ) (lemW1 φ₁ d₁ a₁ o₁ z₁) (lemW1 φ₂ d₂ a₂ o₂ z₂) := by
  dsimp only [lemW1]; maj_auto

theorem lemA1_maj {φ_star : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {φ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ))}
    {dna_star : Ty.interpret X (nwT α γ).hat} {dna : Ty.interpret X (nwT α γ)}
    {da_star : Ty.interpret X α.hat} {da : Ty.interpret X α}
    {o_star z_star : Ty.interpret X Ty.nat.hat} {o z : Ty.interpret X Ty.nat}
    (hφ : am.maj (nwT (orNegW α γ) (orNegC α γ)) φ_star φ) (hdna : am.maj (nwT α γ) dna_star dna)
    (hda : am.maj α da_star da) (ho : am.maj Ty.nat o_star o) (hz : am.maj Ty.nat z_star z) :
    am.maj α (lemA1 φ_star dna_star da_star o_star z_star) (lemA1 φ dna da o z) := by
  dsimp only [lemA1]; maj_auto

theorem lemA1_self {φ₁ φ₂ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {d₁ d₂ : Ty.interpret X (nwT α γ).hat} {a₁ a₂ : Ty.interpret X α.hat}
    {o₁ o₂ z₁ z₂ : Ty.interpret X Ty.nat.hat}
    (hφ : am.selfMaj (nwT (orNegW α γ) (orNegC α γ)) φ₁ φ₂) (hdna : am.selfMaj (nwT α γ) d₁ d₂)
    (hda : am.selfMaj α a₁ a₂) (ho : am.selfMaj Ty.nat o₁ o₂) (hz : am.selfMaj Ty.nat z₁ z₂) :
    am.selfMaj α (lemA1 φ₁ d₁ a₁ o₁ z₁) (lemA1 φ₂ d₂ a₂ o₂ z₂) := by
  dsimp only [lemA1]; maj_auto

theorem lemW2_maj {φ_star : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {φ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ))}
    {dna_star : Ty.interpret X (nwT α γ).hat} {dna : Ty.interpret X (nwT α γ)}
    {da_star : Ty.interpret X α.hat} {da : Ty.interpret X α}
    {o_star z_star : Ty.interpret X Ty.nat.hat} {o z : Ty.interpret X Ty.nat}
    (hφ : am.maj (nwT (orNegW α γ) (orNegC α γ)) φ_star φ) (hdna : am.maj (nwT α γ) dna_star dna)
    (hda : am.maj α da_star da) (ho : am.maj Ty.nat o_star o) (hz : am.maj Ty.nat z_star z) :
    am.maj (orNegW α γ) (lemW2 φ_star dna_star da_star o_star z_star) (lemW2 φ dna da o z) := by
  dsimp only [lemW2]; maj_auto

theorem lemW2_self {φ₁ φ₂ : Ty.interpret X (nwT (orNegW α γ) (orNegC α γ)).hat}
    {d₁ d₂ : Ty.interpret X (nwT α γ).hat} {a₁ a₂ : Ty.interpret X α.hat}
    {o₁ o₂ z₁ z₂ : Ty.interpret X Ty.nat.hat}
    (hφ : am.selfMaj (nwT (orNegW α γ) (orNegC α γ)) φ₁ φ₂) (hdna : am.selfMaj (nwT α γ) d₁ d₂)
    (hda : am.selfMaj α a₁ a₂) (ho : am.selfMaj Ty.nat o₁ o₂) (hz : am.selfMaj Ty.nat z₁ z₂) :
    am.selfMaj (orNegW α γ) (lemW2 φ₁ d₁ a₁ o₁ z₁) (lemW2 φ₂ d₂ a₂ o₂ z₂) := by
  dsimp only [lemW2]; maj_auto

end HelperMaj

-- ============================================================================
-- The closed combinators as monotone realizers
-- ============================================================================

section Combinators

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

/-- The decision `nnImpRevF`'s realizer branches on, as an opaque `def` so that `simp` leaves
the `ite` condition alone until the case split. -/
def revCond {Γ : Ctx ι} (A B : Formula F Γ) (env : Ctx.interpret X Γ)
    (p : dialecticaWitness X (A →ᶠ B)) (c : dialecticaCounter X (A →ᶠ B)) : Prop :=
  dialecticaMatrix si (A →ᶠ B) env p c

instance {Γ : Ctx ι} (A B : Formula F Γ) (env : Ctx.interpret X Γ)
    (p : dialecticaWitness X (A →ᶠ B)) (c : dialecticaCounter X (A →ᶠ B)) :
    Decidable (revCond (si := si) A B env p c) :=
  inferInstanceAs (Decidable (dialecticaMatrix si (A →ᶠ B) env p c))

/-- **`A → ¬¬A`** (`dnn_intro`). -/
def MRealizer.dnnIntroF (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) :
    MRealizer cm (A →ᶠ ¬ᶠ¬ᶠA) :=
  ⟨fun _ _ => dnnFun, fun _ _ => by
    refine ⟨⟨fun _ => dnnFun, ?_, ?_⟩, ?_⟩
    · intro _ _ _; dsimp only [dnnFun]; maj_auto
    · intro env y hm
      simp only [dnnFun, Formula.neg, dialecticaMatrix] at hm ⊢
      intro hn; exact hn hm
    · intro _ _ _; dsimp only [dnnFun]; maj_auto⟩

/-- **`¬¬(A → B) → (¬¬A → ¬¬B)`** (`neg_neg_mp`). The data is `nnMpFun`'s body written out as
a literal lambda: checked against the expected `Ty.interpret X (wTy …)` binder by binder, where
ascribing the polymorphic constant forces one wholesale defeq of two large types that, with
`A B` free (no `whnf` cache), re-unfolds `wTy`'s duplicated subterms exponentially. -/
def MRealizer.nnMpF (cm : ConstMajorants am) {Γ : Ctx ι} (A B : Formula F Γ) :
    MRealizer cm (¬ᶠ¬ᶠ(A →ᶠ B) →ᶠ (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB)) :=
  ⟨fun _ _ =>
    (fun Φ =>
      (fun Ψ =>
        (fun _ => (),
         fun ψ _ =>
          ((Φ.2 (phiIT (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.1
            ((Ψ.2 (chiAT (wTy A) (cTy A) (wTy B) (cTy B)
                (Φ.2 (phiIT (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.1
                (Φ.2 (phiIT (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.2 ψ) ()).1), ())),
       fun Ψ c =>
        (chiAT (wTy A) (cTy A) (wTy B) (cTy B)
          (Φ.2 (phiIT (wTy A) (cTy A) (wTy B) (cTy B) Ψ c.1) ()).1.1
          (Φ.2 (phiIT (wTy A) (cTy A) (wTy B) (cTy B) Ψ c.1) ()).1.2 c.1, ())),
     fun Φ c => (phiIT (wTy A) (cTy A) (wTy B) (cTy B) c.1 c.2.1, ())),
   fun _ _ => by
    refine ⟨⟨fun _ =>
      (fun Φ =>
        (fun Ψ =>
          (fun _ => (),
           fun ψ _ =>
            ((Φ.2 (phiIW (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.1
              ((Ψ.2 (chiAW (wTy A) (cTy A) (wTy B) (cTy B)
                  (Φ.2 (phiIW (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.1
                  (Φ.2 (phiIW (wTy A) (cTy A) (wTy B) (cTy B) Ψ ψ) ()).1.2 ψ) ()).1), ())),
         fun Ψ c =>
          (chiAW (wTy A) (cTy A) (wTy B) (cTy B)
            (Φ.2 (phiIW (wTy A) (cTy A) (wTy B) (cTy B) Ψ c.1) ()).1.1
            (Φ.2 (phiIW (wTy A) (cTy A) (wTy B) (cTy B) Ψ c.1) ()).1.2 c.1, ())),
       fun Φ c => (phiIW (wTy A) (cTy A) (wTy B) (cTy B) c.1 c.2.1, ())), ?_, ?_⟩, ?_⟩
    · intro _ _ _; maj_auto
    · intro env y hm
      simp only [phiIW, chiAW, phiI, chiA, Formula.neg, dialecticaMatrix] at hm ⊢
      intro hΨ hnb
      apply hm; intro hI
      apply hΨ; intro hA
      exact hnb (hI hA)
    · intro _ _ _; maj_auto⟩

/-- **`(A → ¬¬B) → ¬¬(A → B)`** (`neg_neg_imp_rev`). The Hilbert proof uses its `¬(A→B)`
hypothesis twice, so the realizer branches: present `p' := pPrime f g φ` if `φ`'s own counter
against it satisfies the `A→B`-matrix, else the constant witness `q_{b₀}` at `b₀ := p'.1 a₀`
(`a₀` the `A`-witness `φ` challenged `p'` with). In the second case `¬(A_D(a₀,·) → B_D(b₀,y₀))`
gives `¬¬A_D`, the hypothesis then `¬¬B_D(b₀, ψ_φ b₀)`, and `ψ_φ b₀` is by construction the
counter `φ` gives to `q_{b₀}`. The majorant is the `maxT` of the two candidates. -/
def MRealizer.nnImpRevF (cm : ConstMajorants am) {Γ : Ctx ι} (A B : Formula F Γ) :
    MRealizer cm ((A →ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
  ⟨fun _ _ =>
    (fun fg =>
      (fun _ => (),
       fun φ _ =>
        (maxT (wTy (A →ᶠ B)) (pPrime fg.1 fg.2 φ)
          (qB fg.2 ((pPrime fg.1 fg.2 φ).1 (φ.2 (pPrime fg.1 fg.2 φ) ()).1)), ())),
     fun fg c => ((c.1.2 (pPrime fg.1 fg.2 c.1) ()).1, (psiA fg.2 c.1, ()))),
   fun _ _ => by
    refine ⟨⟨fun env =>
      (fun fg =>
        (fun _ => (),
         fun φ _ =>
          (if revCond (si := si) A B env (pPrime fg.1 fg.2 φ) (φ.2 (pPrime fg.1 fg.2 φ) ())
           then pPrime fg.1 fg.2 φ
           else qB fg.2 ((pPrime fg.1 fg.2 φ).1 (φ.2 (pPrime fg.1 fg.2 φ) ()).1), ())),
       fun fg c => ((c.1.2 (pPrime fg.1 fg.2 c.1) ()).1, (psiA fg.2 c.1, ()))), ?_, ?_⟩, ?_⟩
    · intro _ _ _; maj_auto
    · intro env y hAB
      by_cases hc : revCond (si := si) A B env (pPrime y.1.1 y.1.2 y.2.1)
          (y.2.1.2 (pPrime y.1.1 y.1.2 y.2.1) ())
      · simp only [Formula.neg, dialecticaMatrix, hc, ite_true] at hAB ⊢
        simp only [revCond, dialecticaMatrix] at hc
        intro hn; exact hn hc
      · simp only [Formula.neg, dialecticaMatrix, hc, ite_false] at hAB ⊢
        simp only [revCond, dialecticaMatrix, pPrime, qB, psiA, constNB] at hc hAB ⊢
        intro hn
        exact (fun hnA => hc (fun hA => absurd hA hnA))
          (fun hA => hAB hA (fun hB => hn (fun _ => hB)))
    · intro _ _ _; maj_auto⟩

/-- The decision `dnnLemF`'s realizer branches on, opaque for the same reason as `revCond`. -/
def lemCond {Γ : Ctx ι} (A : Formula F Γ) (env : Ctx.interpret X Γ)
    (a : dialecticaWitness X A) (c : dialecticaCounter X A) : Prop :=
  dialecticaMatrix si A env a c

instance {Γ : Ctx ι} (A : Formula F Γ) (env : Ctx.interpret X Γ)
    (a : dialecticaWitness X A) (c : dialecticaCounter X A) :
    Decidable (lemCond (si := si) A env a c) :=
  inferInstanceAs (Decidable (dialecticaMatrix si A env a c))

/-- **`¬¬(A ∨ ¬A)`** (`dnn_lem`), the realizer of excluded middle under the negative
translation. Against the `¬(A ∨ ¬A)`-challenge `φ`: present the RIGHT disjunct `w₁ = (1, (da, na))`
where `na` answers `a` with the counter `φ` gives to the LEFT disjunct at `a`; `φ` challenges
`w₁` with some `a₁`; if the `A`-matrix already holds at `a₁` against that counter, present the
LEFT disjunct `w₂ = (0, (a₁, dna))` instead. Either way `φ`'s counter is defeated. The two
default witnesses `da`/`dna` are `Term.defaultOf` terms, majorized by `termMajorizer` — the
one place a closed *term* survives in these combinators; it is a fixed `unitI`/`mkPair`/`lam`
tree of the witness type's shape, so `termMajorizer` on it is cheap. The majorant is the
`maxT` of the two candidates; the flags `0`/`1` are majorized by `cm.zeroM n` /
`cm.succM n (cm.zeroM n)` (`flagM`'s trick). -/
def MRealizer.dnnLemF (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) :
    MRealizer cm (¬ᶠ¬ᶠ(A ∨ᶠ ¬ᶠA)) :=
  ⟨fun n es =>
    (fun _ => (),
     fun φ _ =>
      (maxT (wTy (A ∨ᶠ ¬ᶠA))
        (lemW2 φ (termMajorizer cm (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) n es)
          (termMajorizer cm (Term.defaultOf (wTy A) : Term F Γ _) n es)
          (cm.succM n (cm.zeroM n)) (cm.zeroM n))
        (lemW1 φ (termMajorizer cm (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) n es)
          (termMajorizer cm (Term.defaultOf (wTy A) : Term F Γ _) n es)
          (cm.succM n (cm.zeroM n)) (cm.zeroM n)), ())),
   fun n hn => by
    refine ⟨⟨fun env =>
      (fun _ => (),
       fun φ _ =>
        (if lemCond (si := si) A env
              (lemA1 φ (Term.interpret si (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) env)
                (Term.interpret si (Term.defaultOf (wTy A) : Term F Γ _) env) 1 0)
              (φ.2 (lemW2 φ (Term.interpret si (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) env)
                (Term.interpret si (Term.defaultOf (wTy A) : Term F Γ _) env) 1 0) ()).1
         then lemW2 φ (Term.interpret si (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) env)
                (Term.interpret si (Term.defaultOf (wTy A) : Term F Γ _) env) 1 0
         else lemW1 φ (Term.interpret si (Term.defaultOf (wTy (¬ᶠA)) : Term F Γ _) env)
                (Term.interpret si (Term.defaultOf (wTy A) : Term F Γ _) env) 1 0, ())),
      ?_, ?_⟩, ?_⟩
    · intro _ _ _; maj_auto
    · intro env y
      -- unfold first (this also rewrites the `¬ᶠA` inside the `ite` condition), then split on
      -- the `ite` as it now stands — a `by_cases` stated beforehand would no longer match it
      simp only [Formula.neg, dialecticaMatrix]
      split
      · rename_i hc
        simp only [lemCond, lemW2, lemA1, lemW1, lemNa, dialecticaMatrix] at hc ⊢
        intro hn'; apply hn'
        exact ⟨fun _ => hc, fun h => absurd rfl h⟩
      · rename_i hc
        simp only [lemCond, lemW2, lemA1, lemW1, lemNa, dialecticaMatrix] at hc ⊢
        intro hn'; apply hn'
        exact ⟨fun h => absurd h Nat.one_ne_zero, fun _ hA => hc hA⟩
    · intro _ _ _; maj_auto⟩

/-- **Exportation as a formula**: `(A ∧ B → C) → (A → B → C)`. -/
def MRealizer.expF (cm : ConstMajorants am) {Γ : Ctx ι} (A B C : Formula F Γ) :
    MRealizer cm ((A ∧ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C)) :=
  ⟨fun _ _ => expFun, fun _ _ => by
    refine ⟨⟨fun _ => expFun, ?_, ?_⟩, ?_⟩
    · intro _ _ _; dsimp only [expFun]; maj_auto
    · intro env y hm
      simp only [expFun, dialecticaMatrix] at hm ⊢
      intro hA hB; exact hm ⟨hA, hB⟩
    · intro _ _ _; dsimp only [expFun]; maj_auto⟩

/-- **Importation as a formula**: `(A → B → C) → (A ∧ B → C)`. -/
def MRealizer.impF (cm : ConstMajorants am) {Γ : Ctx ι} (A B C : Formula F Γ) :
    MRealizer cm ((A →ᶠ B →ᶠ C) →ᶠ (A ∧ᶠ B →ᶠ C)) :=
  ⟨fun _ _ => impFun, fun _ _ => by
    refine ⟨⟨fun _ => impFun, ?_, ?_⟩, ?_⟩
    · intro _ _ _; dsimp only [impFun]; maj_auto
    · intro env y hm
      simp only [impFun, dialecticaMatrix] at hm ⊢
      intro hAB; exact hm hAB.1 hAB.2
    · intro _ _ _; dsimp only [impFun]; maj_auto⟩

/-- **Expansion as a formula**: `(A → B) → (C ∨ A → C ∨ B)`. -/
def MRealizer.expansionF (cm : ConstMajorants am) {Γ : Ctx ι} (A B C : Formula F Γ) :
    MRealizer cm ((A →ᶠ B) →ᶠ (C ∨ᶠ A →ᶠ C ∨ᶠ B)) :=
  ⟨fun _ _ => expansionFun, fun _ _ => by
    refine ⟨⟨fun _ => expansionFun, ?_, ?_⟩, ?_⟩
    · intro _ _ _; dsimp only [expansionFun]; maj_auto
    · intro env y hm
      simp only [expansionFun, dialecticaMatrix] at hm ⊢
      intro hx; exact ⟨hx.1, fun hne => hm (hx.2 hne)⟩
    · intro _ _ _; dsimp only [expansionFun]; maj_auto⟩

end Combinators

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms MRealizer.dnnIntroF
#print axioms MRealizer.nnMpF
#print axioms MRealizer.nnImpRevF
#print axioms MRealizer.dnnLemF
#print axioms MRealizer.expF
#print axioms MRealizer.impF
#print axioms MRealizer.expansionF

end Metatheorems
