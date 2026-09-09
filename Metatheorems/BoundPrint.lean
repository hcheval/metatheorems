/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Monotone
import Metatheorems.Rounding

/-!
# `#bound` — printing the extracted functional of a proof

    #bound <ident> [depth <n>] [unfold] [eval] [cap <n>] [to "<path>"]

Two modes, and they answer different questions; `unfold` is a variant of the first.

**Structural (the default).** `depth n` counts **reduction steps along the derivation**:
`monotone_soundness … prf` is unfolded through `n` levels of the derivation tree, each
unfolded node printed as the `MRealizer.*` combinator that its inference rule maps to
(`MRealizer.induction`, `.syllogism`, `.mp`, …) applied to its subderivations, and everything
deeper left as `monotone_soundness … <name>` — the subproof's name when it has one, `…`
otherwise. `depth 0` prints the root node only. Nothing is ever evaluated, so the output is
linear in the part of the derivation visited and the mode is safe on any proof; the `maxNodes`
cap bounds it absolutely.

**Structural with `unfold`.** The same walk, but each visited combinator is opened to the
majorant it builds — `MRealizer.mp` to `fun n e => (↑hAB n e).1 (↑hA n e)`, `andContract` to
its `maxT`, `induction` to `termMajorizer cm (λᶠ …, R[…] ⬝ ⟨base⟩ ⬝ ⟨step⟩ ⬝ …)` — printed in
terms of the combinator's own binder names, and each sub-realizer listed under its name. Still
nothing is evaluated: the display is the definition's `Subtype.mk` value after β/ζ/projections,
with only the `MRealizer.*` plumbing and the `mt*` object terms δ-opened (`unfoldable`), so
`maxT`, `cm.precM` and `termMajorizer` are where it stops. Safe wherever the plain walk is.

**Evaluative (`eval`).** The capped kernel reducer of `Probes/ExprBound.lean` — repeated
`Lean.Kernel.whnf` under a visit cap, with an arithmetic blocklist so the result reads as
arithmetic rather than as `Nat.rec` Church iteration. Point it at a `def` of the bound
(`def lin5 := mfiV PureWEHA.cm Demo.linearR 5`, or a `fun n => …` left symbolic). The cap is
mandatory and the report says whether it fired (`capAbort=true` means the printed term is a
partial reduction, not the answer).

`to "path"` writes the same output to `path.md`, as `#hilbert` does.

The grammar takes an `ident`, not a `term`, for the same reason `#hilbert` does: after a term
the modifier `depth 2` parses as an application.

Measurements — which proofs, which depths, wall times, converged or capped — are in
`Metatheorems/Probes/BoundPrintDemo.lean`'s header.
-/

namespace Metatheorems
namespace BoundPrint

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

-- ============================================================================
-- The rule → combinator table (it mirrors `monotone_soundness`, case for case)
-- ============================================================================

/-- What `monotone_soundness` builds at each `Derivable` constructor. `none` means the head is
not a constructor of `Derivable`. Keep this in step with `monotone_soundness`. -/
def ctorMRealizer : Name → Option String
  | ``Derivable.premise      => some "MRealizer.ofSRealizer cm (spremise …)"
  | ``Derivable.or_contract  => some "MRealizer.orContract cm _"
  | ``Derivable.and_contract => some "MRealizer.andContract cm _"
  | ``Derivable.or_weak      => some "MRealizer.ofSRealizer cm sOrWeak"
  | ``Derivable.and_weak     => some "MRealizer.ofSRealizer cm sAndWeak"
  | ``Derivable.or_perm      => some "MRealizer.orPerm cm _ _"
  | ``Derivable.and_perm     => some "MRealizer.ofSRealizer cm sAndPerm"
  | ``Derivable.exfalso      => some "MRealizer.ofSRealizer cm sExfalso"
  | ``Derivable.forall_ax    => some "MRealizer.ofSRealizer cm (sForallAx t)"
  | ``Derivable.exist_ax     => some "MRealizer.ofSRealizer cm (sExistAx t)"
  | ``Derivable.mp           => some "MRealizer.mp cm"
  | ``Derivable.syllogism    => some "MRealizer.syllogism cm"
  | ``Derivable.exportation  => some "MRealizer.exportation cm"
  | ``Derivable.importation  => some "MRealizer.importation cm"
  | ``Derivable.expansion    => some "MRealizer.expansion cm"
  | ``Derivable.forall_rule  => some "MRealizer.forallRule cm"
  | ``Derivable.exist_rule   => some "MRealizer.existRule cm"
  | ``Derivable.univ_gen     => some "MRealizer.univGen cm"
  | ``Derivable.succ_ne_zero => some "MRealizer.ofSRealizer cm sSuccNeZero"
  | ``Derivable.succ_inj     => some "MRealizer.ofSRealizer cm sSuccInj"
  | ``Derivable.beta_eq      => some "MRealizer.ofSRealizer cm (sBetaEq eqxi)"
  | ``Derivable.pair_fst     => some "MRealizer.ofSRealizer cm (sPairFst eqxi)"
  | ``Derivable.pair_snd     => some "MRealizer.ofSRealizer cm (sPairSnd eqxi)"
  | ``Derivable.pair_eta     => some "MRealizer.ofSRealizer cm (sPairEta eqxi)"
  | ``Derivable.rec_zero     => some "MRealizer.ofSRealizer cm (sRecZero eqxi)"
  | ``Derivable.rec_succ     => some "MRealizer.ofSRealizer cm (sRecSucc eqxi)"
  | ``Derivable.dist_self    => some "MRealizer.ofSRealizer cm (sDistSelf eqxi i x)"
  | ``Derivable.dist_comm    => some "MRealizer.ofSRealizer cm (sDistComm eqxi i x y)"
  | ``Derivable.dist_tri     => some "MRealizer.ofSRealizer cm (sDistTri eqxi i x y z)"
  | ``Derivable.refl0        => some "MRealizer.ofSRealizer cm sRefl0"
  | ``Derivable.sym0         => some "MRealizer.ofSRealizer cm sSym0"
  | ``Derivable.trans0       => some "MRealizer.ofSRealizer cm sTrans0"
  | ``Derivable.qfer         => some "MRealizer.qfer cm eqxi hqf hvf"
  | ``Derivable.induction    => some "MRealizer.induction cm"
  | ``Derivable.markov       => some "MRealizer.ofSRealizer cm (sMarkov hqf hvf)"
  | ``Derivable.ip           => some "MRealizer.ofSRealizer cm (sIP hqf hvf)"
  | ``Derivable.ac           => some "MRealizer.ofSRealizer cm sAC"
  | ``Derivable.qfac         => some "MRealizer.ofSRealizer cm sAC"
  | ``Derivable.lem          => some "⟨LEM: not available at Allowed.extended⟩"
  | _ => none

/-- The combinator *constant* a rule maps to, for the rules whose combinator has a definition
worth opening: `unfold` mode prints its majorant (`.val`) with the sub-realizers as the
combinator's own binder names. Leaves (`ofSRealizer …`) are not opened. -/
def ctorMRealizerName : Name → Option Name
  | ``Derivable.mp           => some ``MRealizer.mp
  | ``Derivable.syllogism    => some ``MRealizer.syllogism
  | ``Derivable.exportation  => some ``MRealizer.exportation
  | ``Derivable.importation  => some ``MRealizer.importation
  | ``Derivable.expansion    => some ``MRealizer.expansion
  | ``Derivable.forall_rule  => some ``MRealizer.forallRule
  | ``Derivable.exist_rule   => some ``MRealizer.existRule
  | ``Derivable.univ_gen     => some ``MRealizer.univGen
  | ``Derivable.induction    => some ``MRealizer.induction
  | ``Derivable.qfer         => some ``MRealizer.qfer
  | ``Derivable.and_contract => some ``MRealizer.andContract
  | ``Derivable.or_contract  => some ``MRealizer.orContract
  | ``Derivable.or_perm      => some ``MRealizer.orPerm
  | _ => none

/-- Constants that are pure re-typings: walked through, never given a node of their own. Same
list as `Hilbert.isTransparentWrapper`. -/
def isTransparentWrapper : Name → Bool
  | ``Derivable.castAllowed => true
  | ``Eq.mpr | ``Eq.mp | ``Eq.ndrec | ``Eq.rec | ``cast | ``id => true
  | _ => false

/-- Short display name: everything lives under `Metatheorems`, so that prefix carries no
information. -/
def shortName (n : Name) : String :=
  match (privateToUserName n).components with
  | `Metatheorems :: rest => String.intercalate "." (rest.map toString)
  | _ => toString n

/-- `Derivable` applied to its seven arguments has the conclusion last. -/
def derivConcl? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Derivable, args) => return if args.size == 7 then some args[6]! else none
  | _ => return none

/-- Is this expression a derivation? -/
def isDerivProof (e : Expr) : MetaM Bool := do
  return (← derivConcl? (← inferType e)).isSome

/-- The derivation-typed arguments of an application, in order. -/
def derivArgs (args : Array Expr) : MetaM (Array Expr) := args.filterM isDerivProof

/-- Delta-expand the head constant, bypassing smart unfolding — `unfoldDefinition?` refuses on
a structurally recursive function until its recursive argument is a constructor application,
which is exactly the situation here. Copied from `Probes/ExprBound.lean`. -/
def forceDelta (e : Expr) : MetaM (Option Expr) := do
  let .const c us := e.getAppFn | return none
  let some (.defnInfo di) := (← getEnv).find? c | return none
  return some (mkAppN (di.value.instantiateLevelParams di.levelParams us) e.getAppArgs)

-- ============================================================================
-- The structural walk
-- ============================================================================

/-- Structural-mode configuration: how many derivation levels to unfold, and the absolute node
cap that makes the mode safe on any proof. -/
structure Cfg where
  depth : Nat := 0
  maxNodes : Nat := 20000
  /-- Open each visited combinator to its majorant, printed in terms of its sub-realizers. -/
  unfold : Bool := false

/-- The rendered listing so far, as `(indentation, text)` pairs. -/
structure St where
  lines : Array (Nat × String) := #[]
  aborted : Bool := false

abbrev M := ReaderT Cfg (StateRefT St MetaM)

/-- Append one node. -/
def emit (ind : Nat) (s : String) : M Unit :=
  modify fun st => { st with lines := st.lines.push (ind, s) }

/-- An unvisited subderivation, cited by name when it has one. -/
def leaf (ind : Nat) (e : Expr) : M Unit := do
  match e with
  | .fvar id => emit ind s!"monotone_soundness … {(← id.getDecl).userName}"
  | _ =>
    match e.getAppFn with
    | .const c _ => emit ind s!"monotone_soundness … {shortName c}"
    | _ => emit ind "monotone_soundness … …"

/-- Names the `unfold` display may δ-reduce inside a combinator's majorant: the `MRealizer.*`
plumbing (`plug1`/`plug2`/`plugAll`, through which `induction` and `qfer` are built) and the
object-level terms those plug in (`mtInduction`, …). `termMajorizer` itself is deliberately
NOT opened — its δ-expansion is the `brecOn` compilation of a structural recursion, not a
display — so a plugged term shows as `termMajorizer cm ⟨the term, with R[…] visible⟩`. -/
def unfoldable (n : Name) : Bool :=
  (`Metatheorems.MRealizer).isPrefixOf n ||
    (match n with
      | .str `Metatheorems s => s.startsWith "mt"
      | _ => false)

/-- A few bottom-up passes of "δ-reduce an `unfoldable` head, then `whnfCore`" — bounded by
`fuel`, so this is a display normalisation and not a reducer. -/
partial def openTerms (fuel : Nat) (e : Expr) : MetaM Expr := do
  if fuel = 0 then return e
  let e' ← Meta.transform e (post := fun t => do
    match t.getAppFn with
    | .const n _ =>
      if unfoldable n then
        match ← forceDelta t with
        | some u => return .done (← whnfCore u)
        | none => return .done t
      else return .done t
    | _ => return .done t)
  if e' == e then return e else openTerms (fuel - 1) e'

/-- The majorant a combinator builds, as text, with its sub-realizer parameters left as the
binder names of the definition (`hA`, `hAB`, …), plus those names in order. `MRealizer` is a
`Subtype`, so the majorant is the first argument of the `Subtype.mk` the definition reduces to
under `whnfCore` (β, ζ, projections) after the `MRealizer.*` plumbing is opened; inside it
only `unfoldable` names are δ-reduced, so `maxT`, `recMaj`, `cm.precM` and the sub-realizers'
`.val` stay as written. `none` when the body is not in that shape. -/
def combinatorVal (c : Name) : MetaM (Option (Array Name × String)) := do
  let some (.defnInfo di) := (← getEnv).find? c | return none
  lambdaTelescope di.value fun xs body => do
    let mut body ← whnfCore body
    -- `induction`/`qfer` are `plug2 …`/`plug1 …` applications: open the plumbing first.
    for _ in [:6] do
      if body.isAppOfArity ``Subtype.mk 4 then break
      match body.getAppFn with
      | .const n _ =>
        if (`Metatheorems.MRealizer).isPrefixOf n then
          match ← forceDelta body with
          | some u => body ← whnfCore u
          | none => break
        else break
      | _ => break
    unless body.isAppOfArity ``Subtype.mk 4 do return none
    let v ← Core.betaReduce (← openTerms 8 body.getAppArgs[2]!)
    let mut names : Array Name := #[]
    for x in xs do
      if (← inferType x).getAppFn.isConstOf ``MRealizer then
        names := names.push (← x.fvarId!.getUserName)
    let s ← withOptions (fun o => o.setBool `pp.funBinderTypes false) (ppExpr v)
    return some (names, toString s)

/-- How many consecutive definitional unfoldings one node may cost before it is cited instead.
Reaching a `Derivable` constructor from a named lemma or a `pm_*` tactic takes a handful; the
budget only stops a pathological chain, and it is **not** the `depth` dial. -/
def unfoldFuel : Nat := 60

/-- Walk one derivation node with `d` levels of budget left, emitting the combinator
`monotone_soundness` maps it to and recursing into its subderivations at `d - 1`.

`d` counts **inference rules**, not `Expr` steps: reaching a rule through a named lemma or a
proof-mode tactic is free (bounded per node by `u`, the unfold budget), so `depth 2` means two
levels of the derivation tree whether or not they were written through the proof mode. Nothing
is evaluated; a `let`/`have`-bound subderivation is expanded at each use, so the listing is a
tree over a DAG and the node cap is what bounds it. -/
partial def walk (d : Nat) (u : Nat) (ind : Nat) (e₀ : Expr) : M Unit := do
  if (← get).aborted then return
  if (← get).lines.size ≥ (← read).maxNodes then
    modify fun st => { st with aborted := true }
    emit ind "… (node cap reached)"
    return
  let e ← instantiateMVars e₀
  match e with
  | .mdata _ b => walk d u ind b
  | .fvar id =>
    let decl ← id.getDecl
    match decl.value? with
    | some v => walk d u ind v
    | none => emit ind s!"monotone_soundness … {decl.userName}"
  | .letE nm t v b _ => withLetDecl nm t v fun x => walk d u ind (b.instantiate1 x)
  | _ =>
    -- `have` survives elaboration as `letFun v (fun x => body)`.
    if e.isAppOfArity ``letFun 4 then
      let args := e.getAppArgs
      match ← whnf args[3]! with
      | .lam nm t body _ => withLocalDeclD nm t fun x => walk d u ind (body.instantiate1 x)
      | _ => walk d u ind (mkApp args[3]! args[2]!)
    else
      match e.getAppFn with
      | .const c _ =>
        if isTransparentWrapper c then
          match (← derivArgs e.getAppArgs).toList with
          | [a] => walk d u ind a
          | _   => leaf ind e
        else if let some s := ctorMRealizer c then
          emit ind s
          let subs ← derivArgs e.getAppArgs
          let mut labels : Array Name := #[]
          if (← read).unfold then
            if let some cn := ctorMRealizerName c then
              if let some (names, txt) ← combinatorVal cn then
                labels := names
                let ls := txt.splitOn "\n"
                emit (ind + 1) s!"val = {ls.headD ""}"
                for l in ls.drop 1 do emit (ind + 1) s!"      {l}"
          for h : i in [:subs.size] do
            let a := subs[i]
            if let some nm := labels[i]? then emit (ind + 1) s!"{nm} :="
            let ind' := if labels.size > 0 then ind + 2 else ind + 1
            if d = 0 then leaf ind' a else walk (d - 1) unfoldFuel ind' a
        else if u > 0 then
          match ← unfoldDefinition? e with
          | some v => walk d (u - 1) ind v
          | none =>
            match ← forceDelta e with
            | some v => walk d (u - 1) ind v
            | none => leaf ind e
        else leaf ind e
      | _ => leaf ind e

/-- Render the listing as indented text. -/
def render (lines : Array (Nat × String)) : String :=
  String.intercalate "\n" (lines.toList.map fun (i, s) =>
    (String.ofList (List.replicate (2 * i) ' ')) ++ s)

/-- The derivation behind a target: the constant's value, with a `monotone_soundness` wrapper
peeled off so that `#bound` accepts either a `Derivable` or its `MRealizer`. -/
partial def derivationOf (fuel : Nat) (e : Expr) : MetaM Expr := do
  if fuel = 0 then return e
  if ← isDerivProof e then return e
  match e.getAppFn with
  | .const c _ =>
    if c == ``monotone_soundness then
      let args := e.getAppArgs
      if h : args.size > 0 then derivationOf (fuel - 1) args[args.size - 1] else return e
    else
      match ← unfoldDefinition? e with
      | some u => derivationOf (fuel - 1) u
      | none => match ← forceDelta e with
        | some u => derivationOf (fuel - 1) u
        | none => return e
  | _ => return e

/-- The structural listing of `name`, plus whether the node cap fired. -/
def structuralLines (name : Name) (cfg : Cfg) : MetaM (Array (Nat × String) × Bool) := do
  let ci ← getConstInfo name
  let some val := ci.value? | throwError "#bound: `{name}` has no value (opaque or axiom)"
  lambdaTelescope val fun _ body => do
    let prf0 ← derivationOf 8 body
    -- If the target was an `MRealizer` def, `prf0` is the *name* of the derivation; unfold it
    -- once for free, so `depth` counts the same levels whichever of the two is named.
    let prf ← if prf0 == body then pure prf0 else
      match ← unfoldDefinition? prf0 with
      | some u => pure u
      | none   => pure prf0
    unless ← isDerivProof prf do
      throwError "#bound: `{name}` is neither a `Derivable` nor an `MRealizer` of one"
    let (_, st) ← ((walk cfg.depth unfoldFuel 0 prf).run cfg).run {}
    return (st.lines, st.aborted)

-- ============================================================================
-- The evaluative mode — the capped kernel reducer
-- ============================================================================

/-- **The output vocabulary.** These constants are never unfolded, so they survive into the
displayed bound as arithmetic; unblock any of them and `max` becomes `Decidable.rec` and every
`+` a `Nat.rec` Church iteration. Same set as `Probes/ExprBound.blocked`. -/
def blocked : Std.HashSet Name := Std.HashSet.ofList
  [``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.pow, ``Nat.succ, ``Nat.max,
   ``Max.max, ``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HPow.hPow,
   ``Nat.decLe, ``Nat.decEq, ``Nat.ble, ``Nat.beq, ``Nat.rec, ``ite,
   ``Rounding.pairN, ``Rounding.triagN, ``maxT, ``recMaj]

/-- Reducer state: the structural memo, a visit counter, and the caps. There is no fuel; the
visit cap is the whole termination guarantee, and `aborted` says whether it fired. -/
structure KState where
  memo : Std.HashMap ExprStructEq Expr := {}
  visits : Nat := 0
  aborted : Bool := false
  cap : Nat := 4000
  blk : Std.HashSet Name := blocked

abbrev K := StateRefT KState MetaM

/-- Recursion-depth cap, so a pathological chain aborts rather than overflowing the stack. -/
def depthCap : Nat := 3000

/-- **Normalise by repeated `Lean.Kernel.whnf`**, blocklist consulted before each step. The
kernel consumes no heartbeats and caches by structure, which is why it converges on targets
where every `Meta`-level reducer aborts (`Probes/ExprBound.lean`'s finding). -/
partial def knf (depth : Nat) (e : Expr) : K Expr := do
  if (← get).aborted then return e
  if let some v := (← get).memo[ExprStructEq.mk e]? then return v
  if depth > depthCap then
    modify fun s => { s with aborted := true }
    return e
  modify fun s => { s with visits := s.visits + 1 }
  if (← get).visits > (← get).cap then
    modify fun s => { s with aborted := true }
    return e
  let r ← kcore depth e
  modify fun s => { s with memo := s.memo.insert (ExprStructEq.mk e) r }
  return r
where
  kcore (depth : Nat) (e0 : Expr) : K Expr := do
    if ← isProof e0 then return e0
    let blk := (← get).blk
    let blocked? := match e0.getAppFn with
      | .const c _ => blk.contains c
      | _ => false
    let h ← if blocked? then pure e0 else (do
      match Lean.Kernel.whnf (← getEnv) (← getLCtx) e0 with
      | .ok r => pure r
      | .error _ => pure e0)
    match h with
    | .app .. =>
      let f ← knf (depth + 1) h.getAppFn
      let args ← h.getAppArgs.mapM (knf (depth + 1))
      return mkAppN f args
    | .lam n t b bi => withLocalDecl n bi t fun x => do
        mkLambdaFVars #[x] (← knf (depth + 1) (b.instantiate1 x))
    | .mdata _ b => knf (depth + 1) b
    | .proj s i b => return Expr.proj s i (← knf (depth + 1) b)
    | _ => return h

/-- Reduce a constant under the caps and report time, visits, whether the cap fired,
`Expr.numObjs` and the rendered result. -/
def evalBound (name : Name) (cap : Nat) : MetaM (String × Nat × Nat × Bool × Nat) := do
  let e ← mkConstWithLevelParams name
  let t0 ← IO.monoMsNow
  let (r, st) ← (knf 0 e).run { cap := cap }
  let t1 ← IO.monoMsNow
  let n : Nat ← liftM (m := MetaM) r.numObjs
  return (toString (← ppExpr r), t1 - t0, st.visits, st.aborted, n)

/-- The structural listing at depth `d`. A wrapper, because the `#bound` syntax below makes
`depth` a keyword and `{ depth := d }` then no longer parses. -/
def structuralAt (name : Name) (d : Nat) (unf : Bool := false) :
    MetaM (Array (Nat × String) × Bool) :=
  structuralLines name { depth := d, unfold := unf }

end BoundPrint

-- ============================================================================
-- The command
-- ============================================================================

namespace BoundPrint
open Lean Lean.Elab Lean.Elab.Command

/-- `#bound f` prints the root node of `f`'s extracted functional; `depth n` unfolds `n`
levels of the derivation; `eval` reduces the bound with the capped kernel reducer instead;
`cap n` sets that cap; `to "path"` also writes the output to `path.md`.

The modifier words are **non-reserved** keywords (`&"…"`, as Lean's own `induction …
generalizing` is written), so importing this module reserves no token: `depth`, `unfold`,
`eval`, `cap`, `to` stay usable as identifiers — `Hilbert.Config.unfold` is one. (A reserved
`" unfold"` broke `Hilbert.lean` the first time, which is how this was found.) -/
syntax (name := boundCmd)
  "#bound " ident (&" depth " num)? (&" unfold")? (&" eval")? (&" cap " num)? (&" to " str)? :
  command

@[command_elab boundCmd]
def elabBound : CommandElab := fun stx => do
  -- The children are read positionally — `#bound `, the ident, then the five optional
  -- groups — because a quotation pattern for a bare optional atom does not parse here.
  liftTermElabM do
    let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo stx[1]
    let d := if stx[2].getNumArgs > 0 then (stx[2][1].isNatLit?).getD 0 else 0
    let unf := stx[3].getNumArgs > 0
    let isEval := stx[4].getNumArgs > 0
    let visitCap := if stx[5].getNumArgs > 0 then (stx[5][1].isNatLit?).getD 4000 else 4000
    let out? : Option String :=
      if stx[6].getNumArgs > 0 then stx[6][1].isStrLit? else none
    let text ←
      if isEval then do
        let (s, ms, visits, aborted, objs) ← evalBound name visitCap
        let hdr := s!"#bound {name} eval cap={visitCap}: time={ms}ms visits={visits} \
capAbort={aborted} numObjs={objs}"
        -- The info view gets a prefix; a stuck symbolic bound runs to tens of thousands of
        -- objects and printing all of it is not a display. `to` writes the whole thing.
        let shown :=
          if s.length ≤ 4000 then s
          else (s.take 4000).toString ++ "\n… (truncated; use `to`)"
        logInfo m!"{hdr}\n{shown}"
        pure (hdr ++ "\n\n```\n" ++ s ++ "\n```\n")
      else do
        let t0 ← IO.monoMsNow
        let (lines, aborted) ← structuralAt name d unf
        let t1 ← IO.monoMsNow
        let body := render lines
        let capNote := if aborted then " (NODE CAP REACHED)" else ""
        let unfNote := if unf then " unfold" else ""
        let hdr := s!"#bound {name} depth={d}{unfNote}: {lines.size} nodes in {t1 - t0}ms{capNote}"
        logInfo m!"{hdr}\n{body}"
        pure (hdr ++ "\n\n```\n" ++ body ++ "\n```\n")
    if let some base := out? then
      if let some dir := (System.FilePath.mk base).parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile (base ++ ".md") (s!"# `{name}`\n\n" ++ text)

end BoundPrint
end Metatheorems
