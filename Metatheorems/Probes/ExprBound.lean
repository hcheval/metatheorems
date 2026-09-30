/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.MonotoneSpike

/-!
# Displaying `Φ` as arithmetic, by partial reduction at the `Expr` level

Every number this project has reported is `Φ` **applied at a point**: `901` is `Φ` at
`x* = (5,5)`, `1709` at `(5,9)`. `Φ` itself has never been looked at, because unreduced its
syntax is an application spine — `coreBound (mfiU cm (monotone_soundness … prf)) (…)` — with
no information in it, and every bit of content behind a reduction.

This probe asks whether the *syntactic form* of `Φ` can be recovered by **partial** reduction,
and the answer is yes, cheaply.

## The instrument

`pr fuel e`: `whnfCore` (beta/iota/proj) at each node; one `unfoldDefinition?` step when the
head is a constant **not on a blocklist** and fuel remains; recurse into children at the same
fuel; short-circuit on proofs; memoise on `(fuel, ExprStructEq)`.

**The blocklist is the whole design, not the fuel.** What you refuse to unfold *is* the
vocabulary the bound gets written in: block `Nat.add/mul/sub/pow`, `Nat.rec`, `ite`, `maxT`,
`recMaj`, `Rounding.pairN` and you get arithmetic; block less and `max` becomes `Decidable.rec`
and every `+`/`2^·` a `Nat.rec` Church iteration; block more and you get the derivation's shape.
Fuel turned out to be a **display knob, not a cost control** — cost never became a problem.

## Result

On `MonotoneSpike.acSpike` (13 constructors) the bound reads
`fun M h a b => maxT nat (Rounding.pairN (2 * ((a + b) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0`:
`M` and `h` are absent from the body, and it reproduces `1709` at `(5,9)` and `349` at
`(5,1)`. On the proof-mode `MonotoneMCT.rI` the `Meta`-level reducer does not converge; the
KERNEL (`knf`/`runK`, at the bottom of this file, now `BoundPrint.knf` in the library) does.
Tables, the discriminator, limits and the second target are in the notes.
-/

set_option linter.unusedTactic false

namespace Metatheorems
namespace ExprBound

open TriangleBoundDemo (pTy triCm)
open MonotoneSpike (acSpike onceSpike)
open Lean Lean.Meta Lean.Elab

/-- The counter-side bound of the one-`and_contract` derivation, left symbolic in the point
`(a,b)` and in the model `M` and its bound `h`. -/
noncomputable def tgtU (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (a b : ℕ) : ℕ :=
  mfiU (triCm M h) (acSpike M h) (a, b)

/-- The contraction-free control: same statement, no `and_contract`. Its normal form has no
`maxT`, which is the discriminator. -/
noncomputable def tgtU1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (a b : ℕ) : ℕ :=
  mfiU (triCm M h) (onceSpike M h) (a, b)

/-- **The output language.** Constants here are never unfolded, so they survive into the
displayed bound; everything else (`mfiU`, `monotone_soundness`, `MRealizer.*`, `termMajorizer`,
`coreBound`, the model projections) is unfolded freely. Changing this set changes how the bound
reads — it is the specification of the vocabulary, not a performance knob. -/
def blocked : Std.HashSet Name := Std.HashSet.ofList
  [``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.pow, ``Nat.succ, ``Nat.max,
   ``Max.max, ``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HPow.hPow,
   ``Nat.decLe, ``Nat.decEq, ``Nat.ble, ``Nat.beq, ``Nat.rec, ``ite,
   ``Rounding.pairN, ``Rounding.triagN, ``maxT, ``recMaj]

abbrev M' := StateRefT (Std.HashMap (Nat × ExprStructEq) Expr) MetaM

/-- Delta-expand the head constant, **bypassing smart unfolding**.

`Meta.unfoldDefinition?` refuses on a function defined by structural recursion until its
recursive argument is already a constructor application — which is exactly the situation here:
`monotone_soundness … indFinal` cannot unfold until `indFinal` does, and `indFinal` is itself a
`def`. Using it alone the reduction freezes with no fuel consumed, producing the *same* output
at every fuel — a fixed point that is not the normal form. Forcing the delta hands us the
`brecOn`/`rec` body, after which `whnfCore`'s iota can proceed once the argument is exposed. -/
def forceDelta (e : Expr) : MetaM (Option Expr) := do
  let .const c us := e.getAppFn | return none
  let some (.defnInfo di) := (← getEnv).find? c | return none
  return some (mkAppN (di.value.instantiateLevelParams di.levelParams us) e.getAppArgs)

/-- Fueled, memoised partial delta-reduction. A `Nat.rec` on a literal fires; on a variable it
stays **stuck**, and a stuck recursor is exactly the iteration we want to see in the bound. -/
partial def pr (fuel : Nat) (e : Expr) : M' Expr := do
  if let some v := (← get)[(fuel, ExprStructEq.mk e)]? then return v
  let r ← core fuel e
  modify (·.insert (fuel, ExprStructEq.mk e) r)
  return r
where
  core (fuel : Nat) (e0 : Expr) : M' Expr := do
    if ← isProof e0 then return e0
    let e ← whnfCore e0
    if fuel > 0 then
      if let .const c _ := e.getAppFn then
        if !blocked.contains c then
          if let some e' ← unfoldDefinition? e then
            return ← pr (fuel - 1) e'
          else if let some e' ← forceDelta e then
            return ← pr (fuel - 1) e'
    match e with
    -- The head must be reduced too, not merely copied. Found 2026-09-06: with
    -- `let f := e.getAppFn` the head of `(↑r A B n).1` is a `.proj`, not a `.const`, so the
    -- unfolding branch above never fires and the whole reduction freezes there — again with
    -- identical output at every fuel. Reduce the head, rebuild, and re-run `whnfCore` so the
    -- beta/proj redexes the head reduction just exposed actually fire.
    | .app .. =>
      let f ← pr fuel e.getAppFn
      let args ← e.getAppArgs.mapM (pr fuel)
      let e' := mkAppN f args
      let e'' ← whnfCore e'
      if e'' == e' then return e' else pr fuel e''
    | .lam n t b bi => withLocalDecl n bi t fun x => do
        mkLambdaFVars #[x] (← pr fuel (b.instantiate1 x))
    | .mdata _ b => pr fuel b
    -- A stuck projection MUST be descended into, or the whole reduction stops dead at it.
    -- Found 2026-09-06: without this case `mfiV cm r n` — which is `(r.val …).1` — froze at
    -- `↑r` and produced the SAME output at fuel 6, 12 and 25, i.e. a fixed point that was not
    -- the normal form. `whnfCore` cannot reduce `.proj` until the structure is a constructor
    -- application, which needs delta on the argument, which only happens if we recurse.
    | .proj s i b => do
      let b' ← pr fuel b
      let e' := Expr.proj s i b'
      let e'' ← whnfCore e'
      if e'' == e' then return e' else pr fuel e''
    | _ => return e

-- The FUEL-FREE reducer (2026-09-08) — the experiment this file's header named,
-- ⚠ RUN AND **REFUTED**. Kept as the record of the measurement. Use `knf`/`runK` below.

/-!
## The fuel-free reducer: the hypothesis was wrong

Dropping `fuel` and memoising on `ExprStructEq` alone makes the reduction go deeper and the
result larger; sharing was not the blocker. Figures and three side findings in the notes.
Do not re-run this expecting a different answer; run `knf` instead.
-/

/-- The state of the fuel-free reducer: the memo (keyed on `ExprStructEq` **alone**, which is
the whole point — the fuelled version keys on `(fuel, ExprStructEq)` and so cannot share the
same subterm reached at two different fuels), a visit counter, and an abort flag.

Dropping fuel removes the termination guarantee, so the counter replaces it: at `prCap`
visits the reducer stops descending and returns what it has, with `aborted := true`. It never
runs unbounded. -/
structure PRState where
  memo : Std.HashMap ExprStructEq Expr := {}
  visits : Nat := 0
  aborted : Bool := false
  /-- The visit cap for this run. Lower it to sweep: if the rendered result stops changing as
  the cap rises, the reduction has converged; if it keeps growing, it has not. -/
  cap : Nat := 250000
  /-- `IO.getNumHeartbeats` at the start of the run. -/
  hb0 : Nat := 0
  /-- Abort when this many heartbeats have been spent. Set **below** the 200,000 × 1000 default
  budget so the reducer stops itself and reports, instead of dying at `checkMaxHeartbeats`
  with no statistics. No limit is raised anywhere. -/
  hbLimit : Nat := 120000000
  /-- Set when `hbLimit` rather than `cap` is what stopped the run. -/
  hbAborted : Bool := false
  /-- The head constant the reducer was working on last, and what it was doing to it. Read
  after a run that threw: a `Meta` call is not interruptible, so if one call eats the whole
  heartbeat budget this is the only record of which one. -/
  lastConst : Name := .anonymous
  lastStage : String := "—"
  /-- Leave type-valued subterms unreduced (see `core`). **Measured 2026-09-08: off by
  default, because it buys nothing.** On the two induction targets it changed the aborted
  size by 3 objects in 1.5 million (1,500,524 → 1,500,567; 6,503,304 → 6,503,301) — the
  blow-up is entirely value-level — while it *enlarges* the small displays (`acSpike`'s
  normal form went 162 → 219 objects, with unreduced `Ty.interpret` types left in). -/
  skipTypes : Bool := false
  /-- The blocklist for this run — the output vocabulary, per target. Defaults to `blocked`;
  a caller can widen it (`run2p … (extra := [``termMajorizer])`) to keep a constant symbolic
  when unfolding it is what explodes. -/
  blk : Std.HashSet Name := blocked

abbrev M2 := StateRefT PRState MetaM

/-- Hard node cap. Same order as `Probes/NestingDepth.lean`'s 250,000. -/
def prCap : Nat := 250000
/-- Recursion-depth cap, so a pathological chain aborts rather than overflowing the stack. -/
def prDepthCap : Nat := 3000

/-- `Prod.fst e` / `Prod.snd e` as `(isSnd, e)`.

**Why this needs its own case, measured 2026-09-08.** `mfiU`/`mfiV` read the bound off a pair
with `.1`/`.2`, which elaborate to `Prod.fst`/`Prod.snd` *applications* (not `Expr.proj`). On
the induction target, `unfoldDefinition?` at such a node uses **smart unfolding**: it whnfs the
pair argument to expose a `Prod.mk`, and that single call runs the entire realizer computation
and eats the whole 200,000-heartbeat budget in one uninterruptible step — the reducer's own
visit cap and heartbeat guard never get a turn (visit 154, ≈5.4 s, at every cap). So the
projection is reduced **by hand**: reduce the pair under our control first, then select. -/
def prodProj? (e : Expr) : Option (Bool × Expr) :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Prod.fst _, #[_, _, p] => some (false, p)
  | .const ``Prod.snd _, #[_, _, p] => some (true, p)
  | _, _ => none

/-- **Fuel-free partial delta-reduction**: reduce to a normal form with respect to `blocked`
alone, memoising on `ExprStructEq` only.

Identical to `pr` except that (a) there is no fuel, so unfolding continues until every head is
either blocked or stuck, and (b) the memo key is the expression alone, so a subterm reached
twice is reduced once. Bounded by `prCap` visits and `prDepthCap` depth. -/
partial def pr2 (depth : Nat) (e : Expr) : M2 Expr := do
  if (← get).aborted then return e
  if let some v := (← get).memo[ExprStructEq.mk e]? then return v
  if depth > prDepthCap then
    modify fun s => { s with aborted := true }
    return e
  modify fun s => { s with visits := s.visits + 1 }
  let st ← get
  if st.visits > st.cap then
    modify fun s => { s with aborted := true }
    return e
  if st.visits % 64 == 0 then
    if (← IO.getNumHeartbeats) - st.hb0 > st.hbLimit then
      modify fun s => { s with aborted := true, hbAborted := true }
      return e
  let r ← core depth e
  modify fun s => { s with memo := s.memo.insert (ExprStructEq.mk e) r }
  return r
where
  core (depth : Nat) (e0 : Expr) : M2 Expr := do
    if ← isProof e0 then return e0
    -- Type-valued subterms carry no arithmetic and are where the size goes: an argument like
    -- `Ty.interpret X (wTy A).hat` expands into the whole formula's structure. Leave them
    -- alone, exactly as proofs are left alone. Cheap syntactic test — no `whnf` on the type.
    if (← get).skipTypes then
      if (← inferType e0).isSort then return e0
    if let .const c0 _ := e0.getAppFn then
      modify fun s => { s with lastConst := c0, lastStage := "whnfCore" }
    let e ← whnfCore e0
    if let some (isSnd, p) := prodProj? e then
      modify fun s => { s with lastStage := "prodProj" }
      let p' ← pr2 (depth + 1) p
      if p'.isAppOfArity ``Prod.mk 4 then
        let as := p'.getAppArgs
        return ← pr2 (depth + 1) (if isSnd then as[3]! else as[2]!)
      else
        return mkAppN e.getAppFn (e.getAppArgs.set! 2 p')
    if let .const c _ := e.getAppFn then
      if !(← get).blk.contains c then
        modify fun s => { s with lastConst := c, lastStage := "unfoldDefinition?" }
        if let some e' ← unfoldDefinition? e then
          return ← pr2 (depth + 1) e'
        else if let some e' ← forceDelta e then
          return ← pr2 (depth + 1) e'
    match e with
    | .app .. =>
      let f ← pr2 (depth + 1) e.getAppFn
      let args ← e.getAppArgs.mapM (pr2 (depth + 1))
      let e' := mkAppN f args
      if (← get).aborted then return e'
      let e'' ← whnfCore e'
      if e'' == e' then return e' else pr2 (depth + 1) e''
    | .lam n t b bi => withLocalDecl n bi t fun x => do
        mkLambdaFVars #[x] (← pr2 (depth + 1) (b.instantiate1 x))
    | .mdata _ b => pr2 (depth + 1) b
    | .proj s i b => do
      let b' ← pr2 (depth + 1) b
      let e' := Expr.proj s i b'
      if (← get).aborted then return e'
      let e'' ← whnfCore e'
      if e'' == e' then return e' else pr2 (depth + 1) e''
    | _ => return e

/-- Reduce a constant with the fuel-free reducer and log time, visits, whether the cap fired,
`Expr.numObjs`, and the rendered result. -/
def run2 (nm : Name) (chars : Nat := 3000) (cap : Nat := prCap) : MetaM Unit := do
  let e ← mkConstWithLevelParams nm
  let t0 ← IO.monoMsNow
  let (r, st) ← (pr2 0 e).run { cap := cap, hb0 := ← IO.getNumHeartbeats }
  let t1 ← IO.monoMsNow
  let n : Nat ← liftM (m := MetaM) r.numObjs
  logInfo m!"=== {nm} FUEL-FREE  time={t1 - t0}ms  visits={st.visits}  \
capAbort={st.aborted}  hbAbort={st.hbAborted}  numObjs={n}"
  let s := toString (← ppExpr r)
  logInfo (m!"{s.take chars |>.toString}")

/-- Like `run2`, but the state lives in a ref held by the caller, so a heartbeat timeout inside
the reduction is **caught and reported with the statistics reached** instead of killing the
command. This is what distinguishes "the visit cap fired" from "one `whnfCore` call ate the
whole heartbeat budget". -/
def run2p (nm : Name) (chars : Nat := 3000) (cap : Nat := prCap) (extra : List Name := []) :
    MetaM Unit := do
  let e ← mkConstWithLevelParams nm
  let hb ← IO.getNumHeartbeats
  let bl := extra.foldl (fun (s : Std.HashSet Name) n => s.insert n) blocked
  let ref ← IO.mkRef ({ cap := cap, hb0 := hb, blk := bl } : PRState)
  let t0 ← IO.monoMsNow
  -- A heartbeat timeout is a *runtime* exception, which plain `try`/`catch` (and `<|>`)
  -- deliberately re-throw — measured 2026-09-08, both silently failed to catch it.
  -- `tryCatchRuntimeEx` is the one that does.
  let r? ← tryCatchRuntimeEx
    (do let r ← ReaderT.run (pr2 0 e) ref; pure (some r))
    (fun ex => do logInfo m!"(reduction threw: {ex.toMessageData})"; pure none)
  let t1 ← IO.monoMsNow
  let st ← ref.get
  logInfo m!"=== {nm} FUEL-FREE cap={cap}  time={t1 - t0}ms  visits={st.visits}  \
capAbort={st.aborted}  hbAbort={st.hbAborted}  finished={r?.isSome}  \
last={st.lastConst} ({st.lastStage})"
  match r? with
  | some r =>
    let n : Nat ← liftM (m := MetaM) r.numObjs
    logInfo m!"numObjs={n}"
    let s := toString (← ppExpr r)
    logInfo (m!"{s.take chars |>.toString}")
  | none => pure ()

/-- Reduce an already-elaborated term (not a constant) with the fuel-free reducer. -/
def run2e (label : String) (e : Expr) (chars : Nat := 3000) (cap : Nat := prCap) :
    MetaM Unit := do
  let t0 ← IO.monoMsNow
  let (r, st) ← (pr2 0 e).run { cap := cap, hb0 := ← IO.getNumHeartbeats }
  let t1 ← IO.monoMsNow
  let n : Nat ← liftM (m := MetaM) r.numObjs
  logInfo m!"=== {label} FUEL-FREE  time={t1 - t0}ms  visits={st.visits}  \
capAbort={st.aborted}  hbAbort={st.hbAborted}  numObjs={n}"
  let s := toString (← ppExpr r)
  logInfo (m!"{s.take chars |>.toString}")

-- The KERNEL-driven reducer (2026-09-08) — `Kernel.whnf` in place of `Meta.whnfCore`

/-- **Normalise by repeated `Lean.Kernel.whnf`.**

Why: on the induction targets the `Meta`-level reducer above dies inside `unfoldDefinition?`
(one call eats the whole heartbeat budget) while the *kernel* reaches a stuck head in under a
second — the same asymmetry `MonotoneLaneB` records for `kernel_rfl` against `Meta.isDefEq`
(`Meta.whnf` caches closed terms only; the kernel caches by structure). So the display tool is
driven by the kernel here: whnf the node, then recurse into the children of the result.

There is no blocklist: the kernel stops on its own at a stuck head (`Decidable.rec` on a
symbolic comparison, `g 0`, `Nat.add` of symbolic arguments), which is exactly the arithmetic
vocabulary wanted. It consumes **no heartbeats**, so the visit cap is the only bound — keep it
low. A kernel exception (type error in an open subterm) leaves the node untouched. -/
partial def knf (depth : Nat) (e : Expr) : M2 Expr := do
  if (← get).aborted then return e
  if let some v := (← get).memo[ExprStructEq.mk e]? then return v
  if depth > prDepthCap then
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
  kcore (depth : Nat) (e0 : Expr) : M2 Expr := do
    if ← isProof e0 then return e0
    -- The blocklist has to be consulted BEFORE the whnf, not after: `Kernel.whnf` of
    -- `max a b` is already `Decidable.rec …` and of `a + b` already a `Nat.rec` Church
    -- iteration — the "`#reduce` goes too far" failure, one level down. Measured: without
    -- this, `mfiV … (1, g)` normalises to 22,904 objects of `Decidable.rec`/`Nat.rec`.
    let bl := (← get).blk
    let blocked? := match e0.getAppFn with
      | .const c _ => bl.contains c
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

/-- Run `knf` on a constant and report time, visits, cap status, `Expr.numObjs`, result. -/
def runK (nm : Name) (chars : Nat := 3000) (cap : Nat := 4000)
    (extra : List Name := []) (unblock : List Name := []) : MetaM Unit := do
  let e ← mkConstWithLevelParams nm
  let bl0 := extra.foldl (fun (s : Std.HashSet Name) n => s.insert n) blocked
  let bl := unblock.foldl (fun (s : Std.HashSet Name) n => s.erase n) bl0
  let t0 ← IO.monoMsNow
  let (r, st) ← (knf 0 e).run { cap := cap, blk := bl }
  let t1 ← IO.monoMsNow
  let n : Nat ← liftM (m := MetaM) r.numObjs
  logInfo m!"=== {nm} KERNEL cap={cap}  time={t1 - t0}ms  visits={st.visits}  \
capAbort={st.aborted}  numObjs={n}"
  let s := toString (← ppExpr r)
  logInfo (m!"{s.take chars |>.toString}")

/-- Reduce a constant at the given fuel and log the time, the `Expr.numObjs` (NEVER a tree
traversal — the sharing ratio here is ~10^5) and the rendered result. -/
def run (fuel : Nat) (nm : Name) (chars : Nat := 3000) : MetaM Unit := do
  let e ← mkConstWithLevelParams nm
  let t0 ← IO.monoMsNow
  let (r, _) ← (pr fuel e).run {}
  let t1 ← IO.monoMsNow
  let n : Nat ← liftM (m := MetaM) r.numObjs
  logInfo m!"=== {nm} fuel={fuel}  time={t1 - t0}ms  numObjs={n}"
  let s := toString (← ppExpr r)
  logInfo (m!"{s.take chars |>.toString}")

-- The bound, as arithmetic. Expect
--   fun M h a b => maxT nat (Rounding.pairN (2 * ((a + b) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0
#eval show MetaM Unit from run 12 ``Metatheorems.ExprBound.tgtU 2500
-- The discriminator: same shape, no `maxT`.
#eval show MetaM Unit from run 12 ``Metatheorems.ExprBound.tgtU1 2500
-- Fixed point: fuel 30 agrees with fuel 12.
#eval show MetaM Unit from run 30 ``Metatheorems.ExprBound.tgtU 2500

-- The SAME two targets through the fuel-free reducer — the regression check. Expect the same
-- two outputs as fuel 12/30 above, `maxT` present in the first and absent in the second.
#eval show MetaM Unit from run2 ``Metatheorems.ExprBound.tgtU 2500
#eval show MetaM Unit from run2 ``Metatheorems.ExprBound.tgtU1 2500

end ExprBound
end Metatheorems
