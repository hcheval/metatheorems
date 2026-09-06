/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.LemBoundDemo
import Metatheorems.Probes.ConjBoundDemo
import Metatheorems.Probes.MonotoneLaneB
import Metatheorems.ProofMode.MCT
import Metatheorems.ProofMode.RealMCT
import Std.Data.HashMap

/-!
# Nesting depth of the composition constructors (measurement only)

`ARCHITECTURE.md` §14.7 / `Probes/ClassicalMfiProbe.lean` locate the MFI wall at the
**nesting depth** of composition nodes: `MRealizer.syllogism` uses `hAB.val n e` three times
and `hBC.val n e` twice with no sharing, so the kernel's cost grows ≈ ×5 per *level*, and a
synthetic chain OOMs at k ≈ 8. Every size number the project has is a **count**
(`derivSize`, `visitD`); nobody had measured the **depth**, which is what decides whether the
wall is 2^12 or 2^30 away.

This is an `Expr`-level DAG walk over the *elaborated* derivation term — it unfolds
definitions (as `MonotoneLaneB.walk` does) but never evaluates, so it survives derivations
whose `#eval derivSize` OOMs at 12 GB. Per derivation it reports

* `dag`   — distinct (structurally shared) `Derivable`-constructor nodes reached;
* `tree`  — the same counted with multiplicity, i.e. the classical `derivSize`;
* `DEPTH` — the longest path through `syllogism`/`mp`/`exportation`/`importation`/`expansion`;
* the per-constructor histogram (DAG-unique occurrences).

**Caveats, stated because they bound what the numbers mean.**

1. Unfolding is restricted to constants whose type telescopes (syntactically) to a
   `Derivable`/`Seq`/`SeqD` application, so `Term.add_Q` and the ℚ/ℝ constants are never
   entered. A `pm_*`/`seq_*` combinator that recurses on the hypothesis context unfolds only
   as far as `Meta.unfoldDefinition?` (smart unfolding) takes it at the literal `Δ`; where it
   stops the walk descends structurally, which still finds every `Derivable` constructor
   mentioned in the body but attributes depth syntactically rather than by the recursion's
   dynamics. So for proof-mode derivations `DEPTH` and `tree` are **structural** figures and
   are lower bounds. For raw-constructor derivations (`lFinalNoLem`, `acFinal`, `lPren`) they
   are exact.
2. `tree` sums memoised children, so it is exact and cheap even when astronomically large —
   unlike `#eval derivSize`, which materialises the value and OOMs.
3. The walk is capped at 250 000 `Expr` nodes (`budgetHit true` ⇒ the row is a **lower
   bound**). Without the cap the three ℝ-layer rows drive the process into the 12 GB
   `ulimit` — delta-expansion creates fresh `Expr`s faster than the memo shares them.

## MEASURED (2026-09-06, worktree `sharing`, `lake build Metatheorems.Probes.NestingDepth`)

| derivation | dag | tree | **DEPTH** | note |
|---|---|---|---|---|
| `LemBoundDemo.lFinalNoLem` | 6 | 6 | **2** | 12-node raw-constructor control |
| `LemBoundDemo.lFinalLem` | 27 | 27 | **9** | the same with a real `Derivable.lem` |
| `prenexify` / `prenexify_gen` / `lPren` | 252 | 253 | **9** | |
| `classical_to_prenex_extended` | 3434 | 3435 | **11** | prenexify + NT + `nn_all_nn` + cast |
| `ConjBoundDemo.acFinal` | 13 | 13 | **4** | the one-`and_contract` term-route stall |
| `MonotoneLaneB.pmFinal` | 202 | 527 | **4** | proof mode, `U = V = 901` reduces today |
| `le_R_pu_of_le_R` | 281 | 446 | **4** | |
| `le_R_of_le_R_pu` | 403 | 893 | **7** | |
| `le_R_trans_core` | ≥47938 | ≥58559 | **≥23** | budget hit |
| `dist_tri_chain` | ≥47938 | ≥58639 | **≥23** | budget hit |
| `ProofMode.mct_p2` | 7244 | 84335 | **12** | converged |
| `ProofMode.real_mct_p2` | ≥47641 | ≥58819 | **≥23** | budget hit |

**The headline, and it corrects a claim in `CLAUDE.md`/`ARCHITECTURE.md`.** Those say the MFI
wall is "×5 per nested syllogism, **134 levels** in `prenexify`". 134 is `prenexify`'s
`syllogism` **count** (`SizeProbe`); its composition **depth is 9**. That is not a smaller
version of the same problem — it is the explanation of the measurements: the synthetic chain
OOMs at k = 8, i.e. at composition depth 9, and `prenexify` is exactly depth 9 and exactly
OOMs. `5^9 ≈ 2·10^6` is where 12 GB runs out; `5^134` would have been unreachable by any
margin and would have made the whole programme hopeless. It is not.

In those units the remaining distance is small and finite:

* `mct_p2` at depth 12 is `5^3 = 125×` beyond the current failure point;
* `real_mct_p2` / `le_R_trans_core` / `dist_tri_chain` at depth ≥ 23 are `≥ 5^14 ≈ 6·10^9×`.

So for ℕ-MCT the wall is ≈ 2^7 away and for ℝ-MCT ≈ 2^33 away — not 2^300.
-/

namespace Metatheorems
namespace NestingDepth

open Lean Elab Meta

/-- The composition constructors — the ones whose `MRealizer` combinator re-evaluates its
sub-majorants, i.e. the ones the ×5 is charged per. -/
def compNames : NameSet :=
  ([``Derivable.syllogism, ``Derivable.mp, ``Derivable.exportation,
    ``Derivable.importation, ``Derivable.expansion] : List Name).foldl
    (fun s n => s.insert n) {}

structure St where
  memo    : Std.HashMap ExprStructEq (Nat × Nat) := {}
  unf     : Std.HashMap Name Bool := {}
  hist    : Std.HashMap Name Nat := {}
  dag     : Nat := 0
  visits  : Nat := 0
  unfolds : Nat := 0
  caught  : Nat := 0
  aborted : Bool := false
  budget  : Nat := 250000

abbrev M := StateRefT St MetaM

/-- Does this type telescope to a `Derivable` application? `Seq`/`SeqD` are reducible
wrappers, so a bounded syntactic delta-expansion of the head constant is used instead of
`whnfR` — `whnfR` is a heartbeat consumer and it is what made the first version of this file
time out on `le_R_trans_core`. -/
private partial def headIsDerivable (env : Environment) : Nat → Expr → Bool
  | fuel, .forallE _ _ b _ => headIsDerivable env fuel b
  -- a `have x := v;` in a statement is a `letE`, and several statements in this project have
  -- one (`prenexify`, `prenexify_gen`); not stripping it silently rejected them
  | fuel, .letE _ _ _ b _ => headIsDerivable env fuel b
  | fuel, .mdata _ b => headIsDerivable env fuel b
  | fuel, e =>
      match e.getAppFn with
      | .const n us =>
          if n == ``Derivable then true
          else if fuel == 0 then false
          else match env.find? n with
            | some ci => match ci.value? with
              | some v => headIsDerivable env (fuel - 1)
                  ((v.instantiateLevelParams ci.levelParams us).beta e.getAppArgs)
              | none => false
            | none => false
      | _ => false

/-- Is `n` a definition whose type telescopes to a `Derivable` application? Those are the only
constants the walk unfolds — so the ℚ/ℝ `Term` constants are never entered. Cached per name. -/
def unfoldable (n : Name) : M Bool := do
  if let some b := (← get).unf.get? n then return b
  let mut r := false
  if (`Metatheorems).isPrefixOf n then
    if let some (.defnInfo di) := (← getEnv).find? n then
      r := headIsDerivable (← getEnv) 8 di.type
  modify fun s => { s with unf := s.unf.insert n r }
  return r

/-- Namespaces whose values are object-language syntax, never derivations. Subterms headed by
one of these are not entered at all. -/
def syntaxPrefixes : List Name :=
  [`Metatheorems.Term, `Metatheorems.Formula, `Metatheorems.Ty, `Metatheorems.Ctx,
   `Metatheorems.Var, `Metatheorems.eqAtType, `Metatheorems.wTy, `Metatheorems.cTy]

/-- Delta-expand the head constant of an application and beta-reduce. Works under binders
(the arguments' loose bvars are simply substituted into the closed body). -/
def deltaBeta (e : Expr) : M (Option Expr) := do
  let .const n us := e.getAppFn | return none
  let some ci := (← getEnv).find? n | return none
  let some v := ci.value? | return none
  return some ((v.instantiateLevelParams ci.levelParams us).beta e.getAppArgs)

mutual

partial def go (e0 : Expr) : M (Nat × Nat) := do
  let e := e0.headBeta
  if let some r := (← get).memo.get? (ExprStructEq.mk e) then return r
  let st ← get
  if st.visits ≥ st.budget then
    modify fun s => { s with aborted := true }
    return (0, 0)
  modify fun s => { s with visits := s.visits + 1 }
  let r ← node e
  modify fun s => { s with memo := s.memo.insert (ExprStructEq.mk e) r }
  return r

partial def node (e : Expr) : M (Nat × Nat) := do
  match e.getAppFn with
  | .const n _ =>
      -- Object-language payloads cannot contain a `Derivable`, and they are the bulk of a
      -- derivation's `Expr`. Not skipping them is what drove the walk into the 12 GB cap.
      if syntaxPrefixes.any (fun p => p.isPrefixOf n) then return (0, 0)
      if let some (.ctorInfo ci) := (← getEnv).find? n then
        if ci.induct == ``Derivable then
          let mut tree := 1
          let mut dep := 0
          for a in e.getAppArgs do
            let (t, d) ← go a
            tree := tree + t
            dep := max dep d
          if compNames.contains n then dep := dep + 1
          modify fun s => { s with
            dag := s.dag + 1,
            hist := s.hist.insert n ((s.hist.getD n 0) + 1) }
          return (tree, dep)
      -- Plain delta + beta. NOT `Meta.unfoldDefinition?`: that runs `whnf` (smart unfolding),
      -- which costs heartbeats and *panics* ("loose bvar in expression") on a derivation
      -- spine sitting under a binder — and those are most of them, so guarding on
      -- `hasLooseBVars` silently loses ~99 % of the walk. Delta + beta is total and cheap.
      if ← unfoldable n then
        if let some e' ← deltaBeta e then
          modify fun s => { s with unfolds := s.unfolds + 1 }
          return (← go e')
      generic e
  | _ => generic e

partial def generic (e : Expr) : M (Nat × Nat) := do
  match e with
  | .app a b         => do let (t1,d1) ← go a; let (t2,d2) ← go b; return (t1+t2, max d1 d2)
  | .lam _ t b _     => do let (t1,d1) ← go t; let (t2,d2) ← go b; return (t1+t2, max d1 d2)
  | .forallE _ t b _ => do let (t1,d1) ← go t; let (t2,d2) ← go b; return (t1+t2, max d1 d2)
  | .letE _ t v b _  => do
      let (t1,d1) ← go t; let (t2,d2) ← go v; let (t3,d3) ← go b
      return (t1+t2+t3, max d1 (max d2 d3))
  | .mdata _ b       => go b
  | .proj _ _ b      => go b
  | _                => return (0, 0)

end

/-- Walk the elaborated value of `nm` and log the table row. Survives a heartbeat timeout or
a panic inside the walk: the row is then marked `partial` and is a lower bound. -/
def report (nm : Name) (budget : Nat := 250000) : MetaM Unit := do
  let some ci := (← getEnv).find? nm | throwError "unknown constant {nm}"
  let some v := ci.value? | throwError "{nm} has no value"
  let ref ← IO.mkRef ({ budget := budget } : St)
  let ok ← try
      let (tree, dep) ← ReaderT.run (go v) ref
      pure (some (tree, dep))
    catch _ => pure none
  let st ← ref.get
  let hs := st.hist.toList.toArray.qsort (fun a b => a.2 > b.2)
  let body := " ".intercalate (hs.toList.map fun (n, k) => s!"{n.getString!}~{k}")
  let head := match ok with
    | some (tree, dep) => s!"dag {st.dag} | tree {tree} | DEPTH {dep}"
    | none => s!"PARTIAL (walk aborted): dag {st.dag} | DEPTH unknown"
  logInfo m!"{nm}\n  {head}\n  exprNodes {st.visits}, unfolds {st.unfolds}, \
    caught {st.caught}, budgetHit {st.aborted}\n  hist: {body}"

-- ============================================================================
-- `prenexify` as `classical_to_prenex_extended` applies it (at `LemBoundDemo`'s matrices)
-- ============================================================================

open LemBoundDemo (lFE lPremE lB0 lC0 lB0_qf lB0_vf lC0_qf lC0_vf)

/-- Step 1 of `classical_to_prenex_extended`: `SizeProbe` counted 347 constructors and
134 `syllogism`s in it. This measures its depth. -/
def lPren : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat]
    (Formula.imp
      (Formula.imp (Formula.all Ty.nat lB0) (Formula.ex Ty.nat lC0))
      (Formula.ex Ty.nat (Formula.ex Ty.nat
        (Formula.imp (lB0.weakenBy Ty.nat)
          (lC0.renameF (Term.Renaming.ext (σ := Ty.nat)
            (Term.Renaming.shift (σ := Ty.nat)))))))) :=
  prenexify lB0_qf lB0_vf lC0_qf lC0_vf

-- ============================================================================
-- The table
-- ============================================================================

open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.LemBoundDemo.lFinalNoLem
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.LemBoundDemo.lFinalLem
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.NestingDepth.lPren
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.prenexify
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.prenexify_gen
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.classical_to_prenex_extended
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.ConjBoundDemo.acFinal
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.MonotoneLaneB.pmFinal
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.le_R_pu_of_le_R
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.le_R_of_le_R_pu
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.le_R_trans_core
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.dist_tri_chain
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.ProofMode.mct_p2
open Lean Meta in
#eval show MetaM Unit from report ``Metatheorems.ProofMode.real_mct_p2

end NestingDepth
end Metatheorems
