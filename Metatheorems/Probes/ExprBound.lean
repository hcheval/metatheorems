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

## What it measures, on `MonotoneSpike.acSpike` (13 constructors)

`mfiU (triCm M h) (acSpike M h) (a,b)`, symbolic in `a b M h`:

| fuel | wall | `Expr.numObjs` |
|---|---|---|
| 1 | 2 ms | 86 |
| 2 | 12 ms | 582 |
| 3 | 40 ms | 1154 |
| 8 | 74 ms | 1201 |
| 12 | 84 ms | **167** |
| 30 | 77 ms | 164 |

Size *peaks* around fuel 8 and then collapses as the `termMajorizer`/`monotone_soundness`
spine computes away; fixed point at 12. The intermediate fuels are informative in their own
right: at fuel 3 the bound displays as the **shape of the derivation** (`and_weak`,
`and_contract`, `syllogism` under a `maxT`) before it becomes arithmetic.

## The result

```
fun M h a b => maxT nat (Rounding.pairN (2 * ((a + b) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0
```

`M` and `h` are bound and **absent from the body** — the metric metatheorem's uniformity in
the space, visible as syntax rather than asserted.

**It reproduces the independently-obtained numerals.** `pairN` is Cantor pairing
`triagN (x+y) + x`, so at `(5,9)`: `pairN(56,1) = triag 57 + 56 = 1653 + 56 = 1709`, and at
`(5,1)`: `pairN(24,1) = triag 25 + 24 = 325 + 24 = 349`. Those are exactly
`MonotoneSpike.mfi_acFinal_U_at_5_9` and `_at_5_1`, obtained by `kernel_rfl`.

## The discriminator

`acSpike` (one `and_contract`) against `onceSpike` (contraction-free), same fuel: the `maxT` is
present in the first and absent in the second — the known-true structural difference recorded in
`MonotoneSpike`'s header. The instrument reports it correctly.

## Limits, and what is NOT established

- **`#reduce` is the wrong instrument, but not for the reason expected.** It *terminates* here
  (~11 s). It goes too far: `max` becomes `Decidable.rec`, arithmetic becomes Church iteration,
  and nothing is recognisable. Reduction was never the problem; stopping was.
- **Scale is untested.** This target is 13 constructors, composition depth 4. Nothing here
  bounds behaviour at `mct_p2` (depth 12) or `real_mct_p2` (depth ≥23), where the ×5
  sub-majorant re-evaluation bites.

## Second target, 2026-09-06: `MonotoneMCT.rI` — a proof-mode `pinduction`. NEGATIVE.

`mfiV cmE MonotoneMCT.rI n`, symbolic in the point `n`. Two real bugs in the reducer were
found and fixed on the way (both recorded at their fix sites): a stuck **`Expr.proj`** was
returned untouched, and in the `.app` case the **head was copied rather than reduced**. Each
produced the same symptom — *identical output at every fuel*, i.e. a fixed point that is not
the normal form. **If output does not change with fuel, suspect a missing `Expr` case, not
convergence.**

With both fixed the reduction descends and the iteration becomes visible — at fuel 6 as the
object-level recursor `R[…] ⬝ mtIndBase ⬝ mtIndStep`, at fuel 12 as `recMaj` applied to its
base and step. But it **does not converge**:

| fuel | `numObjs` |
|---|---|
| 6 | 1033 |
| 12 | 1295 |
| 20 | 8125 (1.1 s) |
| 30, 45 | `(deterministic) timeout at whnf` |

Size *grows* where `acSpike`'s peaked and collapsed, and no limit was raised. The reason is
structural: `recMaj` is stuck on the **symbolic** point `n`, so nothing downstream collapses to
arithmetic, while the base and step subterms — each an unreduced
`monotone_soundness … (pm_intro …)` — keep re-expanding along every path. That is the same
per-path re-expansion that defeats evaluation, appearing in the display tool for the same
reason, and the memo does not stop it because it is keyed on **`(fuel, ExprStructEq)`**: the
identical subterm reached at two different fuels is two different keys.

**The obvious next experiment** (untried): drop `fuel` from the design entirely and reduce to a
normal form with respect to the blocklist alone, memoising on `ExprStructEq` only. The blocklist
already stops reduction, so fuel may be doing nothing but breaking sharing. The risk is
non-termination on a recursive definition that always delta-expands, which would need the
recursors added to the blocklist.
- **Proof-mode derivations need `mfi_push` first**, since `Derivable.rec` cannot fire until the
  `pm_*`/`seq_*` layer and its `Eq.mpr` casts are rewritten away. Raw-constructor derivations
  like this one need nothing.
- Residual cosmetic noise: `maxT nat` should print as `max`, and `2^(0+1)` should normalise.
  A delaborator and a `norm_num` pass on the result; not done.

The same fuel-plus-blocklist design is what `Hilbert.lean`'s `shouldUnfold` wants: it is
currently a *binary* predicate that stops at the whole `ProofMode` namespace, which is why
`#hilbert … all` cannot expand a proof-mode derivation at all.
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

end ExprBound
end Metatheorems
