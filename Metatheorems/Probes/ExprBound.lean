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
  sub-majorant re-evaluation bites. One encouraging structural point: the memo is keyed on
  `(fuel, ExprStructEq)`, so it *does* share across repeated sub-majorants — the direction that
  blowup would need.
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
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args ← e.getAppArgs.mapM (pr fuel)
      return mkAppN f args
    | .lam n t b bi => withLocalDecl n bi t fun x => do
        mkLambdaFVars #[x] (← pr fuel (b.instantiate1 x))
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
