# Probes/ExprBound.lean

## module header

### What it measures, on `MonotoneSpike.acSpike` (13 constructors)

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

### The result

```
fun M h a b => maxT nat (Rounding.pairN (2 * ((a + b) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0
```

`M` and `h` are bound and **absent from the body** — the metric metatheorem's uniformity in
the space, visible as syntax rather than asserted.

**It reproduces the independently-obtained numerals.** `pairN` is Cantor pairing
`triagN (x+y) + x`, so at `(5,9)`: `pairN(56,1) = triag 57 + 56 = 1653 + 56 = 1709`, and at
`(5,1)`: `pairN(24,1) = triag 25 + 24 = 325 + 24 = 349`. Those are exactly
`MonotoneSpike.mfi_acFinal_U_at_5_9` and `_at_5_1`, obtained by `kernel_rfl`.

### The discriminator

`acSpike` (one `and_contract`) against `onceSpike` (contraction-free), same fuel: the `maxT` is
present in the first and absent in the second — the known-true structural difference recorded in
`MonotoneSpike`'s header. The instrument reports it correctly.

### Limits, and what is NOT established

- **`#reduce` is the wrong instrument, but not for the reason expected.** It *terminates* here
  (~11 s). It goes too far: `max` becomes `Decidable.rec`, arithmetic becomes Church iteration,
  and nothing is recognisable. Reduction was never the problem; stopping was.
- **Scale is untested.** This target is 13 constructors, composition depth 4. Nothing here
  bounds behaviour at `mct_p2` (depth 12) or `real_mct_p2` (depth ≥23), where the ×5
  sub-majorant re-evaluation bites.

### Second target, 2026-09-06: `MonotoneMCT.rI` — a proof-mode `pinduction`. NEGATIVE.

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

**That experiment was run on 2026-09-08 and REFUTED** — drop `fuel`, memoise on `ExprStructEq`
alone, and the reduction goes *deeper* and *larger* (`tgtI`: 53,447 → 6,503,304 objects), then
aborts on the heartbeat guard below the cap. Sharing was not the blocker. The figures and the
three side findings are at the `pr2` section below.

**What works instead: reduce with the KERNEL** (`knf`/`runK`, at the bottom of this file).
`Lean.Kernel.whnf` consumes no heartbeats and has the structural cache `Meta.whnf` lacks, so it
converges where every `Meta`-level variant aborts — every `KERNEL` run in
`Probes/SymbolicBound.lean` reports `capAbort=false`, every `Meta` run reports an abort. That
is the same asymmetry `MonotoneLaneB` records for `kernel_rfl` being the evaluator of record,
and it is the result of this line of work.
- **Proof-mode derivations need `mfi_push` first**, since `Derivable.rec` cannot fire until the
  `pm_*`/`seq_*` layer and its `Eq.mpr` casts are rewritten away. Raw-constructor derivations
  like this one need nothing.
- Residual cosmetic noise: `maxT nat` should print as `max`, and `2^(0+1)` should normalise.
  A delaborator and a `norm_num` pass on the result; not done.

**`knf`/`runK` now also exist in the library**, as `BoundPrint.knf` behind
`#bound <name> eval [cap n]` (`Metatheorems/BoundPrint.lean`, in the umbrella). The copy here
is kept as the record of the measurements above; new evaluative runs should use the command,
whose own measurements — including that its visit cap does **not** bound the work of a single
`Kernel.whnf`, so `real_mct_p2` still `bad_alloc`s at 12 GB — are in
`Probes/BoundPrintDemo.lean`.

The same fuel-plus-blocklist design is what `Hilbert.lean`'s `shouldUnfold` wants: it
is currently a *binary* predicate that stops at the whole `ProofMode` namespace, which is why
`#hilbert … all` cannot expand a proof-mode derivation at all.

## the fuel-free reducer (the `/-! … -/` block before `PRState`)

## The hypothesis, and why it was wrong

This file's header proposed dropping `fuel` and memoising on `ExprStructEq` alone, on the
theory that keying the memo on `(fuel, ExprStructEq)` was defeating sharing and that sharing
was the blocker. **It is not.** Dropping fuel makes the reduction go *deeper* and the result
*larger*:

| target | cap 500 | cap 2000 | cap 8000 / 30000 |
|---|---|---|---|
| `SymbolicBound.tgtI` | 501 visits, **53,447** objects | 704, **6,503,304** | 704, **6,503,304** |
| `SymbolicBound.tgtE` | 501 visits, **1,500,524** | 512, 1,500,524 | 512, 1,500,524 |

The figures stop changing not because the reduction converged but because it aborts at the
same place every time — 704 / 512 visits, on the heartbeat guard, *below* the cap. Sharing was
never the blocker. **The blocker is that `Meta.whnf` has no structural cache and a heartbeat
budget; the kernel has the cache and no budget.** That is what `knf` exploits, and it is the
result of this lane.

Three further measurements, each of which cost time to find:

1. **A single `Meta` call can eat the whole 200,000-heartbeat budget, uninterruptibly.** The
   first version died at visit 154 with `lastConst = Prod.snd`, `lastStage = unfoldDefinition?`:
   `mfiU`/`mfiV` read the bound with `.1`/`.2`, which are `Prod.fst`/`Prod.snd` *applications*,
   and smart unfolding whnfs the pair argument to expose a `Prod.mk` — i.e. runs the entire
   realizer computation in one step. `prodProj?` below handles projections by hand, which moved
   the wall to `termMajorizer`.
2. **A heartbeat timeout is a RUNTIME exception.** Plain `try`/`catch` and `<|>` both silently
   re-throw it; `tryCatchRuntimeEx` is the one that catches. Without it every diagnostic run
   just failed the build with no statistics to show for it.
3. **Skipping type-valued subterms buys nothing**: 1,500,524 → 1,500,567 and 6,503,304 →
   6,503,301. The blow-up is entirely value-level. The flag is kept but defaults to `false`,
   because it *enlarges* small displays (`acSpike` 162 → 219 objects).

Do not re-run this experiment expecting a different answer; run `knf` instead.
