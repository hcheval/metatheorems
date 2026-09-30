# Probes/BoundPrintDemo.lean

## module header

### Structural mode — measured 2026-09-08, all on this machine

| target | depth 0 | 1 | 2 | 3 | 6 |
|---|---|---|---|---|---|
| `Demo.linearInduction` | 3 nodes, 4 ms | 7, 3 ms | 14, 4 ms | 20, 4 ms | 40, 8 ms |
| `Demo.doubling` | 3, 0 ms | 4, 0 ms | 6, 1 ms | 9, 1 ms | 19, 2 ms |
| `ProofMode.real_mct_p2` | 3, 1 ms | 6, 2 ms | 8, 1 ms | 11, 3 ms | — |

…and pushed on the large one, which is the claim worth measuring:

| `real_mct_p2` depth | 8 | 10 | 12 | 15 | 20 | 25 | 30 | 40 |
|---|---|---|---|---|---|---|---|---|
| nodes | 69 | 140 | 268 | 661 | 2241 | 5652 | 11978 | **20001 (cap)** |
| wall | 11 ms | 21 ms | 30 ms | 55 ms | 149 ms | 331 ms | 675 ms | 1208 ms |

**Structural mode is safe on any proof, and this is what "safe" means**: the node cap
(`Cfg.maxNodes = 20000`) is an absolute bound on the output, growth to it is smooth (≈×2 per
2–5 levels), nothing is ever evaluated, and the whole depth sweep above on the project's
largest derivation costs under 4 s in total. At depth 40 the cap fires, the listing says so,
and the command still returns in 1.2 s.

**Where it stops being READABLE is far below that**: depth 3 (11 nodes) is a slide; depth 8
(69 nodes) is a page; depth 12 (268) is a reference listing you scroll; beyond ≈15 it is data,
not a display. So the useful dial on `real_mct_p2` is 1–8, and the cap is a guard rail rather
than a working range.

`#bound Demo.stepOnceR depth 3` gives byte-identical output to `#bound Demo.stepOnce
depth 3` (20 nodes): the command peels `monotone_soundness` so the realizer and the derivation
are the same target.

### Evaluative mode — measured 2026-09-08, default cap 4000 visits

| target | point | wall | visits | capAbort | `numObjs` | result |
|---|---|---|---|---|---|---|
| `mfiV … linearR` | `5` | 2.42 s | 1 | false | 1 | `5` |
| `mfiV … linearR` | symbolic `n` | 2.75 s | 74 | false | 2988 | stuck `Nat.rec` iteration |
| `mfiU … linearR` | symbolic `n` | 2.86 s | 75 | false | 2989 | the same, `.2` side |
| `mfiV … stepOnceR` (2026-09-09) | symbolic `xs` | 0.83 s | 6 | false | 24 | `fun xs ↦ xs.2 xs.1` — the bound as a term |
| `mfiU … stepOnceR` (2026-09-09) | symbolic `xs` | 9.25 s | 106 | false | 44915 | converges, but a nested `Decidable.rec` decision tree: the counter side is case analysis, not a readable term |
| `mfiV … doublingR` | `xs 0` | 0.07 s | 1 | false | 1 | `1` |
| `mfiV … doublingR` | `xs 1` | 0.67 s | 1 | false | 1 | `2` |
| `mfiV … doublingR` | `xs 3` | 1.34 s | 1 | false | 1 | `8` |
| `mfiV … doublingR` | `(1, g)` symbolic | 2.17 s | 39 | false | 9840 | `max (g 0 ⊕ g 0) (g 0)` |

**These reproduce `Probes/SymbolicBound.lean`'s independently measured runs.** Its `tgtI`
(the same `pinduction` argument, over `MonotoneMCT.rI`) is 4.24 s / **74 visits** / 2,962
objects against 2.75 s / **74** / 2,988 here; its `tgtE` at `k = 1` (the same doubling
argument, over `ContentExampleNat.rE`) is 3.46 s / **39 visits** / 9,735 objects against
2.17 s / **39** / 9,840 here. Visit counts agree exactly; the object counts differ by <1 %
because the derivations are the Demo's own copies, and the times are the same machine on a
different day. The numerals (`5`, `1`, `2`, `8`) agree with `Probes/DemoChecks.lean`'s
`kernel_rfl` theorems, which is the check that the reducer is not lying.

The symbolic doubling display is the readable one, and it is the bound as arithmetic:

    fun g => Decidable.rec (fun h => Nat.rec (g 0) (fun k ih => maxT nat (Nat.succ ih) ih) (g 0))
                           (fun h => g 0) (…decLe…)

i.e. `max (g 0 + g 0) (g 0)` — `V(1, f*) = 2·f*(0)`, the `k = 1` case of `2^k · f*(0)`.

### The evaluative mode on `real_mct_p2` — NEGATIVE, and the cap does not save it

`mfiV PureWEHA.cm rmR ((fun _ n => n), ((fun n => n+1), 2))` with `rmR = monotone_soundness …
real_mct_p2` (which *elaborates* instantly): `std::bad_alloc` at the 12 GB ulimit after ≈70 s.

**`cap 1` dies the same way**, which locates it exactly: the cap counts *visits*, and the
very first `Lean.Kernel.whnf` call — on the root — is already the whole reduction. A kernel
`whnf` consumes no heartbeats and cannot be interrupted, so **no cap in this design bounds the
work of one call**; only the ulimit does. That is the same wall the MFI lanes record for
`real_mct_p2` (ARCHITECTURE §14.7), reached here through a different instrument, and it is why
the structural mode exists.

Reproduction (NOT in the file — a file of errors is not a green build; run under
`scripts/lean.sh`, which carries the 12 GB cap):

```lean
def rmD : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (Γ := [])
    RealMCT.rmStatement := ProofMode.real_mct_p2
def rmR := monotone_soundness PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm rmD
def rmV : ℕ := mfiV PureWEHA.cm rmR
  (((fun _ n => n) : ℕ → ℕ → ℕ), (((fun n => n + 1) : ℕ → ℕ), (2 : ℕ)))
#bound rmV eval          -- std::bad_alloc at 12 GB, ≈70 s; `cap 1` identical
```

### Two mechanical facts about the command, each of which cost time

- **`depth` counts inference rules, not `Expr` unfoldings.** The first version charged one
  level per definitional unfolding, and then `depth 3` on `real_mct_p2` showed
  `pm_enter → pm_allI → seq_allI` and no rule at all — the budget was spent getting through
  the proof-mode layer. Unfolding to reach a rule is now free (bounded per node by
  `unfoldFuel = 60`), and `depth 0` prints the root rule of a proof-mode derivation.
- **The modifier words are reserved tokens** for every importer, as `#hilbert`'s are. Inside
  `BoundPrint.lean` itself that bites immediately: `{ depth := d }` no longer parses after the
  `syntax` command, which is why `structuralAt` exists.
