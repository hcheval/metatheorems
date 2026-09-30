# Probes/SymbolicBound.lean

## module header

Measured (this file, 2026-09-08), all converged:

| display | time | visits | `numObjs` |
|---|---|---|---|
| `tgtE` at `k=0` | 113 ms | 4 | **6** |
| `tgtE` at `k=1` | 3.46 s | 39 | 9,735 |
| `tgtE` at `k=2` | 12.0 s | 73 | 15,593 |
| `tgtE` at `k=3` | 30.8 s | 141 | 27,429 |
| `tgtE`, both `k` and `g` symbolic | 8.4 s | 170 | 38,861 |
| `tgtI`, symbolic in `n` | 4.24 s | 74 | 2,962 |

Unrolling is **superlinear in `k`** — 3.5 s, 12 s, 31 s — so do not expect to read the pattern
off at `k = 5`.

## What is PROVED versus what is READ OFF

Proved, kernel-checked, universally quantified in the majorant: `V_closed_0`, that
`mfiV cmE rE (0, g) = g 0` for every `g`. Nothing else.

The general form `V(k, f*) = 2^k · f*(0)` is a **conjecture read off the displays**. The
`k = 1` candidates were probed and the kernel **rejected** the one that looked right; see the
retraction note at `V_closed_0`. Do not promote the reading to a claim.
