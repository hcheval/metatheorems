# Probes/DemoChecks.lean

## module header

### Measured cost, per declaration

Kernel type-checking wall clock, `set_option profiler true` on this file, on a loaded 15 GB
machine. These are the numbers quoted beside the Walkthrough's commented commands, so a
presenter knows which cell is slow:

| theorem | time |
|---|---|
| `once_V_3` / `once_V_5` / `once_V_ys_3` | 0.8 / 0.7 / 0.7 s |
| `once_U_3` / `once_U_5` / `once_Phi_3` | 1.3 / 1.3 / 1.7 s |
| `exp_V_0` / `exp_V_3` / `exp_V_5` | 0.06 / 1.3 / 5.5 s |
| `exp_V_ys_0` / `exp_V_ys_2` | 0.05 / 0.7 s |
| `exp_U_0` / `_2` / `_3` / `_5` | 0.05 / 0.8 / 1.6 / 5.6 s |
| `exp_Phi_3` / `exp_Phi_5` | 2.3 / 9.9 s |
| **`exp_V_7`** | **18 s** |
| every `_ne_` refutation control | under 20 ms |

(Re-measured 2026-09-08 with `-D profiler=true -D profiler.threshold=20`, on a machine running
three other Lean builds; the earlier column read 2.6/2.5, 1.2/4.3, 0.9/1.5/5.5, 10.5 and 30 s,
so load noise here is tens of percent and the *shape* is what matters, not the digits.)

`exp_V_7` and `exp_Phi_5` are over the ten-second line and are guarded anyway: the ceiling is
the single claim in §6 most worth having checked mechanically, and `Φ` at `k* = 5` is the only
numeral that comes out of the metatheorem's own entry point rather than its two components.
Together they are most of this file's ≈62 s. Everything here is a *value*-driven cost —
`recMaj` iterating with no sharing — not a derivation-size cost.

### Where the derivations live

`stepOnce` is written in the Walkthrough itself (proof mode, six lines; it replaced
`linearInduction` on 2026-09-09, whose premise `∀u (u =₀ u)` was never consulted, so its
`U = 0` measured nothing). `doubling` is an alias for
`Metatheorems.Examples.Doubling.derivation` — the raw-constructor derivation was moved out of
the Walkthrough on 2026-09-08, because its de Bruijn bookkeeping is a page of `abbrev`s that
says nothing about proof mining. Nothing about the extraction changed: the alias is
definitionally the same term, and every numeral below is unchanged.
