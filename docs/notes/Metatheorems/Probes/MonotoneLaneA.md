# Probes/MonotoneLaneA.lean

## module header

| theorem | `x*` | value | arithmetic normal form reached by `rfl` |
|---|---|---|---|
| `g1_U_at_5_9` (**the gate**) | `(5,9)` | **`1709`** | `max (pairN (2·((5+5)·2^(0+1))) (2^(0+1)−1)) (max (pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)) 0)` |
| `g1_U_at_5_1` (**the crossover**) | `(5,1)` | **`901`** | `max (pairN (2·((5+5)·2^(0+1))) (2^(0+1)−1)) (max (pairN (2·((5+1)·2^(0+1))) (2^(0+1)−1)) 0)` |
| `g1_V_at_5_9` | `(5,9)` | `1709` | `pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)` |
| `g1_V_at_5_1` | `(5,1)` | `349` | `pairN (2·((5+1)·2^(0+1))) (2^(0+1)−1)` |
| `g1_acFinal_U_at_5_9` (G0 re-run) | `(5,9)` | `1709` | `max (pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)) 0` |

Read the two `U` normal forms: `max s₂* (max s₁* 0)`. The outer `max` is `pair_h`'s own
`and_contract` at the premise formula `∀u tB` — the two branches' counters `s₂*` (the
`g`/`tInst2` branch) and `s₁*` (the `f`/`tInst1` branch); the inner `max … 0` is the
`and_contract` inside `and_intro_XY`/`and_intro_YH`, whose second copy is weakened away
exactly as in `acFinal`. At `(5,9)` the first instantiation wins (`1709 > 901`); at `(5,1)`
the second wins (`901 > 349`). **That crossover is the point**: a `U` that reported either
instantiation alone would be a visibly different function (`cUtOnce_at_5_1 = 349`; refuted
here as `g1_U_at_5_1_ne_349`).

## How the normal forms were obtained — not guessed

`arith_nf_rhs` below reduces the goal's right-hand side with `whnfCore` + `unfoldDefinition?`
stopping at the arithmetic vocabulary (`max`, `pairN`, `+`, `*`, `^`, `-`, numerals) and
recursing into arguments — an elaborator-side read-out of what the kernel `rfl` computes.
The `hval … := rfl` steps then check exactly that shape. This is **not** a both-sides-stuck
no-op (trap 12): during development a `have hval : … = max s₁* s₂* := rfl` with the *wrong*
association was tried and **timed out at `isDefEq`** (200 000 heartbeats) — two different
closed arithmetic expressions do not become `rfl`-equal by evaluation at elaboration time —
so a passing `rfl` here certifies the shape, and `decide` then certifies the number.

## Cost, measured (`lake env lean -D profiler=true`, 2026-09-05)

| theorem | `rfl` to normal form (elab) | `decide` | kernel type-checking |
|---|---|---|---|
| `g1_U_at_5_9` (29 constructors, counter side) | **1.51 s** | 1.9 ms | 116 ms |
| `g1_U_at_5_1` | 1.39 s | 1.6 ms | 103 ms |
| `g1_V_at_5_9` (witness side) | 101 ms | 2.2 ms | 25 ms |
| `g1_V_at_5_1` | 142 ms | 1.2 ms | 27 ms |
| `g1_acFinal_U_at_5_9` (13 constructors; spike measured 207 ms) | 270 ms | 2.0 ms | 52 ms |

No option raised. `arith_nf_rhs` itself takes ≈ 300 ms per goal. For scale: the same
counter-side number on the term route is a 200 000-heartbeat `whnf` timeout at 13
constructors (`ConjBoundDemo.acUt_at_5_9`); here 29 constructors with two contractions cost
1.5 s of elaboration. The counter side is ≈ 10× the witness side, as the counter majorant
mentions the sub-majorants more than once (ARCHITECTURE §14.2, "MFI does not remove
composition's duplication") — benign at this scale, since the kernel shares by pointer.

## Scale

`derivSize_tFinalTwice`: `tFinalTwice` is **29** constructors (`acFinal` was 13). All eleven
distinct constructors it uses — `mp`, `forall_rule`, `syllogism`, `exportation`,
`importation`, `and_contract`, `and_weak`, `and_perm`, `forall_ax`, `exist_ax`, `refl0` — go
through `monotone_soundness`'s own cases; `importation` and `and_perm` were not in the spike.

## Non-vacuity

* `g1_U_at_5_9_ne_1708`, `g1_U_at_5_1_ne_900`: exact from below.
* **`g1_U_at_5_1_ne_349`** — the important one: `349` is what a *non*-`max` `U` (following
  `s₁` alone, as the one-instantiation `cUtOnce` does) would give at `(5,1)`. Refuted.
* `g1_U_at_5_1_ne_1709`: the `U` at `(5,1)` is not the `(5,9)` value either — it moves.
