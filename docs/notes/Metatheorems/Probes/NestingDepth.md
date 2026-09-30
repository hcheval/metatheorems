# Probes/NestingDepth.lean

## module header

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
