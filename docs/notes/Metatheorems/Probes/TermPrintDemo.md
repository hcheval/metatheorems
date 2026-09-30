# Probes/TermPrintDemo.lean

## module header

### What the sharing numbers are and are not

`CLAUDE.md` Track A item 5 separates three questions about a bound: its growth rate
(structurally astronomical), its **tree** size (astronomical, and an artifact of a
presentation nobody needs) and its **DAG** size — the one that decides whether a human can
read it, and the one explicitly recorded as untested at real scale. The only figure the
project had was a sharing ratio of ≈10⁵ on one `mct_p2`-scale goal at the `Expr` level.

These three terms are a few hundred nodes, so what follows is a **calibration point, not an
answer**. At this scale the ratios are small (see the tables); that is consistent with sharing
mattering much more as terms grow, and it is evidence for nothing stronger.

**One thing it does settle, and it is a correction rather than a calibration.** "Number of
distinct subterms" is *not* the size of the `let`-form a human would read, because de Bruijn
indices are context-relative: an open subterm occurring at two binder depths is two different
terms, and cannot be hoisted into a top-level binding at all. The first version of this file
did hoist them — the listing looked plausible and the round-trip check passed, because as a
*tree* rewriting it is exact. `TermPretty.RTerm.openness` is the fix, and
`TermPretty.openness_erase` is the theorem that erasure preserves scope. So each term is
measured twice: the naive DAG size (an upper bound), and the **written size** of the shared
form, which is the honest figure. On these three the gap is large.

### Correctness

Four checks, because a printer that silently mangles structure is worse than none:

1. `TermPretty.size_erase` (a theorem, proved by induction) plus `nodeCount_eq_tSize_*`
   (`rfl`) say the rendered node count equals what `#eval tSize` reports.
2. `TermPretty.openness_erase` (a theorem) says erasure keeps de Bruijn scope straight — a
   term in context `Γ` erases to something needing at most `Γ.length` binders.
3. `expand (share t) = t` — the hash-consed form expands back to the term it came from, and
   `expandedSize` recomputes the tree size from the shared form without expanding it.
4. A **negative control**: `fst`/`snd` swapped, and two different de Bruijn indices. Both
   pairs have *equal size*, so a size check alone could not tell them apart; erasure keeps
   them distinct and so does the rendering.
