# Terms/ClosedSubst.lean

## module header

**Why they live here and not next to their proofs.** `eqAtType` at a base type is
`eq_R (dist i s t) 0ℝ`, so `eqAtType_substF`'s base case is `eq_R_substF` — and
`eqAtType_substF` is proved in `Arithmetic.lean`, *below* `RationalNumbers.lean` and
`RealNumbers.lean` where these used to live. So the whole block moved down, together with
`eq_R_substF` / `le_R_pu_substF` and the two purely-universal facts. Nothing was restated:
these are the same declarations, verbatim, at a lower point in the import order. See
ARCHITECTURE.md §7, which predicted exactly this move.

**Do not prove `subst σ X = X` by `rfl` for a nested closed constant.** `rfl` forces the
constant's whole delta-expansion — `Term.lt_Q_dec` that way costs 28 s. The proofs below are
compositional: unfold one level, push `subst` through the application spine, stop at the
constants already known closed. That needs the `closed_subst` set built up *as the proofs
go*, hence the `attribute` lines interleaved with the proofs rather than collected at the end.

## the rational constants (comment before `attribute [closed_subst] sg_closed_subst …`)

Everything above is small enough that `rfl` is cheap; from here the definitions nest, and
`rfl` has to delta-expand the whole tree. `Term.lt_Q_dec` that way costs 28 s — 14 s in the
tactic and 14 s again in the kernel — because its expansion runs to millions of nodes.

So from here the proofs are *compositional*: unfold one level, push `subst` through the
application spine, and stop at the constants already known closed.

## `ofNat_closed_subst`

Proved by induction rather than `rfl` so the cost is linear in the numeral rather than a
delta-expansion of the whole `succ` tower.
