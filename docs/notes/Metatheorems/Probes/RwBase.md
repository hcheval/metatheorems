# Probes/RwBase.lean

## module header

`prw` used to hardcode the *pattern's* type to `nat` — `let ρ := Ty.nat` in `prwCore` — even
though `Derivable.qfer` was always general in it. This is the case that hardcoding excluded,
and it is the one metric spaces need: the points live in `X`, the distances in `ℕ`, so a
rewrite `s ↦ s'` has a base-typed pattern inside a numeric goal.

## the base-pattern test (docstring)

Equality at a base type used to be the
abstract `EqX () s s'`, identified by comparing the head against the goal's own `EqX`
parameter; with `EqX` gone it is a genuine `eqAtType` application, and the folded match in
`eqView?` covers it.
