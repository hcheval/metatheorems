# TermPretty.lean

## module header

### The untyped mirror

`RTerm` is the **untyped** mirror of `Term`: the same seven node shapes with all the type
indices erased to strings. Erasing first is what makes hash-consing possible at all —
`Term F Γ τ` is indexed by its context and type, so two structurally identical subterms of one
realizer generally live at *different* Lean types and cannot be compared, let alone put in a
`HashMap`. `RTerm` has `DecidableEq` and `Hashable`, so they can.

The price of erasing is that the renderer could in principle conflate two distinct terms. That
is checked rather than assumed, in two ways: `size_erase` proves the node count is preserved
exactly (so nothing is silently dropped), and `Probes/TermPrintDemo.lean` carries a negative
control on a pair of terms differing in one constructor.

### Sharing

`share` collects every distinct subterm of the tree together with its occurrence count, binds
the repeated ones as `let`s (smallest first, so a definition only ever refers to earlier ones),
and rewrites the body against them. `expand` inverts that, and the demo checks
`expand (share t) = t` — which is the statement that the shared rendering has not lost
anything.

The number reported as **DAG size** is the count of *distinct* subterms, i.e. the number of
nodes the term has when maximally shared. Tree size is what `#eval tSize` reports.

## `RTerm.openness`

**This is what makes hash-consing correct.** De Bruijn indices are context-relative, so two
*syntactically identical* subterms occurring at different binder depths do not denote the same
thing, and an open subterm cannot be hoisted into a top-level `let` at all. `share` therefore
binds only subterms with `openness = 0`. Dropping this check produces a `let`-listing that
looks fine, round-trips fine as a tree, and is mathematically wrong.
