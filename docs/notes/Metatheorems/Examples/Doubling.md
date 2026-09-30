# Examples/Doubling.lean

## module header

**Why it lives here rather than in `Demo/Walkthrough.lean`.** The de Bruijn bookkeeping above
is a page of `abbrev`s and intermediate formulas that says nothing about proof mining, and on
a screen it buries the one line that does. The walkthrough now shows the statement, the alias
`Demo.doubling := Examples.Doubling.derivation`, and the extraction; the bookkeeping is here.

**Why raw constructors and not the proof mode.** Measured, in
`Probes/ContentExampleNat.lean`, where this derivation was first built: the *same argument*
written with `pmode/pinduction/pinst/papply/pobtain/pexists/ptrans/prwby` is **42,747**
constructors — 295× — and its bound reduces only at `k* = 0`, against `k* = 7` here. On this
example the proof mode is a liability for extraction, not the route to it (`ARCHITECTURE.md`
§14.8).

That measurement was re-run on 2026-09-08 against *this* statement and `PureWEHA`, before the
move, to check that a leaner script could not clear the demo's gate (`V` at `k* = 0, 3, 5`).
It cannot. The `pmode/pinduction/pinst/papply/pobtain/pexists/ptrans/prwby` form — no `anorm`,
no `canorm`, so none of the `Eq.mpr` casts §14.7 blames — gives `V(0) = 1` by `kernel_rfl` in
**0.21 s**, and is `std::bad_alloc` at the 12 GB cap at `k* = 1` (≈57 s) and at `k* = 3`
(≈68 s). One step of the recursion is the whole margin. A leaner variant replacing
`ptrans`/`pexact` by a second `prwby` does not elaborate without an `anorm` in between, so it
buys nothing. The bound below reduces to `k* = 7`.

Two things that make the extraction a demonstration rather than an anecdote. The premise is
genuinely **consumed** — `forall_ax k` instantiates `∀u B₀` at `u := k`, once per step, so the
extracted `U` reports a property of the proof and not a default. And **no witness term written
by hand mentions `Term.prec`** (the surface-recursor ban, `ProofMode/Linter.lean`): the
iteration in the bound is produced by the extraction, not smuggled into the derivation.
