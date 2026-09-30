# Probes/BoundProbe.lean

## module header

Two things are already known to be favourable:

* **MCT is pure ℕ.** `mctB₀`/`mctC₀` mention only `leF`, `Term.add`, `.eq0`, `.succ` — no ℚ or
  ℝ constants — so the term-size pathology behind `Term.add_Q` (1,945 nodes written,
  1,880,329 reduced) does not apply.
* **`ι = Empty` makes every space-dependent obligation vacuous**, so `EqXInterp` and the
  premise realizer are one-liners.

## The measurement — RESULT: naive `#eval` is not viable, even at `ι = Empty` (closing block)

**Do not uncomment the `#eval`s below without a memory cap** (`ulimit -v`); on this machine
both exhausted 10 GB and one run with no cap took the whole system down (2026-09-04).

All four `def`s above — `mctE`, `realizerE`, `UtE`, `VtE` — elaborate and type-check
**instantly**, with no `#eval` in the file at all. That is consistent with the full
`lake build` being green at 8088 jobs in ~90s: the kernel never needs `syntactic_soundness
eqxiE spremiseE mctE` reduced to a value to check `mct_bound_p2`'s type, only unified up to
whnf where needed. The cost is specific to *forcing full evaluation*.

Two independent `#eval`s were tried, both capped at 10 GB, both ending in
`INTERNAL PANIC: out of memory`:

    #eval termSize UtE            -- the fully extracted, wrapped functional
    #eval termSize realizerE.val  -- the RAW realizer, before extraction wraps it at all

Since the raw realizer already blows up, **the cost is in `syntactic_soundness`'s structural
recursion over `mct_p2`'s 36-constructor derivation, not in `extractUTerm`'s wrapping**
(`weaken`/`fst`/`snd`/`app`, which only add a handful of nodes). This is the same pathology
CLAUDE.md's hard rule 3 bans `#eval`-ing `Term.interpret` for — eager reduction of a large
structurally-recursive term with no sharing — reproduced one layer up, on a *proof* term
rather than an *interpretation*.

**Conclusion for the extraction plan**: a literal evaluated bound for `mct_p2` specifically
cannot be obtained by `#eval`. If a numeral is wanted, it has to come from kernel-checked
`rfl`/`simp` with NAMED intermediate equation lemmas — the same discipline the `qval` bridge
uses (`QValBridge.lean`: one constant unfolded per lemma, citing already-proved lemmas for the
rest) — applied to `syntactic_soundness`/`extractUTerm`/`termMajorizer`. Whether that is
tractable for the full `mct_p2` script, or only for a much smaller hand-built derivation, is
untested and should be the next probe if this direction is pursued.
