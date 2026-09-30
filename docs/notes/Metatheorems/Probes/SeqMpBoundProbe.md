# Probes/SeqMpBoundProbe.lean

## module header

### Summary of what was found

**Negative, measured (Part 1):** the realizer `syntactic_soundness` produces for a *single*
`S_comb` — the combinator `seq_mp` inserts once per context element — cannot even be
materialised: `termSize` of it exhausts a 12 GB cap. So does `seq_mp` at context size 1 with
trivial arguments. The cause is not `seq_mp`'s context recursion (that is "only" `×2` per
context element) but the `SRealizer` combinators underneath it: `sSyllogism` copies its first
argument's realizer three times and its second twice, `sExportation`/`sImportation` copy theirs
three times, and `S_comb` nests those ~12 deep. Numbers below.

**Positive, kernel-checked (Part 2):** none of that has to be looked at. Every copy those
combinators make sits in the **counter** component of the realizer, and the **witness**
component is closed under first projection. So, with the sub-realizers as *variables*, each
combinator gets a one-line "witness-projection" lemma (`wapp_sSyllogism`, …), `S_comb`'s
majorant collapses to the semantic `S` (`wapp_S`, at fully abstract `A B C`), and all three
primitives commute:

| primitive | lemma | content |
|---|---|---|
| `seq_of_thm` | `wit_seq_of_thm` | a theorem lifted into context ignores the hypothesis witnesses |
| `seq_id`     | `wit_seq_id`     | hypothesis lookup is projection out of the hypothesis witnesses |
| `seq_mp`     | `wit_seq_mp`     | modus ponens in context is witness application |

`seq_mp_11_numeral` is the demonstration: a literal `0` out of a `seq_mp` at context size 11
(`mct_p2`'s depth), by `simp only` with the lemmas above, in the same file that measured the
underlying term at ~10¹¹ nodes. The kernel never reduces the term; the lemmas are structural
on the *derivation* (~200 nodes at that depth), not on the realizer.

**Scope, stated plainly:** these lemmas are about the witness path *only* — the `wit`/`wapp`
projections. The counter components (where `extractUTerm` reads its `U`) were not touched, and
that is exactly where the duplication lives, so nothing here says `U` is cheap. See "What is
NOT established" at the end.

## The measurements (the comment block before Part 2)

### The measurements

All taken by `#eval` from scratch files importing this module, every invocation wrapped as
`ulimit -v 12000000; timeout 300 lake env lean …` and run one at a time (the machine has 16 GB).
**Do not add live `#eval`s of `termSize` on `sS_*`/`real k` to this file** — two of them are
known to exhaust the cap, and `BoundProbe.lean` records what an uncapped one did.

**Derivation sizes** (`derivSize`): `hT` 1, `hTB` 6, `I_comb` 3, `K_comb` 2, `and_intro` 4,
`pair_h` 23, `eval_h` 27, **`S_comb` 82** (at either instance). One `seq_mp` at context size
`k`, `derivSize (deriv k)` for `k = 0..11`:

    8, 97, 272, 619, 1310, 2689, 5444, 10951, 21962, 43981, 88016, 176083

— ratio → 2, i.e. `G(k) = 2·G(k-1) + |seq_of_thm_{k-1} S_comb|`, exactly `seq_mp`'s double
recursion (`Packing.lean:91-94`). This is the ordinary exponential cost of the *iterated*
deduction theorem; it lives entirely at the `Derivable` level, before any realizer exists.

**Realizer sizes** (`termSize (… ).val`): `sT` 1, `sTB` 71, `sAndWeak'` 9, `sAndPerm'` 14,
`sAndContract'` 78, `sK` 58, `sI` 272, `sAndIntro'` 1,489, **`sPairH` 231,930**,
**`sEvalH` 709,662**, `real 0` 74; and

    termSize sS_TTT.val   →  INTERNAL PANIC: out of memory   (12 GB cap, 31 s)
    termSize (real 1).val →  INTERNAL PANIC: out of memory   (12 GB cap, 34 s)

So a *single* `S_comb` realizer — 82 derivation nodes, every type `unit` — does not fit in
12 GB, and neither does `seq_mp` at context size **1** with trivial arguments. `sI = 272`
shows the mechanism at the smallest scale: `3·78 + 2·9 + 20` glue, the three-plus-two copies
`sSyllogism` makes of its arguments.

**Leaf-copy counts** (`leafCopies`), the estimator that stands in where the term cannot be
built: `I_comb` 5, `K_comb` 3, `and_intro` 15, `pair_h` 2,733, `eval_h` 8,121,
**`S_comb` 41,932,269**; `leafCopies (deriv k)` for `k = 0..11`:

    6, 41932281, 125796828, 293525919, 628984098, 1299900453, 2641733160,
    5325398571, 10692729390, 21427391025, 42896714292, 85835360823

The estimator is validated where the real term exists: `pair_h` 2,733 copies against 231,930
measured nodes (84.9 nodes per leaf copy) and `eval_h` 8,121 against 709,662 (87.4 per copy),
consistent with the 9–78-node leaf realizers plus glue. At that rate one `S_comb` is
≈3.6×10⁹ nodes, and `seq_mp` at `mct_p2`'s context depth 11 is ≈7×10¹² — per call.

**Why the earlier estimate was too optimistic.** `BoundLemmasP2.lean` attributed the cost to
`seq_mp`'s `×|Δ|` recursion and guessed that `S_comb`-style combinators "force genuine
duplication" in `termMajorizer`. Both halves need correcting: the recursion is `×2^|Δ|`, not
`×|Δ|`, and it is not the dominant term anyway — the `4×10⁷` base from one `S_comb` is, and
that comes from `sSyllogism`/`sExportation`/`sImportation` at the `SRealizer` level, the same
family as the `×2`-per-layer `TinyBoundDemo.lean` measured for `syllogism I_comb`. And
`termMajorizer` does *not* duplicate anything here: `sMP`'s realizer is `.app (.fst _) _`,
so `termMajorizer` commutes with each `Derivable.mp` by bare `rfl` (`tm_sMP` below, checked with
variable sub-realizers). The hypothesis that `S_comb` is "not transparent" to `termMajorizer`
the way `weaken` is was wrong in an instructive way: transparency was never the problem, the
count of sites was.

## The idea (the comment block before `section Wit`)

### The idea

A Meta-level `rfl` on `(((closedMajorizer cmE sS_TTB.val).1 f).1 g).1 a = (f.1 a).1 (g.1 a)`
hits the heartbeat limit (not raised). That is the elaborator's `whnf` walking the term; the
kernel's lazy projection semantics are not what `rfl` at the elaborator exercises.

The discipline that works is the project's own: **one combinator per lemma, sub-realizers as
variables.** `SRealizer.imp f g _` has `.val = .mkPair f g`; the witness component `f` of
every combinator on `S_comb`'s path (`sSyllogism`, `sExportation`, `sImportation`, `sAndWeak`,
`sAndPerm`, `sAndContract`) mentions its sub-realizers **only through `.fst`** — every second
and third copy is in `g`, the counter transformer. So a lemma about the *first projection*
of the majorant, stated with the sub-realizer's majorant as an opaque `termMajorizer cm h.val
n e`, never expands `h.val`, needs `termMajorizer_weaken` for the binder crossings, and is
`O(1)` per site. Chained, they collapse `S_comb` to the semantic `S` and then `seq_mp`,
`seq_id`, `seq_of_thm` to what they mean.

Two named projections, `wapp` and `wfst`, keep the lemmas matching on **formulas** rather than
on `Ty.interpret` types: stated with a bare `.1`, `simp` reduces the projection to a raw
`Expr.proj` and then cannot see the product at reducible transparency ("invalid projection …
from type `Ty.interpret ?X (wTy (∃ᶠ …)).hat`"), so the lemma silently fails to fire.

## What is established, and how (the comment block before the `#print axioms`)

### What is established, and how

- **Part 1's numbers** are direct, capped `#eval` measurements, each in its own process; the
  two OOMs are reproducible and the `leafCopies` predictions are consistent with the measured
  sizes where both exist. The `×2` recurrence is read off `Packing.lean` and confirmed by
  the `derivSize` column. The `≈3.6×10⁹`/`≈7×10¹²` figures are the estimator times the
  measured nodes-per-copy; they are *inferred*, not measured.
- **Part 2's lemmas** are ordinary theorems: every tactic block ends in `rfl` or in a `simp
  only` that closes the goal, so a `conv`-without-closer trap of the kind `BoundLemmasP2.lean`
  fell into cannot occur; the `lean_goal` status at the end of `wapp_S`, `wit_seq_mp`'s `cons`
  case and `seq_mp_11_numeral` was checked to be `complete` after the build, and the axiom
  block below is the record. Whole file: ~8 s on top of the imports.
- **`tm_sMP` is `rfl` with variable sub-realizers**, which is the precise sense in which
  "`termMajorizer` commutes with `seq_mp`'s raw `Derivable` combinator in `O(1)`" is true.

### What is NOT established

- **Only the witness path.** `wit`/`wapp`/`wfst` read first components. The counter
  components — `sSyllogism`'s `g`, where `hAB.val` appears twice, `sAndContract`'s
  `natCase (matrixTerm …)` whose majorant goes through `cm.precM`/`recMaj` — have no lemmas
  here. `extractUTerm` reads its `U` from a `.snd` (`Dialectica/Syntactic.lean:104`), so the
  metatheorem's `U` bound is on the untouched side. A counter-side lemma per combinator is
  the same shape but its right-hand side mentions sub-majorants more than once, so the
  *semantic* normal form would grow multiplicatively with depth unless intermediate values
  are named; whether that is a problem in practice is the next probe.
- **Only the three primitives.** `mct_p2` also goes through `Derivable.induction`,
  `forall_rule`/`univ_gen`/`exist_rule`, `qfer` (`qfer_at_nf`, `qfer_no_premise_at_nf`),
  `qf_lem`, `antitone_chain`, `strict_drop`; `sInduction`, `sForallRule`, `sQfer`, … each
  need their own projection lemma, and the `pm_*` tactic definitions in `Tactics.lean` need
  to be unfolded to the primitives (they are `def`s, so `simp only` naming them should do it,
  but this was not tried).
- **The hypothesis of an earlier note is retracted, not confirmed:** `S_comb` *is* transparent
  to `termMajorizer` — see `wapp_S`. The blow-up is in the realizer term's counter half, and
  the witness side of `termMajorizer` never visits it.
