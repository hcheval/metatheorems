# Dialectica/MonotoneMemo.lean

## module header

The normalising proof-mode tactics (`anorm`/`canorm`/`qfer_*_nf`) rewrite the *goal formula*
of a `SeqD`/`Derivable` goal and leave a Lean-level cast — `Eq.mpr`, `Eq.mp`, or `h ▸`
(`Eq.rec`) — in the derivation term (see `Probes/CombinatorLemmas.lean`'s `Eq.mpr` paragraph
and `syntactic_soundness_eqmpr`). To reduce `monotone_soundness … (Eq.mpr h d)` the kernel
must bring `Eq.mpr h d` to a constructor, i.e. decide `Derivable … B ≡ Derivable … B'`, i.e.
`B ≡ B'` — which runs `Term.subst` through the ℚ constants (the delta-expansion pathology of
CLAUDE.md's "Build cost"). On the ℝ lemmas that is a kernel `std::bad_alloc` at 12 GB
(measured in `Probes/MonotoneLaneB.lean`).

`MRealizer.transport` and the three commutation lemmas here are the MFI analogue of
`syntactic_soundness_eqmpr`: applied as rewrite rules **with the formula equation given**, they
turn `monotone_soundness … (Eq.mpr h d)` into `MRealizer.transport h' (monotone_soundness … d)`,
so the cast is rewritten away and **never reduced**.

### Why the transport is cheap

`MRealizer cm A`'s **data** — the majorant `tstar` — lives at `Ty.interpret X (wTy A).hat`, and
`wTy` depends only on a formula's logical skeleton, never on its terms. The casts these tactics
leave differ in the *terms* of a formula (a `subst`/`rename` normalisation), not the skeleton,
so `wTy B ≡ wTy B'` **structurally**, cheaply, without touching `cauchyfy`/`le_Q_dec`. Hence the
data cast is `congrArg wTy h` composed with `Ty.interpret X ·.hat` — its two type sides are
definitionally equal and the kernel collapses it, exactly as `Term.castTy (congrArg wTy …)`
collapses on the term route. The **Prop** component is transported by `subst h` (proof
irrelevance).

**Reach.** These lemmas fire only where `monotone_soundness` is applied *directly* to a cast.
On a proof-mode-written derivation the casts are buried under the `pm_*`/`seq_*` layer, so
reaching them needs the MRealizer analogues of `Probes/CombinatorLemmas.lean`'s `wit_seq_*` —
that is what `Dialectica/MonotoneSeq.lean` supplies. See `Probes/MonotoneLaneBp.lean` for what
this entry does and does not reach on its own, with measurements.
