# Dialectica/MonotoneSeq.lean

## module header

`Dialectica/MonotoneMemo.lean` gives the `Eq.mpr` entry for `monotone_soundness`; it fires
only where the recursion meets a cast *directly*. In a proof-mode-written derivation the casts
sit under `ProofMode/Packing.lean`'s `seq_*` combinators and `Tactics.lean`'s `pm_*` wrappers,
and unfolding that layer by `simp` is what explodes (`Probes/MonotoneLaneBp.lean`). This module
is the MFI analogue of `Probes/CombinatorLemmas.lean`'s `wit_seq_*` programme: for each
packaging combinator, a lemma

    monotone_soundness … (seq_mp hAB hA) = MRealizer.seqMp … Δ (ms hAB) (ms hA)

whose right-hand side is an explicit `MRealizer` combinator, **Δ-generic** (proved by
structural recursion on the hypothesis context `Δ`, exactly as `wit_seq_mp` is), and never
mentioning the sub-derivation. Applied as rewrite rules (the `mfi_memo` simp set, declared in
`Dialectica/MfiMemoAttr.lean`), they carry `monotone_soundness` through the layer *without
unfolding it* until it meets a raw constructor (where its own equations fire) or a cast (where the
`MonotoneMemo` entry fires). The kernel then reduces the semantic combinators, which are
recursions on `Δ` over the hand-written hat-side λ-terms of `Monotone.lean`.

### `seq_induction` — why it is not the obstacle it was on the term side

`seq_induction` changes the formula it inducts on with depth (`A' := A₀↑ →ᶠ A`), which is what
stopped `sInduction` on the term route: the *witness type* changes, so no fixed type carries a
Δ-generic statement. Here the statement is about `MRealizer cm (pack Δ (∀n A))` for **every**
`A`, and `MRealizer.induction` is already generic in `A` — so `seqInduction` is the same
recursion on `Δ` with `A` generalised, and `ms_seq_induction` is proved by that recursion. The
two `seq_cast`s become `transport`s along `congrArg (pack Δ) _`, whose type sides are
definitionally equal (`wTy` ignores terms), so they cost nothing in the kernel.

### What the `Eq.mpr` of `anorm`/`canorm` still needs

Those casts are `Eq.mpr (le_R_pu_of_le_R._proof_i …) d` with the equation abstracted into an
auxiliary theorem of type `SeqD … B = SeqD … B'`: the formula equation is **not** in the term,
and `Derivable`'s type-constructor injectivity is not available. `monotone_soundness_eqmpr`
takes `hB` as a hypothesis, so it is applied with a discharger — the same normaliser that
produced the cast: `simp (disch := canorm) only [mfi_memo, …]`. See `Probes/MonotoneMemoGates.lean`.

NB. Every lemma's right-hand side elaborates `monotone_soundness … h` with the implicit
formula read off `h`'s own type (`pack Δ B`), which is also what the next lemma's left-hand
side expects; the residual spelling differences (`le_R_pu f g` against its unfolded
`Formula.all …`, from the way `refine pm_allI ?_` unifies) are absorbed because `isDefEq`
checks *implicit* arguments at default transparency after the explicit ones.
