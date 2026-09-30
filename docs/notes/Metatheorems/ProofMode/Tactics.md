# ProofMode/Tactics.lean

## module header

### Where side conditions go

The rules of the extended system carry side conditions — an `allowed` flag, an `isQF` or
`isVFree` check. These cannot be passed as `(by …)` arguments, because at the time such an
argument is elaborated the matrix is still a metavariable: it is fixed only when `refine`
unifies the lemma's conclusion with the goal. They are therefore left as *named holes* and
discharged afterwards by `pside`, which computes when everything is concrete and otherwise
looks in the Lean context.

The one exception is a rule whose matrix comes from a *hypothesis* rather than from the
goal — QF-AC. There the hypothesis argument must be elaborated inline, since nothing else
determines the matrix.

## `pm_destruct`

Stated as a *cut* rather than as an in-place rewrite of one position, so it does not care
where the conjunction sits in `Δ`: the caller proves `A ∧ᶠ B` however it likes (typically
`pexact`), and the two components arrive on top of the context.

## `seqDGoalArgs`

`consumeMData` is load-bearing. Lean's `have`/`obtain` leave the target wrapped in an `mdata`
node, and without stripping it `isAppOf ``SeqD` is false — so every proof-mode tactic used
after a plain `have` failed with "the goal is not a proof-mode sequent", even though the goal
was displayed as a perfectly good sequent box (the delaborator looks through `mdata`, so the
display gave no hint). Measured: `ctor=app, nargs=9` before a `have`, `ctor=mdata,
nargs=0` after.

## the recursor check on user terms (`hasPrec`-style traversal)

The traversal deliberately does not unfold constants: `Term.add` is built from `Term.prec`,
as every primitive-recursive constant must be, and `x + y` is not a smuggled bound. Only an
occurrence the user typed is refused. See `ProofMode/Linter.lean` for why this is the right
reading of "surface", and for the limit of it.

## elaborating a kernel theorem with its context pinned

Pinning by the *expected type* alone does not work: Lean fixes a theorem's `Γ` from its first
explicit argument, before unifying the result type. So the goal's context is injected as a
named argument at the head of the application — which is what lets a theorem mention `x₀`
next to a term from the outer context, the latter then weakening by coercion.

## elaborating a user-written surface term

Decision D-2 (`ARCHITECTURE.md` §12) puts the ban on the surface language as a whole —
instantiation witnesses, `pbound` instantiations, case-split precisions, induction motives —
not only on headline `∃` witnesses. That is deliberately stronger than a headline-only check
and is what makes the non-triviality claim a statement about *expressiveness*: the input
language cannot write the bound, so no enumeration of smuggling routes is needed. The route
that motivated it reached the extracted term through an *instantiation*, never touching an
`∃`, which is exactly why the check has to live here rather than at `∃`-introduction.

## `pspecialize`

The `colGt` matters: without it the bare form would swallow the next line's tactic name as
its `h`.

## `pbound`

This is `bound` v0: a certificate **checker**, not a prover. The user writes the bound; the
tactic checks that it is a bound the extraction could have produced rather than one smuggled
in by hand. It differs from `pexists` only in recording, at the call site, that this is the
headline position — the check itself is the same, because D-2 puts the ban on the surface
language rather than on headline positions specifically.

## `pthm`

Only if that fails is
it retried against the goal's own formula — which is what gives a side condition written as
`rfl`, `qf_lem`'s quantifier-freeness say, something to check against.

The order matters: pinning the formula first would force unification through the goal on
every call, and on a large statement that is where it diverges.

## `papply` (section doc)

Before this the rule was elaborated, probed inside `withoutModifyingState` to count the
antecedents, and then handed back as *syntax* to a `refine` that elaborated and unified it a
second time.

## elaborating a kernel theorem for `papply`

Pinning the goal's formula before the open attempt is what diverged with a stack overflow on
`mct_p1` (`LADDER.md`, "What A3 forced"). The fallback against the goal's formula is what
gives a side condition written as `rfl` something to check against.

## `phave`

The formula is user-written, so the recursor ban applies to the terms inside it: a cut on
`A` contributes `A`'s witness and counter types to the interpretation, which is the same
route to the extracted content that `pinst` has.

The formula is elaborated **once**, against the goal's context, and the resulting expression
is handed to `pm_cut` — not the surface syntax again. Re-elaborating it as a named argument
would leave `pm_cut`'s own `Γ` a metavariable at the moment the formula is processed, and an
`xₖ` token reads its de Bruijn index off exactly that context.

## `pby_contra`

**The shape check comes first, and the tactic is atomic.** Decision D-4
(`ARCHITECTURE.md` §12) makes `by_contra` *be* the Markov rule, and D-1 makes "is this proof
translated?" the question a refusal should provoke. Both require that a wrong-shaped goal be refused before anything is applied
to it — a tactic that half-applies and then complains leaves the user reading errors about a
goal they did not write.

## `pinst`

This is exactly the
route that motivates the ban: a `∀`-premise instantiated at a hand-written iterating term
contributes that term to the Dialectica challenge side, and thence to the extracted bound,
without ever introducing an `∃` for a headline-scoped linter to notice.
