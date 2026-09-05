# Parity with the matching-logic proof mode

Target list, used as a specification. Source: `AML-Formalization/matching-logic/src/ProofMode`
(see `proofmode.md` there). Matching logic is a different system, so the question for each
tactic is *"does this move make sense here"*, not *"can we copy it"*. Where the answer is no,
the reason is recorded — several of those are places our encoding removes the problem rather
than ducking it.

Status: ✅ have · ❌ missing · — not applicable.

## Entering and leaving

| theirs | ours | |
|---|---|---|
| `toMLGoal` | `pmode` | ✅ |
| `fromMLGoal` | — | `Seq` with an empty context *is* `Derivable`, definitionally; `exact` suffices. |

## Structural

| theirs | ours | |
|---|---|---|
| `mlIntro "H"` | `pintro h …` | ✅ |
| `mlRename "H1" into "H2"` | `prename h into k` | ✅ |
| `mlRevertLast` | `prevert` | ✅ definitionally the identity |
| `mlRevert "H"` | `prevert h` | ✅ walks it to the top with exchanges first |
| `mlClear "H"` | `pclear h` | ✅ at any position |
| `mlSwap "H" with "H0"` | `pswap h with k` | ✅ adjacent positions |

## Propositional

| theirs | ours | |
|---|---|---|
| `mlSplitAnd` | `psplit` | ✅ |
| `mlDestructAnd "H" as "H1" "H2"` | `pdestruct h with a b` | ✅ |
| `mlLeft`, `mlRight` | `pleft`, `pright` | ✅ |
| `mlDestructOr "H" as "H1" "H2"` | `pcases h with l \| r` | ✅ |
| `mlExfalso` | `pexfalso` | ✅ |
| `mlDestructBot` | `pcontradiction h` | ✅ |
| `mlExact "H"` | `pexact h` | ✅ |
| `mlAssumption` | `passumption` | ✅ |
| `mlApply "H"` | `papply h` | ✅ peels as many antecedents as needed; since rung 8 the same tactic takes a kernel theorem (`papply e`), so `papplym` is an alias |
| `mlApply "H" in "H0"` | `papply h in k with m` | ✅ |
| `mlConj "H1" "H2" as "HC"` | `pconj h k with m` | ✅ |
| `mlAssert ("H" : phi)` | `phave h : A` | ✅ |
| `mlClassic phi as "H1" "H2"` | `pclassic A with h k` | ✅ guarded by `allowed.lem` |
| `mlDestructImp` | `pdestruct_imp h with k` | ✅ |
| `mlTransitivity` | `ptrans` for `=₀` | ✅ for `→ᶠ` and `↔ᶠ`, chain `papply` — both are proved as scripts in `TacticsTest.lean` rather than added as combinators |

## Meta level — using kernel theorems

| theirs | ours | |
|---|---|---|
| `mlExactMeta` | `pthm e` | ✅ |
| `mlApplyMeta term` | `papply e` (alias `papplym e`) | ✅ implicit arguments and `_` placeholders are read off the goal (rung 8) |
| `mlAdd` | `pfrom h := e` | ✅ |
| `mlApplyMeta term in "H"` | `papplym e in h with k` | ✅ |
| `mlRewrite term at n` | `prw e`, `prw e at n` | ✅ both sides like `rw`, or one occurrence, numbered left to right across the goal |
| `mlDeduct "H"` | — | No deduction theorem at all here. Theirs is restricted to totality patterns; ours does not exist, which is the whole reason the packaging kit does. |

## First order

| theirs | ours | |
|---|---|---|
| `mlIntroAll x` | `pforall` | ✅ takes no name — variable names are generated from the context |
| `mlDestructEx "H" as x` | `pobtain h with x` | ✅ |
| `mlSpecialize "H" with x` | `pspecialize h with k` | ✅ at the bound variable |
| | `pinst h t with k` | ✅ at a term |
| `mlExists x` | `pexists t`, `pbound t` | ✅ `pbound` additionally applies the surface-recursor ban |
| `mlRevertAll x` | — | Their element variables are free in a *named* context that a tactic can generalise over. Ours are de Bruijn: `Γ` is fixed by the statement and `pforall` is the only way into `ρ :: Γ`, so there is no free variable to move back. |
| `mlIntroAllManual`, `mlDestructExManual` | — | The "Manual" variants exist because the automatic freshness side conditions can fail. Intrinsically-typed de Bruijn has no freshness conditions: the eigenvariable condition is discharged by the indices. |

## Equational

| theirs | ours | |
|---|---|---|
| `mlReflexivity` | `prefl` | ✅ |
| `mlSymmetry` | `psym` | ✅ |
| `mlSymmetry in "H"` | `psym in h with k` | ✅ |
| `mlRewriteBy "H" at n` | `prwby h`, `prwby h at n` | ✅ available when the hypothesis context *is* the premise, i.e. holds that one equation. They need the definedness theory and unrestricted reasoning for this; we need QF-ER, whose premise must be quantifier-free and ∨-free. Same shape of restriction, reached from opposite directions. |

## Everything else

| theirs | ours | |
|---|---|---|
| `mlSimpl`, `mlSortedSimpl` | `pnorm`, `anorm` | ✅ substitution normalisation is a user-facing button in both |
| `mlFreshEvar`, `solve_fresh`, `fm_solve` | — | No freshness conditions to solve. |
| `wf_auto2` | — | Ill-formed terms and formulas do not exist: `Term F Γ τ` is intrinsically typed. |
| `use <reasoning> in H` | `pin_system h` | ✅ |
| `try_solve_pile` | — | `Allowed` is a flag, not a constraint system, so there is nothing to *solve*: `pin_system` takes the `Allowed.le` proof directly. |

## Ours with no counterpart there

| | |
|---|---|
| `pinduction` | induction on ℕ with the hypothesis context carried through |
| `pby_contra` | Markov, with the shape check that makes the translation discipline mechanical |
| `pqfac` | QF-AC, forwards |
| `pbound`, `pexists!` | the headline `∃` and its named escape hatch, with the surface-recursor ban |
| `pside` | discharges `allowed` flags and `isQF`/`isVFree` by computation |

## What is left

Every tactic on the list is either implemented or recorded above as not applicable, with the
reason.

## Not yet attempted

Coverage is not maturity, and a tactic table is a weak measure of either. Theirs is exercised
on real developments — `examples/`, a prover, Kore import. This one has been run on about
thirty small theorems, `add_comm`, and nothing else. The honest next test is the MCT
derivation, which does not exist yet in either scripted or hand-built form; until it does,
"we have the moves" is a claim about the list, not about the mode.
