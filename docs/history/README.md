# Historical planning documents

These files are the project's early planning and assessment records, moved here on
2026-09-06. They are kept because their *reasoning* is still instructive, but **none of them
describes the current code**: `CLAUDE.md` (the working record of what is true now) and
`ARCHITECTURE.md` (the reasoning behind the design decisions) supersede all of them, and
`CLAUDE.md` explicitly says to treat the milestone tables below as unreliable.

| file | what it was | when it stopped being current |
|---|---|---|
| `PLAN.md` | The original milestone plan M1–M7 (proof mode, ℚ/ℝ tower, majorizability, metatheorems, space tower). | M1–M4 and M6 landed by 2026-09-04; the plan was never updated after the `syntactic-witnesses` merge (2026-09-01). |
| `FEASIBILITY.md` | The feasibility assessment of the classical metatheorem, with the verdict that `general_metatheorem_classical` as then stated could not be finished (correct) and the decision D-1 to push `¬¬` inside `∀`. | The classical metatheorem was closed 2026-09-02 by the prenexified route it proposed; the rest is superseded by `ARCHITECTURE.md` §12–§14. |
| `DESIGN_DECISIONS.md` | The first design-decision log (intrinsic typing, meta-level Dialectica, no products, `EqX` as a parameter). | Two of its decisions were reversed (products in `Ty` 2026-09-01; base equality defined, `AdmissibleEqX` deleted 2026-09-02). The current table is in `CLAUDE.md`. |
| `SPINOFFS.md` | Ideas for follow-on work (Banach/Hilbert spaces, `pm_theory`, bound printing). | Partly done (normed spaces, `TermPretty`), partly absorbed into `CLAUDE.md`'s tracks. |
| `proof_rules.md` | The Hilbert-system rule list as first written down, before `Derivable` had its final shape. | `Derivable.lean` is the authority (39 constructors as of 2026-09-05). |
| `proof_system_instructions.md` | Early instructions for writing derivations by hand, before the proof mode existed. | `Metatheorems/ProofMode/` and `ProofMode/LADDER.md`. |

`HANDOFF.md`, cited in several places, was deleted on 2026-09-04; its still-enforced
decisions D-1/D-2/D-4 live in `ARCHITECTURE.md` §12 under the same numbering. `REALS_PLAN.md`,
`METATHEOREM_NOTES.md` and `METRIC_PLAN.md`, also cited, were deleted earlier and are not
recoverable from the tree; the citations are historical.
