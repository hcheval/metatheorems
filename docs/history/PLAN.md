# Plan to the talk

45 minutes, ~4 weeks out. Abstract due today. Work is heavily agentic, so volume is cheap and
*unknowns* are the constraint — hence the probes come first.

**Deliverable tiers.** D1 must land, D2 should, D3 is bonus.

| | Deliverable | Status if it lands |
|---|---|---|
| **D1** | The metatheorem instantiated; `Φ` evaluates to a number | The talk has a spine |
| **D2** | One input theorem carried through it | The talk has an anchor |
| **D3** | Proof mode demo | The talk has a future |

---

## Phase 0 — probes (day 0–1, before anything else)

Each is hours, and each decides a downstream choice. Do all three before committing effort.

- **P1. Substitution normalisation.** Take a small concrete `A : Formula F Γ`, apply `forall_ax t`,
  and check whether the index reduces to the substituted formula or sticks as `substF A t`.
  Same for `weakenBy` after `forall_rule`.
  → Decides whether the proof mode (E) is plumbing or a schedule risk.
- **P2. Does the intended input derivation need LEM?** `general_metatheorem` (extended system) is
  proved; `general_metatheorem_classical` has the sorry at `Metatheorem.lean:340`. `qf_lem` gives
  case analysis on QF formulas without LEM.
  → Decides which theorem D2 can be built on. **If it needs LEM, change the input, not the theorem.**
- **P3. Does `Metatheorem.lean`'s proof survive a narrowed `Majorizability`?** Replace the ∀ρ
  fields with `maj` at `ρ` and `majorizer` at `ρ →ₜ nat`, see what breaks.
  → Decides whether phase C is a day or a week.

---

## Phase A — first instance (days 1–5) — **critical path, D1**

Nothing in this repo has ever been instantiated; one `instance` exists repo-wide, a `Decidable`.
This is the first time the pipeline runs.

1. `SpaceInterp X F` at `ι = Empty` — all fields indexed by `i : ι`, so vacuous via `Empty.elim`.
2. `EqXInterp`, `AdmissibleEqX` at `ι = Empty` — likewise vacuous.
3. `Premises := fun _ => False`; `premise_realizer := fun _ _ h => absurd h`.
4. `Majorizability` — see phase C. **Do not** discharge it with the degenerate `maj := (· = ·)`
   instance: it typechecks, but the hypothesis collapses to `x_star = x`, `Φ` depends on `x`, and
   the demo would show a bound with no uniformity. Worse than no demo.
5. Apply `general_metatheorem` to a trivial derivation. `#eval Φ`.

**Gate:** a number appears. Everything downstream assumes this.

---

## Phase B — abstract (day 0, in parallel)

Rest it on: the metatheorem as a function; what formalising reveals about its hypotheses; the
mechanical/mathematical split; the cost of writing proofs inside the system. Mention the proof
mode. **Hedge or omit the worked example** — that's D2 and it may not land.

Avoid "automatic extraction": it will be heard as "from an existing proof". The bound comes from
a derivation you supply.

---

## Phase C — majorizability (days 3–7, overlaps A) — **blocks A4, D2, D3**

Options are in `DESIGN_DECISIONS.md` §1. For three weeks, take **option 1** and record the rest.

- Replace the ∀ρ fields with `maj` at `ρ`, `majorizer` at `ρ →ₜ nat`; instantiate `ρ = nat`,
  `majorizer` = running max (computable — keep it that way, or `#eval` dies).
- Restore the `N` threshold if cheap; the paper's statement and your CiE slide both have it, and
  its absence is a visible deviation.
- **State the narrowing out loud** in the talk. It is not the metatheorem in the paper's generality.

Record but do not attempt now: option 2 (definability side condition), option 3 (switch to MFI),
option 4 (hereditarily majorizable model). Option 3 is the principled fix — MFI's soundness
extracts a majorant directly, so there is no majorization step to lose — and it is the natural
follow-up after the talk.

---

## Phase D — input theorem (days 6–14) — **D2**

Target: metastable MCT over **ℕ**. No ℚ, no ℝ, no abstract space. The ℚ pathology that stalled
`RationalNumbers.lean` (sign-case explosion) is absent over ℕ, and the ingredients exist:
`Derivable.induction`, `qf_lem`, and the arithmetic in `Arithmetic.lean` including the
uncommitted `mul_add`/`mul_assoc`.

**Do the shape work on paper first (T2).** `general_metatheorem` takes one `ρ` plus one ℕ each
side; MCT wants sequence, counterfunction and bound. Two ways out:

- *Fit the example*: fix `g` and `K` as closed terms, quantify over the sequence, so
  `ρ = nat →ₜ nat` and `Φ` depends on a majorant of `a` — the constant `K`. No packing. **Prefer this.**
- *Widen the shape*: generalise to `Formula F (Ty.nat :: Γ)` with `Φ : Ctx.interpret X (Γ.map Ty.hat) → Nat`.
  Cleaner, but a change to a theorem on the critical path.

Then check `B₀`, `C₀` really are QF and ∨-free before writing any derivation.

**Fallback at day 10:** if the derivation has not closed, stop. Ship D1, and make the talk about
the instantiation and what formalising the hypotheses revealed. That is still new and still honest.

---

## Phase E — proof mode (days 1–14, parallel, agentic) — **D3**

Isolated: touches nothing in the soundness chain, only wraps existing combinators. Safe to run
alongside A–D. **Gated on P1.**

Three subsystems, not a thin wrapper:

1. Normalisation of `weakenBy` / `subst0` — simp and `rfl` lemmas pushing them through the
   formula constructors. This is the risk.
2. Name map in tactic state, plus quotation syntax for object terms (`t[ x + 0 ]`) resolving
   names to de Bruijn indices.
3. Pretty-printer undoing the map.

Design: goal stays `Derivable (H →ᶠ C)`, context is a *display* over the antecedents, so no
deduction theorem is needed. `intro x` is `forall_rule`; `specialize` is `forall_ax`. Tactics are
thin over `forall_rule`, `forall_ax`, `exportation`, `importation`, `mp`, `syllogism` plus the
385 lines in `PropositionalLemmas.lean`.

Give the agent the **actual `Derivable` goal from phase D** as its target, not a toy.

---

## Phase F — slides and freeze (days 15–21)

Spine: metatheorem-as-function (recap CiE, briefly — that audience saw it) → nothing was
instantiated → what instantiating revealed → first bound → what it cost.

Be explicit that the bound is certified by the metatheorem, not by kernel-checking a hand proof —
that distinction is worth thirty seconds and pre-empts a question.

Code freeze at day 18. Slides only after that.

---

## Parked — do not start

Recorded in `SPINOFFS.md` and `DESIGN_DECISIONS.md`; none is needed for the talk, and several
will be decided *for* you by phase A.

- `RationalNumbers.lean`, `RealNumbers.lean`, `MetricSpaces.lean` — frozen.
- ℚ or abstract `R` as a base type (§6, §6a) — attractive, not on the path.
- Products in `Ty`; syntactic witnesses; switching to MFI or BFI.
- The program route (unverified extractor + kernel-checked certificate).
- Compiling Lean definitions into object `Term`s.
- Automatic generalisation (§G, §G′), filters (§I), the space ladder (§J).
- `Reference/Mine.lean` — a design point, not a result. Keep it off the slides as a headline.

---

## Housekeeping

- Commit the uncommitted +318 lines in `Arithmetic.lean` and the `RationalNumbers` import before
  starting, so a day of prior work is not lost to a stray checkout.
- Consider a branch for the majorizability refactor, since it edits a theorem everything depends on.

---

## Beyond the talk — the overall arc

### First, pick the end state. It changes the order.

**(a) A verified formalisation of the metatheorems** — a proof-theoretic artifact, with instances
and worked examples. Reachable by one person. Venues: ITP/CPP, or logic.

**(b) A tool proof miners actually use** — takes their proofs, returns bounds. Requires the front
end, real analysis inside the system, and years of ergonomics. Probably *not* reachable via the
verified route at all; it is better served by the program route (unverified extractor emitting a
kernel-checked certificate), which is a **fork, not a later stage**.

Everything below assumes (a), with (b) noted as a branch point.

### Milestones

| | Milestone | Size | Depends on |
|---|---|---|---|
| **M1** | First instance; `Φ` evaluates | 3 weeks | — |
| **M2** | Majorizability done properly | 1–3 months | M1 |
| **M3** | Proof mode usable for real derivations | 1–2 months | P1 |
| **M4** | ℚ as a base type; reals as representations over it | 1–2 months | M3 helps |
| **M5** | A real input theorem (MCT over ℝ, or a mining example) | 1 month | M2, M3, M4 |
| **M6** | Abstract spaces — metric, hyperbolic — instantiated | 3+ months | M4, M5 |
| **M7** | Front end: ordinary Lean proofs → the rule calculus | open | everything |

Roughly a year to M6 at part-time pace. M7 is research and may not terminate.

### Notes per milestone

**M2 — the real fix.** Options in `DESIGN_DECISIONS.md` §1. The principled one is switching to the
**monotone functional interpretation**: its soundness extracts a majorant directly, so there is no
majorization step to lose, and only the per-constant facts are needed — i.e. `AbstractMajorizability`,
already proved and currently orphaned. Expected to *shrink* the soundness clauses (no exact
counter-transformer, no Boolean tag at `∨`, which should also retire the ∨-free restriction on
`qfer`). Cheap probe before committing: write out what the implication and contraction clauses
would need under MFI. If those shrink, the rest will.

Second option: keep Dialectica, add `∃ t : Term F [] ρ, ⟦t⟧ si = w` — or better, carry the term as
data with semantic verification — so `all_closed_terms_majorizable` applies. More conservative,
keeps existing proofs, and may want products in `Ty` for the witness tuples.

**M4 — the encoding, killed rather than finished.** `RationalNumbers.lean` is 7746 lines and stuck
because sign-magnitude makes every algebraic law a case explosion. Do **not** finish it. Add ℚ as a
base type interpreted by mathlib's ℚ, with the ordered-ring axioms as purely universal `Premises`
discharged semantically. Atoms stay decidable, which matters because `qf_lem` / `qf_term_correct`
rest on that. Reals then follow Kohlenbach: sequences over ℚ with a fixed modulus, giving the full
ordered-field structure (the inverse takes the separation modulus as an argument, so it is
majorizable). Cost: the `qf_*` machinery must be extended to atoms at the new base type.

Interpret the real type by **Cauchy representations, not mathlib's `ℝ`** — the intensionality is
faithful, and quotienting it away is what makes extensionality statements look realizable when they
are not.

Alternative worth revisiting at M6: Ferreira's abstract type (`DESIGN_DECISIONS.md` §6a) gives
`d : X → X → R` directly with no representatives, at the cost of ring-only structure and no
completeness, and it leans on the bounded functional interpretation.

**M6 — the payoff.** This is where the project stops being about itself. A metatheorem instantiated
for metric or W-hyperbolic spaces, applied to a genuine mining example, is the result that would
interest the community rather than the formalisation crowd.

**A parallel, cheap track throughout.** Compiling a restricted fragment of Lean definitions into
object `Term`s, with generated correctness proofs, would attack the reason encoding work explodes.
Risk: those proofs evaluate composed `Term.interpret`, which is the thing that has burned you
before. Probe whether the compilation is definitional enough that they are `rfl`.

### Decision points

- **After M1**: does anything else break when instantiated? The thing has never been run, so budget
  for unknown defects rather than assuming the known list is complete.
- **Before M2**: MFI or the term-carrying refactor. Decide by the clause probe, not by argument.
- **Before M4**: ℚ base type versus abstract `R`. Decided by whether M6 wants direct `d : X → X → R`
  badly enough to give up decidable atoms.
- **Any time**: whether to fork to (b). The signal would be wanting results proof miners can use
  more than wanting the formalisation to be faithful.

### The strategic risk

The project's value has so far been assumed rather than tested, because nothing has been run. M1 is
the first evidence either way. If instantiation surfaces defects faster than they can be fixed, that
is information about the design, not just a delay — and the program route exists precisely as the
answer to that scenario.

## Risk register

| Risk | Signal | Response |
|---|---|---|
| `Metatheorem.lean` fights the narrowed structure | P3 | Fall back to widening only what breaks |
| `substF`/`weakenBy` stick | P1 | Drop proof mode to D3-optional; do not let it eat phase D |
| Input derivation needs LEM | P2 | Change the input; do not attempt the sorry |
| Shape packing eats phase D | day 8 review | Switch to *fit the example* if not already |
| `#eval` fails (noncomputable leak) | any time | Check `majorizer` was not defined via `Classical.choice` |
| Instantiation surfaces unknown defects | phase A | Expected — the thing has never been run. Budget slack. |
