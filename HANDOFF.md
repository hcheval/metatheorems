# HANDOFF v3.1 — One-Month Talk Plan

Status: consolidated record of the design discussion. Not a build mandate; the Track/probe
structure below is the agreed plan. Prior docs (`FEASIBILITY.md` — probe protocol;
`PLAN.md`, `DESIGN_DECISIONS.md`, `SPINOFFS.md` — background) remain as reference for
invariants and rationale. Where they conflict with this document, this document wins.

**v3.1 changes:** §2 base sort corrected from ℚ to ℕ; §3 A2/A3 re-budgeted and reordered;
§4 gains D-4; §8 Rung 4 redefined. Rationale in D-4.

---

## 0. Situation

- Maintainer gave a CiE 2025 talk: T^X types, FOL formulas, `Proof Γ A` derivations,
  Dialectica witness/counter types 𝕎/ℂ, verified soundness (`realize`), and a verified
  `metatheorem` producing bounds from proofs of ∀∃-statements. That talk's future work:
  "formalize proofs in T and compare what is extracted to proof-mining results."
- Since then: a NEW implementation exists WITHOUT HOAS (first-order, de Bruijn syntax).
  This restores syntactic inspectability: linting, tree display, term comparison — all
  things HOAS blocked.
- Constraint: one month to a TALK (not a publication). Must not look like the 2025 talk.
  The bar: one honest demo, one clear idea, no claim that can't survive a question.
- Known pain point: encoded reals (ℝ = ℕ→ℕ) were very hard for coding agents ~4 months ago.
  Treat that as an interface problem (dense representation invariants invisible to the
  agent), not a permanent capability fact — but do NOT put encoded reals on the critical
  path.

## 1. The talk thesis

**"Bounds are properties of proofs, not theorems" — demonstrated mechanically.**
Two different lazy proofs of the SAME statement (monotone convergence / metastable MCT),
machine-extracted to DIFFERENT bounds, with a tracer showing WHERE in the derivation trees
the extractions diverge (the reductio+QF-AC proof vs. the dichotomy-style proof; iterated
g̃ bound vs. budget bound). Supporting exhibits: the vacuity linter catching smuggled
bounds (smuggles B and C).

New relative to 2025 (framework → first real extractions + comparison), new relative to the
literature (nobody has displayed the proof-dependence of mined bounds mechanically), and
every component has a fallback rung.

## 2. Base sort decision: ℕ

**Demo statement:** `a : ℕ → ℕ` nonincreasing and bounded, metastable conclusion
`a n =₀ a (n + g n)`.

Rationale (see D-4): ℚ is not a sort of the object system. `Ty ι = nat | base i | arr`;
object-level ℚ requires Cantor-pair encoding with sign handling — i.e. the stalled
`RationalNumbers.lean` — which is the same representation-layer risk the ℝ retreat was
meant to avoid. ℕ is the only base sort that is genuinely free.

What ℕ preserves: order structure, the pigeonhole, the g̃-iteration in one proof and the
budget in the other. Nothing the thesis depends on is lost.

Encoding, verified in `MCTStatement.lean`:

- `ρ := nat →ₜ nat →ₜ nat`, with `a := h ⌜0⌝`, `g := h ⌜1⌝`, `K := h ⌜2⌝ ⌜0⌝`.
  No product types needed; one majorant for `h` covers all three parameters.
- `B₀ := (a(u+1) ∸ a u =₀ 0) ∧ᶠ (a u ∸ K =₀ 0)` — QF and ∨-free by `rfl`.
- `C₀ := a v =₀ a (v + g v)` — QF and ∨-free by `rfl`.
- The whole statement is accepted by `general_metatheorem` (checked, not assumed).

**Boundedness form.** `all .nat B₀` puts every conjunct under the `∀u`, so a one-off
`a 0 ≤ K` is not expressible as a separate conjunct at that level; it can only appear
duplicated under the binder. The pointwise form `a u ≤ K` above is equivalent given
antitonicity, is already encoded and checked, and puts `K` in the same place in the
extracted bound. Use it. Revisit only if the multi-`∀` premise generalization lands.

**For the slide:** representation-independence of Ψ *survives* the retreat to ℕ in sharper
form — extraction only ever used the order structure of the primes, and at ℕ that is
literally all there is.

## 3. Two-track month plan

**TRACK A — demo critical path** (maintainer + agent, agent above frozen layers only):

- **A0.** Shared arithmetic lemmas, as named closed derivations, `mp`'d into both proofs:
  monus transitivity (`x ∸ y =₀ 0 → y ∸ z =₀ 0 → x ∸ z =₀ 0`), the antitone chain
  (`∀i, a(m+i) ∸ a m =₀ 0`), the strict-drop step (from `x ∸ (K+1) =₀ 0`, `y ∸ x =₀ 0`,
  `¬(x =₀ y)` conclude `y ∸ K =₀ 0`). Also `ex_and_left` (`ex ρ A ∧ᶠ B →ᶠ ex ρ (A ∧ᶠ weakenBy ρ B)`)
  — proved in `MCTStatement.lean`, move it to `PureFOLLemmas.lean`.
  These are Π₁ facts with no headline existentials, so the linter ignores them, correctly.
  They are closed subtrees, hence K-wrappable whole under `deduce`, which keeps
  intro-elaboration linear.
- **A1.** Encode the ℕ-MCT statement. **Done** — `MCTStatement.lean`.
- **A2.** Hand-build derivation **p₂ first**: the dichotomy proof. `qf_lem` case split on the
  decidable ℕ-comparison, budget descent as induction on `K`. Zero translation risk; goes
  straight through `general_metatheorem` at `Allowed.extended`.
- **A3.** Hand-build derivation p₁: the lazy reductio proof, hand-translated per D-1 so its
  classical content is exactly Markov-shaped.
- **A4.** Run `general_metatheorem` on p₂, then p₁. Evaluate/normalize both extracted bounds.
  Expected: p₁ → iterated `g̃`; p₂ → the budget-style bound. Verify the divergence is real.
- **A5.** Tracer: instrument extraction as a fold over the first-order derivation tree; emit
  witness-flow graph (dot output is fine). The money frame: the induction node of p₁ is
  where g̃-iteration is manufactured; p₂'s tree lacks it.

**Budget note.** A2/A3 are hundreds of lines each, not ~15 constructor nodes — `Arithmetic.lean`
is 2400 lines for `add`/`mul`/`monus` basics. A0 is what makes the two-proofs thesis
affordable: the shared lemmas are built once, so the marginal cost of the second derivation
is the proof *skeleton* only.

**TRACK B — proof mode, agentically in parallel** (presentation upgrade, never load-bearing):

- **B1.** Raw layer + `check` + the moves MCT needs ONLY: intro/obtain/have,
  `by_contra_markov`, `qfac`, `ind` (user states motive; write the de Bruijn
  motive-abstraction test first), `instantiate`, `bound-v0` (certificate CHECKER, not
  prover). No `split`, no `pm_theory`, no spaces, this month.
  `by_contra_markov` must `check` that the goal is ∃-over-QF (or falls to it after
  prenexing) and fail with *"not a Markov shape — is this proof translated?"* otherwise.
  That error message is the D-1 discipline made mechanical.
- **B2.** Acceptance oracle (fixed day one): the DSL-MCT script must elaborate to a
  derivation α-equal or extraction-equivalent to Track A's hand-built p₂. Differential
  testing against a concrete target term — iterate without maintainer in the loop.
- **B3.** Linter (elaboration-time): headline-witness check = provenance ∪ syntactic
  identity tagging + recursor-free surface term grammar (unwritable beats forbidden).
  **Concrete hook:** `Derivable.exist_ax` takes an explicit witness `Term`, so smuggling is
  localized to that one constructor. The core check is: every `exist_ax` witness term at a
  headline position is recursor-free and not syntactically equal to any candidate bound.
  A small function over first-order syntax. Must reject smuggle-B (re-derive headline ∃
  under `by_contra`, instantiate by hand) and smuggle-C (bound/instantiation list as
  information channel). Honest p₂ must pass.
  Invariant: `exist_ax` / `instantiate` is the SOLE ∃-introduction rule.

**DEPENDENCY RULE:** A never waits on B. Any demo step blocked on tactics reverts to raw
constructors. B on stage only if B2 passes AND B3 rejects both smuggles; else B is one
"in progress" slide.

## 4. Decisions on record (do not relitigate without maintainer)

**D-1 (¬¬-handling).** W-ty/extraction is defined on Shoenfield-normal forms; the ¬¬ over Π₂
cores is collapsed via Markov (validated by Dialectica), never interpreted monolithically
(monolithic Kuroda∘Dialectica = one exponential above Ψ; ProbeR1 exhibited the lift).
Literals are Π⁰₁ atoms — normalization passes challenges through, never decides them.
THIS MONTH'S SHORTCUT: no mechanized translation pass. Formalize the hand-translated proof
directly in the intuitionistic system + M (existing soundness covers T + IP∀ + M + AC).
Slide states "translation applied manually; mechanization = the Shoenfield future-work
item," consistent with the 2025 slides.

**D-2 (linter).** Provenance ∪ identity tagging AND surface-recursor ban, both adopted.
Checked against the corpus: honest MCT, Groetsch, projection-uniqueness all survive the
recursor ban (iteration lives only in EXTRACTED content). Standing check for any new input:
verify its surface terms are recursor-free before accepting it as corpus.

**D-3.** Two-track plan; talk-calibrated claims. (The ℚ base-sort clause of D-3 is
superseded by D-4.)

**D-4 (v3.1, four revisions).**

1. **ℕ base sort, not ℚ.** ℚ is not a sort of the object system; the earlier decision
   conflated the demo statement's Lean-side type with the object system's sorts. ℚ and ℝ
   are both off the critical path this cycle. See §2.
2. **p₂ before p₁.** `general_metatheorem` requires `Allowed.extended`, and
   `Allowed.extended = {markov, ip, ac, qfac}` — **`lem := false`**. A `by_contra` reductio
   is therefore not derivable in the metatheorem's input system. p₂ (dichotomy) is
   constructive over decidable ℕ-comparisons via `qf_lem` and needs no translation, so it
   is the zero-risk path and is built first. p₁ follows, hand-translated per D-1. The
   comparison slide only needs p₁ to land second.
3. **A2/A3 re-budgeted; arithmetic lemmas are shared closed work items.** See §3 A0 and the
   budget note.
4. **`by_contra` = the Markov rule, named as such.** `by_contra_markov` in B1, with the
   shape check and error message given in §3. This is not a restriction suffered but the
   precise statement of what D-1's hand-translation produces: the lazy MCT proof's
   contradiction bottoms out in a Σ₁ statement over decidable primes, so after Kuroda its
   classical content is exactly `¬¬∃n(qf) → ∃n(qf)`.

**Out of scope for the month.** The `sorry` in `general_metatheorem_classical`
(`Metatheorem.lean:298`). p₁ routes around it via hand-translation. Closing it is a named
future-work item — the mechanized-Shoenfield bullet from 2025 wearing a different type
signature. **Do not let an agent wander into it.**

Probe results standing: R1 PASS (W-ty coherent on the corpus; inner types land on
Ψ exactly; metastability = readback of 𝕎(¬¬∃∀qf), n.c.i. is an output format, not the
engine). R4 KILLED then CLOSED by D-2. P1/P2 PASS (`Probe.lean`, `MCTStatement.lean`):
`subst0`/`weakenBy` reduce by `rfl` on the real formulas at four binders deep, through the
real `induction`/`forall_ax`/`exist_ax` constructors. Encoding risk retired; the proof mode
buys ergonomics, not feasibility.

## 5. Claims calibration for the talk

**CLAIM:** first machine extractions through the (already-verified) metatheorem on real
input proofs; proof-dependence of bounds demonstrated mechanically; linter as a
formalization of extraction non-vacuity (first-order syntax is what makes it possible — the
HOAS version could not lint under binders; that contrast is itself a slide).

**DO NOT CLAIM:** mechanized negative translation; encoded-real or ℚ analysis; abstract
spaces; automated bound search (`bound` is a checker); novelty over Minlog without the
differentiation slide (§7). Prefer "demonstrated" to "fully automated" throughout —
"demonstrated" survives every rung.

**FUTURE-WORK FRAMING** (better as promises than half-results): Groetsch collapse test —
extracted term must normalize to the θ-budget bound Φ(ε,η,b,θ) with no residual
counterexample iteration, uniformity signature exactly (ε,η,b,θ); projection-uniqueness in
UCW as the space-machinery test; MET as the contrast fixture where the K-iteration provably
SURVIVES.

## 6. Encoded-ℝ policy (stretch only, not this cycle)

If touched at all: maintainer hand-writes a frozen atom API (~8 primitives: `leR`, `ltR`
with gap datum, `subR`, bounded-monotone predicate, 3–4 comparison lemmas). Agent works
strictly above it and REQUESTS new atoms rather than writing them. Tests-first:
`#eval`-checkable properties at concrete precisions before any lemma. Re-probe current agent
capability for one day before assuming the 4-month-old failure still holds — but nothing on
the critical path may depend on the outcome.

Note for the next cycle: the residual unbounded `∀` in a real-number statement comes from
the *atoms* `=_ℝ`/`≤_ℝ` being Π⁰₁, not from the quantifier prefix. Prenexed into the premise
block that is harmless; in the conclusion it is not. That is a choice about the conclusion
class, independent of whether R is encoded or abstract.

## 7. Q&A preparation

- **Minlog:** mature, has Dialectica + A-translation + classical extraction + exact-real case
  studies. Differentiators: (1) the Kohlenbach corpus — abstract space types,
  majorization-via-reference-point, uniformity in the space — has no Minlog counterpart;
  (2) the vacuity/linter discipline (Minlog never made the laziness claim); (3) trust
  architecture — derivations as data inside Lean, kernel-checked, mathlib-adjacent output.
  Concede honestly that "Kohlenbach corpus in Minlog" was an alternative project shape.
  Cite Schwichtenberg–Wainer and Trifonov–Schwichtenberg as nearest prior art; check their
  ¬¬-normalization conventions (free evidence for D-1's choices). Never omit this slide.
- **Mathlib:** one-way membrane. Core cannot consume mathlib (funext/choice/propext unsound
  as derivation content; mathlib ℝ noncomputable; no derivation structure to walk).
  Integration lives at the boundary: ℝ*→ℝ transport (next cycle), certificates/shadow proofs
  (mathlib-native), denotations of extracted bounds as plain Lean functions.
- **"Isn't the lazy/mined distinction unfalsifiable?"** No: the linter is the falsification
  device; show smuggle-C being caught at `exist_ax`.
- **n.c.i. vs Dialectica** (Kohlenbach's book presents MCT via n.c.i.): they coincide on Π₃;
  n.c.i. is the output format, Dialectica the compositional engine (n.c.i. alone fails
  modularity at Π₄+). Say it in those words.
- **"Why ℕ and not reals?"** Extraction only ever used the order structure of the primes.
  At ℕ that is all there is, so the extracted Ψ is representation-independent by
  construction rather than by argument. Reals are a representation-layer question, not a
  metatheorem question.

## 8. Abort states (each rung is still a talk)

- **Rung 1 (full):** live-ish demo — DSL script → elaborate → lint → extract → trace →
  diff p₁/p₂ bounds.
- **Rung 2:** Track A only — hand derivations, both extractions, tracer, comparison slides.
- **Rung 3:** one derivation extracted + evaluated at sample `(K, g)`, compared to hand-Ψ.
- **Rung 4 (floor):** **p₂ formalized and `general_metatheorem p₂` RUNS.** "First input
  proof the framework has eaten" is already new relative to 2025. A1 is done and the
  plumbing is checked, so this floor is partly standing rather than aspirational.

## 9. Communication protocol

Weekly `STATUS.md` against §3 track steps and §8 rungs. Escalate on: any change to
`Derivable`, `dialectica_soundness_ctx'`, or the linter rules; any B-agent claim that the
derivation type is "awkward" (log, don't fix); any A-step blocked >2 days (drop a rung,
don't push). Timeboxes hard; overruns are evidence, not debts. Prefer dropping scope to
weakening invariants — the invariants are the contribution.
