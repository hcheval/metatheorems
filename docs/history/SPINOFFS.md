# Spin-off project ideas

Notes from the design discussion. Quick bullets only; nothing here is committed to.

## A. Deep development (this repo)

- Finish `general_metatheorem_classical` — 1 sorry, `prenexify` now proved and unblocks it.
- **Freeze** `RationalNumbers.lean` (9 sorries) and `RealNumbers.lean` (19 sorries). Cost is
  concentrated there and the shallow route makes it unnecessary.
- Keep as the *specification* / justification artifact for whatever the shallow tool does.

## B. Rescues for the deep ℚ/ℝ layer (only if A is ever resumed)

- **Premises route.** State the ℚ/ℝ field laws as purely-universal object formulas (so they're
  usable inside `Derivable`) but discharge them *semantically* in Lean via `premise_realizer`.
  For PU ∨-free formulas the realizer obligation collapses to plain `Formula.interpret` via the
  already-proved `dialecticaMatrix_iff_interpFormula`. No language change, no rewrite.
  Cost: the laws become assumptions rather than derivations (legal — Kohlenbach admits any true
  PU premise). Recoverable one law at a time.
- **Difference re-encoding of ℚ.** Numerator as a pair `(a,b) ↦ a − b` instead of
  sign-magnitude. Kills the sign case-explosion that is the actual cost driver: add/mul/neg/abs
  become case-split-free, every field law reduces to ℕ semiring identities. Also deletes
  `div2`/`isEven`/`isOdd`/`rat_sign` (sign is no longer packed into parity).
  Under the Premises route this becomes optional rather than blocking.
- **ℚ as a new base type** via the `ι`/`F` parameter. *Assessed and rejected*: would prove the
  metatheorem for a different system, treats ℚ as an abstract space, and still requires the
  field laws as axioms — so buys nothing that postulation alone doesn't.

## C. Shallow MFI bound-extraction tool (the main new direction)

Separate fresh project, mathlib from day one. Goal is a *tool*, not a formalization; variations
on the metatheorems allowed.

- **Core** — `Maj` typeclass (hat type + majorization relation), `Sk` formula skeletons with
  HOAS binders and `Decidable` atoms, `Pf : Sk → Type` with only MFI-interpretable rules,
  monotone functional interpretation over `Pf`.
- Deep only for the logical skeleton; shallow for types, terms, witnesses, atoms.
  No `Ty`/`Term`/`Ctx`/substitution; ℚ from mathlib.
- Uniformity in the abstract space becomes a **typing discipline** (bound has type `ℕ → ℕ`,
  `X` cannot occur) rather than a theorem.
- Known hard spot: `Maj (W A)` needs instances at `Σ` and dependent `Π`, which HOAS forces.
  Hit this in week one.

## D. Surfaces for C (front-end choice, deferrable — all share the same core)

1. **Write `Pf` directly.** No metaprogramming. Ugly — explicit `Sk` skeletons, same complaint
   as Hilbert-style `Derivable`.
2. **Shallow WE-HA rule lemmas + extract from the proof term.** User applies ordinary Lean
   lemmas; disciplined input makes the `Expr` a first-order application tree over a known
   signature, so compiling to `Pf` is nearly a pattern match. Needs a whitelist checker
   (discipline is *not* type-enforced) and a normalization pass for `Eq.mpr` etc.
3. **Recording tactics.** Each `mine_*` tactic closes its goal step *and* appends a `Pf`
   constructor during elaboration. No `Expr` archaeology, no normalization, no whitelist.
4. **Metavariable-bound tactics (cheapest).** State the goal with the bound as `?Φ`; each
   tactic refines it by unification. Consequence: **no verified MFI needed at all** — a tactic
   that closes its goal is sound by construction, so the interpretation degenerates to a
   heuristic for choosing `Φ`, witnessed after the fact by the kernel. Trade: no reified proof
   object, so you can't re-run a different interpretation or post-process the bound.

## E. Front end for arbitrary Lean proofs (open-ended, later)

- `Expr → Pf` for proofs *not* written in the disciplined fragment.
- Pipeline: fetch proof term → `collectAxioms` audit → normalize (`Eq.mpr`, `id`, `cast`,
  trivial `Eq.rec`) → translate → kernel-check the certificate.
- **Certificate discipline makes the extractor untrusted**: output is kernel-checked, so it may
  fail but cannot produce a wrong bound. Ship at 20% coverage with 100% soundness.
- Obstructions delimiting the fragment: `Quot.sound`/`funext` (mathlib's `Real` is a quotient —
  `Rat` is a structure and is safe), `Classical.choice`, `WellFounded.fix`, motive/cast soup.

## F. Smaller / orthogonal

- **Bound DSL.** Small deep language of bounding terms (`+`, `·`, `max`, primitive recursion)
  with `Maj.hat` landing in it, so extracted bounds are certified primitive recursive rather
  than being arbitrary Lean functions. Addable later without disturbing the combinator library.
- **QF-ER vs `impI` fork.** Deduction theorem fails in WE-HA^ω because of QF-ER; `intro` + QF-ER
  under a hypothesis derives full extensionality, which the interpretation can't handle.
  Resolution: include `impI`, omit QF-ER (⇒ intensional HA^ω, DT holds, natural-deduction
  ergonomics). When ℝ eventually forces QF-ER back, index `Pf` by open/closed assumptions.
  HOAS gives the eigenvariable condition for generalization for free.
- **Calibration study (talk material).** Machine-extracted vs published bounds on a known
  example. Sharper question than "is it ugly": is the human step *asymptotically* load-bearing,
  or is it presentation? Baseline for the diff is now `MCT.lean` in this repo — the hand-written
  `Φ = (shift g)^[2^k + 1] 0` with `it_mono` doing the work a machine would pay for in `max`.

## G. Automatic *generalization* (orthogonal to bounds)

Proof mining yields not only bounds but qualitative generalizations — Hilbert ⇝ uniformly
convex Banach, Hilbert ⇝ CAT(0) ⇝ W-hyperbolic. Logically this is premise weakening: the space
axioms are the `Premises` parameter, so a proof using only a weaker PU set applies to a wider
class. Search space is small and curated (two branches: linear and metric).

**The problem is signature *synthesis*, not premise weakening.** The signature is the output, not
an input. Writing proofs against an abstract signature from the start defeats the purpose — the
point is to *discover* the abstraction in a proof given concretely (e.g. for Hilbert spaces).
This is also what distinguishes it from existing Lean work on identifying unused typeclass
instances: those search a **fixed lattice** for the weakest existing node, whereas proof mining
historically *invents new nodes* (W-hyperbolic spaces exist because someone noticed a
Hilbert-space proof used only that much). Automating the invention is the interesting target.

- **Phase 1 — proof-term generalization (mechanical).** Collect every lemma about the concrete
  structure that the proof term actually uses; lambda-abstract over them. Yields `T` proved from
  an explicit hypothesis set, with no target in mind. Pure `Expr` traversal + rebuild.
  `lean_minimal_hypotheses` (MCP) is a primitive version of this.
  **Valuable standalone**: "here is the exact interface your proof uses" is the artifact a human
  then stares at to invent the new class, even if Phases 2–3 find nothing.
- **Phase 2 — operation abstraction (hard, creative).** Replace concrete operations by opaque
  symbols (`(x+y)/2 ↦ m x y`, `‖x-y‖ ↦ d x y`). This is anti-unification; the search space is the
  problem. Heuristic for candidate subterms: head is a structure operation, and occurs in the
  statement or in several places.
  Practical algorithm — **generalize-and-repair**: abstract aggressively, let the proof term fail
  to typecheck, read off from each failure which concrete property was relied on, add it as a
  hypothesis, iterate to fixpoint. Delta debugging on the axiom set with the proof term fixed.
- **Phase 3 — PU filter + class lookup.** Keep hypotheses in the purely universal fragment (same
  fragment condition the bound work needs), then match against known classes. Database question.

- **The statement generalizes too, not just the hypotheses.** `‖x-y‖ ↦ d x y`, `(x+y)/2 ↦
  W(x,y,1/2)`. Abstraction must act on statement and proof simultaneously — anti-unification over
  the pair. This is what makes Phase 2 more than a linter.
- **Cost note:** mathlib has **no** CAT(0) or W-hyperbolic spaces — they must be defined first.
  Short definitions (convexity map `W` + axioms, plus CN), ~a day, but not free.
- **Feasibility: research project, not a 3-week deliverable.** Phase 1 on a toy example is
  plausibly 3 weeks by itself.
- **Interaction with C/D: this is an argument for keeping a reified proof object.** Generalization
  = replay the same proof under a different premise set, which `Pf` makes trivial and the
  metavariable-tactic surface (D4) makes impossible. Raises the value of D1–D3.
- Possibly *more* novel to a proof mining audience than bound calibration — automating the
  qualitative side is less discussed than automating bounds.

### G′. Refinement: restrict to the typical *nonlinear* generalization

Restricting to Hilbert/Banach ⇝ geodesic/hyperbolic makes three of the four open-ended parts
finite. This is the version worth attempting.

- **The target is a ladder, not a lattice.** metric → convex metric (Takahashi's condition on a
  convexity map `W`) → W-hyperbolic (Kohlenbach) → CAT(0) (CN inequality), with uniformly convex
  hyperbolic (carrying a modulus) as a side branch. "Weakest class" becomes "lowest rung" — a
  linear scan over ~5 candidates. Formalize the ladder once; bounded, reusable cost.
  *Check the exact axiom lists against a source before formalizing.*
- **Term translation is a fixed dictionary, not anti-unification.** `‖x-y‖ ↦ d x y`,
  `(1-λ)•x + λ•y ↦ W x y λ`, `(x+y)/2 ↦ W x y (1/2)`. This is the biggest saving: Phase 2's
  heuristic for choosing candidate subterms — which was doing all the load-bearing work and which
  I had low confidence in — is simply not needed, because the target language prescribes the
  abstraction. Same dictionary handles the statement, so the "statement must generalize too"
  obstacle is dissolved.
- **The creative content localizes to inner-product uses.** Norm and convex combination translate;
  `⟪·,·⟫` has no metric counterpart, so every step genuinely using inner-product structure is an
  *obstruction site*. Finding them is the tool's real job. Catalogue of substitutes is small and
  known: parallelogram ⇝ CN, quasi-nonexpansiveness inequalities, uniform convexity moduli.

Algorithm:

1. translate statement and proof by the dictionary (mechanical);
2. report every step still mentioning inner-product / linear structure — the obstruction sites;
3. per site, try the catalogue of metric analogues; check the proof still goes through;
4. the union of analogues used names the rung.

Generalize-and-repair as before, but step 3 now has a **finite** candidate set — which is what
turns this from research into engineering.

- **Also report which parameters survive** (diameter bound, modulus of uniform convexity). The
  literature's nonlinear generalizations come with bounds uniform in the space, so this connects
  G′ to the bound work instead of leaving it orthogonal.
- **Realistic v1 is an assistant, not an automaton.** mathlib's Hilbert-space proofs are
  `rw`/`simp`-heavy, so proof terms are messy and obstruction sites will be numerous. Translating
  what it can and *reporting the sites* is still the artifact a proof miner wants — finding them
  by hand is the tedious part — and it degrades gracefully rather than failing wholesale.

## H. A `dialectica` / `mfi` tactic

> **It does not compute bounds.** The bound comes from the *proof*; this transforms the
> *statement* and justifies the rewrite with `Classical.choice`, so the witness it produces is
> noncomputable by construction. It automates the specification step, which is the easy half —
> a proof miner can write a metastable form by hand. Partial exception: applied to hypotheses,
> assuming them in already-Skolemized ("with modulus φ") form propagates explicit moduli forward
> — but what the tactic contributed there was telling you *which* modulus form to assume, which
> is still statement-level.
>
> **Consequence for scoping:** H alone yields a talk about automating a transformation, not about
> bounds. **H + the D4 mining tactics** is the minimal system that produces a number — `mfi` sets
> up the goal with `?Φ` unknown, `mine_exists` / `mine_cases_dec` / `mine_induction` instantiate
> it. That is ~1 week + ~2 weeks, i.e. the whole budget with no slack. Fallback if it overruns:
> `MCT.lean` already has a hand-mined bound, so the transformation can be shown automated and the
> extraction done by hand, presented honestly as half a pipeline.

In a proof state, `dialectica h` rewrites hypothesis (or goal) `P` to its Dialectica form
`∃ w, ∀ c, P_D w c`.

- **Coherent with no metatheory.** The equivalence `P ↔ ∃w∀c P_D` is the characterization
  theorem, needing AC + IP + Markov — all available in Lean (classical + choice). The tactic
  justifies its own rewrite by composing one small equivalence lemma per connective.
- **Generalizes `choose`.** Mathlib's `choose` handles the `∀x∃y` case (the AC step). This carries
  the same move through the whole connective structure, including implication's contravariant
  counter-transformer — the case nobody does by hand and `choose` cannot touch.
- **Honest limitation:** it reshapes the *statement*, it does not extract a program. The witness
  comes from `Classical.choice` and is noncomputable. Computational content lives in the proof.
- **What it is actually for: it computes the mining target.** Given a theorem it produces the
  quantitative version to aim at — currently done by hand and error-prone for nested implications
  (getting the counterfunction structure right). Then prove that ∃∀ form with explicit witnesses;
  the equivalence certifies the original.
- **Build the monotone variant** (`mfi`, bounded ∃) rather than exact Dialectica. On `MCT.cauchy`
  it should emit `MCT.metastable` with the bound left as a metavariable. Ten-second live demo,
  immediately legible to a proof mining audience.
- **Composes with D4**: `mfi` sets up the goal with `?Φ` unknown; the `mine_*` tactics discharge
  it and instantiate `?Φ`. Two halves of one workflow, sharing one metavariable.
- **Better 3-week bet than C/D**: needs the translation + one lemma per connective, and can stop
  at whatever fragment is covered. No induction handling, no rule-by-rule tactic set.
  Same fun payload — the machine-computed Dialectica of a statement with nested implications is
  hair-raising, shown next to the hand-written version.
### Implementation: sequential prenexation rewrites

Classically this is not an approximation but exact. Check the implication clause: Dialectica gives
`A → B` the form `∃F,G ∀w,c (A_D(w, G w c) → B_D(F w, c))`; prenexing `(∃w∀c A_D) → (∃v∀d B_D)`
yields `∀w ∃v ∀d ∃c (A_D → B_D)`, and Skolemizing the two existentials gives exactly `F` and `G`.

Three ingredients, all available in Lean:

- **prenexation simp set** (classical; nonemptiness side conditions on some rules),
- **Skolemization** — `choose` already does this,
- **Herbrandization**, its dual: `(∃n ∀i, P n i) ↔ ∀g ∃n, P n (g n)`. This is the counterfunction
  move. The metastable form *is* the Herbrand normal form, up to repackaging two counterfunctions
  into one window `[n, n + g n]`.

**Big win: no reification.** Work on Lean `Prop`s throughout, produce Lean `Prop`s. No `Sk`, no
`W`/`C` types, and the dependent `Σ`/`Π` problem never arises — Skolem functions are just Lean
functions. Removes most of section C from this deliverable's critical path.

**Serious catch: a simp set does not determine quantifier order, and Dialectica does.** Pulling
`∀x` before vs. after `∃y` decides whether `y` depends on `x` — the difference between a uniform
bound and a useless one. Needs a *directed* strategy matching Dialectica's clauses, not a
confluent rewrite set. Getting this wrong yields something that typechecks and is silently weaker.

Smaller caveats:
- Disjunction loses Dialectica's Boolean tag (prenexed `A_D ∨ B_D` doesn't say which disjunct).
  Probably irrelevant for bounds.
- The bounded step `∃n ↝ ∃n ≤ Φ` is **not** a rewrite — that is majorization, and it is where the
  mathematical content stays.
- Only valid for the classical/prenexable case; intuitionistic Dialectica is not prenexation. Fine
  here, since mining targets classical proofs.

Revised feasibility: first demo (`MCT.cauchy ↝ MCT.metastable`) plausibly ~1 week, remaining time
on the directed strategy and the bounded step.

## I. Mining through mathlib's filters (the gate to mathlib input)

Mathlib states convergence as `Tendsto f l₁ l₂`, so **any** tool taking mathlib proofs as input
must handle filters. Apparently unstudied.

- Filters are third-order, but the *fragment actually used* is first-order representable:
  `∀ᶠ n in atTop, p n` is `∃ N, ∀ n ≥ N, p n`; `𝓝 x` in a metric space unfolds to an `ε`.
  Characterizing exactly that fragment is a genuine question.
- **Concrete project: a quantitative filter calculus.** Give each filter lemma a modulus-carrying
  counterpart — `eventually_and` ↦ max of two thresholds, `Tendsto.comp` ↦ composition of moduli,
  etc. Most everyday combinators should go through.
- **The interesting output is where they don't.** Anything routed through `Filter.lim`,
  ultrafilters, or other choice-heavy constructions has no modulus. Cataloguing those failures
  says precisely which mathlib idioms are unminable.
- Distinguishes itself from a generic "quantitative API" by having real content: which filter
  operations admit moduli is not obvious in advance, and the answer decides whether mathlib input
  is possible at all.

## J. The space ladder, shallowly, following the proof-mining definitions

Formalize metric → convex metric (Takahashi) → W-hyperbolic (Kohlenbach) → CAT(0) (CN), plus
uniformly convex hyperbolic, as Lean classes. mathlib has **none** of it.

- **Not a toy: it is the shared prerequisite for G′**, whose whole refinement depends on having a
  ladder to scan. Also feeds I.
- **Intellectual payoff beyond the artifact:** writing the definitions out forces annotating which
  axioms are **purely universal** — the fragment condition every other idea here depends on, and
  which is nowhere recorded in one place. A PU-annotated ladder is a reference object.
- Carry the quantitative data (modulus of uniform convexity, diameter bound) as **fields**, not
  side hypotheses — that is what extracted bounds end up depending on.
- Keep standalone; do not aim at mathlib initially, or the hierarchy-design argument eats the
  project.
- Low risk, useful regardless of which other project wins.

## Target example (for C/D)

Metastable monotone convergence. Tier 1: `a : ℕ → ℕ` nonincreasing bounded by `K`, bound
iterates `g̃ n = n + g n` about `K` times. Tier 2: `a : ℕ → ℚ` in `[0,1]`, about `2^k` times.
Chosen because it forces `Maj` at function type, has genuine classical content (the minimum
principle is where the iteration is born), needs no abstract space or reals, and its uniformity
in `a` is checkable by inspecting the extracted term's type.
