# FEASIBILITY

Append-only probe log. Current verdict at the top. Verdict changes cite the probe that caused them.

---

## CURRENT VERDICT: **YELLOW**

*As of 2026-08-10, after probes R1 (complete) and R4.*

No KILL has fired. Two **maintainer decisions** are required before implementation starts;
both fall under §10's stop-and-ask, and neither is a scope cut:

> **D-1 (W-ty convention, from R1).** Fix how Kuroda's *outermost* `¬¬` is discharged.
> Applied monolithically it lifts the extracted type one exponential above `Ψ` and M1's
> unit test fails on type grounds. Discharged first by `¬¬∀x A → ∀x ¬¬A` (intuitionistic)
> the inner types land on `Ψ` exactly. W-ty is maintainer-owned; agents cannot choose this.
>
> **D-2 (linter rules, from R4).** The vacuity linter as stated in §2(i) is **not**
> sufficient: two of three smuggling attempts succeed against it. Two additions close them
> — headline tagging by provenance *∪ syntactic identity*, and a **recursor-free surface
> term language**. Both change §2/§4 and need sign-off.

The named scope cut, if one is later needed, is the §8 abort state (hand-executed
interpretation + machine-checked certificate), which is **already half-built** — see
Fallbacks below.

**Confidence: still low on schedule.** The two probes run were the *design*-risk probes
(R1, R4) and both are answerable on paper. The *schedule*-risk probes (R2 PMTerm, R3
elaboration boundary, R6 extractor) are unrun, and M1-by-deadline is entirely their
question. Expect the verdict to move on R2.

**Verdict history.** YELLOW (initial, after R1-partial: cut was "classical route dead").
That cut is **withdrawn** — R1's completion shows the route is live once D-1 is fixed.

---

## BLOCKER — RESOLVED

Design doc supplied by the maintainer in-session (not committed to disk, per instruction).
R2–R7 are unblocked. Original entry kept below for trajectory.

## BLOCKER (escalation, as originally logged)

**`AGENT_HANDOFF.md` does not exist.** Searched the working tree, all five branches
(`main`, `sumtype`, `primitive-lambda`, both `worktree-agent-*`), and the reflog for added
files matching `*HANDOFF*`; also grepped the tree for `PMTerm`, `Groetsch`, `vacuity`,
`AGENT_HANDOFF` — zero hits anywhere outside the task prompt.

Consequence: the following are **specified only by name** and cannot be probed as written —

| Risk | What is missing |
|---|---|
| R1 | the polarity-indexed formula grammar, Π⁰₁/Σ⁰₁ real literals, "gap witnesses", "enriched premises" |
| R2 | the intended `PMTerm` fragment and its relation to the existing `Metatheorems/Term.lean` |
| R3 | the `Raw` grammar and what `check` is supposed to infer |
| R4 | the definition of "the vacuity linter" and of `PMDeriv` |
| R5 | the `bound` v0 certificate fragment and its `split` construct |
| R6 | the "six moves" |
| R7 | the intended space signature |

What I did instead: ran R1 against the **existing** Dialectica implementation in this repo,
which is the closest available proxy and answers the mathematical core of R1 for the MCT
corpus. Everything below is scoped accordingly. R2–R7 are blocked on the design doc or on a
decision to reconstruct it; I have not reconstructed it, because guessing a design and then
declaring it feasible is the failure mode this assessment exists to prevent.

**Requested from maintainer:** the design doc, or authorisation to reconstruct §R2–R6 from
the existing repo plus the standard proof-mining presentation, with the reconstruction itself
logged as an assumption.

---

## PROBE LOG

### R1 · Dialectica type assignment is coherent for the fragment

- **Timebox** ≤3 days · **Actual** ~1 h
- **Artifact** [ProbeR1.lean](ProbeR1.lean) (disposable; typechecks clean, exit 0).
  Corpus taken from the existing [MCTStatement.lean](MCTStatement.lean), which also
  typechecks clean.
- **Scope caveat** probes `Metatheorems.dialecticaWitness` / `dialecticaCounter`, not the
  (unavailable) new W-ty. No real literals, no gap witnesses, no enriched premises — the
  statement is metastable MCT over **ℕ**, `ι = Empty`.
- **Result: PARTIAL PASS with one hard finding.**

**Evidence.** Every type below is asserted by `rfl` against a hand computation; all elaborate.

1. *No formula in the corpus needs a case W-ty can't classify.* W-ty is total and uniform
   across the statement, its Kuroda inner translation, and its full negative translation.
   Zero ad-hoc patches. This is the criterion the handoff names, and it holds.

2. *The matrices collapse.* `B₀`, `C₀` are QF and ∨-free, so `𝕎 = ℂ = Unit`-built. Double
   negation around a QF matrix stays a singleton — no blow-up where one might fear it.

3. *Extended route: types line up with `Ψ`.* For `S = ∀h(∀u B₀ → ∃v C₀)`,

   ```
   𝕎(S) = R → ( ((ℕ→1) → ℕ×1)  ×  ((ℕ→1) → 1 → ℕ×1) )      R = ℕ→ℕ→ℕ
                 └── the V-part ─┘   └──── the U-part ────┘
   ```

   `U, V : R → ℕ`, and `Φ : ⟦mctTy.hat⟧ → ℕ = R → ℕ`. The hand-written `Ψ` in
   [MCT.lean:75](MCT.lean#L75) is `(shift g)^[2^k+1] 0`; over ℕ with `a ≤ K` its analogue is
   `(shift g)^[K+1] 0`, of type `(ℕ→ℕ) → ℕ → ℕ`, which is exactly `R → ℕ` once `a, g, K` are
   read off one fused majorant. **Arities match.** The application of `general_metatheorem`
   to this shape already elaborates (MCTStatement.lean:84–98).

4. **The finding — classical route.** For `NT(S) = ¬¬ nt(S)`:

   ```
   nt(S) = ∀h ¬¬(∀u ¬¬B₀ → ∃v C₀)
   𝕎(nt(S)) ≅ R → ℕ×ℕ            =: Wnt      ℂ(nt(S)) ≅ R
   𝕎(NT(S)) ≅ (Wnt → R) → Wnt
   ```

   The witness for the negatively translated statement is **not** a solution function; it is
   a functional that yields one only when handed a *challenge* `Wnt → R` selecting a
   counterexample parameter. One exponential above `Ψ`'s type.

   `general_metatheorem_classical` extracts by feeding `dialecticaDefaultWitness` as that
   challenge. The probe confirms mechanically (last `example`, by `rfl`) that the default
   challenge **ignores its argument** and returns `Ty.interpret_default si mctTy` — a fixed
   junk `h`, not the `h` the theorem is quantified over. So the extracted `U, V` are sound
   only against one junk challenge.

   **Therefore the `sorry` at [Metatheorem.lean:340](Metatheorems/Metatheorem.lean#L340) is
   not a missing lemma.** It is the point where the proof needs an `x`-dependent challenge
   and none exists. No amount of local work closes it; the entry point must change.

- **Schedule delta.** Removes an unknown rather than adding time: the classical entry point
  is now known-dead instead of suspected-hard, and CLAUDE.md's "1 remaining sorry" should be
  reclassified from *unfinished* to *unfinishable as stated*. Cost of the route back
  (prenexify → Markov → extended) is unmeasured; call it a fresh probe, not a fix.
- **Kill criterion.** Not fired. The stated KILL was "repeated ad-hoc patches to W-ty per
  formula"; there were none.
- **Open questions raised.**
  - Does `prenexify` (proved, commit 89d0480) compose with a Markov ¬¬-elimination on
    `∃u∃v(B₀→C₀)` to land the input in `Allowed.extended`? Nothing in the repo does this.
    This is the smallest artifact that would restore the lazy-classical-input claim.
  - Does the same one-exponential lift appear for Groetsch, or is it specific to the
    `∀(∀→∃)` shape? Unprobed; bears on R7.
  - The finding is about the *interaction* of ¬¬ with meta-level (approach b) extraction. It
    would not arise if witnesses were object terms. That is evidence **for** the handoff's
    deeply-embedded design and **against** the current one — but I cannot check the new
    design without the doc.

---

### R1 (continued) · re-run against the actual fragment

- **Timebox** ≤3 days · **Actual** ~1 h more (2 h total)
- **Artifact** paper, below. The Lean part of the earlier entry stands unchanged.
- **Result: PASS, conditional on maintainer decision D-1.**

With the design doc in hand the corpus is the *real* one: `a : ℕ → ℝ*` with the 2⁻ⁿ
representation, `≤*` and `=*` Π⁰₁ over a decidable rational matrix, threshold `ε` rational,
`b` a rational bound, monotonicity and boundedness as Π₁ premises. Headline statement in
unbounded Cauchy form per §2(ii):

```
S  ≡  ∀ε:ℚ⁺ ∃n:ℕ ∀i,j:ℕ ∀k:ℕ  QF(ε,n,i,j,k)          -- Π₃, matrix decidable over ℚ
```

Write `D = ∃n ∀m QF` (fusing `i,j,k` into one `m`). Then, layer by layer:

```
𝕎(D)      ≅ ℕ            ℂ(D)      ≅ ℕ           -- the challenge m
𝕎(¬D)     ≅ ℕ → ℕ        ℂ(¬D)     ≅ ℕ           -- ← this is where g comes from
𝕎(¬¬D)    ≅ (ℕ→ℕ) → ℕ    ℂ(¬¬D)    ≅ ℕ → ℕ       -- ← takes the counterfunction, returns n
𝕎(∀ε ¬¬D) ≅ ℚ → (ℕ→ℕ) → ℕ
```

With `b` arriving from the Π₁ premise side, the extracted type is
`ℚ → ℚ → (ℕ→ℕ) → ℕ` — **exactly `Ψ(b,ε,g)`'s type.** Metastability is not imposed; it is
the readback of `𝕎(¬¬∃n∀m QF)`, which is precisely §1's "n.c.i. is an output format, never
the engine". This is the strongest available evidence that the interpretation design is
sound for the corpus, and it is the R1 PASS criterion.

**D-1, the finding.** Kuroda gives `NT(S) = ¬¬ nt(S)`, `nt(S) = ∀ε ¬¬D`. Interpreting that
outer `¬¬` monolithically gives

```
𝕎(NT(S)) ≅ ( (ℚ→(ℕ→ℕ)→ℕ) → ℚ×(ℕ→ℕ) ) → ( ℚ→(ℕ→ℕ)→ℕ )
```

— a challenge functional, one exponential above `Ψ`. The earlier Lean probe
([ProbeR1.lean](ProbeR1.lean)) exhibits exactly this lift mechanically on the ℕ-valued
statement, and confirms by `rfl` that the repo's current workaround (feeding
`dialecticaDefaultWitness` as the challenge) supplies a challenge that ignores its argument.

The fix is standard and cheap — `¬¬∀x A → ∀x ¬¬A` is intuitionistically derivable, so the
outer `¬¬` is discharged *before* W-ty is applied; the remaining `¬¬` in front of the Σ⁰₁
conclusion is discharged by Markov, which the fragment has. But **which of these is baked
into W-ty is a maintainer decision** (§3: agents conform to W-ty, do not modify it; §10:
stop and ask). Getting it wrong is invisible until M1's unit test fails by one exponential,
which is the §9 hazard "agents produce plausible wrong Dialectica types" firing exactly as
predicted.

**Second finding — the g̃ off-by-one is already live.** §8 requires `Ψ = g̃^(⌈b/ε⌉)(0)` with
the convention recorded. The hand-computed Ψ in [MCT.lean:75](MCT.lean#L75) is
`(shift g)^[2^k + 1] 0` with `ε = 2⁻ᵏ`, `b = 1`, i.e. `g̃^(⌈b/ε⌉ + 1)(0)` — one iteration of
slack, because that proof takes `2^k + 1` windows where `2^k` suffice. So **M1's unit test
"machine Ψ ≡ hand Ψ" will fail against the existing hand value** unless the fixture is
recomputed to `⌈b/ε⌉`. Cheap to fix now, expensive to debug at M1 under a deadline.

- **Schedule delta.** None added. Removes the largest single unknown.
- **Kill criterion.** Not fired: W-ty needed no per-formula patching anywhere in the corpus.
- **Open questions.** Groetsch's statement not yet run through this (that is R7). The
  Σ⁰₁ `<*` gap witness does not occur in MCT's statement, so its W-ty case is untested.

---

### R4 · Is the vacuity linter well-defined?

- **Timebox** ≤2 days · **Actual** ~1 h · **Artifact** paper, this entry.
- **Result: KILL criterion FIRED against §2(i) as written, then closed by two additions.**
  Reported as **conditional PASS**, requiring maintainer decision D-2.

**Spec attempted.** Extend `PMFormula`'s index with a `headline` tag, computed (never
user-supplied) by tracking positive occurrences of the theorem's conclusion through the
moves. Judgment: `d ⊢ lazy` iff no `instantiate t` node in `d`, or in any `pm_lemma` it
invokes, targets a headline-tagged `∃`. Lemma invocation checks the lemma's own certificate
transitively.

**Attempt A — smuggle via a lemma. REJECTED, as designed.** A helper lemma carrying
`instantiate (g̃^⌈b/ε⌉ 0)` fails its own lazy check; transitivity propagates the failure.
The Π₁-laundering variant is more interesting: declare an opaque symbol `psi` via
`pm_theory` with the Π₁ axiom `∀ε g ∀i,j,k QF(psi(b,ε,g),i,j,k)` — this **passes** §7's
Π₁ axiom checker, since "the window property holds at n" is genuinely Π₁. But consuming it
still requires `instantiate (psi b ε g)` at the headline `∃`, which the linter rejects
*without needing to recognise Ψ*. That robustness is real and worth keeping. It rests
entirely on one invariant: **`instantiate` must be the only ∃-introduction in the move
set** — nothing inside `qfac`, `ind`'s motive, `split`, or `bound` may introduce one. That
invariant is not stated in §4 and should be.

**Attempt B — re-derive the headline inside a reductio. SUCCEEDS against the spec.**
`by_contra` on the headline goal yields `¬∃n φ ⊢ ⊥`; inside, prove `∃n φ` by
`instantiate Ψ` and contradict the hypothesis. Under provenance-only tagging the inner
`∃n φ` descends from a *hypothesis*, not from the conclusion, so it is tagged auxiliary and
the `instantiate` is accepted. The derivation is honest-looking, lints clean, and contains Ψ.
**Fix:** tag headline by provenance **∪ syntactic identity** with the theorem's headline
`∃`-node modulo its parameters. Cost: possible false positives when a genuinely auxiliary
existential is an instance of the headline shape — MCT is safe (its auxiliary is
`∃k. k·ε > b`, a different formula), Groetsch is unchecked. §9 already flags this cluster
("test both directions"); B is the concrete counterexample it warns about.

**Attempt C — smuggle through a `bound` instantiation. SUCCEEDS against the spec, and is
the dangerous one.** `bound [fact @ t]` instantiates Π₁ facts at ground terms. It never
introduces an `∃`, so a linter scoped to headline `∃`-intro never looks at `t`. But under
Dialectica a Π₁ premise instantiated at `t` contributes `t` to the challenge side, which
flows into the extracted term. So `bound [monotone @ g̃^⌈b/ε⌉(0)]` injects Ψ into the output
while the derivation lints clean and contains no `instantiate` at the headline. The machine
then "extracts" a bound the human wrote. This defeats the non-triviality claim silently —
precisely the §9 hazard "`bound` doing too much", arriving by an unexpected route.

**Fix, and it is the better spec anyway:** make Ψ *unwritable* rather than forbidden.
`Ψ = g̃^(⌈b/ε⌉)(0)` requires iteration, i.e. a recursor. Ban the recursor from the **surface
term language** (instantiation witnesses, `bound` instantiations, `split` precisions, `ind`
motives) — leaving variables in scope, theorem parameters, and the ground arithmetic/ℚ
operations. `PMTerm` keeps its recursor; only the *input* language loses it. The
non-triviality claim then reads: *the input language cannot express the bound; only the
extractor's target can* — a statement about expressiveness, checkable by a grammar rather
than by a linter pass, and immune to smuggling routes nobody enumerated. This also matches
§1's stated philosophy that the grammar should make illegitimate forms unwritable.

**Does it break honest proofs?** MCT: no. Its instantiations are `max i j`-shaped terms and
the Archimedean `k`, which is *obtained*, not instantiated; `ind` supplies a motive, not a
term. Groetsch: **unchecked, and this is the thing to check at M2** — if any honest step
needs an iterated term, the ban needs a carve-out and the whole argument weakens.

- **Schedule delta.** None yet; both fixes are spec-level and land before implementation.
  If the Groetsch check fails at M2, budget a redesign of the non-triviality argument.
- **Kill criterion.** §2's stated linter: FIRED (attempts B and C accepted). Strengthened
  spec: no surviving smuggle among the three the handoff names, plus the Π₁-laundering
  variant. Honest MCT proof accepted under both readings.
- **Open questions.** Are there smuggles through `qfac`'s prenexing, or through `ind`'s
  motive, that inject terms into the extracted output the way `bound` does? Not enumerated
  — the `bound` route was found by asking "what else reaches the extracted term", and that
  question has more answers than I checked.

---

## STANDING QUESTIONS (§3)

- **One-month demo floor (R6).** Still not assessable, but for a better reason: R1 and R4
  are design-risk probes and both are answerable on paper, so they carry no schedule
  information. R2 is now the binding evidence and is next.
- **Invariants bent under pressure.** None enacted. Two flagged, not enacted (D-1, D-2),
  both raised *before* implementation rather than under it — the intended direction.
- **Literature / tooling sweep.** Not yet run. Now scopeable: the question is whether any
  existing Lean Dialectica formalization supplies a `PMTerm` + normalizer worth importing
  (bears on R2 only). Worth one pass before R2 starts.
- **R8 human bandwidth.** Two data points, mixed. Adverse: probe 1 stalled outright on a
  missing document. Favourable: the design doc, once supplied, converted ~2 h of agent work
  into two decisions that a maintainer can settle in one sitting (D-1, D-2) — a good ratio.
  The pattern to watch is that both completed probes *ended* in maintainer decisions; if
  R2/R3 do the same, review becomes the binding constraint by week 2 as R8 anticipates.

---

## FALLBACK DE-RISKING (§5)

- **F1 (shallow quantitative library) is already partly built and unblocked.**
  [MCT.lean](MCT.lean) contains the mined metastable MCT over ℝ with `Φ k g = (shift g)^[2^k+1] 0`,
  fully proved against mathlib, plus `example : Φ 3 (·+1) = 511 := by decide`. That is the
  handoff's "abort state" artifact, in hand today, at zero marginal cost. Any ORANGE
  recommendation can point at it.
- **F3 (soundness as a standalone theorem) is largely done.** Dialectica soundness,
  Kuroda negative translation soundness, and their composition are proved with zero `sorry`.
  This is v2 of §3 in all but the intrinsic-syntax framing — evidence that the deferred
  soundness theorem is not the risk it might look like.
- **The §8 abort state is the cheapest live fallback.** It needs a hand-executed
  interpretation plus a machine-checked certificate; MCT.lean already supplies the
  certificate half (modulo the `⌈b/ε⌉` vs `⌈b/ε⌉+1` fixture correction found in R1).
