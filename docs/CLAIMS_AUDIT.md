# CLAIMS AUDIT — what is checked, what is measured, what is inferred, what is only asserted

*Compiled on branch `audit` (= `demo` merged with `main`, so that both the talk documents —
which live only on `demo` — and the four 2026-09-06 lanes — which live only on `main` — are in
one tree). Scope: `docs/RESULTS.md`, `docs/QA.md`, `CLAUDE.md`, `ARCHITECTURE.md`, and
`prezentare-bath/main.tex` (the 2026 deck), which was in scope in substance even though the
brief named four files: it is where a wrong claim would actually be said out loud.*

**This is a review, not a rewrite. Nothing outside this file was changed for it.**

## Method, and what "verified" means below

No Lean was run for this audit. Verification used three instruments, in this order:

1. **The last full build log**, `.lake/build-last.log` in the parent checkout — a completed
   `lake build Probes` on `main`, **8147 jobs, "Build completed successfully"**, timestamped
   2026-09-07 00:35. It contains every `#print axioms` line and every `#eval` output of the
   whole library and the whole probe sweep. Where an entry below says *log*, that is the source
   and the number is a machine output, not a transcription from a document.
2. **Reading the declaration** at the cited `file:line` — that a theorem of the claimed shape
   exists, what tactic closes it, and whether a refutation control sits beside it.
3. **Counting in source** (constructors, tactics, `sorry`s).

Categories, as the brief defines them:

| | meaning |
|---|---|
| **CHECKED** | a named Lean declaration, with its closing tactic and its axiom list |
| **MEASURED** | a number produced by a probe run (`#eval`, a timing, an `Expr.numObjs`) and recorded; reproducible, not a theorem |
| **INFERRED** | a pattern extrapolated from finitely many data points — the count is given |
| **PROSE** | asserted, with no backing found |

---

## Safe to state

Each of these is CHECKED and, where a number is involved, appears verbatim in the build log.

*(Two caveats that belong with this list rather than buried in the table: six headline
declarations have no axiom line anywhere in the build because `Headline.lean` is not built —
C8; and `TinyBoundDemo`/`LemBoundDemo` have no `#print axioms` of their own — C11. Both are
closed by running one more target and adding two lines.)*

1. **The library has no `sorry` and no custom axiom.** The 8147-job build carries no
   `declaration uses 'sorry'` warning anywhere. The only `sorry`s in the tree are in
   `Metatheorems/Probes/CounterSideProbe.lean`, which is deliberately outside the sweep.
2. **`Derivable` has 39 constructors and `soundness` covers all of them.** 39 counted in
   `Metatheorems/Derivable.lean`; `Metatheorems.soundness` in the log at
   `[propext, Classical.choice, Quot.sound]`.
3. **Three central results are axiom-free.** Log: `all_closed_terms_majorizable`,
   `termMajorizer_maj` and `mfi_extract_core` each "does not depend on any axioms".
4. **Every numeral quoted on the "Extracted bounds" slide is a machine-checked equation.**
   901, 1273, 1709, 349, 0, 5, 9, 8, 32, 12, 128 — each is a named theorem closed by
   `kernel_rfl`, `rfl` or `decide`. All of them print
   `[propext, Classical.choice, Quot.sound]` in the log **except** `TinyBoundDemo`'s `0` and `5`
   (rows 1–2 of RESULTS), whose file prints no axioms at all — see C11. The slide's own eight
   rows are unaffected: none of them is the `TinyBoundDemo` pair.
5. **The bounds are uniform in the space.** This is visible in the *statement*, not inferred:
   e.g. `TriangleBoundDemo.triUt_is_901` (`:347`) binds `(M : WHyperbolicModel)` and
   `(h : M.d M.ref M.zeroX ≤ 5)` as hypotheses, so the numeral is a fact about every model with
   that one parameter.
6. **The bound is a property of the proof.** `TriangleBoundDemo.triUt_is_901` (`:347`, `U = 901`)
   and `triUncUtB_is_zero` (`:498`, `U = 0`) are two derivations of one formula under one
   `ConstMajorants` value. Two theorems, not an argument.
7. **`N = 0`.** By the shape of the type: `syntactic_general_metatheorem_at`
   (`SyntacticMetatheorem.lean:100–104`) produces `{ Φ : Ty.interpret X ρ.hat → Nat // … }`,
   with no index argument at all. Nothing to check beyond reading it.
8. **A faulty tactic cannot produce a false theorem.** `Seq` is an `abbrev` for `Derivable`
   (`ProofMode/Packing.lean:63,68`) and `SeqD` is `@[reducible]` (`ProofMode/Display.lean:58`).
   This is a structural fact about definitions, so there is nothing to prove; it is safe to
   state and should be stated *as* a definitional identity, not as a verification result.
9. **ℝ-MCT is derived without LEM and without Markov.** `ProofMode.real_mct_p2` in the log at
   `[propext, Quot.sound]`, generic in `Allowed`.
10. **Mathlib structures are models and the axioms are proved in them.** `Instances.lean`;
    `WHyperbolicModel.w_metatheorem`, `CAT0Model.cat0_metatheorem`,
    `NormedModel.normed_metatheorem`, both metric metatheorems, all in the log at
    `[propext, Classical.choice, Quot.sound]` and taking no axioms hypothesis.
11. **Composition depths 9 / 11 / 12 / ≥23.** MEASURED, but reproducibly and in the log:
    `prenexify` 9, `classical_to_prenex_extended` 11, `mct_p2` 12, and `le_R_trans_core`,
    `dist_tri_chain`, `real_mct_p2` all 23 **with `budgetHit true`** — the ≥ in the documents is
    correct and must be kept.
12. **Derivation sizes 145 and 42,729.** Log, `ContentExampleNat.lean:240` and `:341`. (Note the
    probe's own header says 42,747 — see Corrections.)

---

## Must not be stated as a theorem

Nine items. The first four are closed-form or symbolic claims that no declaration asserts; the
rest are numbers whose provenance is weaker than the sentence around them.

1. **`V = 2^k · f(0)`** (`Probes/ContentExampleNat.lean:35`, `ARCHITECTURE.md` §14.8 item 5,
   deck "Extracted bounds — with content"). INFERRED from **six** sampled points —
   `V_at_0 = 1`, `V_at_3 = 8`, `V_at_5 = 32`, `V_at_7 = 128`, `V_ys_at_0 = 3`, `V_ys_at_2 = 12`
   — every one of which is CHECKED. There is no `∀ k, mfiV … = 2^k * …`, and none is provable
   by `rfl`. *The deck already says "a fit to four points"; that sentence is the correct
   register and should survive editing. It undercounts — there are six — which is a change in
   the safe direction.*
2. **`U(k) = k − 1`, and the word "sharp"** (`ContentExampleNat.lean:38`, `ARCHITECTURE.md`
   §14.8 item 5). INFERRED from **five** points (`U(0)=U(1)=0, U(2)=1, U(3)=2, U(5)=4`), all
   CHECKED. Two separate problems: the formula is wrong at `k = 0` and `k = 1` as literally
   written (it is `max(k−1,0)`), and **"sharp" is PROSE** — sharpness is a claim that no
   smaller `U` works, and nothing in the repository bears on it. The probe's own justification
   ("the step at `k` instantiates the premise at `u := k`") is an argument about the derivation,
   which is a good reason to believe it and is not a check. Say "matches `k−1` at the five
   points computed"; do not say "sharp".
3. **`U_rec = 2^{k*} · f*(0)`** (`Probes/ContentExampleSpace.lean` header). INFERRED from
   three points. Same treatment.
4. **`Φ(a,b) = max(pair(2·((a+b)·2), 1), 0)`** (deck "Reducing Φ symbolically";
   `Probes/ExprBound.lean:51–53`). This is the **rendered output of a `MetaM` reduction**
   (`#eval`), not an equation the kernel accepted; nothing states `tgtU = <that expression>`.
   It is MEASURED and it is good evidence — the log shows it stable at fuel 12 and fuel 30, and
   evaluating it by hand reproduces two independently kernel-checked numerals (1709 at (5,9),
   349 at (5,1)). Present it as "the reduction prints", with the numeral agreement as the
   corroboration; do not write it with an `=` on a slide that also carries proved equations.
   **A second, independent display corroborates it and is not mentioned in any document**:
   `Probes/MonotoneLaneA.lean:179,190` prints the *contraction* bound's normal form at concrete
   points as `max (pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) (max (pairN (2 * ((5 +
   9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0)` — the same `pairN (2·((a+b)·2)) 1` shape,
   arrived at by a different route, showing the `max` that the crossover story needs. Worth
   putting on the slide instead of, or beside, the single `ExprBound` display.
5. **"×5 per nested syllogism" and "evaluation fails at depth ≈8"** (`ARCHITECTURE.md` §14.7,
   `docs/QA.md` Q3, `docs/RESULTS.md` rows 55–56, deck "Costs"). These come from a scratch run
   that was **never committed** — `Probes/SharingProbe.lean:13–21` says so in as many words.
   The committed reconstruction of the same object measures **×3.7 per level with
   `std::bad_alloc` at k = 6** (`SharingProbe.lean:42–54`), on both sides of the `let`
   experiment. Two different numbers are in circulation as if they were one.
   *Separately*, "each sub-majorant is evaluated five times over" is a different claim and it is
   checkable by reading `MRealizer.syllogism` (3 uses of `hAB.val`, 2 of `hBC.val`). Keep that
   one; qualify the growth ratio and the wall.
6. **"ℕ-MCT ≈5³ away and ℝ-MCT ≈5¹⁴"** (`ARCHITECTURE.md` §14.8 item 1). The arithmetic does not
   follow from the numbers in the same paragraph: depth 12 against a wall at 8 is four levels
   (5⁴), and ≥23 against 8 is fifteen (5¹⁵). PROSE-grade as written. The underlying point — a
   finite engineering gap rather than 5¹³⁴ — is sound and is the paragraph's real content.
7. **"Counting repeated subterms once gives a factor up to 10⁵"**, said of extracted realizers
   (deck "Growth rates"). The measurement on **realizers** is tree/DAG **2.77–3.21** and
   tree/written **1.00–1.35** (`Probes/TermPrintDemo.lean`, five realizers of 186–563 nodes).
   The 10⁵ is a sharing ratio of a *different object* — an `Expr` goal in the counter-side
   probe, 954,412,881 tree nodes against ~5,000 `numObjs`. The slide attributes it to realizer
   size. Two measurements of two things have been merged into one sentence.
8. **"Every numeral is checked by a refutation control"** (`docs/RESULTS.md:20–21`). FALSE as a
   universal. `Probes/TinyBoundDemo.lean` — rows 1 and 2, the project's first extraction —
   contains no `≠` or `¬ (… = …)` theorem at all; `Probes/WBoundDemo.lean` has one control for
   four numerals (rows 3–6). Most files do have them (ConjBound 7, MonotoneMemoGates 5,
   MonotoneMCT 4, MonotoneLaneA 4, TriangleBound 4, ContentExampleNat 8, ContentExampleSpace 7).
   Either add the two missing controls or weaken the sentence to "almost every".
9. **"The encoded reals are a complete Archimedean ordered field inside the object theory"**
   (`CLAUDE.md`, `docs/QA.md` Q11, deck "Input proofs"). There is no declaration saying this;
   it is a conjunction of ~24 separately named lemmas plus `approx_R` and `cauchy_complete_R`,
   each CHECKED in the log. Safe if phrased as "each of the ordered-field axioms is proved, and
   they are named individually"; not safe as a single structure-level theorem, and an audience
   of this kind will ask which axiomatisation and where the bundle is.

---

## Corrections — small, mechanical, and each one findable on a slide

| # | claim | where | actual | source |
|---|---|---|---|---|
| C1 | proof-mode derivation is **42,747** constructors | `Probes/ContentExampleNat.lean:54` (header) | **42,729** — the file's own `#eval` on the next-but-one line | log, `ContentExampleNat.lean:341`. `ARCHITECTURE.md` §14.8 and the deck already say 42,729; only the probe header is wrong |
| C2 | symbolic reduction "in 84 ms", `numObjs` 167 | `Probes/ExprBound.lean:41`, deck "Reducing Φ symbolically" | this build: **118 ms**, `numObjs` **166** (fuel 12); 93 ms / 163 at fuel 30 | log, `ExprBound.lean:227,231`. Timings are machine- and load-dependent; either drop the number or say "under a tenth of a second" |
| C3 | "43 `elab`/`macro` declarations in `ProofMode/Tactics.lean`" | `docs/QA.md:151` | **41** (plus 4 bare `syntax`) | count in source. The deck's "∼40 tactics" is fine |
| C4 | "exactly one `sorry`, in `CounterSideProbe.lean:288,293`" | `docs/QA.md:109–111` | **three**: `:288`, `:293`, `:385` | grep. The substantive claim (one probe, outside the sweep) is unaffected |
| C5 | "Build: 8102 jobs"; "429 lint warnings" | `CLAUDE.md` status block | **8147 jobs**, **435 warnings** | log |
| C6 | "`Probes/` — 27 files; the sweep target lists the 26 that must build" | `CLAUDE.md` module table | **39** probe files on `main` | `ls` |
| C7 | "`soundness` … all 36 constructors" | `CLAUDE.md`, "Soundness (2026-09-03)" and "Fully proved" | **39**; the status block already corrects this and says several places still say 36 | count in source |
| C8 | `#print axioms` for "every headline declaration" is checked | `docs/QA.md:111–118` | **`Metatheorems/Headline.lean` is not imported by the umbrella and was not built.** Six of its names have no axiom line anywhere in the 8147-job log: `syntactic_general_metatheorem`, `_classical`, `_at`, `_classical_at`, `add_Q_assoc`, `distrib_Q`. Their claimed lists are currently PROSE | log. Cheap to close: `lake build Metatheorems.Headline`, ideally wired into CI |
| C9 | RESULTS/QA "what it does not show: no numeral yet from any derivation with real mathematical content" | `docs/RESULTS.md:181` | superseded by `ContentExampleNat`/`ContentExampleSpace` (2026-09-06) | see the staleness note below |
| C11 | RESULTS gives an axiom list for every row | throughout | **`Probes/TinyBoundDemo.lean` and `Probes/LemBoundDemo.lean` contain no `#print axioms` at all** (7 and 9 theorems between them), so rows **1–2** — "the project's first evaluated bound, full stop" — and rows **22** carry no axiom check anywhere in the 8147-job build. Their claimed `[propext, Classical.choice, Quot.sound]` is PROSE. Every other bound probe has a hygiene block, though several are partial (`ConjBoundDemo` prints 19 of 30 theorems, `TriangleBoundDemo` 14 of 20, `MonotoneLaneB` 19 of 25, `WBoundDemo` 6 of 10 — the unprinted ones are mostly `_qf`/`_vf` side conditions closed by `rfl`) | grep + log. Two `#print axioms` lines close this |
| C10 | realizer tree/DAG ratio "**2.77**–3.21" | `docs/RESULTS.md:135`, `docs/QA.md:174`, deck | the five measured ratios are 2.77, 3.21, 2.79, **2.76**, 3.09 — the range is **2.76–3.21** | log, `TermPrintDemo.lean:187–191`. The written ratios 1.00 / 1.14 / 1.20 / 1.20 / 1.35 and the sizes 186–563 are exactly as documented |

---

## A structural note on the two talk documents

`docs/RESULTS.md` and `docs/QA.md` exist **only on `demo`**, whose tree predates the four
2026-09-06 lanes. Consequently:

* their 64 numbered rows contain none of `ContentExampleNat`, `ContentExampleSpace`,
  `ExprBound`, `NestingDepth`, `SharingProbe`, `WHyperbolicLemmas`;
* `RESULTS.md`'s closing section and `QA.md` Q3/Q14 describe the state of the blocker *before*
  the depth measurement (which reduced 134 to 9) and *before* the `let`-sharing refutation;
* `RESULTS.md`'s row-level line citations spot-check **clean** — `TriangleBoundDemo:347,356,498`,
  `MonotoneLaneB:411,416,420,427,432,436,439`, `TinyBoundDemo:183,188` all land on the named
  theorem. The apparatus is reliable; only the coverage is stale.

If either file is shown or handed out, it should be regenerated against `main` first.

---

## Full table

Category and evidence for every quantitative or load-bearing claim found. `log` means the line
appears in the 8147-job build log.

### `docs/RESULTS.md`

| claim | class | evidence |
|---|---|---|
| Rows 1–2, `U = 0` / `V = 5` from a 12-constructor derivation | CHECKED (`rfl`), but the axiom list is PROSE | `TinyBoundDemo.lean:183,188`. **No refutation control and no `#print axioms` in the file** — see C11. The weakest-evidenced pair of rows in the table, and they are row 1 |
| Rows 3–6, W-hyperbolic `U = 0`, `V = Φ = 901`, `Φ = 1273` | CHECKED | `WBoundDemo.lean:241,254,264,284`; one control in the file |
| Rows 7–11, premise consumed: `U = V = Φ = 901`, `1273`, `1709`; `WBoundDemo`'s `U = 0` under this file's majorants | CHECKED | `UPremiseDemo.lean:202,213,223,244,280,286`; 3 controls |
| Rows 12–16, triangle inequality in the premise slot | CHECKED | `TriangleBoundDemo.lean:347,356,365,380,389,498`; 4 controls |
| Rows 17–20, contraction: `1709`/`349`, and `V` of the stalling derivation | CHECKED | `ConjBoundDemo.lean:421,431,447,463,637`; 7 controls |
| Row 21, the `and_contract` `whnf` timeout | MEASURED (negative) | probe header snippet; not a declaration, correctly |
| Row 22, `U = 0` / `V = 5` at `Allowed.extended` | CHECKED, axiom list PROSE | `LemBoundDemo.lean:364,367`, control `lVtExt_at_5_ne_4` at `:371`; no `#print axioms` in the file (C11) |
| Row 23, both classical extractors time out | MEASURED (negative) | `LemBoundDemo.lean:63–99` |
| Row 24, `0` through a depth-11 `seq_mp`, term ≈7×10¹² nodes | CHECKED for the numeral; the node count is MEASURED | `SeqMpBoundProbe.lean:384` |
| Row 25, `901 = closedMajorizer …` in any `MetricModel` | CHECKED | `MetricSpaces.lean:474` |
| Rows 27–46, the MFI numerals | CHECKED | each a `kernel_rfl` theorem; log lists all axiom lines |
| Row 31, `max(1709, 901) = 1709`, the crossover | CHECKED | `MonotoneLaneA.lean:177,188`; control at `:239` |
| Rows 36–40, proof-mode derivation, counter side | CHECKED | `MonotoneLaneB.lean:420,423,427,432,436,439`; 5 controls |
| Row 41, `dist_tri_chain` `V = 901` / `U = 0` "**but by laziness**" | CHECKED, correctly qualified | `MonotoneLaneB.lean:411,416` — the qualification is the honest part and must not be dropped |
| Rows 42–44, induction through `t^M` | CHECKED | `MonotoneMCT.lean:154,156,158,161` |
| Rows 47–48, the two ℝ-layer lemmas' casts, read-out `3` | CHECKED | log, `MonotoneMemoGates.lean:386–389`; 2 controls |
| Rows 49–50, 52, 58: OOMs | MEASURED (negative) | probe headers |
| Rows 55–56, ×5 per syllogism, k=8 OOM, evaluator wall at k=3 | MEASURED **from an uncommitted run** | superseded by `SharingProbe` — see "Must not" item 5 |
| Row 59, `acFinal`'s realizer 2,529 nodes, dag = tree | MEASURED | `SizeProbe` header. Note this is pointer identity after `#eval`; TermPrintDemo's tree/DAG ≈3 is a *structural* count of a different object. Both true, easily conflated |
| Row 60, `negTrans_sound` ≈230 constructors per node | MEASURED, **one derivation** | `SizeProbe` header. The deck's "×230 larger per node" inherits the same single data point |
| Rows 61–62, derivation sizes; `derivSize` OOMs on the big ones | MEASURED | `MonotoneLaneB.lean:78–98` |
| Row 63, tree/DAG 2.77–3.21, tree/written 1.00–1.35 | MEASURED, five realizers under 600 nodes | `TermPrintDemo.lean:119–125`. The file's own "do not extrapolate" is the right caveat |
| Row 64, `extractTerm` sizes 533 and 27 | CHECKED (`rfl`, `[propext]`) | `ExtractTermDemo.lean:90,100,132` |
| "the MFI strictly dominates the term route here" | INFERRED from the row set | true of every pair actually run; it is a summary of ~10 comparisons, not a theorem. Fine as stated ("here") |

### `docs/QA.md`

| claim | class | evidence |
|---|---|---|
| Q1 numerals and the "honest caveat" that content is an instantiation term | CHECKED / PROSE-but-correct | the caveat is a judgement about the derivations, and it is the right one; `ContentExampleNat` is now the counterexample to it, so Q1 is stale |
| Q2 bounds are properties of proofs | CHECKED | two theorems, above |
| Q3 `mct_p2`'s Φ named and never evaluated; the two candidate causes | CHECKED (named) / MEASURED (the OOM) / see item 5 for the ×5 | `MonotoneMCT.lean:96,117` |
| Q4 classical route proved, type-checks, does not reduce | CHECKED / MEASURED | log has `monotone_general_metatheorem_classical_at`, `monotone_nd_soundness` |
| Q5 faithfulness: `_gen` matches `B∀`/`C∃`; 20 fields vs 3; `arrow_intro` *is* Lemma 17.80 | CHECKED (the Lean side) / PROSE (the identification with 17.80) | the identification is a reading of the source document, argued at length in `CLAUDE.md`. It is a good argument and is not machine-checked. Say "is", but be ready to defend it as a reading |
| Q6 trust base, no `sorry`, no custom axiom | CHECKED | log — with corrections C4 and C8 |
| Q7 nothing to verify about the proof mode | CHECKED (definitional) | `Packing.lean:63,68`, `Display.lean:58` |
| Q8 "43 `elab`/`macro`" | MEASURED, wrong | C3 |
| Q9 ℝ-MCT budget `2^{k+1}` vs the book's `2^k`; reference Φ one iterate above sharp | PROSE (an accounting argument in a header) | `ProofMode/RealMCT.lean:61–70`, `Reference/MCTBridge.lean`. No Lean statement compares the two; `Reference/` is not in `lake build` |
| Q10 four theories, axioms proved in every model | CHECKED | log |
| Q11 encoded ℝ a complete Archimedean ordered field | see "Must not" item 9 | |
| Q12 `dist_tri_chain`, `dist_rev_tri*`, `real_mct_p2` | CHECKED | log, all `[propext, Quot.sound]` |
| Q13 soundness, 39 constructors, five model facts, the refuted weakening | CHECKED / MEASURED | log; `Probes/SoundnessProbe.lean` is the compiling counter-construction |
| Q14 next steps | PROSE (a plan) | fine |

### `CLAUDE.md`

Almost every quantitative claim in `CLAUDE.md` is a MEASURED number recorded at the time it was
taken, and the file's own convention (record the measurement, name the probe) is what made this
audit cheap. Items needing attention:

| claim | class | note |
|---|---|---|
| "8102 jobs", "429 lint warnings", "27 probe files", "36 constructors" | MEASURED, stale | C5, C6, C7 |
| "`Term.add_Q` is 1,945 nodes as written, 1,880,329 reduced; `mul_Q` 590,955" | MEASURED | single measurements, load-bearing for the build-cost rule; no current probe reproduces them |
| "264 hand-written `lam` uses, 99 in `RationalNumbers.lean`" | MEASURED (a grep) | reproducible, not reproduced here |
| "`seq_mp_11_numeral` … from a term measured at ≈7×10¹² nodes" | MEASURED | the numeral is CHECKED; the node count is an estimate recorded in the probe |
| "realizer size roughly doubles per 4 extra raw constructors, OOMing around ~90" | INFERRED, and the file says so ("specific to that padding construction") | good register, keep |
| "`U`/`V` are read off the instantiation term; the matrix is never entered" | PROSE (a structural explanation) | it is corroborated by `TriangleBoundDemo`'s cost being *lower* than `UPremiseDemo`'s, which is MEASURED |
| the several retractions in the file ("that attribution is WRONG", "the first reading of that measurement was wrong") | — | these are the file's most valuable content and are why the same dead ends were not re-entered. **Do not lose them in any tidying pass** |

### `ARCHITECTURE.md`

| claim | class | note |
|---|---|---|
| §14.8.1 depths 9 / 11 / 12 / ≥23 | MEASURED, in the log | the `≥` and `budgetHit true` are load-bearing; the table omits that `le_R_pu_of_le_R` is depth 4 and `le_R_of_le_R_pu` depth 7, both measured |
| §14.8.1 "≈5³ away / ≈5¹⁴" | INFERRED, arithmetic slip | "Must not" item 6 |
| §14.8.2 the `let`-sharing refutation, ×3.7, OOM at k=6, kernel zeta-reduces `let` | MEASURED, well controlled (interleaved runs, one variable) | this is the strongest negative result in the repository and it is stated correctly. It also contradicts the ×5/k=8 numbers quoted elsewhere |
| §14.8.3 the value wall, `V = 128` ok / `V = 256` OOM | CHECKED (`V_at_7`) + MEASURED (the OOM) | log |
| §14.8.4 ×295 proof-mode blow-up | MEASURED | 42729/145 = 294.7 |
| §14.8.5 "`U(k) = k−1` sharp", "`V = 2^k f(0)` kernel-checked at four points" | INFERRED (six points for `V`, five for `U`) + PROSE ("sharp") | items 1–2 |
| §14.8.6 W-hyperbolic derived lemmas, and the named gap in multiplicative monotonicity | CHECKED / PROSE (the non-derivability claim) | "not derivable from what does [exist]" is an assessment, not a proof of unprovability. Say "we have no route", not "not derivable" |
| §13 the comparison with Kohlenbach 17.52 | PROSE, argued against the book | as with Q5: a reading, carefully made, unmechanised |
| §2 `AdmissibleEqX` had an *unsatisfiable* field, refuted by a model | CHECKED-by-argument | a semantic counterexample is given (`metric x y = fun _ => 1`); it is not formalised. Still much stronger than an assertion |
| "`Majorizability` with a total majorizer has no instances" | PROSE-with-proof-sketch | the argument (at `(ℕ→ℕ)→ℕ`, `f* = id`) is in the docstring and is convincing; there is no Lean `¬ Nonempty` theorem. The deck states it flatly under "Discrepancies with the source" |

### `prezentare-bath/main.tex` (the deck)

| slide | claim | class |
|---|---|---|
| The implementation | the seven bullets | CHECKED (each names a module that builds) |
| Types and terms | 39 rules; λ primitive, no Π/Σ; β-equality an axiom | CHECKED |
| Dialectica | `wTy` clauses; `deg(ρ×τ) = max` | CHECKED (`rfl`-level facts in `TypeSystem.lean`) |
| Majorizability of realizers | closed terms majorizable; Def 6.0.1 with a total majorizer has no instances | CHECKED / PROSE-with-sketch |
| The metatheorem | the `Subtype` shape, `N = 0`, three versions | CHECKED |
| Input proofs | "∼40 tactics" | CHECKED (41 in `Tactics.lean`) |
| Input proofs | the `contract` derivation is 16 steps raw / 7 sequent steps | the **7** is CHECKED — `hilbert-out/Metatheorems_Scratch_contract_pm.md` is in the tree and says "7 steps" with the same justifications. The **16-step** table has no committed listing in the tree; regenerate it with `#hilbert … all` before the talk, or the slide's first table is unbacked |
| Input proofs (MCT) | 655 lines; no LEM, no M; ℝ is a complete Archimedean ordered field | CHECKED / CHECKED / see item 9 |
| Spaces | models from Mathlib; majorants never mention the space; the one datum is `n₀` | CHECKED |
| MFI | "the negatively translated derivation … is ×230 larger per node" | MEASURED, one derivation |
| Extracted bounds | all eight rows | CHECKED, and the "with a control theorem refuting the neighbouring value" caption is **not true of every row in the project** — it happens to be true of the eight rows on this slide, so the slide is safe; `docs/RESULTS.md`'s universal version is not |
| Extracted bounds — with content | `V` at four points; "consistent with `2^k f(0)`"; "is a fit to four points. No closed form has been proved" | INFERRED, **and correctly labelled**. Best-calibrated slide in the deck |
| Reducing Φ symbolically | the displayed Φ; "84 ms"; "the method has not been run on a larger one" | MEASURED (item 4, C2); the last bullet is the right caveat |
| Costs | ×5 per composition, wall at ≈8, depths 9/12/≥23; `V=128` vs `V=256`; ×295; `let` does not help | items 5–6 for the first; the rest CHECKED/MEASURED |
| Growth rates | "a factor up to 10⁵" attributed to realizers | item 7 — the one outright misattribution found in the deck |
| Discrepancies with the source | six bullets | all PROSE-with-argument except "`0 ≤ℝ f → f =ℝ 0` is false without non-negativity", which is CHECKED in the sense that the repaired statement is proved and the original was found refutable |

---

## What I could not classify, and would ask about

1. **Is the metatheorem's conclusion meant to be read model-theoretically?** In Lean it is
   `Formula.interpret si B₀ …` — truth in a model — where the book states it as a derivability
   result in `T`. The two are related through `soundness`, but no declaration composes them.
   An expert audience is likely to ask, and the answer is not in any of the four documents.
2. **`Reference/` is not in `lake build`.** The ℝ-MCT comparison with the hand-written textbook
   `Φ` (`Reference/MCT.lean`, `Reference/MCTBridge.lean`) is therefore not covered by the
   8147-job green build and was not checked by this audit. If the "budget `2^{k+1}` against
   `2^k`" comparison is stated on a slide, it rests on a file the CI does not compile.
3. **The `1.00–1.35` "written" figure** is described in two documents as simultaneously an
   over- and an under-estimate of achievable sharing, for two independent reasons. Both
   arguments look right; the net is genuinely unknown, and the deck says so. Nothing to fix,
   but do not let a question turn it into a number.

---

## Appendix — the staleness pass on `CLAUDE.md` and `ARCHITECTURE.md`

A separate task, done after this audit and committed separately: **delete chronology, never
delete content.** No Lean source was touched. `CLAUDE.md` 2605 → 2516 lines,
`ARCHITECTURE.md` 1068 → 1057.

**Removed** (counts are of edit sites, not lines):

| category | CLAUDE | ARCH |
|---|---|---|
| `YYYY-MM-DD` stamps in prose, headings and table cells | 183 occurrences, all gone | 28, all gone |
| commit SHAs cited as provenance (`af9de4e`, `67228bd`, `3089af9`, `511f5a2`, `5003bb4`, `c332fd7`, `32ea2eb`, `27366a2`, `fb25083`, `6abbfc4`) | 10 | 2 |
| branch-lifecycle narration: merge dates, deleted branch names, `trial/*` snapshots, per-lane merge table, "live branches as of …" | ~1 page | ~2 paragraphs |
| build-job counts quoted as of a date (8061 / 8063 / 8065 / 8088 / 8102 / 8111) | 6 | 1 |
| "this entry used to say / an earlier draft said / corrected on …", where the correction itself was kept | 14 | 4 |
| "Remaining sorries — HISTORICAL" section (a list of sorries that no longer exist) | 1 section | — |

**Kept, rewritten into the present tense at the point where someone would retry the thing:**
every failed approach and every corrected belief. Specifically, and these were checked
one by one after the edit:

* `let`-binding the sub-majorants does not help — the kernel zeta-reduces `let` (ARCH §14.8.2,
  verbatim);
* the composition cost is exponential in **depth** (9 for `prenexify`), not in the syllogism
  **count** (134) — both in ARCH §14.7/§14.8 and in the CLAUDE Lane C block, now phrased as a
  standing instruction ("do not write 134") rather than as a correction;
* the delta-expansion pathology is a `prw`/`subst` phenomenon, **not** a term-size one;
* `Majorizability` with a total majorizer is uninhabitable, with the `f* = id` argument;
* a `conv` block with no closing tactic can be vacuous (trap 12, and the `BoundLemmasP2`
  retraction that produced it);
* `AdmissibleEqX.eqx_refl` was *unsatisfiable*, not merely unproved, with the refuting
  interpretation;
* the `#eval lTermSize` OOM is not evidence about a bound (`sizeWithoutSharing` ban);
* a filtered `diagnostics.threshold` profile is a different claim, not a smaller one;
* `Term.monus`/`Term.pd` are **not** what the Stage-B stall is;
* `sInduction`'s difficulty is not `cm.precM`;
* the classical stall is two-sided where the intuitionistic one is one-sided;
* extraction with content does **not** require the proof mode — the proof mode is a liability
  (×295);
* `mul_Q`'s node count predicted nothing about its elaboration cost;
* `cauchyfy_congr` does not need `seq_induction`;
* two lanes can prove different lemmas under the same name;
* `git merge-tree` has reported zero conflicts for a merge that had one.

**Judgement calls, listed so they can be spot-checked rather than trusted:**

1. **Deleted one whole section**, "Remaining sorries — HISTORICAL": a per-file count of sorries
   that are all closed. Its three non-chronological sentences were moved up into "THE BUILD HAS
   NO SORRIES" — the `le_zero_eq_zero_R`-was-false lesson, the `eqxi`-as-a-hidden-sorry lesson,
   and the four-metatheorem axiom lists. Nothing else in it was content.
2. **Rewrote a stale claim rather than only de-dating it**, in ARCH §3: it said
   `MetricModel.eqXInterp` has "five `sorry`" fields and that both metric metatheorems depend
   on `sorryAx`. That is false now. The paragraph's content — that all of them stall on one
   missing evaluation bridge — is kept and pointed at `QValBridge.lean`.
3. **Deleted a note about the file itself** in ARCH §14.5 saying the file "carries **two**
   `## 14` headings, the second a truncated duplicate". There is now exactly one; the duplicate
   was already resolved.
4. **Replaced the "live branches" paragraph** with an undated statement of the branch layout
   plus `demo`'s two concrete merge obstacles. A live-state list is not chronology, but it
   cannot be kept accurate without a date, so it is now the smallest true statement.
5. **Corrected two counts while de-dating them**, because leaving the old number would have
   been worse than either alternative: `soundness` "all 36 constructors" → 39 (three sites),
   and the `Probes/` file count, which is now stated as no count at all.
6. **Left the three `[HISTORICAL]` `AdmissibleEqX` sections in place**, only de-dated. They
   duplicate `ARCHITECTURE.md` §1–§3, which is where the same reasoning lives in better shape;
   deleting them is a defensible next step but is more than a staleness pass.
7. **Left every claim this audit flags as INFERRED or PROSE exactly as it stands** — including
   "`U(k) = k−1` sharp" — because fixing them is the *other* task, and mixing the two would
   make both unreviewable.
