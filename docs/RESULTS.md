# RESULTS — every bound this project has extracted, and every one it has not

*Rows 1–64 compiled 2026-09-06; **section 6 (rows 65–80) added 2026-09-07** after the four
presentation lanes landed on `main`. Every row was re-checked against the probe file named in
it — the theorem was opened and read, not copied from `CLAUDE.md`. Line numbers are of the
declaration's first line.*

*Two claims in "What it does not show" were falsified by rows 65 and 72 and are struck through
there rather than deleted. `docs/CLAIMS_AUDIT.md` classifies every claim in this file by what
backs it, and lists the nine that must not be stated as theorems.*

**How to read a row.** A **numeral** row is a Lean theorem stating `<literal> = <extraction>`
that the build accepts; the extraction is a `Nat`-valued projection of a metatheorem's `Φ`,
of the premise functional `U`, or of the witness functional `V`. A **NEGATIVE** row is a
statement that was written and run and did **not** close — a `whnf` heartbeat timeout or a
12 GB `std::bad_alloc`. Those statements are not in the files (a file of errors is not a
green build); each probe's header carries the verbatim snippet, and the "where" column points
at it.

Two conventions used throughout:

* `U` = the bound on the premise variable of `∀x(∀u B → ∃v C)` — *how far into the assumption
  the proof reaches*. `V` = the bound on the existential witness. `Φ = coreBound U V`, which
  is `max` of the two at the given `x*`.
* Every numeral is checked by a **refutation control** (`n ± 1 ≠ …`), because a `rfl` whose
  two sides stall at the same point looks like a success (`CLAUDE.md` note 12).

---

## 1. Term route (Dialectica realizer built as a `Term`, then majorized)

`syntactic_soundness → extractedUTerm`/`extractedVTerm` → `closedMajorizer`, or
`syntactic_general_metatheorem_at(_gen)` for `Φ`.

| # | probe | derivation | evaluated | `x*` | value | status | where |
|---|---|---|---|---|---|---|---|
| 1 | `Probes/TinyBoundDemo.lean` | `tFinal`, 12 raw constructors, `ι = Empty` | `U` | `5` | **0** | PASS (`rfl`) | `TinyBoundDemo.lean:183` |
| 2 | `Probes/TinyBoundDemo.lean` | `tFinal` | `V` | `5` | **5** | PASS (`rfl`) | `TinyBoundDemo.lean:188` |
| 3 | `Probes/WBoundDemo.lean` | `wFinal`, raw, W-hyperbolic space | `U` | `(5,g)` | **0** (premise weakened away) | PASS | `WBoundDemo.lean:241` |
| 4 | `Probes/WBoundDemo.lean` | `wFinal` | `V` | `(5,g)` | **901** | PASS | `WBoundDemo.lean:254` |
| 5 | `Probes/WBoundDemo.lean` | `wFinal` | `Φ` | `(5,g)` | **901** | PASS | `WBoundDemo.lean:264` |
| 6 | `Probes/WBoundDemo.lean` | `wFinal` | `Φ` | `(7,g)` | **1273** | PASS | `WBoundDemo.lean:284` |
| 7 | `Probes/UPremiseDemo.lean` | `uFinal` — premise *consumed* (`forall_ax s ⟶ exist_ax s`) | `U` | `(5,g)` | **901** | PASS | `UPremiseDemo.lean:202` |
| 8 | `Probes/UPremiseDemo.lean` | `uFinal` | `V` | `(5,g)` | **901** | PASS | `UPremiseDemo.lean:213` |
| 9 | `Probes/UPremiseDemo.lean` | `uFinal` | `Φ` | `(5,g)` | **901** | PASS | `UPremiseDemo.lean:223` |
| 10 | `Probes/UPremiseDemo.lean` | `uFinal` | `U` | `(7,g)` / `(9,g)` | **1273** / **1709** | PASS | `UPremiseDemo.lean:244`, `:286` |
| 11 | `Probes/UPremiseDemo.lean` | `WBoundDemo.wUt` under **this file's** majorants | `U` | `(5,g)` | **0** | PASS (`rfl`) — the controlled comparison | `UPremiseDemo.lean:280` |
| 12 | `Probes/TriangleBoundDemo.lean` | `triFinal`, premise = **the triangle inequality** (`Derivable.dist_tri`), via `_at_gen` | `U` | `(5,5)` | **901** | PASS | `TriangleBoundDemo.lean:347` |
| 13 | `Probes/TriangleBoundDemo.lean` | `triFinal` | `V` | `(5,5)` | **901** | PASS | `TriangleBoundDemo.lean:356` |
| 14 | `Probes/TriangleBoundDemo.lean` | `triFinal` | `Φ` | `(5,5)` | **901** | PASS | `TriangleBoundDemo.lean:365` |
| 15 | `Probes/TriangleBoundDemo.lean` | `triFinal` | `U` | `(7,5)` / `(5,7)` | **1273** / **1273** | PASS — tracks *both* points | `TriangleBoundDemo.lean:380`, `:389` |
| 16 | `Probes/TriangleBoundDemo.lean` | `triUncondFinalB` — **same formula**, premise weakened in instead of consumed | `U` | `(5,5)` | **0** | PASS — one formula, two proofs, two `U`s | `TriangleBoundDemo.lean:498` |
| 17 | `Probes/ConjBoundDemo.lean` | `cFinalOnce`, one instantiation | `U` | `(5,9)` / `(5,1)` | **1709** / **349** | PASS | `ConjBoundDemo.lean:421`, `:431` |
| 18 | `Probes/ConjBoundDemo.lean` | `cFinalOnce` | `Φ` | `(5,9)` | **1709** | PASS | `ConjBoundDemo.lean:447` |
| 19 | `Probes/ConjBoundDemo.lean` | `tFinalOnce` (contraction removed) | `U` | `(5,9)` | **1709** | PASS | `ConjBoundDemo.lean:637` |
| 20 | `Probes/ConjBoundDemo.lean` | `cFinalTwice` — premise used at **two** terms | `V` | `(5,9)` | **1709** | PASS — the *witness* side goes through | `ConjBoundDemo.lean:463` |
| 21 | `Probes/ConjBoundDemo.lean` | `cFinalTwice`/`tFinalTwice`/`sFinalTwice`/`acFinal` | `U` | `(5,9)` | — | **NEGATIVE**: `whnf` heartbeat timeout | snippets at `ConjBoundDemo.lean:646–663` |
| 22 | `Probes/LemBoundDemo.lean` | `lFinalExt` — the LEM-free derivation at `Allowed.extended` | `U` / `V` | `5` | **0** / **5** | PASS (`rfl`) | `LemBoundDemo.lean:364`, `:367` |
| 23 | `Probes/LemBoundDemo.lean` | `lFinalNoLem` / `lFinalLem` through `…_classical_at` | `U`, `V` | `5` | — | **NEGATIVE**: `whnf` timeout, *both* sides | table + snippet at `LemBoundDemo.lean:63–99`, `:161` |
| 24 | `Probes/SeqMpBoundProbe.lean` | `seq_mp` at hypothesis depth **11** (`mct_p2`'s deepest), term ≈7×10¹² nodes | witness projection | — | **0** | PASS, via commutation lemmas (never materialising the term) | `SeqMpBoundProbe.lean:384` |
| 25 | `MetricSpaces.lean` | not a derivation — `closedMajorizer` of `d_X(0_X,0_X)` in **any** `MetricModel` with `d(a,0_X) ≤ 5` | majorant at index `0` | `n₀ = 5` | **901** | PASS | `MetricSpaces.lean:474` |
| 26 | `Probes/BoundProbe.lean` | `mct_p2`'s extracted realizer | `#eval termSize` | — | — | **NEGATIVE**: 8–10 GB exhausted | `BoundProbe.lean` header |

Row 21 is the sharpest cost datum on this route: `acFinal` and `tFinalOnce` prove the **same
formula** and differ by exactly one `and_contract`/`and_weak` pair (a logical identity); row 19
reduces and row 21 does not. Six variants in the probe kill matrix size, numeral magnitude and
the duplicating plumbing as explanations.

Row 23's headline is *not* excluded middle: `lFinalExt` (row 22) and `lFinalNoLem` are **the
same derivation term at two `Allowed` values**, so the cost is classicality's *plumbing*
(`prenexify` → negative translation → `nn_all_nn`), not `Derivable.lem`.

---

## 2. Monotone functional interpretation (MFI) — majorant computed directly, no realizer term

`monotone_soundness` → `mfiU`/`mfiV`, or `monotone_general_metatheorem_at(_gen)` for `Φ`.
The evaluator of record is `kernel_rfl` (`Probes/MonotoneLaneB.lean:155`): assign `Eq.refl`
and let the **kernel** decide. Meta-level `rfl` has no `whnf` cache when the model `M`, `h`
are free variables and times out where the kernel succeeds in seconds; its live non-vacuity
control is the kernel *rejecting* `900` (`MonotoneLaneB.lean:462–476`).

| # | probe | derivation | evaluated | `x*` | value | kernel time | status | where |
|---|---|---|---|---|---|---|---|---|
| 27 | `Probes/MonotoneSpike.lean` | `acFinal` — 13 constructors, **one `and_contract`**; row 21's timeout | `U` | `(5,9)` | **1709** | ≈207 ms (elab `rfl`) | **PASS — gate G0** | `MonotoneSpike.lean:157` |
| 28 | `Probes/MonotoneSpike.lean` | `acFinal` | `V` | `(5,9)` | **1709** | — | PASS | `MonotoneSpike.lean:166` |
| 29 | `Probes/MonotoneSpike.lean` | `acFinal` | `U` | `(5,1)` | **349** | — | PASS | `MonotoneSpike.lean:175` |
| 30 | `Probes/MonotoneSpike.lean` | `tFinalOnce` (contraction-free control) | `U` | `(5,9)` | **1709**, and **no `max`** in the normal form | — | PASS | `MonotoneSpike.lean:184` |
| 31 | `Probes/MonotoneLaneA.lean` | `tFinalTwice` — 29 constructors, premise at **two different terms** | `U` | `(5,9)` | **`max(1709, 901) = 1709`** | 1.51 s elab, 116 ms kernel | **PASS — gate G1** | `MonotoneLaneA.lean:177` |
| 32 | `Probes/MonotoneLaneA.lean` | `tFinalTwice` | `U` | `(5,1)` | **`max(901, 349) = 901`** — the **crossover** | 1.39 s / 103 ms | PASS | `MonotoneLaneA.lean:188` |
| 33 | `Probes/MonotoneLaneA.lean` | `tFinalTwice` | `V` | `(5,9)` / `(5,1)` | **1709** / **349** | 101 / 142 ms | PASS | `MonotoneLaneA.lean:199`, `:208` |
| 34 | `Probes/MonotoneLaneA.lean` | control: `349 ≠ U(5,1)` — a `U` following one instantiation only | — | `(5,1)` | refuted | — | PASS | `MonotoneLaneA.lean:239` |
| 35 | `Probes/MonotoneLaneB.lean` | `triFinal` (raw constructors) through MFI | `U` / `V` | `(5,5)` | **901** / **901** — agrees with rows 12–13 | ≈120–140 ms elab | PASS | `MonotoneLaneB.lean:400`, `:405` |
| 36 | `Probes/MonotoneLaneB.lean` | **`pmFinal` — written in the PROOF MODE** (`pforall/pintro/pinst/pexists/pexact`, 449 constructors) | `U` (counter side) | `(5,5)` | **901** | 2.22 s | **PASS — the term route never got a counter-side numeral from any proof-mode derivation** | `MonotoneLaneB.lean:420` |
| 37 | `Probes/MonotoneLaneB.lean` | `pmFinal` | `V` | `(5,5)` | **901** | — | PASS | `MonotoneLaneB.lean:423` |
| 38 | `Probes/MonotoneLaneB.lean` | `pmFinal` through `monotone_general_metatheorem_at` | `Φ` | `(5,5)` | **901** | 2.06 s | PASS | `MonotoneLaneB.lean:427` |
| 39 | `Probes/MonotoneLaneB.lean` | `pmFinal` | `U` | `(7,5)` | **1273** | — | PASS | `MonotoneLaneB.lean:432` |
| 40 | `Probes/MonotoneLaneB.lean` | `pmFinalBig` — same script over the **triangle-inequality matrix** | `U` / `V` | `(5,5)` | **901** / **901** | 1.75 / 0.76 s | PASS | `MonotoneLaneB.lean:436`, `:439` |
| 41 | `Probes/MonotoneLaneB.lean` | `finalA` — `dist_tri_chain` derived, in the premise slot, weakened away | `V` / `U` | `x*` | **901** / **0** | 170 ms / 5.9 s | PASS **but by laziness** — `wTy (le_R f g)` is `unit`-valued throughout, so nothing is entered | `MonotoneLaneB.lean:411`, `:416` |
| 42 | `Probes/MonotoneMCT.lean` | `indFinal` — a real `pinduction` (368 constructors), through the book's `t^M` (`recMaj`) | `V` | `5` / `9` | **5** / **9** | ≈2 s | **PASS — induction is not a blocker** | `MonotoneMCT.lean:154`, `:156` |
| 43 | `Probes/MonotoneMCT.lean` | `indFinal` | `U` | `5` | **0** | ≈2 s | PASS | `MonotoneMCT.lean:158` |
| 44 | `Probes/MonotoneMCT.lean` | `indFinal` through `monotone_general_metatheorem_at` | `Φ` | `5` | **5** | — | PASS | `MonotoneMCT.lean:161` |
| 45 | `Probes/MonotoneLaneBp.lean` | `uFinalC` = `UPremiseDemo`'s route with **two `mul_Q` `Eq.mp` casts injected** on the syllogism middle | `U` | `(5,g)` | **901** | — | **PASS via `monotone_soundness_eqmp` + `kernel_rfl`**; bare `kernel_rfl` is 12 GB `bad_alloc` | `MonotoneLaneBp.lean:150` |
| 46 | `Probes/MonotoneLaneBp.lean` | same | `U` | `(7,g)` | **1273** | — | PASS | `MonotoneLaneBp.lean:158` |
| 47 | `Probes/MonotoneMemoGates.lean` | **`le_R_pu_of_le_R`** — a real ℝ-layer proof-mode lemma, 650 constructors, `Eq.mpr` from `canorm`; counter transformer fed index `3` | index out | — | **3** | ≈3.7 s | **PASS — gate G-D1(a)**; on the term route and on bare MFI this was a 12 GB `bad_alloc` | `MonotoneMemoGates.lean:263` |
| 48 | `Probes/MonotoneMemoGates.lean` | **`le_R_of_le_R_pu`** — 4167 constructors, `pobtain`/`pinst`, 4 `Eq.mpr`; same read-out | index out | — | **3** | 23.8 s open form; 13.5 s / 8.4 GB peak at a closed model | **PASS — gate G-D1(b)** | `MonotoneMemoGates.lean:305` |
| 49 | `Probes/MonotoneMemoGates.lean` | `puFinal` — the two conversions **composed** into `∀q(∀n[d ≤ T]ₙ → ∃v[d ≤ T]ᵥ)` | `U`, `V`, `Φ` | `(5,5)` | — | — | **NEGATIVE**: 12 GB `std::bad_alloc`; **association-sensitive** (one association reduced once in 22.3 s then panicked) | WIP block, `MonotoneMemoGates.lean:344–378` |
| 50 | `Probes/MonotoneMCT.lean` | **`mct_p2`** (ℕ-MCT, proof mode) — `mct_bound_p2_at`, `mctPhi` | `Φ` | `λ_ _.1` | — | — | **NEGATIVE**: `Φ` is *named and type-checked*, never evaluated. Kernel 12 GB `bad_alloc` ≈1 min; Meta profile `Eq.rec ↦ 1458`, 75 nodes reached | `MonotoneMCT.lean:96`, `:117`; snippet at `:80–92` |
| 51 | `Probes/ClassicalMfiProbe.lean` | `lFinalExt` at `Allowed.extended` through MFI (no prenexify, no NT) | `U` / `V` | `5` | **0** / **5** | ≈17 s | PASS — the localisation control for row 52 | `ClassicalMfiProbe.lean:197`, `:200` |

---

## 3. MFI, classical route (`monotone_nd_soundness` — negative translation fused into the interpretation)

| # | probe | what | status | where |
|---|---|---|---|---|
| 52 | `Probes/ClassicalMfiProbe.lean` | `monotone_general_metatheorem_classical_at` applied to `lFinalNoLem`/`lFinalLem`: `U`, `V` at `x* = 5` | **NEGATIVE**: 12 GB `std::bad_alloc`, 65 s wall / 25 s user (memory-bound) | snippet at `ClassicalMfiProbe.lean:172–182` |
| 53 | `Probes/ClassicalMfiProbe.lean` | `lFinalNoLem` **alone** through `monotone_nd_soundness` (12 classical nodes, no `prenexify`): the `∃v` projection | **PASS, 37 ms** | STATUS block, `ClassicalMfiProbe.lean:100–140` |
| 54 | `Probes/ClassicalMfiProbe.lean` | `prenexify` **alone** (347 nodes, 134 nested `syllogism`) | **NEGATIVE**: 12 GB `bad_alloc`, 74 s | same |
| 55 | `Probes/ClassicalMfiProbe.lean` | synthetic chain of `k` classical `syllogism`s | k=2 **140 ms**, k=4 **3.68 s**, k=8 **OOM** — ≈ **×5 per syllogism** | same |
| 56 | `Probes/ClassicalMfiProbe.lean` | the same chain under the **compiled evaluator** (`#eval` of the hat-level ℕ projection) | k=0, k=2 give `5`; k=3 no result in 400 s, k=4 none in 240 s, CPU-bound, RSS flat | same |
| 57 | `Probes/ClassicalMfiProbe.lean` | the composed *term*-route classical derivation (`classical_to_prenex_extended`, **85,180** constructors) under MFI: elaboration | **type-checks in ≈4 s** — MFI builds no realizer term, so the ×230 does not bite at elaboration | `ClassicalMfiProbe.lean:63`, `:69`, `:82`, `:87` |
| 58 | `Probes/ClassicalMfiProbe.lean` | …its reduction | **NEGATIVE**: 12 GB `bad_alloc` after ≈47 s | `ClassicalMfiProbe.lean:36–39` |

Rows 53–56 are the localisation: it is **not** the `¬¬`-combinator leaves (they were
hand-written in `Dialectica/MonotoneNDLeaves.lean` and the OOM was unchanged), **not**
`negTrans_sound`'s ×230 (the fused recursion removes it), and **not** excluded middle
(4,376 constructors of 89,556). It is the **nesting depth of `syllogism`s**.

---

## 4. Size measurements that bound what any route can do

| # | probe | measurement | value | where |
|---|---|---|---|---|
| 59 | `Probes/SizeProbe.lean` | physical size of `ConjBoundDemo.acFinal`'s realizer, by pointer identity | **2,529 nodes, dag = tree** — the compiled evaluator preserves *no* sharing | `SizeProbe.lean` header, item 1 |
| 60 | `Probes/SizeProbe.lean` | `derivSize` of the classical route's output on a 12-node derivation | **85,180** = `prenexify` 347 + `nn_all_nn` 274 + `negTrans_sound` 363→84,905 (≈230/node) | `SizeProbe.lean` header, item 2 |
| 61 | `Probes/MonotoneLaneB.lean` | `derivSize`/DAG of proof-mode and ℝ-layer derivations | `pmFinal` 449/429; `le_R_pu_of_le_R` 650/622; `le_R_of_le_R_pu` 4167/3979 | `MonotoneLaneB.lean:78–98`, `#eval`s at `:362–371` |
| 62 | `Probes/MonotoneLaneB.lean` | `derivSize` of `le_R_trans_core`, `dist_tri_chain`, `mct_p2` | **OOM at 12 GB while the value is being built** — a sharing-free tree count is not a ruler here | `MonotoneLaneB.lean:86–87` |
| 63 | `Probes/TermPrintDemo.lean` | five extracted realizers, rendered and measured: tree / DAG / **written** | 186–563 nodes; tree/DAG 2.76–3.21 but tree/**written** only **1.00–1.35** | `TermPrintDemo.lean:119–125`, table in `term-print-out/realizers.md` |
| 64 | `Probes/ExtractTermDemo.lean` | `extractTerm` — the realizer **with the model deleted**, hence computable at a space | `UPremiseDemo.uFinal` ↦ **533** nodes, kernel-checked; a Markov-using derivation ↦ **27** | `ExtractTermDemo.lean:90`, `:100`, `:132` |

Row 63 corrects the natural conjecture: "DAG size" is an **upper** bound on achievable
sharing, because de Bruijn indices are context-relative and an open subterm cannot be
`let`-bound at top level; the written size is the honest figure, and it is close to the tree
size. Five toy points under 600 nodes — do not extrapolate.

---

## 5. The walkthrough file

`Demo/Walkthrough.lean` re-derives, in one file and on one fixed statement, the numerals of
rows 12–14 (term route), 31–32 (contraction under MFI) and 36–40 (proof-mode derivation under
MFI). It contributes **one new derivation**: `Demo.proofMode`, the six-tactic proof-mode
derivation of the same statement as `TriangleBoundDemo.triFinal` — `Demo.mfi_U`/`mfi_V`/
`mfi_phi` give `901` from it by `kernel_rfl`, `mfi_U_at_7_5` gives `1273`, `mfi_U_ne_900`
refutes. It also emits two `#hilbert` listings of the same statement — `Demo/hilbert/triFinal.md`
(9 steps, fully expanded) and `Demo/hilbert/proofMode.md` (7 steps, `pm_*` lemmas cited by
name) — and the rendered realizer of `triFinal` (413 tree nodes, 148 DAG, 344 written).

It is checked with `scripts/lean.sh Demo/Walkthrough.lean`, not by `lake build Probes`:
`Demo` is not a `lean_lib` in `lakefile.toml`. See the note at the bottom of `Probes.lean`.

---

## 6. 2026-09-06/07 — content bounds, space-theory premises, symbolic display

*Added 2026-09-07. Rows 1–64 above are numbered as of 2026-09-06 and the prose cross-references
them ("row 19", "row 23"), so these continue the numbering rather than being interleaved.*

| # | source | what | value | where |
|---:|---|---|---|---|
| 65 | `Probes/ContentExampleNat.lean` | **the first bound whose value is a function of the mathematics.** `∀x(∀u (f(Su) =₀ f u +ᵗ f u) → ∃v (f k =₀ v))` at `x = (k,f)`, by raw `Derivable.induction`; the witness at each step is built from the induction hypothesis's | `V` = **8 / 32 / 128** at `k* = 3 / 5 / 7` with `f* = λn.n+1`; **12** at `(2, λn.n+3)`, so it moves with *both* components | `:255`, `:256`, `:261`, `:265`; controls `:298–306` |
| 66 | `Probes/ContentExampleNat.lean` | the premise side of the same derivation | `U` = **0 / 0 / 1 / 2 / 4** at `k* = 0…5` | `:269–273` |
| 67 | `Probes/ContentExampleNat.lean` | `Φ` through `monotone_general_metatheorem_at` itself | **8** at `k* = 3`, **32** at `k* = 5` | `:276`, `:279` |
| 68 | `Probes/ContentExampleNat.lean` | the **term route** on the same derivation, as an independent check | `closedMajorizer … = 8`, agreeing with row 65. Its `U` is `INTERNAL PANIC: out of memory` at 12 GB | `:292` |
| 69 | `Probes/ContentExampleNat.lean` | **NEGATIVE — the value ceiling, and it is independent of proof size.** Same fixed 145-constructor derivation | `V = 128` reduces in ≈9 s; **`V = 256` exhausts 12 GB.** `Term.add`'s majorant is a `prec`, so `recMaj` iterates *value*-many times unshared | header `:61–65` |
| 70 | `Probes/ContentExampleNat.lean` | **NEGATIVE — the proof mode is a liability for extraction.** The *same theorem by the same argument*, written in the proof mode | **42,729** constructors against **145** raw — ×295 — and it reduces only at `k* = 0` | header `:318`, `#eval` at `:341` |
| 71 | `Probes/ContentExampleSpace.lean` | one statement at a W-hyperbolic model, **two proofs, two bounds** — `M` and `h` free, so it holds of every model with `d(a,0_X) ≤ 5` | `eDir` (index from the space): `U = V = Φ` = **901** at `(5,5)`, **1273** at `(7,5)`. `eRec` (index from the doubling induction): **1 / 8 / 32** at `k* = 0/3/5`, and **unchanged** at `(7,5)` — provably indifferent to the space majorants | `:329–397`; controls `:404–419` |
| 72 | `Probes/WExtBoundDemo.lean` | **the first bound mined through a space-theory `.premise`.** Rung 2 runs `monotone_soundness` through `W2_at`, which ends in `Derivable.premise WHyperbolic.W2` and whose body is a proof-mode script — where every earlier space extraction consumed `Derivable.dist_tri`, a *free constructor* | `V` = **901** at `(5,5)`, **1273** at `(7,5)`; composition depth **8**, seconds | `:404`, `:408` |
| 73 | `Probes/WExtBoundDemo.lean` | rungs 3–4: a bound whose premise is a **derived** theorem — `W_ext_left`, then `W_ext_param` | `V` = **901**, in ≈36 s, through derivations of composition depth **≥66** and **≥62** | `:447`, `:466` |
| 74 | `Probes/WExtBoundDemo.lean` | **NEGATIVE, and it localises the failure.** The counter side of rows 73 | `mfiU` is `std::bad_alloc` at 12 GB (≈100 s) on the *same* derivations whose `V` reduces. **The failure is the counter side specifically, not depth** | header `:64–70`, `:128`; snippet in header |
| 75 | `Probes/ExprBound.lean` | **`Φ` displayed as arithmetic**, by fueled `ExprStructEq`-memoised partial reduction at the `Expr` level — not a numeral but the *function* | `Φ(a,b) = maxT nat (pairN (2·((a+b)·2^(0+1))) (2^(0+1)−1)) 0`, `numObjs` **166**, ≈0.1 s. `M` and `h` are bound and **absent from the body** — uniformity as syntax. Reproduces 1709 at `(5,9)` and 349 at `(5,1)` | `:227`, `:231`; header for the fuel/size table |
| 76 | `Probes/ExprBound.lean` | **NEGATIVE.** The same tool on a proof-mode `pinduction` bound | the iteration becomes visible as `recMaj`, but output *grows* with fuel — 1033 / 1295 / 8125 objects — and times out at fuel 30. `recMaj` stuck on a symbolic point never collapses | header, "Second target" |
| 77 | `Probes/NestingDepth.lean` | composition **depth** — the longest path through composition nodes, memoised on `ExprStructEq`, no `whnf` | `prenexify` **9** (its syllogism *count* is 134 — do not quote the count); `mct_p2` **12**; `le_R_trans_core`/`dist_tri_chain`/`real_mct_p2` **≥23** | header table |
| 78 | `Probes/NestingDepth.lean` | **two limits on that instrument**, found 2026-09-07 | the walk is **capped at 250 000 `Expr` nodes**, so every "≥" is the cap: `clamp01_congr_R`, a slack-free single-index lemma, reports ≥35. It **cannot discriminate inside the ℝ layer**. And depth does not predict the *witness* side at all (row 73) | `WExtBoundDemo.lean` header `:96–102` |
| 79 | `Probes/SharingProbe.lean` | **NEGATIVE — the `let`-sharing hypothesis is refuted.** Binding each sub-majorant with `let` in `MRealizer.syllogism` | identical before and after: **×3.7 per level, `std::bad_alloc` at k = 6**. The kernel zeta-reduces `let` by substitution, so binding-site sharing never survives. *(A "×5, k = 8" pair circulated in the docs; that run was never committed — this file's header says so.)* | header `:8–26` |
| 80 | `Metatheorems/WHyperbolicLemmas.lean` | not a bound — **extensionality of `W`, derived** from (W2)/(W4). The ambient system is only *weakly* extensional, so a space constant is legitimate only if its extensionality follows from the space's own axioms | `W_ext_left`, `W_ext_right`, `W_ext_param`, `W_ext`, all `[propext, Quot.sound]`, at **every** `Allowed`; read back in an arbitrary model | `:973–976`; model demo in `Probes/WHyperbolicLemmasDemo.lean` |

Row 72 and row 65 are the two that change what this document could previously claim, and both
are struck through in "What it does not show" below.

Row 74 is the sharpest statement of the blocker the project has: on one derivation, at one
`x*`, with one set of majorants, the witness functional reduces and the premise functional does
not. Everything else — casts, the proof-mode layer, induction, `.premise`, classicality — has
been eliminated by measurement.

## What this shows

* **The extraction pipeline runs end to end and produces kernel-checked literals** — from
  raw-constructor derivations (rows 1–20), from derivations at an *arbitrary* W-hyperbolic
  space with the model left as a variable (rows 3–20, 27–46), from a derivation whose premise
  is a genuine **space axiom** (row 12), from a **proof-mode** derivation (rows 36–40), through
  a real **induction** (rows 42–44), and through the `Eq.mpr` casts of two genuine ℝ-layer
  lemmas (rows 47–48).
* **The bound is a property of the proof, not of the theorem.** Row 16 is the clean statement
  of this: one formula, two derivations, the same majorants, `U = 901` against `U = 0`.
* **The bounds are uniform in the space.** Every space row holds with `M` and `h : d(a,0_X) ≤ 5`
  as free variables, so the numeral is a fact about *every* W-hyperbolic model with that one
  parameter — which is the whole point of Kohlenbach's metric metatheorems.
* **The monotone functional interpretation strictly dominates the term route here.** Every
  term-route negative that was re-run under MFI became positive (rows 21→27/31, and the
  proof-mode counter side, rows 36–40), and no MFI row is worse than its term-route
  counterpart.

## What it does not show

**⚠ The 64 rows above predate 2026-09-06 and three of the claims in this section have since
been falsified. They are kept, struck through, because what replaced them is the more useful
statement. Regenerate the table before showing it; `docs/CLAIMS_AUDIT.md` has the full list.**

* ~~**No numeral yet from any derivation with real mathematical content.**~~ **False since
  2026-09-06.** `Probes/ContentExampleNat.lean` mines `V = 2^k·f(0)` from
  `∀x(∀u (f(Su) =₀ f u +ᵗ f u) → ∃v (f k =₀ v))` by a raw `Derivable.induction`, kernel-checked
  at six points with refutation controls, the term route agreeing on `V`. The *theorem* there is
  trivial and the **bound** is the mathematics — which is this project's own thesis with a
  number attached. What remains true is the narrower claim: `mct_p2` (row 50), `real_mct_p2`,
  `le_R_trans_core` and `dist_tri_chain` still have named, type-checked `Φ`s and no values.
* ~~**Every numeral above comes from a derivation whose content is an instantiation term.**~~
  **False since 2026-09-07.** `Probes/WExtBoundDemo.lean` rung 2 mines a bound through
  `Derivable.premise WHyperbolic.W2` — a genuine space-theory premise with a proof-mode script
  inside it, at composition depth 8 — where every earlier space extraction consumed
  `Derivable.dist_tri`, a *free constructor*. So neither `.premise` nor the `pm_*` layer is
  what stops extraction.
* **The classical route reduces nothing** (rows 23, 52). Still true.
* **The failure is on the counter side specifically.** Rungs 3–4 of `WExtBoundDemo` reduce `V`
  to `901` through derivations of depth ≥66 in ~35 s; only `mfiU` exhausts memory. Depth alone
  does not predict failure — the duplication in `MRealizer.syllogism` does.

## The single named blocker

`ARCHITECTURE.md` §14.7. Two causes were separated and only one survives:

1. ~~`Eq.mpr` casts buried under the `pm_*`/`seq_*` layer~~ — **addressed** by Lane D1
   (`Dialectica/MonotoneSeq.lean`, the `mfi_memo` set + `mfi_push`), which is what makes rows
   47–48 pass.
2. **The composition combinators re-evaluate their sub-majorants.** `MRealizer.syllogism`
   uses `hAB` three times and `hBC` twice, and neither the kernel nor the compiled evaluator
   shares them: **×3.7 per nested syllogism, dying at k = 6** (row 79 — the committed
   measurement; a "×5, k = 8" pair circulated in these documents and came from a run that was
   never committed). This is the Dialectica exponential in its last hiding place and it is
   route-independent.

**Sharpened 2026-09-07 by rows 73–74**, and this is the most precise statement available: on
one derivation, at one `x*`, with one set of majorants, `mfiV` reduces to `901` in ≈36 s while
`mfiU` exhausts 12 GB. **The failure is the counter side specifically** — the side where that
duplication is charged — and *not* depth as such, since the same derivation's witness side goes
through 66 levels without trouble. Everything else once suspected — casts, the `pm_*` layer,
induction, `.premise`, classicality — has been eliminated by measurement.

**The `let` fix has been attempted and is refuted** (row 79): the kernel zeta-reduces `let` by
substitution, so binding-site sharing never survives to the reduction that matters, and the
compiled evaluator already shares closure results by pointer. A fix must change what is
*applied* — staged evaluation with per-stage literal reification, or an `MRealizer` whose
counter component does not call its witness component.

A second, **independent** wall was found the same week and is not this one: the extracted
*value* (row 69). On a fixed 145-constructor derivation `128` reduces and `256` does not,
because `recMaj` iterates value-many times unshared. For MCT, whose bound is of order `2^k`,
that is the nearer of the two.
