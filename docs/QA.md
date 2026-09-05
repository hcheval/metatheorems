# QA — the questions a proof-mining / formalisation audience asks

*Compiled 2026-09-06 on branch `demo`. Every factual claim carries a declaration name or a
`file:line`. Where a claim is negative ("does not reduce"), the pointer is to the probe header
that records the measurement, because the failing statement is deliberately not in the build.
Numbers are tabulated in `docs/RESULTS.md`; this file is the prose.*

---

### 1. Have you actually extracted anything concrete, and from what proofs?

Yes — kernel-checked natural-number literals, from real `Derivable` terms, with the model left
as a free variable. The clearest single row: `Probes/TriangleBoundDemo.lean:347` proves
`901 = closedMajorizer (triCm M h) (triUt M) (5,5)` where `M` is an **arbitrary**
W-hyperbolic model and `h : d(a, 0_X) ≤ 5`; the derivation `triFinal`
(`TriangleBoundDemo.lean:193`) has the triangle inequality of the space in its premise slot
(`triAll_eq`, `:127`, proves the premise formula *is* what `Derivable.dist_tri` concludes), so
the extracted `U` is the precision at which that axiom has to be known. The first extraction of
any kind was `Probes/TinyBoundDemo.lean:183–188` (`U = 0`, `V = 5`) from a 12-constructor
derivation at `ι = Empty`. On the monotone route the same numbers come out of a derivation
written **in the proof mode** (`Probes/MonotoneLaneB.lean:420`, `U = 901`, counter side
included, 2.2 s of kernel time), through a real **induction** (`Probes/MonotoneMCT.lean:154`,
`V(5) = 5`, `V(9) = 9`), and through the `Eq.mpr` casts of two genuine ℝ-layer lemmas
(`Probes/MonotoneMemoGates.lean:263`, `:305`). What every one of these has in common, and it is
the honest caveat: the mathematical content is an **instantiation term**, and `U`/`V` are read
off that term rather than off the matrix.

### 2. Are the bounds properties of the proof or of the theorem?

Of the proof, and this is checked rather than asserted. `Probes/TriangleBoundDemo.lean:498`
(`triUncUtB_is_zero`) and `:347` (`triUt_is_901`) are **the same formula with the same
majorants**, differing only in whether the premise is consumed (`forall_ax s ⟶ exist_ax s`) or
weakened in: `U = 0` against `U = 901`. Sharper still,
`Probes/UPremiseDemo.lean:280` (`wUt_is_zero_under_uCm`) evaluates `WBoundDemo`'s own `U` term
under *this* file's `ConstMajorants` **value**, so the majorant argument is literally the same
expression in both statements. The project's other instance of this is `mct_p1` vs `mct_p2`
(`ProofMode/MCTLazy.lean`, `ProofMode/MCT.lean`): two derivations of one ℕ-MCT statement.

### 3. Why is there no number from MCT yet, and what is the plan?

`mct_p2`'s `Φ` is **named and type-checked** — `MonotoneMCT.mct_bound_p2_at`
(`Probes/MonotoneMCT.lean:96`) and `mctPhi` (`:117`) — and has never been evaluated. The
kernel dies with `std::bad_alloc` at the 12 GB cap after ≈1 minute; the Meta profile
(`MonotoneMCT.lean:26–40`) reaches 75 derivation nodes with `Eq.rec ↦ 1458` dominant. Two
candidate causes were separated. The first, `Eq.mpr` casts under the `pm_*`/`seq_*` layer whose
equations are `closed_subst`-style normalisations the kernel's K-rule has to *recompute*, is
**addressed**: `Dialectica/MonotoneSeq.lean` (Lane D1) pushes `monotone_soundness` through that
layer and turns each cast into an `MRealizer.transportTo` at the kernel-normalised hat type,
which is what makes `MonotoneMemoGates.d2c_is_3` and `d1c_is_3` pass. The second is not:
`MRealizer.syllogism` uses its first argument three times on the counter side, and neither the
kernel nor the compiled evaluator shares the re-evaluations — measured as **≈×5 per nested
syllogism** (`Probes/ClassicalMfiProbe.lean:100–140`, k=2 140 ms, k=4 3.68 s, k=8 OOM), and
visible as association-sensitivity in `MonotoneMemoGates.lean:344–378`. The plan is a majorant
representation with explicit sharing — `let`-bound sub-majorants evaluated once. It has not been
attempted; `ARCHITECTURE.md` §14.7 is the standing statement.

### 4. Is the classical route working?

It is proved, it type-checks, and it does not reduce. `syntactic_general_metatheorem_classical`
and `_classical_at` are complete (`SyntacticMetatheorem.lean`; axioms printed by
`Metatheorems/Headline.lean`), routed prenexify → Kuroda negative translation → `nn_all_nn` →
Dialectica. `MonotoneMetatheoremClassical.monotone_general_metatheorem_classical_at` has the
*same statement* and fuses the negative translation into the interpretation
(`Dialectica/MonotoneND.lean`), so `negTrans_sound`'s 85,180-constructor output is never built;
a welcome side effect is that **NT-stability disappears** — the premise case takes an
`MRealizer` of the translated premise directly, and `spremise_nd_of_pu` builds it for any
purely universal premise set. But no classical bound reduces: `Probes/LemBoundDemo.lean:63–99`
records the term-route timeout and `Probes/ClassicalMfiProbe.lean:172–182` the MFI 12 GB
`bad_alloc`. The cause is **not excluded middle** — `LemBoundDemo.lFinalExt` and `lFinalNoLem`
are the *same derivation term at two `Allowed` values*, and the extended one reduces
(`LemBoundDemo.lean:364`, `ClassicalMfiProbe.lean:197`) — it is `prenexify`'s 134 nested
syllogisms hitting the ×5 of question 3.

### 5. How faithful is this to Kohlenbach?

The target is Theorem 17.52 of *Applied Proof Theory*, and the `_gen` entry points
(`syntactic_general_metatheorem_gen`, `_at_gen`, `_classical_gen`, `_block`) match its
`B∀`/`C∃` shape — an arbitrary purely universal premise matrix and purely existential
conclusion; the quantifier-free versions are instances. Two deliberate deviations, both
recorded in `ARCHITECTURE.md` §13 and in `CLAUDE.md`'s "Lambda vs. combinators":

*Tuples.* Kohlenbach needs a tuple `b̲` because his type system has no products; `Ty` has
them, so one `∀b^(ρ₁ ×ₜ … ×ₜ ρₙ)` block suffices, and `degree (.prod ρ τ) = max ρ.degree
τ.degree` leaves the type level — hence the bound extraction — undisturbed.

*Binders instead of combinators.* `Term` has a primitive `lam` and **no `Π`/`Σ`**
(`Term.lean`), so where the document's `all_closed_terms_majorizable` is a two-case induction
(constant, application), ours has cases for `lam`, `mkPair`/`fst`/`snd`, `unitI`, and
`AbstractMajorizability` correspondingly has 20 fields where Definition 6.0.1 has 3
(`Majorizability.lean:66` is `arrow_intro`). This is a **relocation, not a strengthening**:
`arrow_intro` *is* Kohlenbach's Lemma 17.80 (`x* ≽ x ↔ ∀y*,y(y* ≽ y → x*y* ≽ xy) ∧ <self-maj>`),
which the document needs anyway to discharge condition 3 for `Π` and `Σ` — and whose
`\solution{}` in the reference document is empty, while `bezemAbstract` discharges it as
`fun _ _ h₁ h₂ => ⟨h₁, h₂⟩`. The residual formal difference is that our `arrow_intro`
quantifies over arbitrary semantic `f*, f` where the document needs 17.80 at two constants; for
any relation defined by recursion on types — Howard 3.34, Bezem 3.48, `≽ᵃ` 17.50 — the two
coincide. `ι` and `κ` are split (`Term {ι κ} (F : κ → Ty ι)`) so normed and inner-product
signatures are expressible over one base type. The metric is **structural**, `Term.dist`, so
`eqAtType (.base i) s t` is *defined* as `d_i(s,t) =ℝ 0ℝ` rather than being a parameter
(`EqAtType.lean`, `ARCHITECTURE.md` §1, §8).

If literal faithfulness ever matters, the recorded route is a separate combinatory inductive
`CTerm` with `Π`/`Σ`, a translation, and an interpretation-preservation theorem — not a
rewrite of `Term`.

### 6. What is the trust base?

Lean 4's kernel plus Mathlib, and nothing else: **there is no `sorry` anywhere in
`Metatheorems/`**, and no custom axiom. `Metatheorems/Headline.lean` (`lake build
Metatheorems.Headline`) prints `#print axioms` for every headline declaration in one place —
`soundness`, `all_closed_terms_majorizable`, the seven term-route metatheorems, the five
monotone ones, the four space instantiations, `mct_p1`/`mct_p2`/`real_mct_p2`,
`real_mct_of_bound`, `dist_tri_chain`, `dist_rev_tri`, `add_Q_assoc`, `distrib_Q`,
`cauchy_complete_R`, `le_R_trans_core`. The expected lists are stated in its header:
object-level derivations `[propext, Quot.sound]` or nothing at all; anything mentioning a
model, Mathlib `ℝ`, or Markov's principle `[propext, Classical.choice, Quot.sound]`.
`sorryAx` must never appear, and does not. On the syntactic route `Classical.choice` enters
from exactly two places, both traced: `sMarkov` (Markov's principle — expected) and
`matrixTerm_correct` (a `Prop`-level correctness theorem, so it cannot obstruct extraction).
`Derivable` is `Type`-valued, so a "proof" in this system is a term whose head constructors
*are* the inference rules; `Metatheorems/Hilbert.lean`'s `#hilbert` renders any of them as a
numbered Hilbert derivation (`Probes/HilbertDemo.lean`, output in `hilbert-out/`).

### 7. Is the proof mode itself verified?

There is nothing to verify: `Seq` is an `abbrev` for `Derivable F a Premises (pack Δ B)`
(`ProofMode/Packing.lean:63,68`) and `SeqD` is a `@[reducible]` name-carrying wrapper
(`ProofMode/Display.lean:58`). Every tactic is a lemma about `SeqD` plus a macro, so the whole
layer is *definitionally* the kernel inductive and a tactic bug can only fail to elaborate — it
can never produce a false theorem. That is also why the extraction machinery can see through
it: `monotone_soundness` reduces a 449-constructor `pm_allI`/`pm_intro`/`pm_inst`/`pm_exI` tree
to a numeral in 2 s (`Probes/MonotoneLaneB.lean:420`).

### 8. What does a user actually write?

This, and nothing else — the full derivation of `∀p^(X×X)(∀n B(n,p) → ∃v B(v,p))` at a
W-hyperbolic space (`Probes/MonotoneLaneB.lean:341`):

```lean
def pmFinal : D [] (Formula.all pTy (Formula.all Ty.nat tB →ᶠ Formula.ex Ty.nat tB)) := by
  pmode                      -- open the hypothesis context (definitionally free)
  pforall                    -- ⊢ ∀p …          introduce p
  pintro h                   -- h : ∀n B(n,p) ⊢ ∃v B(v,p)
  pinst h triWit with h1     -- h1 : B(s(p), p)
  pexists triWit             -- ⊢ B(s(p), p)
  pexact h1
```

Around forty tactics exist (`ProofMode/Tactics.lean`): `pintro`, `papply`, `pexact`,
`pexists`, `pobtain`, `pinduction`, `prw`/`prwby` (rewriting by quantifier-free extensionality,
in the goal or in a hypothesis), `pcases`, `pleft`/`pright`, `psym`, `pthm`. The goal displays
as a named-hypothesis box with object-level notation. The scale it carries:
`ProofMode/RealMCT.lean` is 655 lines of this and derives ℝ-MCT.

### 9. How large are the bounds, and are they comparable to the book's?

Two different questions. **Growth rate**: astronomical, and structurally so — the term route
builds the exact Dialectica realizer and *then* majorizes, where Kohlenbach's tool is the
monotone interpretation, which never builds it and simplifies at every step; the factors come
from that gap and no care in our extraction closes it. The claim this project defends is
*verified mechanical extraction*, not competitive constants. **Concrete comparison**: for ℝ-MCT
it is exact. `ProofMode/RealMCT.lean:61–70` states that the derivation's budget is `2^{k+1}`
windows of drop `2^{-(k+1)}` against the book's `2^k` windows of `2^{-k}` — one extra iteration
of `m ↦ m + g m` in the exponent, `Φ ≈ g̃^{(2^{k+1})}(0)` against `g̃^{(2^k)}(0)` — and says
exactly where the factor comes from: the dichotomy is taken on the *quantifier-free* window
test at a single rational index, so a failing window is only known to drop by `5·2^{-(k+3)}`,
and the dyadic budget unit under `5/8` is `2^{-(k+1)}`. That is the price of a derivation that
needs neither LEM nor Markov. `Reference/MCT.lean:120` (`metastable`) is the hand-written
textbook comparison with `Φ k g = (shift g)^[2^k + 1] 0`, itself one iterate above the sharp
`2^k` because its `descent` is non-strict; `Reference/MCTBridge.lean` locates that off-by-one.
On **readability**, `Probes/TermPrintDemo.lean` measures five extracted realizers: tree/DAG is
2.77–3.21, but tree/**written** — nodes actually spelled out, after hoisting only the closed
repeated subterms a `let` can legally bind — is only **1.00–1.35**
(`term-print-out/realizers.md`). De Bruijn indices are the pessimal representation for this,
since the same content at two binder depths is textually distinct.

### 10. Which theories are instantiated, and what did discharging their axioms cost?

Four, all with the object-level axioms **proved true in every model**, so no metatheorem takes
an axioms hypothesis:

| theory | file | signature | axioms |
|---|---|---|---|
| (pseudo)metric spaces | `MetricSpaces.lean` | `ι = Unit`, **zero** function constants | the three are free `Derivable` constructors (`dist_self`, `dist_comm`, `dist_tri`), all Π⁰₁ |
| W-hyperbolic | `WHyperbolic.lean` | one constant `W` | (W1)–(W4), `WHyperbolicModel.axiomsHold` (`:555`) |
| CAT(0) | `CAT0.lean` | same signature | (W1)–(W4) + CN, `CAT0Model.axiomsHold` (`:223`) |
| normed spaces | `Normed.lean` | five constants (`+`, `·`, `‖·‖`, `−`, `1_X`) | thirteen, checked against Kohlenbach §17.3, `NormedModel.axiomsHold` (`:848`) |

`Instances.lean` says the Mathlib structures *are* models: `MetricModel.ofMetricSpace`,
`NormedModel.ofNormed`, `WHyperbolicModel.ofNormed`, `CAT0Model.ofInner`, each with its
`_axiomsHold`. What discharging cost was one bridge, `CodeRealOps.lean`: `codeReal f` is the
real a Cauchy code denotes, and `interpret_le_R_pu_of_codeReal_le` /
`interpret_eq_R_of_codeReal_eq` plus the `codeReal_interp_*` homomorphism lemmas turn each
object axiom into a Mathlib identity. One lesson worth repeating: a **defined** operation
inherits the majorant of its definiens, so anything routed through the rational encoding pays
an encoding-sized constant — `(−1)·x` was majorized by `(⟨−1⟩ + 1)·n`, a factor with no
mathematical content. Making `−` a primitive constant gives the exact majorant `n ↦ n`, and
`NormedModel.neg_maj_lower_bound` proves that *no* majorant is smaller. Mathlib has neither
CAT(0) nor W-hyperbolic spaces, so that semantic side is from scratch.

### 11. Why encode ℚ and ℝ *inside* the object theory instead of using Mathlib's?

Because the metatheorem is a statement about **WE-HA^{ω,X}**, and its bound-extraction
argument works by majorizing closed terms of that language. A real number has to be an object
of the language — Kohlenbach's representation, a Cauchy sequence of rational codes with a fixed
modulus, `realTy ι = nat →ₜ nat` — or there is nothing to majorize and the theorem is about
something else. The cost was the whole ℚ/ℝ tower (`RationalNumbers.lean`, `RealNumbers/*.lean`,
zero sorries): the encoded reals are a complete Archimedean ordered field inside the object
theory, which is Kohlenbach's condition (m). Mathlib's `ℝ` is used on the *semantic* side, and
`QValBridge.lean`/`CodeReal.lean` is the bridge (`qval` for codes, `codeReal` for sequences).
The representation is also what makes the metatheorem's uniformity work: `Ty.hat` sends every
base type to `nat` (`TypeSystem.lean:80`), so a majorant is always an ℕ-valued object and
never mentions the carrier — which is why the numerals in `docs/RESULTS.md` hold with the model
as a free variable.

### 12. Is anything in the object theory actually *proved*, or only stated?

Yes, and this was a real gap until the `≤ℝ` package landed. `BaseEquality.dist_tri_chain`
(`d(x,w) ≤ℝ (d(x,y) +ℝ d(y,z)) +ℝ d(z,w)`) and `dist_rev_tri` / `dist_rev_tri'` /
`dist_rev_tri_abs` (the reverse triangle inequality, three forms) are derived from the free
constructors alone, so they hold in **every** `Derivable F al Premises`;
`Probes/RevTriangleDemo.lean` reads them back in an arbitrary `MetricModel` through
`MetricModel.soundness` (`MetricSpaces.lean:815`) as ordinary Mathlib statements
`M.d a c - M.d b c ≤ M.d a b`. The substantial one is `ProofMode.real_mct_p2`
(`ProofMode/RealMCT.lean:621`): ℝ-MCT in metastable form, 655 lines, at **every** `Allowed`
— no excluded middle and no Markov, because the window dichotomy is `qf_lem` on a
quantifier-free matrix. `RealMCT.real_mct_of_bound` (`RealMCTStatement.lean:610`) composes the
metatheorem with the semantic bridge and yields Mathlib metastability with the extracted `Φ`.

### 13. Does soundness hold — is the proof system connected to the models at all?

`Soundness.lean:262`: `Derivable F allowed Premises A → ∀ env, Formula.interpret si A env`, all
39 constructors, zero sorry, general in `{ι} {X} {F}`. It takes five model facts as section
variables and each is forced by a named constructor: `hprem` by `premise`; `hdist_self` by
`dist_self` **and** by `beta_eq`/`rec_zero`/`rec_succ`/`qfer` (all four "equality" constructors
collapse to reflexivity of `=_X`); `hdist_comm` and `hdist_tri` by their own constructors; and
`hsep` — separation, `d(s,t) =ℝ 0ℝ → ‖s‖ = ‖t‖` — by `qfer` alone, which is genuinely needed
rather than bookkeeping, since `qfer` concludes `r[s] =_σ r[t]` and `r` may be an arbitrary
function constant. A soundness parameterised on `dist_comm`/`dist_tri` only was tried and
**refuted with a compiling counter-construction** (`Probes/SoundnessProbe.lean`).

### 14. What would you do next, in priority order?

1. **Sharing in the majorant combinators** (question 3). Everything else is downstream: it is
   the one blocker shared by the classical route, by `mct_p2`, by `real_mct_p2` and by the
   composed ℝ-layer statement of `MonotoneMemoGates.puFinal`.
2. **The rounding constant `(·)◦`** as a `κ`-constant with majorant `Mmaj 1`
   (`Rounding.roundR_le₁_Mmaj` is already proved and used by nothing). This buys uniformity in
   the sequence for ℝ-MCT and uniformity in `λ` for hyperbolic spaces —
   `RealMCTStatement.codeReal_zero_code_unbounded` (`:636`) is the proof that it is *needed*:
   a code for `0` can have arbitrarily large entries, so "`a n ∈ [0,1]`" bounds nothing about
   `a` as a functional.
3. Then the capstone the project has been aiming at: `real_mct_p2`'s `Φ` as a numeral, against
   `Reference/MCT.lean`'s hand-computed one.
