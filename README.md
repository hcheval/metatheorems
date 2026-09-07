# WE-HA^{ω,X} and the Dialectica interpretation, in Lean 4

A formalization of **Weakly Extensional Heyting Arithmetic in all finite types over an
abstract space `X`** (WE-HA^{ω,X}), of **Gödel's Dialectica interpretation** of it, and of the
**proof-mining metatheorems** of Kohlenbach's *Applied Proof Theory* — together with the
machinery that turns a formal derivation into an explicit, kernel-checked numerical bound.

The object theory, its semantics, the interpretation, the soundness theorems, the
majorizability layer and four concrete space theories (metric, W-hyperbolic, CAT(0), normed)
are all in the build, with no `sorry` anywhere.

---

## What is proved

| | |
|---|---|
| **The proof system** | `Derivable F allowed Premises A`, a `Type`-valued Hilbert-style inductive with **39 constructors** — the propositional and first-order rules, `induction`, quantifier-free extensionality (QF-ER), the three pseudometric axioms, and the optional principles (`lem`, `markov`, `ip`, `ac`, `qfac`) each guarded by an `Allowed` flag, so one inductive presents the whole ladder of systems from WE-HA^ω to WE-PA^ω + AC + IP + MP. |
| **Semantics and soundness** | `Soundness.lean`: every derivation is true in every model, all 39 constructors, relative to five explicitly named model facts (premise truth, the three pseudometric facts, and separation — which only the QF-ER case needs). |
| **Dialectica** | Full soundness of the interpretation (`Dialectica/Lemmas.lean`), and a **syntactic** version (`Dialectica/Syntactic.lean`) in which witness and counter *types* are object-level `Ty` and realizers are object-level `Term`s, so extracted realizers are majorizable. Also the Kuroda negative translation with its own soundness theorem, and their composition. |
| **The metatheorems** | `syntactic_general_metatheorem` and `syntactic_general_metatheorem_classical`, with `_at` variants that return the bound as *data* (`{ Φ // … }`) rather than as an existential, and `_gen` variants that take an arbitrary purely-universal premise and purely-existential conclusion (Kohlenbach 17.52's `B∀`/`C∃`). Majorants come free from `all_closed_terms_majorizable`. |
| **Monotone functional interpretation** | `monotone_general_metatheorem_at` / `_at_gen` / `_classical_at`: the majorant of a realizer computed directly by recursion on the derivation, never building the realizer term (Kohlenbach ch. 9). This is the route that actually produces numbers. |
| **ℚ** | The rationals, encoded as naturals through a sign-magnitude Cantor pairing. Each ordered-field axiom is derived *inside the object theory* and named individually — associativity, commutativity, distributivity, the additive and multiplicative inverses, and the four order facts (`lt_Q_add`, `lt_Q_trans`, `lt_Q_mul_pos`, `lt_Q_trichotomy`). Zero sorries. |
| **ℝ** | Cauchy sequences of ℚ-codes with a fixed modulus. All 22 ordered-field facts, the approximation lemma, and **completeness** (`cauchy_complete_R`, which needs no choice) — each a named theorem. Together these are Kohlenbach's condition (m); there is no single bundling declaration. |
| **Space theories** | Metric, W-hyperbolic, CAT(0) and real normed spaces, each with its signature, axioms, model, majorants, and its own metatheorem. Every axiom is **discharged**: `Instances.lean` turns an arbitrary Mathlib `MetricSpace`, `NormedAddCommGroup`/`NormedSpace ℝ` or real inner-product space into a model, so the space metatheorems take no hypothesis beyond the Mathlib structure. |
| **A proof mode** | Around seventy tactic, notation and command declarations giving named-hypothesis reasoning, a sequent display, object-level notation, rewriting through QF-ER, and induction carrying a hypothesis context. Everything in it is *definitionally* `Derivable`, so a tactic bug can only fail to elaborate — there is nothing to trust. See [`docs/TACTICS.md`](docs/TACTICS.md). |
| **Worked examples** | Two contrasting derivations of the monotone convergence theorem over ℕ (`mct_p1`, `mct_p2`); **ℝ-MCT in metastable form** (`real_mct_p2`, 655 lines of real-analysis content, with a proved bridge to Mathlib's reals); the chained and reverse triangle inequalities, derived and read back in every metric model; extensionality of the convex-combination operator `W`, derived from the W-hyperbolic axioms. |

Extraction, end to end, has produced kernel-checked numerals from raw-constructor derivations,
from proof-mode derivations, through a real induction, through the `Eq.mpr` casts of genuine
ℝ-layer lemmas, from a derivation whose premise is a space axiom, and from one whose premise is
a *derived* space theorem — with the model left as a free variable, so each numeral is a fact
about every space of that kind. `docs/RESULTS.md` tabulates all of them, and every negative
result, row by row with a file and line for each.

## Limitations

Stated plainly, because the interesting part of this project is where the boundary sits.

* **Small and medium derivations extract to numerals; large ones do not.** Bounds reduce for
  derivations up to roughly a few hundred constructors, including proof-mode ones and ones at
  a space. They do not reduce for the four largest derivations with mathematical content —
  `mct_p2`, `real_mct_p2`, `le_R_trans_core`, `dist_tri_chain` — whose bounds are named and
  type-checked but never evaluated.
* **The cause is identified and is not any of the things first suspected.** It is not
  classicality, not the proof mode, not induction, not casts, not the use of a `.premise`, and
  not formula size — each was eliminated by measurement. It is that the **composition
  combinators re-evaluate their sub-majorants**: `MRealizer.syllogism` uses one argument three
  times and the other twice, and neither the kernel nor the compiled evaluator shares them, so
  cost multiplies by ≈3.7 per nesting level and exhausts 12 GB at depth 6. The failure is
  charged to the *counter* side specifically: on one derivation, at one point, with one set of
  majorants, the witness functional reduces in seconds while the premise functional exhausts
  memory. Binding sub-majorants with `let` does not help — the kernel zeta-reduces `let` by
  substitution.
* **A second, independent ceiling is on the extracted *value*.** The majorant of addition
  recurses, so a bound of size `n` costs `n` unshared iterations: on a fixed derivation, `128`
  reduces and `256` does not. For MCT, whose bound is of order `2^k`, this is the nearer wall.
* **No bound has yet been extracted through the classical route.** Both the term route and the
  monotone route type-check the classical metatheorem cleanly, and both exhaust memory when
  asked for a numeral. The cost is the composition depth of the prenexification step, not
  excluded middle — the same derivation at two `Allowed` values reduces intuitionistically and
  does not classically.
* **Growth rate is not competitive with hand-mined bounds, and structurally cannot be.**
  Kohlenbach simplifies at every step by hand; a mechanical interpretation does not. Expect
  iterated exponentials. The claim this project defends is *verified mechanical extraction*,
  not sharp constants.

## Building

Lean **4.28.0** with Mathlib **v4.28.0** (`lake-manifest.json` pins the exact revisions).

```sh
lake exe cache get     # Mathlib oleans
lake build             # the library — about 70 s once Mathlib is in place
lake build Probes      # the probe/demonstration sweep, deliberately not in defaultTargets
lake build Metatheorems.Headline   # `#print axioms` of every headline declaration
```

`Metatheorems/Probes/` holds the measurement and demonstration files. Five of them are
imported by the umbrella (they are regression tests for the rewriting engine and the general
matrix form); the rest are covered only by the `Probes` target, so run it after any change to
`Term`'s or `Derivable`'s indices.

`Metatheorems/Headline.lean` prints the axiom dependencies of every headline result in one
place — the project's claims, machine-checked. `Metatheorems/Hilbert.lean` provides
`#hilbert foo`, which renders any `Derivable` value as a numbered Hilbert-style derivation in
Markdown and LaTeX.

## Module map

`docs/import-graph.svg` is the full picture (`docs/import-graph-probes.svg` includes the probe
layer). The tower, bottom to top:

| layer | modules |
|---|---|
| **Core syntax** | `TypeSystem` (finite types over `ι`, the hat map, degrees), `Term` (intrinsically typed, de Bruijn, primitive `lam`, structural `dist`), `Subst`, `Language` (formulas), `EqAtType` (equality at every type, base case defined as `d(s,t) =ℝ 0ℝ`), `Derivable` |
| **Semantics** | `Semantics` (`SpaceInterp` and the interpretation functions), `Soundness` |
| **Interpretations** | `Dialectica/{Defs,Lemmas,Syntactic}`, `NegTrans`, `NDTranslation`, `Dialectica/{Monotone,MonotoneND,MonotoneNDLeaves,MonotoneMemo,MonotoneSeq}` |
| **Majorizability** | `MajorizabilityRel` (the relation on semantic values), `Majorizability` (`AbstractMajorizability`, `ConstMajorants`, `termMajorizer`, `all_closed_terms_majorizable`) |
| **Metatheorems** | `Metatheorem` (shared parts: the bound, the extraction, the classical reduction), `SyntacticMetatheorem`, `MonotoneMetatheorem`, `MonotoneMetatheoremClassical` |
| **Numbers** | `Terms/{Arith,Rational,Real}` (definitions), `Arithmetic`, `RationalNumbers`, `RealNumbers/*`, `QVal`, `QValBridge{,Mul}`, `CodeReal{,Ops}`, `Rounding` |
| **Spaces** | `BaseEquality`, `MetricSpaces`, `MetricTransfer`, `WHyperbolic{,Lemmas}`, `CAT0`, `Normed`, `Instances` |
| **Proof mode** | `ProofMode/{Packing,Display,Pretty,Tactics,Rewrite,Induction,Arith,Linter}` |
| **Examples** | `MCTStatement`, `ProofMode/{MCT,MCTLazy}`, `RealMCTStatement`, `ProofMode/RealMCT` |

## Further reading

* [`docs/report/report.pdf`](docs/report/report.pdf) — a self-contained mathematical account of
  the formalization: the type system, the proof system, the interpretations, the
  majorizability layer, the metatheorems, the number tower, the space theories, and extraction.
* [`ARCHITECTURE.md`](ARCHITECTURE.md) — the *reasoning*: why the parametrisation is what it is,
  which alternatives were tried and rejected, and what each redesign cost. Read it before
  changing `Ty`, `Term`'s indices or `Derivable`'s indices.
* [`docs/RESULTS.md`](docs/RESULTS.md) — every bound extracted and every one not, with values,
  timings and refutation controls.
* [`docs/TACTICS.md`](docs/TACTICS.md) — reference for the proof mode.
* [`docs/REAL_MCT.md`](docs/REAL_MCT.md) — the ℝ-MCT derivation in detail.
* `Metatheorems/ProofMode/LADDER.md`, `PARITY.md` — how the proof mode was built and how its
  tactic set compares with the matching-logic proof mode it is modelled on.

## References

* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and Their Use in Mathematics*,
  Springer, 2008 — the source of the metatheorems (ch. 17), the monotone functional
  interpretation (ch. 9), and the representation of ℝ.
* `Metateorema-New3/` — the primary reference document this formalization follows; chapter 6 is
  the general metatheorem, and the metric-space instantiation is its companion section. (Not
  tracked in this repository; its PDF is the specification the development was written against.)

## Licence

Every source file carries an Apache 2.0 header. The `LICENSE` file the headers refer to is not
yet in the repository.
