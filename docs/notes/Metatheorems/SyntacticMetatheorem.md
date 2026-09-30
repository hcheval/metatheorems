# SyntacticMetatheorem.lean

## `syntactic_general_metatheorem_at`

This is the same `Prop`→`Type` move the design table records for the Dialectica realizer
("Subtype, not `∃` — lives in `Type`, witness extractable via `.val`"), and that
`ConstMajorants`/`termMajorizer`/`closedMajorizer` made for majorizability.

**Why the extra hypothesis** (`ConstMajorants am`, where the `∃` version needs only
`AbstractMajorizability`). That is forced, not stylistic: `majorant_of_closed_term` returns a
`Prop`-existential, which cannot be eliminated into a `Type`-valued goal, so the majorants must
come from `closedMajorizer` instead. `ConstMajorants` is inhabited where it matters —
`bezemConstMajorantsEmpty` at `ι = Empty`, `MetricModel.constMajorants n₀` for metric spaces.

**What it does not do.** It does not make Φ *reduce*; the bound is only as computable as
`syntactic_soundness` is reducible on the given derivation, which for a proof-mode derivation
is what the `Probes/SeqMpBoundProbe.lean` line of work is about. What it provides is a
statement in which a computed bound can be *put*.

## `syntactic_general_metatheorem`

**The point of the whole branch.**

This is what replaced the document's Def. 6.0.1 route, which assumed a *total* majorizer on
every semantic value — an assumption that is not satisfiable (`MajorizabilityRel.lean`'s
closing section). Getting the majorants from the syntax instead is the whole content of the
`syntactic-witnesses` design.

## `syntactic_general_metatheorem_classical`

The total-majorizer version of this statement was not merely
harder to apply but impossible: that field is unsatisfiable over the full set-theoretic type
structure, which is why the metric model could never have used it
(`MajorizabilityRel.lean`'s closing section).

The default challenge in step 3 is legitimate for the same reason the semantic version's is:
`B₀' →ᶠ C₀'` is quantifier-free and ∨-free, so `dialecticaMatrix_iff_interpFormula` reduces
its matrix to the formula's interpretation **for every** counter. That is precisely the
property the unprenexified route lacks.

## `prenexRealizer`

It exists as a `def` rather than as a `let` inside a proof for two reasons. First, CLAUDE.md
hard rule 4: as a `let`-value an enormous realizer makes every later defeq check try to
`whnf` it. Second, `syntactic_general_metatheorem_classical_at` below must mention the
extracted terms in its *value* component, which a tactic-mode `obtain` cannot reach.

## `extraction_of_prenex_realizer`

**`w` must be a variable, not the applied `prenexRealizer`.** This is the whole reason the
lemma is stated separately rather than inlined into `syntactic_extraction_classical` below.
`syntactic_general_metatheorem_classical` gets its realizer from `obtain ⟨w, hw⟩`, so `w` is
an opaque local and `Term.interpret si w` is stuck; written directly against
`(prenexRealizer …).val` the `simp only [dialecticaMatrix]` step tries to reduce the realizer
itself and the elaboration dies at a `whnf` heartbeat timeout with no error to point at. This
is the same failure mode as binding a large realizer with `let` instead of `obtain`: an
enormous term in a position where every later defeq check tries to reduce it.

## `syntactic_general_metatheorem_classical_at`

The reason it takes a `ConstMajorants`: `majorant_of_closed_term` returns a `Prop`-existential,
which cannot be eliminated into a `Type`-valued goal, so the majorants must come from
`closedMajorizer`.

CLAUDE.md's Track D1 recorded this entry point as the missing half of the `_at` work;
`Probes/LemBoundDemo.lean` is its first client, and the first extraction in the project from a
derivation containing `Derivable.lem`.

## The metatheorem with general matrices — Kohlenbach, Theorem 17.52 (section `GeneralMatrices`)

Kohlenbach's statement (Applied Proof Theory, Thm. 17.52, p. 403) reads: *let `B∀(x,u)`,
resp. `C∃(x,v)`, be ∀- resp. ∃-formulas … from a proof of `∀x^ρ (∀u⁰ B∀(x,u) → ∃v⁰ C∃(x,v))`
one can extract `Φ` such that `∀u ≤ Φ(x*) B∀(x,u) → ∃v ≤ Φ(x*) C∃(x,v)`.* The reference
document transcribes `B∀` as `∀b̲ B₀` and `C∃` as `∃c̲ C₀` with `B₀`, `C₀` quantifier-free.

`syntactic_general_metatheorem` above demands `B₀.isQF` and `C₀.isQF` — i.e. `b̲`, `c̲`
empty — which is a genuine restriction against both sources (`ARCHITECTURE.md` §13).

**Single quantifier block = the book's tuple, because `Ty` has products.** Kohlenbach needs
a tuple `b̲ = b₁,…,bₙ` only because his type system has no product types. Ours does (`Ty.prod`,
since the `syntactic-witnesses` merge), and `Formula.all` binds a variable of *any*
`ρ : Ty ι`, so `∀b₁^ρ₁ … ∀bₙ^ρₙ B₀` is `∀b^(ρ₁ ×ₜ … ×ₜ ρₙ) B₀[fst/snd projections]`. So a
`∀b^σ B₀` with `σ` arbitrary — `syntactic_general_metatheorem_block` below — is *equivalent
to* 17.52's `∀b̲ B₀`, not a weaker special case; and `isPurelyUniversal` allows any nesting
anyway. `degree (.prod ρ τ) = max ρ.degree τ.degree`, so products never raise the type
degree. Only `u` and `v` stay at `Ty.nat`: `Φ` bounds them numerically, exactly as in 17.52.

**What replaced `dialecticaMatrix_iff_interpFormula`.** That lemma says a QF ∨-free matrix
equals its interpretation *at every witness and counter*; it is what let the old extraction
ignore the realizer's challenge. For a ∀-formula that is false — the matrix at counter
`(b, …)` is the *instance* at `b`, not the ∀ — so it is replaced by the pair
`dialecticaMatrix_of_interp_pu` (a true ∀-formula has a true matrix at every witness and
counter) and `interp_of_dialecticaMatrix_pe` (an ∃-formula whose matrix holds is true), in
`Dialectica/Defs.lean`. Nothing else in the pipeline changed: `extractUTerm`/`extractVTerm`,
`syntactic_soundness`, `closedMajorizer` and `metatheorem_core_of_majorants` never looked at
the matrices' shape.

**Prenexification was not needed for the extended route.** The book and the document expand
`∀u∀b̲ B₀ → ∃v∃c̲ C₀` to the prenex `∃u,v,b̲,c̲ (B₀ → C₀)` because they interpret a *classical*
proof. For an `Allowed.extended` input, Dialectica interprets `∀u B∀ → ∃v C∃` directly: the
realizer's counter component already returns `(u, (b, …))`, and the witness component
`(v, (c, …))`. The classical route (`syntactic_general_metatheorem_classical_gen`) does go
through `classical_to_prenex_extended_gen`, where the only new work is restoring `B'` from
`B'ₙₜ` after the negative translation.
