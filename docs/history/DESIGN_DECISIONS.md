# Design decisions

Decisions that are open, or settled in a way with consequences worth recording. Not an idea
list — see `SPINOFFS.md` for those. One section per decision.

| # | Decision | Status |
|---|---|---|
| 1 | The majorizability hypothesis | **open** |
| 2 | Meta-level Dialectica (approach b) | settled, now under pressure from 1 |
| 3 | `Derivable` has no assumption context | settled by default; constrains proof mode |
| 4 | ∨-free restriction on `qfer` | settled; may be removable |
| 5 | Which majorizability development ships | **open** |
| 6 | ℚ/ℝ: derive inside the system, or assume as PU premises | frozen |

## Target demo (for reference)

1. **Proof mode** — Iris-style tactics building `Derivable` terms. Context is a *display* over the
   antecedents of a nested implication, so no deduction theorem is needed (see decision 3).
   Parallelisable.
2. **Extraction pipeline** — `Derivable` proof → Lean bound, `#eval`-able.
3. **A formalized theorem** — MCT the target; abstract spaces desirable.
4. **Map real Lean proofs into the proof mode** — stretch.

## Open troubles

**T1. Nothing is instantiated.** No `SpaceInterp`, `EqXInterp`, `AdmissibleEqX`, `Premises` or
`premise_realizer` exists anywhere, even at `ι = Empty` — one `instance` in the whole repo, a
`Decidable`. The pipeline cannot run because its arguments do not exist. This is prior to, and
larger than, the real-number question.

**T2. Shape mismatch.** `general_metatheorem` takes one `ρ` parameter plus one ℕ on each side
(`B₀ C₀ : Formula F [Ty.nat, ρ]`). MCT needs sequence, counterfunction and bound; `Ty` has no
products. Either fit the example — fix `g` and `K` as closed terms, quantify over the sequence,
so `ρ = nat →ₜ nat` and `Φ` depends on a majorant of `a` (the constant `K`) — or widen to
`Formula F (Ty.nat :: Γ)` with `Φ : Ctx.interpret X (Γ.map Ty.hat) → Nat`. The latter should not
disturb the proof, since `maj`/`majorizer` are used pointwise.

**T3. Abstract spaces are blocked on reals.** `AdmissibleEqX` needs `EqX`, which for metric spaces
is `d(x,y) =_ℝ 0`, which needs the frozen `RealNumbers.lean`. An **ℕ-valued distance** sidesteps
this entirely and still exercises `ι`, `F`, `EqX` and `Premises` — a genuine second instance,
just not the metric spaces of the literature. Say the restriction out loud.

**T4. Which metatheorem the demo can use.** `general_metatheorem` (extended system) is proved;
`general_metatheorem_classical` still carries the sorry at
[Metatheorem.lean:340](Metatheorems/Metatheorem.lean#L340). If the input derivation uses LEM, the
demo lands on the unproved one. `qf_lem` supplies case analysis on QF formulas without LEM, so
MCT may not need it — **check early**, it decides which theorem the demo can be built on.

**T5. Computability of the demo.** `#eval Φ` requires the whole extraction path to stay
computable. It currently is. The majorizability refactor could break it if `majorizer` is defined
by `Classical.choice`; running max is computable, so keep it that way.

**T6. Sequencing.** The majorizability refactor (decision 1) is upstream of demo items 2, 3 and 4.
If `Metatheorem.lean`'s proof fights the narrower structure, everything slips together. Do it
first.

**T7. Cost of item 4 is not only tokens.** Mapping Lean proofs into the rule calculus needs a
specified target fragment first. Known obstructions: `Quot.sound` (mathlib's `Real` is a
quotient; `Rat` is a structure and is safe), `Classical.choice`, `WellFounded.fix`, and `Eq.mpr`
motive soup from `rw`/`simp`. Attempt only against proofs written for the purpose, not mathlib.

---

# 1. The majorizability hypothesis

**Status:** open. Affects `Metatheorem.lean`, `StrongMajorizability.lean`, `Majorizability.lean`.

## The problem

`Majorizability.majorizer` ([StrongMajorizability.lean:47](Metatheorems/StrongMajorizability.lean#L47))
is **total**: a majorant for every semantic value at every type, with `majorizer_maj`
([:49](Metatheorems/StrongMajorizability.lean#L49)) requiring it to majorize at every `ρ`.

Verified facts:

- Under the intended relation (`maj .nat` = `≥`, Bezem's `≤*`), the full set-theoretic structure
  `S^ω` fails this at degree 2. Counterexample: `f* = λn.1`; `F f = least n with f n = 1` is
  unbounded over the 0/1 sequences pointwise below `f*`, so no `F*(f*)` exists.
- The structure does **not** force that relation — `maj_le`
  ([:40](Metatheorems/StrongMajorizability.lean#L40)) only gives `maj .nat ⊆ (· ≥ ·)`. So at
  `ι = Empty` it is satisfiable degenerately by `maj ρ x* x := (x* = x)`, `majorizer := id`.
  That instance makes the hypothesis at [Metatheorem.lean:88](Metatheorems/Metatheorem.lean#L88)
  collapse to `x_star = x`, so `Φ` depends on `x` and uniformity is lost.
- Accurate statement: **not satisfiable non-vacuously in `S^ω`.** Not "has no model".
- Nothing in the repo is instantiated — one `instance` exists repo-wide, a `Decidable`.

## Why it arose

Kohlenbach never needs total majorizability. He majorizes the extracted **closed term**, by
induction on term syntax. That lemma is proved here — `all_closed_terms_majorizable`
([Majorizability.lean:160](Metatheorems/Majorizability.lean#L160)) — and is **unused**, as is
`AbstractMajorizability` (the paper's Def 6.0.1, with the ℕ-indexed threshold).

It is unusable by construction: meta-level Dialectica ("approach b") extracts `U`, `V` as Lean
functionals ([Metatheorem.lean:107-110](Metatheorems/Metatheorem.lean#L107-L110)), not terms, so
there is no term to majorize and the majorant must come from a semantic hypothesis instead.

Corroborating symptom: the paper's statement (and the CiE 2025 slide) carries an `N` with
"for all `n ≥ N`", from `AbstractMajorizability`'s threshold form. `Metatheorem.lean` has no `N`,
because a total majorizer makes it unnecessary. The deviation is visible in the statement.

`M^ω` is **not** the fix. It is Bezem's model for bar recursion; absent bar recursion, `S^ω`
models `T` and suffices — precisely because only terms are ever majorized.

## Options

| | Change | Cost | Effect |
|---|---|---|---|
| 1 | Restrict `majorizer` to `ρ →ₜ nat` and `maj` to `ρ`; require `ρ` degree ≤ 1 | days | satisfiable (running max), theorem narrows, must be stated |
| 2 | Add `∃ t : Term F [] ρ, ⟦t⟧ si = w` to the realizer subtype | weeks, contained | keeps approach (b); `all_closed_terms_majorizable` applies; deletes `StrongMajorizability`; restores `N` |
| 3 | Switch to the **monotone functional interpretation** | new interpretation, ~scale of `Dialectica/Lemmas.lean` | soundness extracts a majorant directly, so no majorization step to lose; only per-constant facts needed, i.e. `AbstractMajorizability` |
| 4 | Interpret arrows as hereditarily majorizable functionals | touches `Semantics.lean` | total majorizer exists by construction |

Option 2 works because a majorant exists for any functional that is definable or continuous —
the set of `f` below a given `f*` is compact. Extraction never produces a pathological
functional; (2) merely records that.

Option 3 is the principled one: MFI exists to fuse "extract exact realizer" with "majorize it".
On paper the two-step route is harmless because the term is present; a formalization that erases
the term makes the fusion **necessary** rather than convenient. Expected to *shrink* the
soundness clauses (no exact counter-transformer, no Boolean tag at `∨` — which should also remove
the ∨-free restriction on `qfer`), at the price of a monotonicity side condition per clause.

## Not yet checked

- How much of `Dialectica/Lemmas.lean` survives a switch to MFI. Cheap probe: write out what the
  implication and contraction clauses would need under MFI.
- Whether the base-type clause (`n maj x` iff `n ≥ ‖x‖`, `Ty.hat (.base i) = .nat`) forces
  `maj .nat` to be `≥` once `ι` is nonempty — if so, the degenerate escape exists only at
  `ι = Empty` and option 3 in the confirm/reject list becomes "not satisfiable at all".

## Consequence for the talk

The defensible line: the syntactic majorization lemma is proved and inapplicable by construction,
and the semantic replacement is either vacuous or unsatisfiable in `S^ω`. Do **not** present
"`S^ω` is not strongly majorizable" as a discovery — it is standard. The finding is the
interaction with the meta-level extraction choice.

---

# 2. Meta-level Dialectica (approach b)

Settled early (see `CLAUDE.md`): witnesses are Lean types and values, not object-level terms.
Bought computable, directly inspectable witnesses. Cost, only now visible: extraction yields a
functional rather than a term, which severs the syntactic majorization route and forces the
hypothesis in decision 1. Options 2 and 3 there both revisit this.

# 3. `Derivable` has no assumption context

`Derivable F EqX allowed Premises Γ A` derives closed judgments; assumptions enter only via
`Premises`. Consequence: no deduction theorem question arises, but also no `intro`.

For an Iris-style proof mode this is fine — the context is a *display* over the antecedents of a
nested implication, so `intro` peels an antecedent rather than discharging an assumption, and
`.exportation` / `.importation` / `.syllogism` do the work. Adding a real assumption context
would raise the DT question, and `qfer` is an ungated constructor, so that route is not free.

# 4. ∨-free restriction on `qfer`

`Derivable.qfer` requires `isVFree` as well as `isQF` ([Derivable.lean:163](Metatheorems/Derivable.lean#L163)),
because the Dialectica counter needs `Subsingleton`. The document's QF-ER requires only QF.
Under MFI (decision 1, option 3) disjunction takes a max instead of carrying a Boolean tag, which
should remove the need for the restriction. Check when evaluating that option.

# 5. Which majorizability development ships

`AbstractMajorizability` (`Majorizability.lean`) is the paper's Def 6.0.1 — per-constant, with the
ℕ-indexed threshold — fully proved and referenced nowhere outside its own file.
`Majorizability` (`StrongMajorizability.lean`) is the total-majorizer version and is what
`Metatheorem.lean` actually takes. The paper's one is the orphan. Decide which is the real one
before publishing anything about the formalization's generality; it is the first question a
careful reader will ask.

# 6. ℚ/ℝ: derive inside the system, or assume as PU premises

`RationalNumbers.lean` (7746 lines, 9 sorries) and `RealNumbers.lean` (19 sorries) are frozen.
The alternative is to state the field and order laws as purely universal object formulas and
discharge them semantically via `premise_realizer` — legitimate, since the metatheorem admits any
true PU premise, and `dialecticaMatrix_iff_interpFormula` already collapses the obligation to
`Formula.interpret` for QF ∨-free formulas. Cost: the laws become assumptions rather than
derivations, recoverable one at a time. See `SPINOFFS.md` §B.

## 6b. What Kohlenbach's representation actually buys and costs (§4.1 of the book)

**ℚ.** Rationals are codes `j(n,m)` via Cantor pairing, with `=_Q` decidable (cross
multiplication), `+_Q`, `·_Q`, `<_Q`, `≤_Q` primitive recursive. `(N, +_Q, ·_Q, 0_Q, 1_Q, <_Q)` is
an **ordered field, provable in WE-HA^ω**. A canonical representative is available by bounded
search (`min m ≤ n [n =_Q m]`) but general representatives are used, and are unavoidable for
reals.

**ℝ.** Reals are `f : ℕ → ℕ` (sequences of rational codes) with the *fixed* Cauchy modulus
`2^(-n)`. Three consequences worth having explicitly:

1. **Modulated completeness is provable.** A sequence with a Cauchy modulus has a limit, and the
   limit is given by an **explicit term**. So the earlier note that "you only get the ring
   fragment, no completeness" applies to Ferreira's *abstract* type (§6a), **not** to the
   representation. Here you get an Archimedean ordered field *plus* modulated Cauchy
   completeness, all inside WE-HA^ω — most of what analysis needs.

2. **The `f ↦ f̂` construction keeps quantifiers clean.** A primitive recursive functional forces
   any type-1 function to satisfy the Cauchy condition, so "∀ reals" is literally "∀ f¹" with no
   relativising premise. Without it, every statement about reals would carry
   `f represents a real →`, pushing it out of the shape the metatheorem accepts. This is a real
   design constraint satisfied for free by the representation.

3. **The cost, and we had not noted it: the real relations are not quantifier-free.**
   `=_R` and `≤_R` are Π⁰₁; `<_R` is Σ⁰₁. So **a matrix mentioning real equality or inequality is
   not QF**, and a real-valued statement does not directly fit the metatheorem's requirement.
   The way out is that `f̂(k)` is a rational `2^(-k)`-approximation, so the matrix is reduced to a
   decidable statement about rational codes. This is exactly why Kohlenbach's Prop. 2.26 is stated
   with `<_Q` on rationals rather than `<_R`.

**Practical consequence for the first input theorem.** A real-valued statement needs the
rational-approximation layer as an extra step; a ℚ- or ℕ-valued one has decidable atoms and does
not. Another reason the first input should not be over ℝ.

## 6a. Ferreira's abstract type of the reals — the principled version of this

F. Ferreira, *The abstract type of the real numbers*, Archive for Mathematical Logic (2021);
`ferreira2021.pdf` in this repo.

Rather than representing reals by rapidly converging Cauchy sequences of rationals, take **`R` as
a primitive ground type** with a **purely universal axiomatisation**: the ordered-ring axioms
(`0, 1, +, −, ·, ≤, =`) plus a function symbol `inv : N → R` governed by the universal axiom
`∀n((n+1)·inv n = 1)`, which embeds the rationals. Deliberately **no field axiom** — "every
nonzero element has an inverse" is not universal.

The real-number equality and order are then *defined* on top of the primitive ones:
`x ≤_ℝ y := ∀n(x ≤ y + 1/(n+1))`, `x =_ℝ y := ∀n(|x−y| ≤ 1/(n+1))`, `x <_ℝ y := ∃n(x + 1/(n+1) ≤ y)`.
Primitive `=`/`≤` stay quantifier-free; the ℝ-versions do not.

**Why it fits this repo directly.** `ι` gains an index for `R`; the ring axioms are universal, so
`isPurelyUniversal` holds and they are legal `Premises`; `=_ℝ` is `∀n` over a QF body, so
`AdmissibleEqX.eqx_pu` is satisfied. `RationalNumbers.lean` and `RealNumbers.lean` leave the
critical path entirely.

**Metric spaces become reachable** (his Comment I): three ground types `N`, `X`, `R` with
`d : X → X → R` interpreted directly, no choice of representatives. Expressible as-is via `ι`/`F`.

**Caveats to record, not discover.**
- The construction is designed to work *in tandem with the bounded functional interpretation*.
  Completeness (his Proposition 1) leans on the characteristic principles (C1a), (C1b), (C2) —
  and (C1b) is bounded König's lemma. Under Dialectica/MFI you get the Archimedean ordered ring
  for free but **not** completeness. Enough for stating metric-space axioms and for a first
  instantiation; not enough for doing analysis inside the system.
- (C2), `∀x∃m(|x| ≤ m)`, is ∀∃ rather than universal — an added principle, not a premise.
- His Comment II: under the BFI reading `R` may be interpreted by ℚ; BFI "completes the rationals
  with ideal elements". Relevant if the interpretation choice is ever revisited (decision 1).
- His Comment III is a clean citation for the extensionality point: `x =_ℝ y → ∀Φ(Φx =_ℝ Φy)` is
  not derivable, which he frames as a discovered limitation of extracting quantitative content
  rather than a defect of the method. Relates to `qfer` and decision 4.
