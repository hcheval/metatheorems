# Majorizability.lean

## `AbstractMajorizability.selfMaj`

Introduced with the two-clause widening of `bezemMaj`: with two clauses a majorization at
an arrow type carries strictly more information than the pointwise statement, so
`arrow_intro` is no longer simply the converse of `app_compat`.

**Why this is a field and not a definition.** It is *not* that the notion cannot be
recovered — `Ty.hat` is idempotent and sends every base type to `.nat`, so
`maj ρ.hat` has exactly this type, and for `bezemMaj` it *is* this relation (the
`base i` clause is unreachable at a hat type, leaving `hatMaj`). What blocks defining
`selfMaj ρ := maj ρ.hat` is that `ρ.hat.hat = ρ.hat` holds only *propositionally* for a
variable `ρ`, so the definition would carry a transport and every use site would carry an
`Eq.rec`. Dependent-cast traffic is this project's measured pathology — `Eq.rec ↦ 60474`
in a stalling profile — so the notion is carried rather than derived. An earlier version
of this docstring said "there is no way to recover it", which is true of `maj` at `ρ` and
false at `ρ.hat`.

## `AbstractMajorizability.arrow_intro`

The second hypothesis is the self-majorization obligation; it is what the widening
costs, and it is what `all_terms_majorizable` has to thread through the `lam` case.

## `AbstractMajorizability.maxT_maj_left`

Forced by `and_contract`'s monotone majorant (Kohlenbach Thm 9.1, p. 143 case 1:
`t*_Y := λx y' y''. max(y', y'')`): the monotone functional interpretation replaces the
matrix-branching counter of contraction by a `max`, and "a `max` of majorants majorizes"
is not derivable from the other fields — the abstract relation has no `max`. The book
has it free because its `maj` is Howard's concrete relation; our abstraction must
state it. True of every `bezem*` instance (`maxT_bezemMaj_left`); promoted here from
`Probes/MonotoneSpike.lean`'s `MaxCompat`.

## `all_terms_majorizable`

### Why this does not contradict `Majorizability` being uninhabitable

This is the question the whole architecture turns on, so it is recorded here rather than
left to be rediscovered.

`Majorizability.majorizer` asks for a majorant of **every semantic value** `x : ⟦ρ⟧`, and
provably cannot exist: fix `f* = id` at `(ℕ→ℕ)→ℕ`; the functions it majorizes are
`S = {f | ∀n, f n ≤ n}`, and a single number `Φ* id` would have to bound `Φ` on all of `S`.
Take `Φ f :=` the least `n ≥ 1` with `f n = 0`, else `0`, and `f_k :=` the identity with a
zero planted at `k`: every `f_k ∈ S`, and `Φ (f_k) = k` is unbounded. So no majorant.

This lemma looks stronger — it even handles open terms — but it quantifies over a
**different domain**. `⟦ρ⟧` is the full set-theoretic type structure, uncountable, and
contains functionals like `Φ` above, which is discontinuous (hence not computable, hence
certainly not System T definable) and lives in Lean only via `Classical.dec`. `Term F Γ ρ`
is countable syntax, every member of which is a System T term. **Majorizability holds on
the definable part and fails on the whole**, and the environment generalisation does not
bridge that: "given majorants for the free variables, produce one for the term" is the
fundamental lemma of a logical relation over *syntax*, extending the induction through
binders, not the domain from syntax to semantics. Closed terms are the empty-environment
case, which is `all_closed_terms_majorizable`.

Stated pen-and-paper, with no de Bruijn indices: *for all valuations `σ*`, `σ` with
`σ*(x) ≽ σ(x)` at every free variable `x` of `t`, we have `⟦t⟧σ* ≽ ⟦t⟧σ`.* Kohlenbach
needs only the closed case because a combinatory language has no free variables; binders
force the generalisation, exactly as they do in any Tait/Girard-style argument.

**The consequence for the design**: a Dialectica realizer built by recursion on a
derivation *is* definable — but once its type is a Lean `Type`, that fact is erased, and
majorization needs it. Making the witness type an object-level `Ty ι`, so that realizers
are `Term`s, is exactly the act of keeping it. Note the converse fails — there are
majorizable functionals no term denotes — so the syntactic route preserves something
strictly stronger than needed; it is simply the property that survives by construction.

## The majorant as DATA (section before `ConstMajorants`)

`IsMajorizable` is a `Prop`, so `all_closed_terms_majorizable` proves a majorant *exists*
and then discards it. That is the wrong side of the `Prop`/`Type` line for this project: the
Dialectica layer deliberately uses `Subtype` rather than `∃` precisely because "`∃` in `Prop`
prevents computational extraction", and the majorizability layer then undoes that at the last
step — the bound `Φ` a metatheorem produces is provably there but cannot be computed.

Nothing about the mathematics forces this. `all_terms_majorizable`'s proof is structural on the
term and entirely constructive; the only genuinely `∃`-shaped inputs are
`AbstractMajorizability`'s six per-constant majorant fields. `ConstMajorants` is exactly those
six, as **data**, and `termMajorizer` is the same recursion written as a function.

The existing `Prop` API is untouched — `all_terms_majorizable` and `majorant_of_closed_term`
still say what they said, and the metatheorems still call them. This is an additional, sharper
route for callers who need the number rather than its existence.

## `termMajorizer` commutes with renaming, weakening, casting and substitution (section `Structural`)

These mirror `Term.interpret_rename_gen` / `interpret_weaken` / `interpret_subst0` in
`Semantics.lean` exactly, and they are what makes bound extraction *possible* rather than
merely well-defined.

Every `SRealizer` combinator in `Dialectica/Syntactic.lean` builds its `.val` by
`.app`/`.lam`/`Term.weaken`/`Term.castTy`-wrapping of its sub-realizers' `.val`s, never by
unfolding them. So with these lemmas `simp` pushes `termMajorizer` straight through the
wrapping to the sub-realizer's own majorant — `O(1)` per use-site, and in particular **never
forcing the wrapped term to whnf**. Without them the only route is delta-expansion, which is
the pathology in this file's sibling note and in "Build cost": a single `S_comb` is 82
derivation nodes but ≈4×10⁷ leaf-realizer copies.

Promoted from `Probes/BoundLemmasP2.lean` and `Probes/CounterSideProbe.lean`, where they were
written; they are general facts about `termMajorizer`, not probe scaffolding.

## `bezemAbstract`

`hbase : BaseMono base` is what the three `maxT_*` fields cost at a base
type: `maxT (.base i) a b = max a b`, and `base i (max a b) c` follows from `base i a c` only
if the relation is upward closed in its numeric argument. Every instance in the tree already
had it (`MetricModel.base_mono`), because `bezem_prec_maj` needed it for the same reason.

## The recursor (section before `recSem`)

`R` is the constant the two-clause relation was widened for. The document's induction
(`particular-cases-metric-spaces.tex:82–96`) gives the mixed statement at *equal* `n`; the
formal obligation is at `n* ≥ n`, and the gap is closed by `recMaj_hatMaj` (the majorant is
`hatMaj`-monotone in its numeric argument) composed with `bezemMaj_of_hatMaj`. Neither is
available from the one-clause relation.

## `bezem_prec_maj_at`

This is the obligation `METRIC_PLAN.md` §2.5 identified as unreachable with the one-clause
relation; with the self-majorization conjunct it goes through.

## Pure WE-HA^ω (section before `bezemAbstractEmpty`)

That is the setting the MCT bounds live in, and the reason `ι = Empty` rather than `ι = Unit`
is the right first target for evaluating an extracted bound: at `ι = Unit` the carrier is an
abstract metric space and no majorant can be computed even in principle.

## The majorant computes (section `ComputesDemo`)

These are the point of the whole `ConstMajorants` layer: before it, the majorant of a closed
term was `∃`-bound in a `Prop`, and the numbers below could not be written down at all. They
are kernel-checked, not `#eval`ed — the project bans `#eval` on composed interpretations.

`rfl` alone does **not** close them, and the reason is worth knowing: the goal has to unfold
`closedMajorizer → termMajorizer` *and* the projection chain
`(bezemAbstractEmpty si).N → (bezemAbstract …).N`, and bare `rfl` gets stuck on the latter.
`simp` with those four definitions named succeeds, because it uses `termMajorizer`'s equation
lemmas rather than raw whnf. So the recursion really does compute; it is the structure
projections that are opaque, which is the ordinary `Ty.interpret`-reducibility story again.

## the `example` "The numeral `3` majorizes itself"

The interpretation `si` is left as a variable — the majorant does not depend on it, which is
the point: `termMajorizer` consumes only `ConstMajorants`, so it reduces without knowing
anything about the model.

Stated with `ℕ` on the **left**, deliberately: `Ty.interpret X Ty.nat` is only *reducibly* `ℕ`,
so a numeral on the right has no `OfNat` instance to synthesise against and fails to elaborate.
Putting the numeral first fixes its type before unification reaches the stuck side. Same
reducibility trap as the `qval` bridge; see CLAUDE.md.
