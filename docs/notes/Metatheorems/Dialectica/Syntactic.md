# Dialectica/Syntactic.lean

## module header

`dialecticaWitness`/`dialecticaCounter` produce Lean *types*, so realizers are Lean values
with no syntax attached. That is what severs the bounding half of the metatheorem: the
majorization lemma (`all_closed_terms_majorizable`) applies to closed `Term`s, and a Lean
function is not one.

* `SRealizer A` — a realizer is a `Term` whose interpretation satisfies the (unchanged,
  semantic) Dialectica matrix **at every environment**. The uniformity is the point: a
  per-environment version does not survive the `forall_rule` case, which needs one term that
  works at every extension of the environment.

## Realizers as terms (comment before `SRealizer`'s section)

Realizers as terms: see `SRealizer` below. A per-environment variant
(`syntacticRealizerCtx`, taking `env` as a parameter and quantifying only over counters)
existed here and was deleted unused — nothing ever constructed or consumed
it. `SRealizer` quantifies over environments *inside* the subtype, which is what the
`forall_rule` case needs; the weaker form has no use site. The same asymmetry appears at
`realizer_of_pu` vs `realizer_of_pu_at`, where both forms are genuinely used.

## `extract_majorants`

**The root cause, fixed.** Both extracted functionals are closed terms, so
`all_closed_terms_majorizable` supplies their majorants outright — no per-derivation
obligation, and no total majorizer.

## `termMajorizer_castTy`

It sits here rather than there only because `Term.castTy` is defined in this file, downstream
of that one. Trivial, since `castTy` is a bare `cast`.

## `sForallRule`

Note the syntactic version needs no `∀ env` on the hypothesis: one term in context
`ρ :: Γ` already works at every environment, which is what the semantic version had to
simulate by quantifying.

## `eqAtTypeBaseRealizeTerm`

Was the `EqXInterp.realizeTerm` field. It became definable when base equality stopped being
an abstract predicate, and the field outlived that change — one instance of a recurring
pattern, a binder kept after a refactor made the thing it demanded constructible.

## `eqAtTypeBase_realizeTerm_sound`

Was the `EqXInterp.realizeTerm_sound` field, and it **collapses into `realize`**: the witness
type `ℕ → Unit` is a subsingleton, so the interpretation of `λn.⋆` is *forced* to equal the
witness of the semantic realizer `realize` already provides. No new model input.

## `srealizer_of_pu`

The syntactic counterpart of `realizer_of_pu` (`Dialectica/Defs.lean`), and the reason the
`EqXInterp` interface asks only for *model facts* about the distance: `wTy` of
`∀x₁…∀xₖ. A_qf` bottoms out in `Ty.unit` at every leaf, so the realizing term is a stack of
`Term.lam`s (and `Term.mkPair`s, at `∧`) over `Term.unitI` — which is exactly
`Term.defaultOf`, i.e. `defaultWTerm`. All the content is `htrue`, the formula's truth in
the model, and `dialecticaMatrix_iff_interp_qf` turns it into the matrix *at every counter*.

Three cases, mirroring `isPurelyUniversal`: `∀` (a `lam`), `∧` (a `mkPair`, the clause
products in `Ty` make necessary), and the quantifier-free core.

## `wt*` — the term half of every rule combinator (section `WitnessTerms`)

This is the `ConstMajorants` pattern one layer down: the `Prop`/model-parameterized API is
untouched, the computational one is added beside it.

## `srealizer_of_pu_val`

`wTy` of `∀x₁…∀xₖ.A_qf` bottoms out in `Ty.unit`, and `srealizer_of_pu`'s `lam`/`mkPair`
stack is exactly what `Term.defaultOf` builds there. So its payload carries no information at
all — which is why `extractTerm` needs no model input for any of `srealizer_of_pu`'s
clients.

## `syntactic_soundness`

Because the witness is a term, `all_closed_terms_majorizable` applies to it — which is what
the semantic version could not offer.

## `extractTerm`

Why this matters: every model in the project routes through Mathlib `ℝ`, so `si` is
`noncomputable` and `#eval` on anything mentioning it is impossible. `extractTerm` makes the
realizing term of a derivation **at a space** evaluable — see
`Probes/ExtractTermDemo.lean`.
