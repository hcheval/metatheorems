# Instances.lean

## module header

Everything above this file is quantified over `MetricModel`, `WHyperbolicModel`, `CAT0Model`
or `NormedModel` **as variables**. Until this file, the project constructed **no inhabitant of
any of them** — so every space metatheorem was a statement about a class not known to be
non-empty. That is not a hypothetical worry here: the total-majorizer `Majorizability` had
provably no instances and was deleted for it (`MajorizabilityRel.lean`), and
`AdmissibleEqX.eqx_refl` was outright *refutable* while looking like ordinary unfinished
work. Both were found by trying to build the thing.

The nontriviality side condition is confined to `NormedModel`, and it is not bookkeeping:
`Normed.ax_norm_one` (Kohlenbach's (9), `‖1_X‖ =ℝ 1ℝ`) is *false* in the zero space.
`WHyperbolicModel` and `CAT0Model` are over `WHyperbolic.F`, a different signature with no
`1_X`, so `WHyperbolicModel.ofNormed` and `CAT0Model.ofInner` are untouched by it and still
take only the two/three Mathlib instances.

`NormedModel` is not an imitation of Mathlib's notion — it is a bundling of it (`E : Type`
plus the three instance fields, no axioms of its own), so `ofNormed` is essentially the
identity and the instances come straight back out.

### Two mechanical hazards, both paid for here

* **`WHyperbolicModel.ofNormed` must be an `abbrev`.** As a `def`, `(ofNormed E).carrier` does
  not reduce to `E` at elaboration time and every subsequent `•`/`−` fails instance synthesis
  with `failed to synthesize HSMul ℝ (ofNormed E).carrier`. Same reason
  `NormedModel.toMetricModel` is an `abbrev`.
* **Every Mathlib `‖·‖` in this file is parenthesised.** The project's `‖t‖ si env` notation
  takes *three* arguments, so an unparenthesised `‖a‖ * ‖a‖` tries to consume the `*` as `si`.
  This is a live hazard in any file mixing the object notation with Mathlib norms.

The four W-axiom identities are all discharged by Mathlib's `module` tactic; hand-rolled
`abel` versions of them do **not** go through.

### Scope

All three space theories are covered. Normed spaces were the last to join: until
`NormedModel.axiomsHold` was proved, `ofNormed` gave a model but the normed metatheorem still
carried an `AxiomsHold` binder, so it was inhabited-but-not-applicable. No such gap remains,
and no `AxiomsHold` binder survives anywhere in the tower.

`ℝ` witnesses all of it — and `Nontrivial ℝ` is an instance, so the added binder costs the
examples below nothing.

## `NormedModel.ofNormed`

`[Nontrivial E]` is what interprets `1_X` and validates Kohlenbach's axiom (9),
`‖1_X‖ =ℝ 1ℝ` — false in the zero space, so the hypothesis is not removable. Carrying it as a
*typeclass* rather than as an explicit unit vector is what keeps this the identity: the
normalisation `‖v‖⁻¹ • v` happens once, inside `NormedModel.unitVec`, not at every
instantiation site.
