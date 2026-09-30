# MetricSpaces.lean

## `MetricSpace.F`

**There are none.** The metric is no longer a function constant: every base type carries a
structural `Term.dist`, and equality at `X` is *defined* from it (`EqAtType.lean`). `F` must
still assign a type to the one index, so it gets `Ty.unit` — a constant carrying no
information, and one that `Term.unitI` already inhabits.

Leaving the slot free is the point: `F ()` is now available for the next structure in the
tower — W-hyperbolic's `W`, for instance — without needing the `ι`/`κ` split first.

## `d_X`

Now the **structural** `Term.dist ()`, not a function constant. Before this, the model had
two unrelated distances — `Term.func ()`, which the premises spoke about, and `Term.dist ()`,
which `eqAtType` used — interpreted by the same function but joined by no axiom.

## Equality at type X (section comment)

`MetricSpace.EqX` — DELETED. Equality at `X` is now `eqAtType (Ty.base ())`, defined in
the core as `d_X(s,t) =ℝ 0ℝ`, so a metric-space-specific restatement would be a synonym.
Facts about it live in `BaseEquality.lean`: `eqAtType_refl_base`, `eqAtType_sym_base`.

## `MetricSpace.Premises`

The three axioms above are no longer assumed: `Term.dist` is structural, and `d(x,x) =ℝ 0ℝ`,
`d(x,y) =ℝ d(y,x)`, `d(x,z) ≤ℝ d(x,y) +ℝ d(y,z)` are the constructors `Derivable.dist_self`,
`.dist_comm`, `.dist_tri`. They are kept above as *formulas* — the theorems just below show
each is derivable — because the document names them, and because a future theory may want
to state something relative to them.

An empty premise set is what makes `MetricSpace.premises_pu` and the `spremise` hypothesis
of both metatheorems vacuous.

## Lemma 17.8(4) (section doc before `roundR_smaj_of_le`)

`Rounding.lean` proves Lemma 17.8 parts (2),(3),(5),(6); part (4) was blocked there
because it mentions `s-maj₁`, which lives in `MajorizabilityRel.lean`. With the two-clause
`bezemMaj` it is a corollary of (2) and (3): at type `1 = nat →ₜ nat` the
relation unfolds to a *pair* of monotonicity statements, and (3) discharges the
self-majorization one outright.

## `roundR_smaj_of_le`

`_hx` is unused: only `0 ≤ y` is needed, since `roundR_le₁_of_le` rests on `Nat.floor_mono`,
which does not care about sign. The hypothesis is kept because the book states 17.8 for
`x, y ∈ [0,∞)` and callers will have it anyway.

## `MetricModel`

`MetricSpaceInterp` above takes `metric : carrier → carrier → (ℕ → ℕ)`, i.e. the metric
*already in code form*. That is the wrong starting point for majorization: to majorize `d_X`
one has to know the codes came from actual reals. Kohlenbach builds the model the other way
round — `[dX]_M := λx,y ∈ X.(d(x,y))◦` (p. 430) — so we do too.

Axioms are passed explicitly rather than via a `MetricSpace` instance, matching the project's
precedent for structures of this kind.

**The theory is a pseudometric; the model is a genuine metric space.** The two are
deliberately not the same, and the asymmetry is the point:

* the *theory*'s axioms are `dist_self`/`dist_comm`/`dist_tri` — reflexivity, symmetry,
  triangle — with **no separation**. Keeping the theory weak is what makes every derivation
  in it apply to more structures, so nothing here should ever add separation to `Derivable`;
* the *models* are the separated ones. `EqXInterp.extract` has to turn a Dialectica realizer
  of `d(x,y) =ℝ 0ℝ` into **Lean equality** `x = y` of the interpretations, and only
  separation gives that. A pseudometric model would satisfy every axiom of the theory and
  still fail `extract`.

So `d_eq_zero` below is a *model* condition with no object-level counterpart, exactly as
Kohlenbach's `A^ω[X,d]` is interpreted in genuine metric spaces while its axioms are the
pseudometric ones.

## `MetricModel.d_eq_zero`

This has **no object-level counterpart**: the theory deliberately stops at
reflexivity/symmetry/triangle, so that derivations in it apply to pseudometric
structures too. It is asked of the *model* because `EqXInterp.extract` must produce
Lean equality `x = y` from a realizer of `d(x,y) =ℝ 0ℝ`, and nothing weaker than
separation delivers that. See the structure docstring.

## `MetricModel.toMetricSpaceInterp`

`noncomputable` because `(·)◦` is `Nat.floor` on a Mathlib real. This does **not** violate the
project's "no `noncomputable` on the extraction path": that path is
`Derivable → NegTrans → Dialectica → Term`, and it stays computable. What is noncomputable is
the *model the extracted bound is interpreted in*, which is a set-theoretic object and was
never going to be executable.

## `MetricModel.dist_maj`

The self-majorization half is what the document flags separately — *"We also need to check
that `λx⁰,y⁰.(x+y)∘` majorizes itself"* — and it needs no metric input at all, only that
`m ≥ n → (m)∘ s-maj₁ (n)∘`.

The majorant is named (`distMajorant`) and the proof is `dist_maj_at`; `dist_maj` itself is
the `∃`-packaging `bezemAbstract` consumes. The split is what lets
`MetricModel.constMajorants` carry the witness as data.

## `MetricModel.abstractMajorizability`

Every obligation is now discharged:

* the structural conditions and `arrow_intro` — `bezemAbstract`, definitionally;
* `0`, `S` — `bezem_zero_maj` / `bezem_succ_maj`, for any base relation;
* `R` — `bezem_prec_maj`, which is what the two-clause widening bought;
* `0_X`, `d_X` — `zeroX_maj` / `func_maj` above, the only space-specific ones.

`N` is `0`: nothing here needs a threshold, since every majorant is uniform in the index.
That the `ℕ →` indexing does no work is discussed in CLAUDE.md.

## The majorants as DATA (section doc before `MetricModel.constMajorants`)

`abstractMajorizability` proves every constant *has* a majorant and `∃`-binds it, so a
bound extracted through it exists but cannot be evaluated. `constMajorants` below is the same
six majorants as data, which is what `termMajorizer`/`closedMajorizer` need to run.

This is possible at `ι = Unit` for the same reason it is at `ι = Empty`: `Ty.hat` sends every
base type to `nat`, so `Ty.interpret X ρ.hat` is built from `ℕ`/`unit`/`×`/`→` and never
mentions the carrier. The majorants are ℕ-valued whatever the space is. Concretely:

* `0`, `S`, `R`, `unitI`-typed `F ()` — the same values as `bezemConstMajorantsEmpty`,
  since none of them looks at the space;
* `d_X ↦ λn₁⁰n₂⁰.(n₁+n₂)∘` (`distMajorant`) — closed, no space dependence at all;
* `0_X ↦ n₀` — the **one** space-dependent number, `n₀ ≥ d(a, 0_X)`. It is a *parameter*:
  Kohlenbach's bounds are computable functionals of the majorants of their inputs, and a bound
  on `d(a, 0_X)` is an input. Nothing here computes it, and nothing needs to.

So the metric `ConstMajorants` is a function of `n₀`, and every majorant `closedMajorizer`
produces from it is a closed ℕ-expression in `n₀`.

## The majorants compute (section `ComputesDemo`)

Kernel-checked, not `#eval`ed (the project bans `#eval` on composed interpretations), and in
the same style as the two `ι = Empty` examples in `Majorizability.lean`: bare `rfl` gets stuck
on the `(M.abstractMajorizability).N → (bezemAbstract …).N` projection chain, so `simp` names
the definitions and uses `termMajorizer`'s equation lemmas.

## the `example` "`d_X(0_X, 0_X)`'s majorant"

This is the reading of "the metric metatheorem produces runnable bounds": a closed term at the
real type, involving the metric and the distinguished point, has a majorant that is a literal
once `n₀` is. Stated with the literal on the left for the same reducibility reason as the
`ι = Empty` examples.

## `EqXInterp` for a metric model — what each field costs (section doc)

`MetricModel.eqXInterp` below constructs the interface in full; this file has zero `sorry` and
both metric metatheorems are `sorryAx`-free. This note records *why* the construction is
shaped as it is, because the reasoning is what located the one blocker.

**The structural part is free, and is therefore not a field at all.**
`eqAtType (.base ()) s t` is `eq_R (d s t) 0ℝ`, a `Formula.all Ty.nat (Formula.eq0 _ _)`, so
`wTy` of it is `nat →ₜ unit` and `cTy` is `nat ×ₜ unit`. The witness type is `ℕ → Unit`: a
subsingleton, canonically inhabited, syntactically realized by `λn.⋆`. Nothing about the model
enters, so these live as ordinary definitions — `eqAtTypeBaseWitness`, `eqAtTypeBaseCounter`,
`eqAtTypeBaseWitness_subsingleton` (`Dialectica/Defs.lean`) and `eqAtTypeBaseRealizeTerm`
(`Dialectica/Syntactic.lean`) — and `realizeTerm_sound` collapses into `realize` (see
`eqAtTypeBase_realizeTerm_sound`). `EqXInterp` is left with four fields, all genuine model
facts. They were fields for two days after they stopped needing to be; see
`docs/notebook/MetricSpaces.md`.

**The semantic fields all need one thing, and it is not a metric fact.** `realize`, `extract`,
`dist_comm_holds` and `dist_tri_holds` each ask for `Formula.interpret M.si (eq_R …) env` or
the `le_R_pu` analogue — that is, for the *value* of the object-level decision term

    lt_Q_dec (abs_Q (sub_Q (cauchyfy f (n+1)) (cauchyfy g (n+1)))) (pow2neg_Q n)

in the standard model. Every ingredient of that term is a `Term`-level `prec` recursion
(`div2`, `inv_triag`, `lt_Q_dec`, …). `QVal.lean` supplies everything needed *about rationals*
— `qval : ℕ → ℚ`, with `qval_roundR`, `qval_roundR_dist_le`, `roundR_cauchy` — but connecting
`qval` to `Term.interpret` of `Term.rat_num`/`Term.lt_Q_dec` is a separate matter, and it is
the whole of what these fields need.

That connection is the **evaluation bridge** of `QValBridge.lean`, whose load-bearing instance
is

```lean
theorem interpret_lt_Q_dec (si : SpaceInterp X F) (a b : Term F Γ Ty.nat) (env) :
    Term.interpret si (Term.app2 Term.lt_Q_dec a b) env = 0
      ↔ Rounding.qval (Term.interpret si a env) < Rounding.qval (Term.interpret si b env)
```

together with its companions for `abs_Q`, `sub_Q`, `pow2neg_Q`, `add_Q` and `cauchyfy`. With
the bridge in hand each field is short: `dist_comm_holds` is `M.d_comm` (the two sides then
have **literally the same** interpretation, so `qval` reflexivity finishes it),
`dist_tri_holds` is `M.d_triangle` plus `Rounding.qval_roundR_dist_le`, and `realize` and
`extract` are `M.d_self` and `M.d_eq_zero` plus `Rounding.qval_roundR`.

**Soundness is not an alternative route to these fields — it is circular.** One might hope to
discharge `dist_comm_holds` from a soundness theorem
`Derivable … A → ∀ env, Formula.interpret si A env` applied to the object-level
`lt_Q_abs_sub_self`. But soundness's `dist_comm`/`dist_tri` cases are *exactly* these two
fields, which is precisely why `Soundness.lean` takes `hdist_comm`/`hdist_tri` as hypotheses.
`MetricModel.soundness`, 280 lines below, discharges them *from* the finished `eqXInterp`: the
dependency runs bridge → fields → soundness, never the reverse.

No `EqXInterp` field is weakened. See `ARCHITECTURE.md` §3.

## Semantic soundness for the metric model (section doc)

`Soundness.lean` proves soundness relative to five model facts, taken as section
`variable`s. None of them used to be dischargeable for `MetricModel` — `hsep` in particular
*is* `EqXInterp.extract`, and nothing in the project could build one. All five are available
now, and every one is a result proved above:

## `MetricModel.soundness`

This is the syntactic and semantic halves of the project meeting. Note it is *not* circular
with the metatheorems: `hsep` comes from `M.d_eq_zero` and the evaluation bridge, never from
soundness itself.

## `MetricModel.metric_metatheorem`

**`spremise` is gone.** `MetricSpace.Premises` is empty — the pseudometric axioms are
constructors of `Derivable`, not assumptions — so the premise-realizer obligation is vacuous
and is discharged inline. One of the three unconstructed hypotheses this theorem used to
carry has therefore ceased to exist rather than been satisfied.

**`eqxi` is gone too, as of the `dist_nonneg` session**: it is discharged internally with
`MetricModel.eqXInterp`. The principle behind that is still the one to keep: re-abstracting a
hypothesis with exactly one intended inhabitant is a `sorry` moved into a binder
(ARCHITECTURE.md §3).

`MetricModel.eqXInterp` is fully constructed, so this theorem is
`[propext, Classical.choice, Quot.sound]` — see the `#print axioms` block at the bottom of the
file, which is the authority. Treat prose in any source file as dated commentary and that
block as current: two copies of a stale `sorryAx` claim stood in this file for two days while
its own evidence contradicted them (`docs/notebook/MetricSpaces.md`).

A design note, kept because it is the shape of a mistake worth not repeating: `spremise`
was where `MetricModel`'s `d_self`/`d_comm`/`d_triangle` were *going* to be consumed. They
are consumed by `EqXInterp` now instead, on the semantic side, which is cheaper — the
obligation is real-number arithmetic in Mathlib `ℝ` rather than object-level ℝ codes.

## `MetricSpace.premises_pu`

The `ax_*_pu` theorems above are kept: they still record that the three *formulas* are Π⁰₁,
which is what makes the corresponding constructors' Dialectica witness types singletons.

## Equality at the base type (section comment)

Base-type equality is *defined* (`eqAtType (.base i) s t ≡ d_i(s,t) =ℝ 0ℝ`), so the metric
theory owes nothing on the equality side: reflexivity, symmetry and transitivity are
`Derivable.dist_self` and the theorems `BaseEquality.eqAtType_sym_base` /
`eqAtType_trans_base`, which hold in *every* `Derivable F al Premises` because the
pseudometric axioms are free constructors. `ARCHITECTURE.md` §1 and §8 explain why they
have to live above the ℝ layer, and `docs/notebook/MetricSpaces.md` records the
`AdmissibleEqX` structure this section used to be about.

## `MetricSpace.d_self_derivable`

Once `Term.dist` became structural this stopped needing a premise at all — it is the
`dist_self` constructor. Kept under its old name because it records where the metric-space
`=_X` reflexivity comes from.

One asymmetry is worth knowing, because it is what exposed the design problem this file is
arranged to avoid. Reflexivity is a *direct instance of an axiom*; symmetry and transitivity
are not — they need reasoning about `=ℝ`, hence the whole ℚ/ℝ tower, which in the old design
itself demanded the equality interface being defined. See ARCHITECTURE.md §1.

## `MetricSpace.admissibleEqX` (comment before `metric_metatheorem_classical`)

`MetricSpace.admissibleEqX` is gone, because the structure it inhabited is gone: `EqX` is no
longer a parameter and `AdmissibleEqX` was deleted with it. Each of its five fields survives
somewhere else, which is the whole point of the restructuring:

  `substF_nat` → `eqAtType_base_substF`  (a theorem, `EqAtType.lean`)
  `eqx_pu`     → `eqAtType_base_isPurelyUniversal`  (a theorem, `EqAtType.lean`)
  `eqx_refl`   → `Derivable.dist_self`  (a constructor; cf. `d_self_derivable` above)
  `eqx_sym`    → `BaseEquality.eqAtType_sym_base`   (`dist_comm` + symmetry of `eq_R`)
  `eqx_trans`  → `BaseEquality.eqAtType_trans_base` (`dist_tri` + transitivity of `eq_R`)

The last two are proved, above the ℝ layer, which is where they had to move to. See
ARCHITECTURE.md §8.

## `MetricModel.metric_metatheorem_classical`

This is the combination the document's Def. 6.0.1 route cannot deliver: it asks for a total
majorizer on every semantic value, and a metric model supplies only an
`AbstractMajorizability` (`MetricModel.abstractMajorizability`) — nor could it supply more,
since that assumption is unsatisfiable (`MajorizabilityRel.lean`'s closing section).

**`adm` is gone, not discharged.** This theorem used to take an `AdmissibleEqX` parameter,
and then (correctly) to discharge it with `MetricSpace.admissibleEqX` — which was `sorry`-ed,
so the theorem depended on `sorryAx`. The structure no longer exists: base-type equality is
defined rather than parameterised, and its equivalence properties are theorems
(`BaseEquality.lean`) or constructors (`Derivable.dist_self`/`dist_comm`/`dist_tri`).

`spremise` and `nts` are likewise gone: `MetricSpace.Premises` is empty, so both are vacuous
and are supplied inline.

**And `eqxi` is now discharged rather than assumed**, by `MetricModel.eqXInterp` — so all
three of the hypotheses this theorem once carried have gone.
