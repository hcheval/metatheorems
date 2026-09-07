# Notebook — `Metatheorems/MetricSpaces.lean`

Prose moved out of the module. See `docs/notebook/README.md`: nothing here is authoritative.

---

## 1. `EqXInterp` for a metric model — the diagnosis that identified the evaluation bridge

*Written while `MetricModel.eqXInterp` still had unfinished fields. All of them are now
constructed and the file has zero `sorry`; `EqXInterp` has four fields, all genuine model
facts. The diagnosis is kept because it is what identified `QValBridge.lean` as the single
blocker, and because its account of which field costs what is still accurate. Read every
present tense as past tense.*

> `EqXInterp` is the last hypothesis of the two metric metatheorems that nothing constructed.
>
> **The four structural fields are free.** `eqAtType (.base ()) s t` is `eq_R (d s t) 0ℝ`, a
> `Formula.all Ty.nat (Formula.eq0 _ _)`, so `wTy` of it is `nat →ₜ unit` and `cTy` is
> `nat ×ₜ unit`. The witness type is therefore `ℕ → Unit`: a subsingleton, canonically
> inhabited, and syntactically realized by `λn.⋆`. Nothing about the model enters.
>
> **The five semantic fields all stall on one missing piece, and it is not a metric fact.**
> `realize`, `extract`, `realizeTerm_sound`, `dist_comm_holds` and `dist_tri_holds` each ask
> for `Formula.interpret M.si (eq_R …) env` or the `le_R_pu` analogue — that is, for the
> *value* of the object-level real-number machinery at a concrete model.

Because nothing about the model enters the four structural fields, they **stopped being
fields**: they are `eqAtTypeBaseWitness`, `eqAtTypeBaseCounter` and
`eqAtTypeBaseWitness_subsingleton` in `Dialectica/Defs.lean`, and `eqAtTypeBaseRealizeTerm` in
`Dialectica/Syntactic.lean`; `realizeTerm_sound` collapsed into `realize` (see
`eqAtTypeBase_realizeTerm_sound`). The paragraph above is what should have retired them at the
moment base equality became defined, and it took two days to act on — one instance of the
recurring pattern where a binder outlives the refactor that made the thing it demands
constructible.

## 2. Two copies of a stale `sorryAx` claim

Both metric metatheorems carried a paragraph saying that `MetricModel.eqXInterp` has five
`sorry`-ed fields and that the theorem therefore depends on `sorryAx`. Both statements were
false from the moment the evaluation bridge closed those fields, and both were left standing
for two days while the file's own `#print axioms` block contradicted them. Both theorems are
`[propext, Classical.choice, Quot.sound]`.

The lesson is the reason the `#print axioms` block at the bottom of the module exists: it is
the authority, and prose in a source file is dated commentary.

## 3. `AdmissibleEqX` at the metric site

The module used to carry a block explaining what an `AdmissibleEqX` instance for the metric
`EqX` would need. The structure no longer exists — base-type equality is *defined*
(`eqAtType (.base i) s t ≡ d_i(s,t) =ℝ 0ℝ`) and the pseudometric axioms are constructors of
`Derivable` — so each of its five fields has gone somewhere else:

| field | where it went |
|---|---|
| `substF_nat` | `eqAtType_base_substF`, a theorem in `EqAtType.lean` |
| `eqx_pu` | `eqAtType_base_isPurelyUniversal`, a theorem in `EqAtType.lean` |
| `eqx_refl` | `Derivable.dist_self`, a constructor |
| `eqx_sym` | `BaseEquality.eqAtType_sym_base`, proved from `dist_comm` |
| `eqx_trans` | `BaseEquality.eqAtType_trans_base`, proved from `dist_tri` |

The last two were the interesting ones and the source of the whole redesign. `eqx_refl` is a
direct instance of an axiom; symmetry and transitivity are not — they need *reasoning about*
`=ℝ`, which pulls in the ℚ/ℝ tower, which in the old design itself took an `AdmissibleEqX`.
That circularity is what forced base equality to be defined rather than parametrised;
`ARCHITECTURE.md` §1 and §8 have the argument. Both are now ordinary theorems in
`BaseEquality.lean`, above the ℝ layer, which is the one stratification the design forces.

An earlier version of this material recorded the two as still owed, and as living as `sorry`s
in `Arithmetic.lean`. That has not been true since `BaseEquality.lean` was written; the build
has no `sorry` anywhere.

There was also a note that, before `AdmissibleEqX` gained its `Premises` parameter, its
equality fields quantified over *every* premise set including the empty one, and were
therefore **unsatisfiable** rather than merely unproved: with `d_X` an uninterpreted constant,
the interpretation `metric x y = fun _ => 1` refutes `d(t,t) =ℝ 0ℝ`. That finding is the
substance of `ARCHITECTURE.md` §2 and is why the project's standing check exists — *for each
field, can it be constructed from the other data with no model input? If yes it is a
definition, not a field.*
