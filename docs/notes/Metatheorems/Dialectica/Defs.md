# Dialectica/Defs.lean

## `wTy`

Making this a `Ty ι` rather than a Lean `Type` is what lets a realizer be a `Term`, and
hence be majorized by `all_closed_terms_majorizable`.

## `dialecticaWitness`

Definitionally the familiar clause-by-clause definition — `Unit`, products, function
spaces — so nothing that used the old definition changes.

## `dialecticaMatrix_decidable`

Defined by structural recursion on `A` in term mode (rather than
`induction A generalizing`) because the context `Γ` is indexed into
`A`'s type and changes in the `all`/`ex` arms.

## `dialecticaMatrix_renameF`

We prove this by mutual induction with the type invariance, avoiding
separate cast decomposition. The proof uses the fact that
`dialecticaWitness`/`dialecticaCounter`/`dialecticaMatrix` all unfold
structurally on `A.renameF r` and `A` in the same way.

## `dialecticaMatrix_iff_interp_qf`

This duplicates `dialecticaMatrix_iff_interpFormula` (`MetatheoremPrereqs.lean`), which cannot
be used here: that file sits far above this one. When the two are ever unified, this is the
one to keep — it is the lower of the two.

## `realizer_of_pu`

The witness type of such a formula is a *singleton*: `wTy` of `∀x₁…∀xₖ. A_qf` is
`ρ₁ →ₜ … →ₜ ρₖ →ₜ unit`-shaped, everything bottoming out in `Ty.unit` (or products of
such). So a realizer carries no information, and all the content is that the formula holds
in the model — which is exactly the hypothesis `htrue`.

The recursion has three cases: `∀` (a function), `∧` (a pair — `isPurelyUniversal` is
closed under `∧`, which is needed because `eqAtType` at a product type is a conjunction),
and the quantifier-free core, where
`dialecticaMatrix_iff_interp_qf` discharges the matrix *for every counter*.

## `realizer_of_pu_at`

`realizer_of_pu` asks for `∀ env, Formula.interpret si B env`, but the consumers that matter —
`EqXInterp.realize` and `realizeTerm_sound` — have the formula only at the one `env` they were
handed. That is enough: the `∀` case only ever needs truth at *extensions* of the given
environment, which `htrue v` supplies, and the quantifier-free cases use `env` alone. The two
definitions are otherwise identical.

## `interp_of_realizer_pu`

Needed by `EqXInterp.extract`, which has to turn a realizer of `s =_X t` back into a semantic
statement about the distance.  The `∀` case reads the realizer componentwise — the witness of
`.all ρ A` is a function and its counter a dependent pair, so `⟨r.val v, fun y => r.property
⟨v, y⟩⟩` realizes `A` at `(v, env)`.  The quantifier-free cases just feed the default counter
to `dialecticaMatrix_iff_interp_qf`, which reduces the matrix *for every* counter.

## `dialecticaMatrix_of_interp_pu`

Sharper than `realizer_of_pu_at`, which only produces *some* witness: the witness
type of a ∀-formula is built from `unit`, `×ₜ` and `→ₜ unit`-shaped arrows, so no witness
carries information and the matrix at counter `(b, y)` is just the instance of the body at
`b`, which `htrue` supplies.

This is the lemma that lets the metatheorem take a premise matrix `B∀` that is a ∀-formula
rather than quantifier-free (Kohlenbach 17.52): the realizer's `U`-component hands back a
counter `(u, (b, …))`, and this lemma turns the *assumed* truth of `∀b B₀(x,u,b)` into the
matrix at exactly that counter.

## `interp_of_dialecticaMatrix_pe`

The dual of `dialecticaMatrix_of_interp_pu`: the witness of an ∃-formula
is the tuple of existential witnesses (plus `unit`-shaped padding), its counter carries no
information, and the matrix at witness `(c, …)` is the body at `c`, which is exactly what the
∃ asks for.

This is the lemma that lets the metatheorem's conclusion matrix `C∃` be an ∃-formula rather
than quantifier-free (Kohlenbach 17.52).

## `Formula.isPurelyUniversal_of_qf`

Quantifier-free formulas are purely universal — the old `hB_qf` hypothesis is an instance
of the new `hB_pu` one.

## `Formula.isPurelyExistential_of_qf`

Quantifier-free formulas are purely existential — the old `hC_qf` hypothesis is an instance
of the new `hC_pe` one.

## Base-type equality (section before `wTy_eqAtType_base`)

Base-type equality used to be an **abstract** predicate `EqX i s t`, and
nothing could be said about its Dialectica witness/counter types — hence four fields of
`EqXInterp` (`witnessSubsingleton`, `witnessDefault`, `counterDefault`, `realizeTerm`) which
had to be *supplied* by each theory.

With `eqAtType (.base i) s t ≡ eq_R (d_i s t) 0ℝ` fixed, `eq_R` is `Formula.all .nat <QF>`,
so `wTy` of it is `nat →ₜ unit` and `cTy` is `nat ×ₜ unit` **by `rfl`** — at every `ι`, `κ`,
`Γ`, `s`, `t`. All four are therefore outright definable, and the fields were vestigial.
The definitions below replace them; see also `eqAtTypeBaseRealizeTerm` in
`Dialectica/Syntactic.lean`, which needs `wTy` and so lives one module up.

## `eqAtTypeBaseWitness`

Was `EqXInterp.witnessDefault`.

## `eqAtTypeBaseCounter`

Was `EqXInterp.counterDefault`.

## `eqAtTypeBaseWitness_subsingleton`

Was `EqXInterp.witnessSubsingleton`.

## `EqXInterp`

**What this structure is for.** It asks *only for model facts* — things that are true of the
space and are not derivable from the syntax. Everything that the "base equality is defined"
refactor made computable has been removed from it and lives as an ordinary definition (`eqAtTypeBaseWitness`, `eqAtTypeBaseCounter`,
`eqAtTypeBaseWitness_subsingleton` above; `eqAtTypeBaseRealizeTerm` and
`eqAtTypeBase_realizeTerm_sound` in `Dialectica/Syntactic.lean`).

## `EqXInterp.dist_comm_holds`

`Derivable.dist_comm` is a constructor, so Dialectica soundness owes its truth in the
model. It is *not* an instance of `realize`: `eq_R (d x y) (d y x)` is not of the form
`eqAtType (.base i) s t`, which is `eq_R (d s t) 0ℝ`. See ARCHITECTURE.md.

Only the model fact is asked for — no realizer and no realizing term. `eq_R` is purely
universal and ∨-free, so `realizer_of_pu` / `srealizer_of_pu` build both from this;
see `EqXInterp.dist_comm_realize` just below and `sDistComm` in
`Dialectica/Syntactic.lean`.

## `EqXInterp.dist_comm_realize`

Was once a field (`dist_comm_realize`); it is now derived from the model fact
`dist_comm_holds` by `realizer_of_pu`, since `eq_R` is purely universal and ∨-free
(`isPurelyUniversal` and `isVFree` are both `true` by `rfl`). Its signature is unchanged,
so call sites in `Dialectica/Lemmas.lean` are untouched.

## `EqXInterp.dist_tri_realize`

`le_R_pu` is the ∨-free purely universal form of `≤ℝ` precisely so that this works.
