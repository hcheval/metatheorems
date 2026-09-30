# MetatheoremPrereqs.lean

## module header

**This file is a library of shared parts, not a metatheorem.** It is named for what it
contains rather than for what it once contained: the three components below, out of which
every live entry point is assembled. Nothing here is an entry point, and nothing here is
dead — 16 of its 17 declarations are cited from other modules.

The live entry points are `syntactic_general_metatheorem{,_classical,_at,_gen}`
(`SyntacticMetatheorem.lean`) and `monotone_general_metatheorem{_at,_classical_at}`
(`MonotoneMetatheorem.lean`, `MonotoneMetatheoremClassical.lean`); both are built from the
three parts above. Delete this file and every metatheorem in the project stops compiling.

*Named `Metatheorem.lean` until 2026-09-08. It did hold `general_metatheorem`,
`general_metatheorem_classical` and `metatheorem_core` — the transcription of the reference
document's Def. 6.0.1 with a total majorizer — and all three were deleted on 2026-09-07 with
the `Majorizability` structure they took, which is uninhabitable (`MajorizabilityRel.lean`).
Do not re-add them. What the old name then advertised was a metatheorem that was no longer
here, which reads as a vestigial file; the rename says what survived instead.*

## `prenexify_gen`

**`prenexify_gen` is the general form: no hypothesis on `B₀`, `C₀` at all.**
The argument is pure classical predicate logic — `Derivable.lem` on arbitrary formulas —
and never inspected the matrices; `prenexify`'s four QF/∨-free hypotheses were always
unused, and it is now a wrapper. This is what lets the general-matrix metatheorem
(Kohlenbach 17.52: `B∀` a ∀-formula, `C∃` an ∃-formula) reuse the classical route:
with `B₀ := ∀b̲ B₀₀` and `C₀ := ∃c̲ C₀₀` the prenexified body `B₀' →ᶠ C₀'` is not
quantifier-free, and that is fine here.

Working notes that sat in the proof, in the branch `∀u∀v ¬(B₀w→C₀r) → ∀v ¬C₀`:

    Instantiate outer ∀u at zero: get ∀v ¬(B₀w' → C₀r')
    where B₀w' = B₀w.subst0 zero, C₀r' = C₀r.subst0 zero
    C₀r = C₀.renameF (ext shift), so C₀r.subst0 zero = C₀ by substF_renameF_id
    Then forall_map with not_imp_right gives ∀v ¬C₀

    C₀r.substF(Subst.ext(subst0_map zero)) = C₀
    This is NOT C₀r.subst0 zero (which is direct subst0_map).
    The ∀v binder pushes subst0 through Subst.ext.
    C₀r = C₀.renameF(ext shift). Under Subst.ext(subst0_map zero):
    vz → vz (by Subst.ext), vs w → (subst0_map(zero)(w)).weaken
    At ext_shift(vz) = vz: Subst.ext gives var vz. ✓
    At ext_shift(vs w) = vs(vs w): Subst.ext(vs(vs w)) = (subst0_map(zero)(vs w)).weaken = (var w).weaken = var(vs w). ✓

## `prenexify`

The hypotheses are unused (see `prenexify_gen`); kept so that every existing call site is
unchanged.

## `classical_to_prenex_extended`

This is the classical route CLAUDE.md note 2 prescribes and the one the paper takes.
`syntactic_general_metatheorem_classical` and, through it,
`monotone_general_metatheorem_classical_at` are its consumers.

**The surviving inner `¬¬` is real** and every consumer must go through it, semantically or
otherwise. The semantic discharge is `Classical.not_not` on the matrix, and it is sound and
cheap here **precisely because of the prenexification**: the body `∃u∃v(B₀' → C₀')` has a
quantifier-free ∨-free matrix, so `dialecticaMatrix_iff_interpFormula` reduces it **for
every counter**, and the counter the `¬¬` layer hands us is therefore irrelevant. That is
exactly what fails on the *unprenexified* route, where the witness depends on a challenge
that genuinely matters (FEASIBILITY R1).

**An object-level Markov step is not available at this shape without new machinery**, and
the reason is worth keeping because it recurs. `Derivable.markov` needs a quantifier-free
body, and `∃v(B₀' → C₀')` is not one. Collapsing `∃u∃v` into a single `∃w` over
`nat ×ₜ nat` would need `Term.fst (Term.mkPair a b) = a` as a *derivable* equation, and the
proof system has **no product β-rules** (`beta_eq` covers `lam` only) — the same wall
`Probes/ConjBoundDemo.lean`'s nested-existential variant hits, and the one
`Derivable.lean`'s `pair_fst` comment refers to. The Cantor-pairing alternative has the
equations but drags in `RationalNumbers` (the 43 s module) and needs QF-ER rewriting under
two binders. Both are avoidable: Markov's principle is true in the model, and
`Classical.not_not` is precisely its semantic content. Nothing is given up by taking it,
since `dialectica_soundness_ctx'` already brings in `Classical.choice` via its own Markov
case.

*Provenance.* The three paragraphs above were the docstring of
`general_metatheorem_classical`, deleted along with `general_metatheorem` and
`metatheorem_core` because all three took the uninhabitable `Majorizability`. Proving the
classical one is what produced this factoring in the first place, so its reasoning is
inherited here rather than lost with it.

## The core bound construction (section before `coreBound`)

**The majorants are supplied explicitly**, rather than obtained from a total `majorizer`.
That is what makes this form usable: it needs only `MajorizabilityRel`, which is inhabited
(`bezemRel`), together with majorants for the two extracted functionals — which
`all_closed_terms_majorizable` or a `ConstMajorants` provides.

*There was also a `metatheorem_core` taking a whole `Majorizability`, with
`U_star := majorizer U`, `V_star := majorizer V` as the special case. It was deleted with
that structure: the total majorizer is uninhabitable (`MajorizabilityRel.lean`), so it could
never be applied, and its name differed from the live one by a suffix.*

## `coreBound`

Same `_at` convention as `bezem_prec_maj_at` and `MetricModel.dist_maj_at`.

## `general_metatheorem_extract`

Note the MFI route does **not** reuse this: it fixes the realizer to
`dialectica_soundness_ctx'`'s, whereas an `MRealizer`'s majorization fact is about the
*existential* realizer. `mfi_extract_core` is this lemma's analogue, stated over an abstract
realizer. See `MonotoneMetatheorem.lean`.
