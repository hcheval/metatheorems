# MCTStatement.lean

## the section "Does it actually fit a metatheorem entry point?"

An `example` used to sit here applying `general_metatheorem` to `mctStatement`, as the shape
check: if it elaborates, the only remaining input is the derivation. It went with
`general_metatheorem` itself, whose `Majorizability` argument is uninhabitable
(`MajorizabilityRel.lean`), so no instantiation of it could ever have been run.

Nothing is lost, because the check is made twice over further down and both times against a
live entry point:

## the comment before `mctB₀`'s induction lemma

`ex_and_left` now lives in `PureFOLLemmas`; the local copy was removed.

## Probe P2d (section doc)

The document's Def. 6.0.1 route needs a *total* majorizer, and no instance of that exists
(nor can one, non-degenerately, at the type level this statement needs — see
`MajorizabilityRel.lean`'s closing section).

## `mct_bound`

`mct_bound_p1`/`mct_bound_p2` go through
`syntactic_general_metatheorem`, which produces the two majorants itself from
`all_closed_terms_majorizable` — so the `mj`, `U_star`, `V_star`, `hU`, `hV` arguments below
are all unnecessary. It is kept as the record of an early probe, written before the Dialectica
witness types became object-level, which established that the extraction/bounding split
composes — at a time when the only alternative was the total-majorizer route, which turned out
to be uninhabitable and was deleted.
