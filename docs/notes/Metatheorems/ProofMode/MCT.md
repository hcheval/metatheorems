# ProofMode/MCT.lean

## `mct_bound_p2`

It used to route through `mct_bound` (`MCTStatement.lean`), which predates the object-level
Dialectica witness types and therefore had to hypothesise a `MajorizabilityRel` *and*
majorants `U_star`/`V_star` for the two extracted functionals — because the only alternative
then was the total-majorizer structure, which has no instances and was deleted for it (see
`MajorizabilityRel.lean`). That is no longer the situation: the
extracted functionals are closed `Term`s, so `all_closed_terms_majorizable` supplies their
majorants and the four extra hypotheses disappear. The only majorizability input is
`AbstractMajorizability`, which `bezemAbstract` inhabits.
