# ProofMode/Rewrite.lean

## module header

### How the abstraction is found

`Derivable.qfer` takes the abstraction `r : Term F (nat :: Γ) σ` as an argument, so the work
is finding it: given the goal's side `L` and the pattern `s`, produce `r` with the
occurrences of `s` replaced by the bound variable and every other leaf weakened. One
traversal computes that and the rewritten side `L[s := t]` at once.

The `subst0` round-trip proofs are not `rfl` — a weakened leaf only comes back by
`Term.subst_subst0_map_weaken` — but they need exactly that one lemma plus the structural
unfolding of `Term.subst`, with nothing theory-specific. `prw_norm` is that simp call.

## `qfer_nf` (QF-ER at an arbitrary pair of types)

The constructor was always general — `Derivable.qfer`
is stated for `eqAtType ρ`/`eqAtType σ` — so nothing here is new metatheory; only the
`_nf` wrappers were specialised.

## the equation recogniser (comment inside the base-type case)

The base-type case used to need a comparison against the goal's own `EqX` fvar. With
`EqX` gone, `eqAtType (.base i) s t` is a genuine application of `eqAtType`, so the
folded match above already covers it.

## the goal-rewriting core (comment before the gluing)

At other types transitivity comes from
`eqAtType_trans`, which needs an `AdmissibleEqX` this tactic is not given.
