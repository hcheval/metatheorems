# TypeSystem.lean

## `Ty.eqBaseFree`

**The recursion must mirror `eqAtType`'s own, not the type's syntax.** `eqAtType` at an arrow
recurses only into the *codomain* — the domain appears solely as a binder — so `X →ₜ nat` is
eq-base-free even though `X` occurs in it. The obvious wrong definition
(`| .arr ρ τ => ρ.eqBaseFree && τ.eqBaseFree`) is not an error, it just silently makes fewer
lemmas applicable. Only the codomain spine matters.

This is what lets the arithmetic tower — everything at `nat` and `realTy = nat →ₜ nat` — use
`eqAtType_sym`/`eqAtType_trans` *below* the real-number layer, where the base case (which
needs `eq_R` symmetry and transitivity) is not yet available. See ARCHITECTURE.md.

## `realTy`

Lives in `TypeSystem.lean` rather than in `RationalNumbers.lean` because `Term.dist` mentions
it, and `Term` is below the ℚ layer. It is a pure `Ty` abbreviation, so nothing comes with it.

## `Ty.isGround`

Products are not arrows, so they count as "ground" for the `ρ₁→…→ρₖ→ρ₀` decomposition.

## `Ty.prod`

Needed so that Dialectica witness/counter *types* are object-level types, hence witnesses are
`Term`s.
