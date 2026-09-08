# EqAtType.lean

## module header

Split out of `Language.lean` because equality at a base type is **defined** as
`d_i(s,t) =ℝ 0ℝ`, so this file must sit above the ℚ/ℝ term layer — while `Language.lean`,
which defines `Formula`, must sit below it. `eqAtType` was the last declaration in
`Language.lean` and had no dependants inside it, so only this 30-line tail moved.

The old `EqX` parameter is gone. It used to let each theory choose its own base-type
equality, at the cost of an `AdmissibleEqX` record threaded through ~2,700 call sites whose
refl/sym/trans fields could not be discharged for a *defined* equality without circularity.
With `Term.dist` structural and the pseudometric axioms as constructors of `Derivable`,
those three become ordinary theorems. See ARCHITECTURE.md.

## `eqAtType_base_isPurelyUniversal`

This was the `eqx_pu` field of `AdmissibleEqX`; with `EqX` fixed it is a theorem.

## `eqAtType_base_substF`

This was the `substF_nat` field of `AdmissibleEqX`; with `EqX` fixed to `d_i(·,·) =ℝ 0ℝ` it
is a theorem, from `eq_R_substF` plus the fact that `Term.dist i` and `Term.zero_R` are
closed. It is the base case of `eqAtType_substF` in `Arithmetic.lean`.
