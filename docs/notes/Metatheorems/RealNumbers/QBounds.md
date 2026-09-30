# RealNumbers/QBounds.lean

## module header

Everything here is pure ℕ/ℚ — no `cauchyfy`, no real operations — so the file sits beside
`RealNumbers/Defs.lean` rather than above it. Several small `private` computations from
`RationalNumbers.lean` (`isEven_zero`, `isEven_succ`, `two_mul_eq_add`, …) are re-derived
here because that file is another workstream's and its privates are module-scoped.
