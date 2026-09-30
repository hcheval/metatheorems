# Probes/ExtractTermDemo.lean

## module header

**Why it could not be demonstrated before.** Every model in the project — metric,
W-hyperbolic, CAT(0), normed — is built over Mathlib `ℝ`, so `si` is `noncomputable` and any
`#eval` mentioning it is impossible. `UPremiseDemo.uUt` is `noncomputable def` for exactly
that reason. `extractTerm` takes no `si`, so the realizer of a derivation **at a space** is
now an ordinary computable `Term`, and `#eval` on it works.
