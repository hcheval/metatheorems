# Terms/Arith.lean

## module header

The `Term`-level arithmetic of WE-HA^ω, split out of `Arithmetic.lean` so that it sits
**below** `eqAtType` and `Derivable` in the import order.

Why the split exists: `eqAtType` at a base type is defined as `eq_R (dist i s t) 0ℝ`, so it
depends on `eq_R`, hence on the ℚ/ℝ term layer, hence on this file. Everything here is pure
`Term` construction — no `Formula`, no `Derivable` — which is what makes the ordering possible.
The *proofs* about these operations stay in `Arithmetic.lean`, above `Derivable`.

Following arithmetic.tex §Def 2.3.?. All terms are polymorphic in the ambient context `Γ`,
since they use only closed constants (`prec`, `succ`, `zero`) and `lam`, which exist in any
context.
