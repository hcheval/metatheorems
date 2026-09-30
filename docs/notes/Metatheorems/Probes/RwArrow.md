# Probes/RwArrow.lean

## module header

**Result: `prw` works; `prwby` cannot and never will.** `prwby` instantiates QF-ER's premise
`A₀` with the hypothesis's own formula and discharges `A₀.isQF = true` by `rfl`; at an arrow
type that formula is a `Formula.all`, so it is not quantifier-free. Function-typed rewriting
is therefore available only from *closed* rules (`prw`), never from a hypothesis.
