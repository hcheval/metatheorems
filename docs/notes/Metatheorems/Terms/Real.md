# Terms/Real.lean

## module header

The `Term`- and `Formula`-level encoding of ℝ, split out of `RealNumbers.lean` so that it
sits **below** `eqAtType` and `Derivable` in the import order.

This is the file the whole layering exists for: `eqAtType` at a base type is
`eq_R (dist i s t) 0ℝ`, so `eqAtType` must be able to see `eq_R`, which is defined here.

Only definitions live here. Every proof — the `closed_subst` lemmas, the `cauchyfy` theory,
the ordered-field axioms — stays in `RealNumbers.lean`, above `Derivable`.

## `le_R_pu`

**A bug worth remembering, because of how long it survived.** This once negated the body of
`lt_R f g` rather than of `lt_R g f`, so `le_R_pu f g` meant `g ≤ℝ f` — the opposite of
`le_R f g`, and the opposite of what its own docstring claimed. Definition and docstring
agreed with each other and with nothing else, and no consumer cared about the direction until
`Derivable.dist_tri` began asserting the triangle inequality with it. At that point the
constructor was asserting `d(x,y) +ℝ d(y,z) ≤ℝ d(x,z)` — the *reverse* triangle inequality,
satisfied by no metric.

It is now definitionally aligned with `le_R`: `le_R_pu f g` and `le_R f g` unfold to the
same statement, the first as `∀n. ¬…` and the second as `¬∃n. …`.
