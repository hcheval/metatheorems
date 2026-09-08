# SimpSets.lean

## module header

Every constant of the object language — `Term.add`, `Term.rat_encode`, `Term.cauchyfy`, … —
is a closed term, so substitution leaves it alone, and each one carries a `by rfl` lemma
saying so. There are 47 of them. They were already `@[simp]`, so the cost was never *proving*
them: it was that `simp only` takes an explicit list, and a goal mentioning fourteen closed
constants needed all fourteen named. That is 435 mentions across 303 `simp only` calls in
`RationalNumbers.lean` alone, and omitting one fails the call rather than degrading it.

`closed_subst` is that list, under one name. New closed constants — the real-number
operations especially — tag themselves in at their definition and every downstream
normalisation picks them up for free.
