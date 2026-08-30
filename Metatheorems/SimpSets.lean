/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean

/-!
# Named simp sets

An attribute cannot be *used* in the module that declares it, so the declarations live here,
alone, and everything downstream tags into them.

## `closed_subst`

Every constant of the object language — `Term.add`, `Term.rat_encode`, `Term.cauchyfy`, … —
is a closed term, so substitution leaves it alone, and each one carries a `by rfl` lemma
saying so. There are 47 of them. They were already `@[simp]`, so the cost was never *proving*
them: it was that `simp only` takes an explicit list, and a goal mentioning fourteen closed
constants needed all fourteen named. That is 435 mentions across 303 `simp only` calls in
`RationalNumbers.lean` alone, and omitting one fails the call rather than degrading it.

`closed_subst` is that list, under one name. New closed constants — the real-number
operations especially — tag themselves in at their definition and every downstream
normalisation picks them up for free.
-/

register_simp_attr closed_subst
