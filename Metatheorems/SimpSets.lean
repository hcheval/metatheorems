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

Every constant of the object language is a closed term, so substitution leaves it alone.
`closed_subst` collects the `by rfl` lemmas saying so, under one name. New closed constants
tag themselves in at their definition.
-/

register_simp_attr closed_subst
