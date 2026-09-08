# Subst.lean

## `Subst.cons` — the normal form for substitute-after-rename

Instantiating a *weakened* `∀` at a term composes a renaming with a substitution. Written
naively — via `rename_subst` — the composite is an anonymous `fun v => s (r v)`, which matches
none of the named forms above, so no rewrite can fire on it. It can still be pushed
structurally down to the variables, where it beta-reduces; but at an *opaque* leaf (a term
parameter, as opposed to a variable or a constant) there is nothing to push into, and
collapsing it needs `subst_id` under a `funext` — not a rewrite.

Every composite we actually meet has one shape: *put `t` at variable 0, rename the rest by
`r`*. Naming that shape, `Subst.cons`, is enough. It is closed under the compositions that
arise (`Renaming.comp` absorbs the renamings), and — the point — it has a leaf rule,
`subst_cons_weaken`, that fires on an opaque term because the substitution is a named
constructor rather than a lambda.

## `Term.subst_cons_weaken`

**The leaf rule.** Because `Subst.cons` is a named constructor, this fires on an opaque
term `u` — which is exactly what the anonymous composite could not do.

## `Term.rename_ext_eq_cons`

A renaming under a binder is a `cons` too: it keeps variable 0 and renames the rest. This is
what lets a bare *weakening under a binder* — the shape `∀`-elimination at the bound variable
leaves behind — join the same normal form, opaque leaves included.

## `Term.subst_shift_eq_weaken`

`rename_eq_subst` reads left-to-right, turning a rename into a subst; this is the
right-to-left direction at `Renaming.shift`, which is the form a `Formula.weakenBy` leaves
behind once `renameF_eq_substF` has been applied to it. Without this, a weakened hypothesis
and a hand-written `t.weaken.weaken` are equal but not syntactically so, and the proof mode
cannot match them.

## `Term.weaken_subst0'`

Normalizing a goal left behind by `induction` pushes `Formula.subst0` down to bare
`Term.subst`, at which point `weaken_subst0` no longer matches. This form does.

## `Term.Subst.ext_vz` / `ext_vs`

Needed to normalise a goal under *nested* binders, where the substitution arrives as an
iterated `Subst.ext`. Stated so that `simp` can step through: unfolding alone leaves a `match`.
