# ProofMode/Arith.lean

## module header

### What the mode does and does not buy

The *logic* — induction, the induction hypothesis as a named assumption, chaining equalities
— becomes a script. What does not go away is the substitution bookkeeping: `induction` leaves
goals of the form `A.subst0 0` and `∀n (A → A[Sn])`, and those have to be normalised before
they are recognisable. `anorm` below does that with the same rewrite set the hand-built
proofs spell out one `_nf` lemma at a time.

There is no rewriting tactic, and there cannot be a general one: the system is *weakly*
extensional, so equals may be substituted for equals only through QF-ER, at quantifier-free
∨-free formulas. `ptrans` is the closest thing — a `calc` step, named midpoint and all.

## `anorm_ren`

A renaming under a binder is a `Term.Subst.cons` too — it keeps variable 0 and renames the
rest — so one rewrite brings it into the same normal form and `anorm` finishes.

Kept separate from `anorm` because the two rules compete: turning a renaming into a `cons`
*before* an enclosing `subst0` has absorbed it produces a substitution-after-substitution,
which is outside the vocabulary. Use this only when the renaming stands alone.

## `antitone_chain`

The premise sits **inside** the quantifiers on purpose. Put outside, it would be weakened by
each `pforall`, and instantiating a weakened `∀`-hypothesis at a compound term leaves a
substitution `anorm` cannot normalise — see `LADDER.md`. Inside, every use is either at the
bound variable, where `pspecialize` applies and no substitution appears, or on an unweakened
hypothesis, where `pinst` does.

## `antitone_chain_outside`

This is the shape `antitone_chain` was written to avoid: `hmono` is weakened once by the
induction and again by each `pforall`, and it is then instantiated at the compound term
`m + i` — a substitute-after-rename composite over an *opaque* parameter `a`. Before
`Term.Subst.cons` this could not be normalised at all.

## Rung 6a — strictness

Not in `Arithmetic.lean` and not a consequence of what is: `monus_disjunct` at `(S y, x)`
leaves the branch `x ∸ S y = 0`, which is consistent with the premises — the case `x = S y`,
where the goal happens to hold anyway. So it needs its own induction, on `y`.

The shape is rung 4's: split on whether `x` is zero, kill the zero branch with
`succ_ne_zero`, and in the other branch replace `x` by `S (pd x)` so `monus_succ_l` strips a
successor off both the premise and the goal. What is new is that the *disequality* has to be
transported down to the predecessor as well, which is what the `phave` below does.

## Rung 6b — the strict-drop step

With rung 6a in hand this is two moves — strictness turns `y ≤ x` plus `x ≠ y` into
`S y ≤ x`, transitivity chains that against `x ≤ S K`, and `monus_succ_l` cancels the
successors. It is the first rung that is *composed* rather than proved: no induction, no
rewriting of its own beyond the last cancellation.
