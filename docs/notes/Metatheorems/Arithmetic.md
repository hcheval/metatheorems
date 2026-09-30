# Arithmetic.lean

## Section 1: Arithmetic Term Definitions — MOVED

`Term.sg_bar`, `pd`, `add`, `mul`, `monus`, `abs_diff` now live in
`Metatheorems/Terms/Arith.lean`, which sits BELOW `eqAtType` and `Derivable`
in the import order.

Reason: `eqAtType` at a base type is `eq_R (dist i s t) 0ℝ`, so it depends on the ℚ/ℝ
term layer, which depends on these. Only the *definitions* moved; every proof about
them stays in this file. See ARCHITECTURE.md.

## the arithmetic `closed_subst` lemmas (comment after `add_body_nf`)

`pd_closed_subst` and the other arithmetic `closed_subst` lemmas MOVED to
`Metatheorems/Terms/ClosedSubst.lean`, which sits below `eqAtType`: `eqAtType_substF`'s
base case is `eq_R_substF`, which needs the whole ℚ/ℝ `closed_subst` set. See that file.

## `weaken_substVar0`

Public: this is one of the rewrites a proof script needs to see through the goals that
`induction` leaves behind — see `ProofMode/Arith.lean`.

## the arithmetic `closed_subst` lemmas (comment after `weaken_substVar0`)

`mul_closed_subst`, `monus_closed_subst`, `abs_diff_closed_subst`, `sg_bar_closed_subst`
and `add_closed_subst` MOVED to `Metatheorems/Terms/ClosedSubst.lean`, together with the
`attribute [closed_subst]` line that tags them. The primed private variants above are the
same statements and stay here because they are used earlier in this file.

## `qnorm`

`qnorm` is the substitution-normalising `simp only` that this development writes out by
hand roughly 300 times: push `subst`/`subst0` through the application spine, and leave the
closed constants alone. The explicit lists it replaces had to name every closed constant
appearing in the goal, and omitting one *fails* the call rather than weakening it.

`qnorm [h₁, h₂]` adds lemmas to the front — in practice the local `let` abbreviations a
goal is stated in terms of, which have to be zeta-unfolded in the same pass.

## Truncated subtraction against multiplication, and `geq`

`monus` had a theory of its own — `monus_zero/succ/cancel/self/zero_l/succ_l`,
`monus_eq_zero_antisym`, `monus_disjunct` — but nothing relating it to `mul`, and `geq` had
no theory at all. These five are what the ℚ order theory needs: `add_Q`'s opposite-sign
branch takes an `abs_diff` of two cross products and compares them with `geq`, and both
have to survive being scaled by a denominator.

## `qtrans`

The development spells this out as `.mp (.mp h₂ (.mp h₁ and_intro)) .trans0` several hundred
times.

## `abs_diff_unfold`

It was built inline inside `abs_diff_eq_zero_iff`; named here because the distributivity below
needs it.

## `monus_add_comm` (section comment `(x ∸ y) + y =₀ (y ∸ x) + x`)

Both sides are `max x y`, written without a `max`. This is the fact that *recovers* a
truncated difference: specialised with `y ∸ x =₀ 0` it says `(x ∸ y) + y =₀ x`, which is
what the signed-value identity for `add_Q` needs in its opposite-sign branch.

Proved by induction on `x` with `∀y` bundled, in the shape `monus_eq_zero_antisym` uses:
the base needs no inner split, and the successor step splits on `y` because `S x ∸ y` only
reduces once `y` is exposed as a successor.

## Associativity/commutativity shuffles for `+`

There is no AC normaliser for the object language, and the signed-value bookkeeping in
`RationalNumbers.lean` needs a handful of fixed rearrangements. Each is a short chain of
`add_assoc`/`add_comm`; naming them keeps the call sites to one rewrite apiece.
