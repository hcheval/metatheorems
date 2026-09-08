# Term.lean

## module header

**There are no `Π` and `Σ` combinators**, and no combinatory compilation (Def. 2.3.19).
Lambda is a primitive constructor instead, and beta reduction `(λx.t) u =_τ t[u/x]` is an
axiom of the proof system (`Derivable.beta_eq`) rather than a consequence of combinator
axioms. So the combinatory sublanguage the reference document works in **does not exist here**;
`CLAUDE.md`'s "Lambda vs. combinators" section sets out what that costs — in short, an
arrow-introduction condition on the majorizability relation, which is Kohlenbach's Lemma 17.80
and which the document pays for its combinators anyway — and why it is still the right call.

## `Term` (the `ι`/`κ` split)

The two index sets are separate (ARCHITECTURE.md §6) so that a theory may have one base
type and several constants (normed spaces: `+`, scalar multiplication, `‖·‖`). Every
existing instantiation takes `κ := ι`, which is inferred when `F : ι → Ty ι`.

## `Term.dist`

Structural rather than a function constant in `F`, because equality at a base type is
*defined* as `d_i(s,t) =ℝ 0ℝ` — so `eqAtType` must be able to name it without going
through a signature. The pseudometric axioms for it are constructors of `Derivable`,
and every model owes a `distInterp` satisfying them. See ARCHITECTURE.md.

## `Term.Renaming.ext_vz` / `ext_vs`

Stated so that `simp` can step through them: unfolding the definition alone leaves a `match`.
