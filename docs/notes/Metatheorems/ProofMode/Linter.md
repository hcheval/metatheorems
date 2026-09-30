# ProofMode/Linter.lean

## module header

The rationale is that iteration is what extraction is supposed to *produce*. Across the
corpus (MCT, Groetsch, projection-uniqueness) every honest surface term is recursor-free —
`Term.prec` appears only in extracted content. So banning `prec` in surface witnesses costs
nothing honest and makes the interesting smuggle unwritable rather than merely forbidden.

### Surface, and what that word has to mean

The predicates below see through *everything*, including the definition of `Term.add` — which
is built from `Term.prec`, as every primitive-recursive constant of the language must be. So
they are **not** the check the tactics run. Writing `x + y` is not smuggling a bound; writing
`R_nat 0 (λ…) n` is. The tactic check is therefore syntactic on what the user typed: a named
constant of the language counts as an atom, and only an occurrence of `Term.prec` in the
user's own expression is refused.

That is the honest reading of "surface". Its limit is equally honest: a user who wraps an
iteration in a `def` of their own defeats it, exactly as `pexists!` does, and equally
visibly. The principled version is a *whitelist* of surface constants rather than a blacklist
of one; that is the shape to move to once the corpus fixes which constants are allowed.

The predicates below remain useful for the other direction — asking whether an *extracted*
term iterates.

## `seq_bound` (docstring of the headline `∃`-introduction)

`Derivable.exist_ax` is the sole `∃`-introduction rule of the kernel, so routing every
proof-mode `∃`-introduction through these two definitions localises the smuggling surface to
one place. The recursor check itself is a *tactic-level* lint on what the user typed (see
above), not a hypothesis of this lemma — it is a check on the input language, not a
soundness side condition, and making it a hypothesis would wrongly reject `x + y`.
