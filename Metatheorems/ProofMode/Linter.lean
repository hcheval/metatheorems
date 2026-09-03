/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Packing

/-!
# Non-vacuity of extraction: the surface-recursor ban

`HANDOFF.md` D-2 adopts two checks against a bound being *smuggled* into a proof rather than
extracted from it. This file implements the mechanical half of the second one: witness terms
written by hand at a headline `∃`-position must be **recursor-free**.

The rationale is that iteration is what extraction is supposed to *produce*. Across the
corpus (MCT, Groetsch, projection-uniqueness) every honest surface term is recursor-free —
`Term.prec` appears only in extracted content. So banning `prec` in surface witnesses costs
nothing honest and makes the interesting smuggle unwritable rather than merely forbidden.

This is a check on *what the user writes*, not on what the derivation contains: extracted
terms are free to iterate, and `Term.prec` is of course still a term.

## Surface, and what that word has to mean

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
-/

namespace Metatheorems

namespace Term

variable {ι κ : Type} {F : κ → Ty ι}

/-- Does this term mention the primitive recursor? -/
def usesPrec : {Γ : Ctx ι} → {ρ : Ty ι} → Term F Γ ρ → Bool
  | _, _, .prec _  => true
  | _, _, .app f x => usesPrec f || usesPrec x
  | _, _, .lam b   => usesPrec b
  | _, _, _        => false

end Term

namespace Formula

variable {ι κ : Type} {F : κ → Ty ι}

/-- Does this formula mention the primitive recursor, anywhere in its terms?

A user-written *formula* is a surface position too: a cut on `A` contributes `A`'s witness
and counter types to the Dialectica interpretation, so a hand-written iterating term inside
`A` reaches the extracted content by the same route `R4`'s attempt C used for
instantiations. `HANDOFF` D-2's list of surface positions does not name this one. -/
def usesPrec : {Γ : Ctx ι} → Formula F Γ → Bool
  | _, .bot     => false
  | _, .eq0 s t => s.usesPrec || t.usesPrec
  | _, .and A B => usesPrec A || usesPrec B
  | _, .or  A B => usesPrec A || usesPrec B
  | _, .imp A B => usesPrec A || usesPrec B
  | _, .all _ A => usesPrec A
  | _, .ex  _ A => usesPrec A

end Formula

namespace ProofMode

variable {ι κ : Type} {F : κ → Ty ι}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

open Formula

/-- **Headline `∃`-introduction.** The same rule as `seq_exI`; the separate name records
that this is the position the certificate is about.

`Derivable.exist_ax` is the sole `∃`-introduction rule of the kernel, so routing every
proof-mode `∃`-introduction through these two definitions localises the smuggling surface to
one place. The recursor check itself is a *tactic-level* lint on what the user typed (see
above), not a hypothesis of this lemma — it is a check on the input language, not a
soundness side condition, and making it a hypothesis would wrongly reject `x + y`. -/
def seq_bound {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F a Premises Δ (A.subst0 t)) :
    Seq F a Premises Δ (Formula.ex ρ A) :=
  seq_exI t h

end ProofMode
end Metatheorems
