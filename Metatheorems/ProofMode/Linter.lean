/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Packing

/-!
# Non-vacuity of extraction: the surface-recursor ban

Decision D-2 (`ARCHITECTURE.md` §12) adopts two checks against a bound being *smuggled* into a
proof rather than extracted from it. This file implements the mechanical half of the second one: witness terms
written by hand at a headline `∃`-position must be **recursor-free**.

This is a check on *what the user writes*, not on what the derivation contains: extracted
terms are free to iterate, and `Term.prec` is of course still a term.

The predicates below see through *everything*, including the definition of `Term.add`, so they
are **not** the check the tactics run (that one is syntactic on what the user typed); they
are useful for asking whether an *extracted* term iterates.
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
`A` reaches the extracted content by the same route an instantiation does. D-2's list of
surface positions does not name this one, so it is covered here. -/
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
that this is the position the certificate is about. The recursor check itself is a
*tactic-level* lint on what the user typed, not a hypothesis of this lemma. -/
def seq_bound {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F a Premises Δ (A.subst0 t)) :
    Seq F a Premises Δ (Formula.ex ρ A) :=
  seq_exI t h

end ProofMode
end Metatheorems
