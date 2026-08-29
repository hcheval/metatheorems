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
-/

namespace Metatheorems

namespace Term

variable {ι : Type} {F : ι → Ty ι}

/-- Does this term mention the primitive recursor? -/
def usesPrec : {Γ : Ctx ι} → {ρ : Ty ι} → Term F Γ ρ → Bool
  | _, _, .prec _  => true
  | _, _, .app f x => usesPrec f || usesPrec x
  | _, _, .lam b   => usesPrec b
  | _, _, _        => false

end Term

namespace ProofMode

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

open Formula

/-- **Checked `∃`-introduction.** Identical to `seq_exI` except that the witness must carry
a proof that it does not use the recursor.

`Derivable.exist_ax` is the sole `∃`-introduction rule of the kernel, so routing every
proof-mode `∃`-introduction through this one definition localises the smuggling surface to a
single place. -/
def seq_bound {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (_hrf : t.usesPrec = false)
    (h : Seq F EqX a Premises Δ (A.subst0 t)) :
    Seq F EqX a Premises Δ (Formula.ex ρ A) :=
  seq_exI t h

end ProofMode
end Metatheorems
