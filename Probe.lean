import Metatheorems.Language

/-!
# Probe P1: do `subst0` and `weaken` reduce on concrete formulas?

Decides whether a proof mode over `Derivable` is plumbing or needs a normalisation layer first.
Every `rfl` below that succeeds means the index computes on its own.
-/

namespace Metatheorems
open Formula

variable {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}

-- A concrete open formula: `x =₀ 0` with `x` the outermost bound variable.
abbrev A0 : Formula F (Ty.nat :: Γ) :=
  .eq0 (.var .vz) Term.zero

-- P1a: does `subst0` compute?
example (t : Term F Γ Ty.nat) :
    (A0 (F := F) (Γ := Γ)).subst0 t = .eq0 t Term.zero := rfl

-- P1b: a binder underneath — does `substF` push through `.all`?
abbrev A1 : Formula F (Ty.nat :: Γ) :=
  .all Ty.nat (.eq0 (.var (.vs .vz)) (.var .vz))

example (t : Term F Γ Ty.nat) :
    (A1 (F := F) (Γ := Γ)).subst0 t
      = .all Ty.nat (.eq0 (Term.weaken t) (.var .vz)) := rfl

-- P1c: does `weaken` compute?
example :
    (Formula.weaken (σ := Ty.nat) (.eq0 (F := F) (Γ := Γ) Term.zero Term.zero))
      = .eq0 Term.zero Term.zero := rfl

-- P1d: connectives
example (t : Term F Γ Ty.nat) :
    (Formula.and (A0 (F := F) (Γ := Γ)) (A0 (F := F) (Γ := Γ))).subst0 t
      = .and (.eq0 t Term.zero) (.eq0 t Term.zero) := rfl

end Metatheorems
