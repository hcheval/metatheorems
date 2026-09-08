/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Majorizability
import Metatheorems.Dialectica.Syntactic

/-!
# Pure `WE-HA^ω`: the instance with no space

`ι = Empty`: no base types, so no carrier, no function constants, no premises. Every
`Ty.interpret` is then built from `ℕ`, `Unit`, `×` and `→`, every value is a plain natural
number, and a bound extracted here is a **magnitude** rather than a code through the ℚ/ℝ
encoding. This is the setting the demonstrations of extraction run in.

One definition per thing the metatheorems ask for, under one name, so that a file wanting the
pure system says `PureWEHA.F`, `PureWEHA.Premises`, `PureWEHA.cm` and nothing else:

| what | the metatheorem's binder |
|---|---|
| `X`, `F` | the carrier family and the signature — both `Empty.elim` |
| `si`, `eqxi` | the (vacuous) model and its `EqXInterp` |
| `Premises`, `spremise` | the empty premise set and its (vacuous) realizer |
| `cm` | the Bezem majorants, `bezemConstMajorantsEmpty` |

Before 2026-09-08 this instance existed only inside `Probes/` (`TinyBoundDemo.tXE`, `tFE`,
`tSiE`, `tEqxiE`, `tPremE`, `tSpremiseE`; `MonotoneMCT.cmE`), and `Demo/Walkthrough.lean`
imported a probe to reach it. Probes are measurements; library and demo code must not depend
on them. The probes keep their own copies — the definitions are one-liners and the copies are
definitionally equal to these, so nothing there had to move.
-/

namespace Metatheorems
namespace PureWEHA

/-- No base types: the carrier family is empty. -/
def X : Empty → Type := fun i => i.elim

/-- No function constants. -/
def F : Empty → Ty Empty := fun i => i.elim

/-- The model. Every field is about a base type or a constant, and there are none. -/
def si : SpaceInterp X F where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

/-- The equality interpretation, likewise vacuous. -/
def eqxi : EqXInterp X F si where
  realize         := fun i => i.elim
  extract         := fun i => i.elim
  dist_comm_holds := fun i => i.elim
  dist_tri_holds  := fun i => i.elim

/-- No premises. -/
def Premises : PremiseSet F := fun _ => False

/-- The premise realizer, with nothing to realize. -/
def spremise : ∀ (Γ' : Ctx Empty) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B :=
  fun _ _ h => h.elim

/-- The majorants of the constants `0`, `S`, `R`: Bezem's, as data. -/
def cm : ConstMajorants (bezemAbstractEmpty si) := bezemConstMajorantsEmpty si

end PureWEHA
end Metatheorems
