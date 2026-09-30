/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.MCT
import Metatheorems.Majorizability

/-!
# Probe: does the extracted realizer term reduce?

**Step 0 of the end-to-end bound extraction.** Before building any infrastructure for
"derivation → realizing term → majorant → numeral", measure the one genuine unknown: the
realizer `syntactic_soundness` produces recurses over a 36-constructor derivation, and
`mct_p2` is a proof-mode script. If the resulting term is astronomically large, the whole
pipeline plan changes shape.

NOT imported by `Metatheorems.lean`.
-/

namespace Metatheorems
namespace BoundProbe

/-- Structural node count of a term. Deliberately not in `Term.lean`: it exists to measure
this probe, not as library API. -/
def termSize {ι : Type} {F : ι → Ty ι} :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → Nat
  | _, _, .var _      => 1
  | _, _, .app f a    => 1 + termSize f + termSize a
  | _, _, .lam b      => 1 + termSize b
  | _, _, .zero       => 1
  | _, _, .succ       => 1
  | _, _, .prec _     => 1
  | _, _, .func _     => 1
  | _, _, .zeroX _    => 1
  | _, _, .dist _     => 1
  | _, _, .unitI      => 1
  | _, _, .mkPair a b => 1 + termSize a + termSize b
  | _, _, .fst p      => 1 + termSize p
  | _, _, .snd p      => 1 + termSize p

-- The `ι = Empty` model: everything space-dependent is vacuous

/-- The empty space interpretation. All three fields quantify over `ι = Empty`. -/
def siE : SpaceInterp XEmpty FEmpty where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

/-- `EqXInterp` at `ι = Empty`: every one of the four fields begins `∀ (i : ι)`, so with no
base types each is `fun i => i.elim`. This is why `ι = Empty` is the cheap setting. -/
def eqxiE : EqXInterp XEmpty FEmpty siE where
  realize             := fun i => i.elim
  extract             := fun i => i.elim
  dist_comm_holds     := fun i => i.elim
  dist_tri_holds      := fun i => i.elim

/-- No premises, so the premise realizer is vacuous. -/
def PremE : PremiseSet FEmpty := fun _ => False

def spremiseE : ∀ (Γ' : Ctx Empty) (B : Formula FEmpty Γ'), PremE ⟨Γ', B⟩ → SRealizer siE B :=
  fun _ _ h => h.elim

-- The measurement

/-- The MCT derivation, at `ι = Empty` with an empty premise set. -/
def mctE : @Derivable Empty Empty FEmpty Allowed.extended PremE [] mctStatement :=
  ProofMode.mct_p2 (al := Allowed.extended)

/-- Its syntactic realizer. -/
def realizerE : SRealizer siE (mctStatement (F := FEmpty)) :=
  syntactic_soundness eqxiE spremiseE mctE

/-- The two extracted functionals, as closed terms. -/
def UtE : Term FEmpty [] (mctTy Empty →ₜ Ty.nat) :=
  extractUTerm (ρ := mctTy Empty) (B₀ := mctB₀) (C₀ := mctC₀) realizerE.val

def VtE : Term FEmpty [] (mctTy Empty →ₜ Ty.nat) :=
  extractVTerm (ρ := mctTy Empty) (B₀ := mctB₀) (C₀ := mctC₀) realizerE.val

/-! **Do not `#eval` `termSize UtE` or `termSize realizerE.val` without a memory cap**
(`ulimit -v`): naive evaluation is not viable even at `ι = Empty`. -/

end BoundProbe
end Metatheorems
