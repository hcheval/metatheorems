/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.MonotoneMetatheoremClassical
import Metatheorems.Probes.LemBoundDemo
import Metatheorems.Probes.MonotoneLaneB

/-!
# Part C0: the COMPOSED classical route under MFI (measurement only)

`classical_to_prenex_extended` turns `LemBoundDemo.lFinalNoLem` (12 `Derivable` constructors)
into an **85,180-constructor** `Allowed.extended` derivation (`SizeProbe`, item 2;
`prenexify` 347 + `nn_all_nn` 274 + `negTrans_sound` 363 → 84,905). The LEM-using
`lFinalLem` is 89,556. On the *term* route those OOM under `#eval` while being built.

**Question (Lane B's prediction).** Under MFI nothing is built as a term, and a single node
costs ≈3 ms in the kernel — predicting *minutes*, not OOM.

**RESULT: the prediction was optimistic — it is OOM, and the wall is the translation layer,
not the interpretation.** The 85k-node derivation and
its monotone realizer elaborate in ≈4 s (MFI builds no realizer term), but reducing the `U`/`V`
projection is `std::bad_alloc` at 12 GB after ≈47 s. MFI clears the per-cast cost, not the
classical route's per-node blowup, which is at the translation layer. The two measurements and the
reproduction are in the notes.

The `def`s below are what type-checks; the two OOMing theorems are recorded above, not here
(a file of errors is not a green build).
-/

namespace Metatheorems
namespace ClassicalMfi

open Formula
open LemBoundDemo (lXE lFE lSiE lEqxiE lPremE lSpremiseE lNts lB0 lC0 lB0_qf lB0_vf lC0_qf
  lC0_vf lFinalNoLem lCmE)

/-- The prenexified, negatively translated, `nn_all_nn`-stripped, cast-into-extended classical
derivation of the LEM-free proof — **85,180 `Derivable` constructors** (`SizeProbe`). -/
def cDerivNoLem : @Derivable Empty Empty lFE Allowed.extended lPremE []
    (Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
      (lB0.weakenBy Ty.nat →ᶠ lC0.renameF (Term.Renaming.ext Term.Renaming.shift)))))) :=
  classical_to_prenex_extended lNts lB0_qf lB0_vf lC0_qf lC0_vf lFinalNoLem

/-- Its monotone realizer. Type-checks in ≈4 s (lazy); **no realizer term is built**. -/
noncomputable def crNoLem :
    MRealizer lCmE (Formula.all Ty.nat (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
      (lB0.weakenBy Ty.nat →ᶠ lC0.renameF (Term.Renaming.ext Term.Renaming.shift)))))) :=
  monotone_soundness lEqxiE lSpremiseE lCmE cDerivNoLem

/-- The `¬E` formula the surviving `¬¬` is challenged with. -/
abbrev Eneg := ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat
  (lB0.weakenBy Ty.nat →ᶠ lC0.renameF (Term.Renaming.ext Term.Renaming.shift))))

/-- The classical `U`-projection through `¬¬∃u∃v`, the MFI analogue of
`interpret_extractUTermP`: feed the default `¬E` challenge to the outer `¬¬`'s counter side,
read the `∃u` index of the resulting `∃u∃v` witness. Type-checks; does **not** reduce
(header, measurement 2). -/
noncomputable def cU (xs : Ty.interpret lXE Ty.nat.hat) : ℕ :=
  (((crNoLem.val (bezemAbstractEmpty lSiE).N () xs).2
      (Ty.interpret_default lSiE (wTy Eneg).hat) ()).1.1)

/-- The classical `V`-projection (the `∃v` witness index). -/
noncomputable def cV (xs : Ty.interpret lXE Ty.nat.hat) : ℕ :=
  (((crNoLem.val (bezemAbstractEmpty lSiE).N () xs).2
      (Ty.interpret_default lSiE (wTy Eneg).hat) ()).1.2.1)

#print axioms cDerivNoLem
#print axioms crNoLem

-- The FUSED classical route (Lane C): `monotone_nd_soundness`, no `negTrans_sound`

/-!
## STATUS (Lane C, second pass — hand-written leaves) and NEXT STEP

With every per-node `¬¬`-combinator leaf hand-written (`Dialectica/MonotoneNDLeaves.lean`), gate
G-C1/G-C2 (`kernel_rfl` numeral) is still negative, and the wall is the fan-out of the
combinators' counter sides under `syllogism` nesting (≈ ×5 per level; `k = 8` OOM, `prenexify`
has 134 `syllogism`s), on the kernel and on the compiled evaluator alike. `lFinalNoLem` alone
through the fused recursion reduces to `5` in 37 ms. Next step: a majorant representation with
explicit sharing (Lane D1's memo direction). Measurements in the notes.
-/

/-!
## Lane C: the fused negative-translation + MFI recursion, and gates G-C1 / G-C2

`monotone_general_metatheorem_classical_at` interprets the classical derivation directly
(`prenexify`, `monotone_nd_soundness`, `nn_all_nn`), never builds the 85,180-node
`negTrans_sound` output, and type-checks (`[propext, Classical.choice, Quot.sound]`); NT-stability
is gone. The numeral gate is negative (`std::bad_alloc` at 12 GB); the control
`CGate.extR = monotone_soundness … lFinalExt` (same derivation at `Allowed.extended`, no
prenexify, no NT) reduces to `U = 0`, `V = 5` in ≈17 s. The corrected localisation and the
reproduction snippet (kept out of the file) are in the notes.
-/

open LemBoundDemo (lFinalExt)

/-- The EXTENDED MFI realizer of the SAME 12-node derivation — MFI, but no `prenexify`, no NT.
The localisation control for the classical OOM above. -/
noncomputable def CGate.extR :=
  monotone_soundness lEqxiE lSpremiseE lCmE lFinalExt

/-- **G-C1 control (PASS): the MFI machinery reduces and gives the expected `U = 0`.** Agrees
with `LemBoundDemo.lUtExt_at_5` (the term-route intuitionistic control). ≈17 s, `kernel_rfl`. -/
theorem extU5 : (0 : ℕ) = mfiU lCmE CGate.extR (5 : ℕ) := by kernel_rfl

/-- **G-C1 control (PASS): `V = 5`.** Agrees with `LemBoundDemo.lVtExt_at_5`. -/
theorem extV5 : (5 : ℕ) = mfiV lCmE CGate.extR (5 : ℕ) := by kernel_rfl

/-- Non-degeneracy: `4` is refuted, so the `rfl` genuinely reduces (trap 12). -/
theorem extV5_ne_4 : (4 : ℕ) ≠ mfiV lCmE CGate.extR (5 : ℕ) := by rw [← extV5]; decide

#print axioms extU5
#print axioms extV5

end ClassicalMfi
end Metatheorems
