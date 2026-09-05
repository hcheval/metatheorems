/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
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
not the interpretation.** Two measurements (2026-09-05):

1. **Type-checking is cheap.** `cDerivNoLem` (the 85k-node classical derivation), `crNoLem`
   (its monotone realizer `monotone_soundness … cDerivNoLem`), and `cU`/`cV` (the `U`/`V`
   projections through the surviving `¬¬∃u∃v`, mirroring `interpret_extractUTermP`/`VTermP`
   on the majorant: feed the default `¬E` challenge, read the `∃u`/`∃v` index) all **elaborate
   and type-check in ≈4 s** — MFI genuinely builds no realizer term, so the ×230 blowup does
   not bite at elaboration, unlike the term route which OOMs `#eval` *building* the realizer.

2. **Reducing the projection is `std::bad_alloc` at the 12 GB cap after ≈47 s.** The bare
   `kernel_rfl` (which is the only route — there is no `Eq.mpr` on this path for the memo
   lemma to rewrite; the classical derivation is `negTrans_sound`/`castAllowed` output, raw
   recursion) forces `monotone_soundness` through all 85k nodes and dies. Reproduce (scratch,
   reverted — kept out of the file because it OOMs the build):

       theorem cU_probe : (0 : ℕ) = cU (5 : ℕ) := by kernel_rfl   -- std::bad_alloc @ 12 GB, ≈47 s
       theorem cV_probe : (5 : ℕ) = cV (5 : ℕ) := by kernel_rfl   -- (expected 0 / 5 per LemBoundDemo)

So **MFI clears the per-cast cost (Part B') but not the classical route's per-node blowup**:
85k nodes at even a small constant each exhausts 12 GB. This is exactly `SizeProbe` item 2 and
`ARCHITECTURE.md` §14.5's "Explicitly out of scope: the classical route's ×230 from
`negTrans_sound` — a fix to the translation, not to the interpretation." The MFI redesign does
not change that verdict; it moves the OOM from *elaboration* (term route, `#eval`) to *kernel
reduction*, and only a shared/`wit_seq_*`-style `negTrans_sound` (NT-case commutation, one
layer down) removes it. Not attempted here — the brief says do not start the fused NT+MFI
recursion.

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

end ClassicalMfi
end Metatheorems
