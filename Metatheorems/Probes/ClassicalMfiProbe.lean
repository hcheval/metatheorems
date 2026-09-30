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

-- The FUSED classical route (Lane C): `monotone_nd_soundness`, no `negTrans_sound`

/-!
## STATUS (Lane C, second pass — hand-written leaves) and NEXT STEP, for whoever continues

**What is built and green** (commit on `mfi-classical`): `Dialectica/MonotoneNDLeaves.lean` —
hand-written monotone realizers of every `¬¬`-combinator `negTrans_sound` applies per node
(`dnnIntroF`, `nnMpF`, `nnImpRevF`, `expF`, `impF`, `expansionF`, `dnnLemF`, all axiom-free or
`[propext, Quot.sound]`), a syntactic majorization dispatcher `maj_auto`, and
`Dialectica/MonotoneND.lean` rewritten to use them (`nnAllNnF` assembled; `leafM` survives only
for the propositional/`forall_ax`/`exist_ax` axiom TERMS and the cases not on the classical
route — `succ_*`, `rec_*`, `beta_eq`, `pair_*`, `dist_*`, `qfac`, `qfer`'s `negTrans_iff_pu`
legs). `monotone_general_metatheorem_classical_at` type-checks, `[propext, Classical.choice,
Quot.sound]`.

**Gate G-C1 / G-C2 (`kernel_rfl` numeral): STILL NEGATIVE, and now localised to a different
cause than the first pass claimed.** With every per-node leaf gone:
- `lFinalNoLem` ALONE through `monotone_nd_soundness` (12 classical nodes, no `prenexify`):
  the `∃v` projection of `(∀x(∀u B → ∃v C))ᴺᵀ` reduces to `5` by `kernel_rfl` in **37 ms**.
- `prenexify` ALONE (347 nodes, 134 `syllogism`, 2 `lem`): `std::bad_alloc` at 12 GB, 74 s.
- a synthetic chain of `k` classical `syllogism`s (`I_comb`s composed, no `lem`): kernel time
  k=2 **140 ms**, k=4 **3.68 s**, k=8 **OOM** — ≈ ×5 per syllogism.
So the wall is the **fan-out of the `¬¬`-combinators' counter sides under nesting**: one
classical `syllogism` is three `MRealizer.syllogism`s (counter side uses `hAB` 3×) and two
`neg_neg_mp`s (`nnMpFun` uses `Φ` 4×), and the kernel's `whnf` shares nothing across binder
depths — ARCHITECTURE §14.2's "MFI does not remove composition's duplication; on paper it is
free because terms are DAGs by notation" hitting at k ≈ 8, and `prenexify` has 134.

**Compiled evaluator (`#eval` of the hat-level ℕ projection — not a composed
`Term.interpret`, so hard rule 3 does not apply): ALSO NEGATIVE beyond k = 2.** Same synthetic
chain, one value per run, `timeout` per run: k=0 → `5` (22 s wall, all olean loading),
k=2 → `5` (17 s wall, same), k=3 → **no result in 400 s**, k=4 → **no result in 240 s**, the
`lean` process at 100 % CPU throughout (CPU time = elapsed, RSS flat at the 6.1 GB of mmapped
oleans — compute-bound, not memory-bound, not a hang). The evaluator is call-by-value and
shares *values* by pointer but re-evaluates every *application* `hAB.val n e` at every call
site inside the composed counter-side closures, so the same fan-out that is ×5 per syllogism
in the kernel is far steeper in the interpreter. The gate values on `lFinalNoLem`/`lFinalLem`
(134 nested `syllogism`s from `prenexify`) were therefore not attempted on the evaluator.

**Next step** (not started): the classical route needs a majorant representation with
explicit sharing — `let`-bound sub-majorants evaluated once, Lane D1's memo direction — not
more hand-writing: with the leaves gone, nothing per node is left to hand-write, and both
the kernel and the evaluator die on the same nesting.
-/

/-!
## Lane C: the fused negative-translation + MFI recursion, and gates G-C1 / G-C2

`monotone_general_metatheorem_classical_at` (`MonotoneMetatheoremClassical.lean`) interprets
the CLASSICAL derivation directly — `prenexify` under `∀x`, then `monotone_nd_soundness`
(`Dialectica/MonotoneND.lean`), then `nn_all_nn` at the `MRealizer` level. It never builds
`classical_to_prenex_extended`'s 85,180-node `negTrans_sound` output (part C0 above), so the
×230 does not bite at ELABORATION: the whole classical metatheorem **type-checks and is
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`** — verified in the umbrella build.
And **NT-stability is gone**: `monotone_nd_soundness`'s premise case takes an `MRealizer` of
the translated premise directly, so no `NTStableD` argument appears anywhere on this route
(`lNts` is unused by it).

**Gate G-C1 / G-C2 (reduce to a numeral): NEGATIVE — kernel `std::bad_alloc` at 12 GB
(65 s wall, 25 s user: memory-bound).** The fused recursion removes negTrans_sound's blow-up,
but the classical bound's kernel REDUCTION still exhausts 12 GB, and did not make the classical
numeral reducible by bare `kernel_rfl`.

**Localised — corrected in the second pass.** The FIRST pass attributed the OOM to "`prenexify`
plus the `¬¬`-combinator leaves realized by `syntactic_soundness`". That was not tested before
being written; the second pass hand-wrote every per-node leaf (`MonotoneNDLeaves.lean`) and the
OOM is unchanged, so the leaves were NOT the cause. What the measurements support (STATUS block
above): `lFinalNoLem` alone through the fused recursion reduces (37 ms); `prenexify` alone OOMs;
a bare chain of k classical `syllogism`s grows ≈ ×5 per syllogism and OOMs at k = 8. The wall is
the nesting depth of `prenexify`'s 134 `syllogism`s under the `¬¬`-combinators' counter sides.
The control still stands: `CGate.extR = monotone_soundness … lFinalExt` — the SAME derivation at
`Allowed.extended`, MFI, **no prenexify, no NT** — reduces to `U = 0`, `V = 5` by `kernel_rfl`
in ≈17 s (`extU5`, `extV5` below, both PASS).

**Reproduction of the OOM (kept out of the file — a file of errors is not a green build):**

    -- `std::bad_alloc` at 12 GB after ≈50 s:
    noncomputable def cmfiRNoLem :=
      clMRealizer lEqxiE lSpremiseE lCmE (fun _ _ h => h.elim)
        lB0_qf lB0_vf lC0_qf lC0_vf lFinalNoLem
    theorem gC1_U : (0 : ℕ) = mfiU_cl lCmE cmfiRNoLem (5 : ℕ) := by kernel_rfl
    theorem gC1_V : (5 : ℕ) = mfiV_cl lCmE cmfiRNoLem (5 : ℕ) := by kernel_rfl
    -- `cmfiRNoLem` itself type-checks (it is what `monotone_general_metatheorem_classical_at`
    -- builds); only the `kernel_rfl` reductions OOM. G-C2 (`lFinalLem`, genuine `Derivable.lem`)
    -- is the same: type-checks, reduction OOMs. Excluded-middle is invisible under the prenexify
    -- cost, exactly as `LemBoundDemo` found for the term route.

The next step is stated in the STATUS block above (a shared/memoised majorant representation);
a `monotone_nd_soundness`-commutation simp set, the first pass's suggestion, would rewrite
leaves that no longer exist.
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
