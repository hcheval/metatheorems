/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneSeq
import Metatheorems.Probes.MonotoneLaneB
import Metatheorems.Probes.MonotoneMCT

/-!
# Gates for the `mfi_memo` programme (MFI Lane D1)

`Dialectica/MonotoneSeq.lean` pushes `monotone_soundness` through the proof-mode packaging
layer and the casts. This file runs the three gates the lane was given, with the instrument
`mfi_push` (below) + `kernel_rfl` (`Probes/MonotoneLaneB.lean`).

## STATE (WIP commit, 2026-09-05) — read this first if continuing

* **G-D1 (a) PASSES** (`d2c_is_3`): Lane B's stalling read-out verbatim — the counter
  transformer of `le_R_pu_of_le_R dxw Tq` (3 `Eq.mpr` from one `canorm`) fed the challenge
  index `3` returns `3`; on Lane B it was a 12 GB `std::bad_alloc` (`MonotoneLaneB.lean`,
  finding 3). Kernel ≈ 3.7 s including the proof term; `4` refuted.
* **G-D1 (b) NOT YET** (`pu_*`, in the `-- WIP:` block): the premise-slot statement
  `∀q (∀n [d(x,w) ≤ T]ₙ → ∃v [d(x,w) ≤ T]ᵥ)` with the premise converted through
  `le_R_of_le_R_pu` (4167 constructors, `pobtain` = `pm_exE`, `pinst`, 4 `Eq.mpr`) **and**
  `le_R_pu_of_le_R`. First attempt: 12 GB `std::bad_alloc` at build. Not localised. What to
  do next: the bisection recipe below (crash-safe file log; `mfi_report`; then the
  proof-term walk with `addDecl` per `congrArg`/`Eq.trans` node — the scratch tool that found
  item 3 below). Suspects, in order: (i) a cast shape not in the set yet (`pm_exE`'s
  `seq_allI` at `A →ᶠ weakenBy ρ B` puts `exist_imp_pull` = `eipComb` in the goal — it
  unfolds via the attribute, but its `forall_ax_vz` sits under `pair_h`; check the
  `mfi_report` heads are empty); (ii) a definitional gap of the kind in item 3 from another
  rfl-lemma (`ms_seq_exE` is not rfl; `ms_pm_exE` is an application — check with
  `implicitDefEqProofs := false` that every step has a proof); (iii) the kernel's own
  reduction of `MRealizer.existRule`'s `cast (dialecticaCounter_weaken …)`.
* **G-D2, G-D3 not attempted yet.** The reachable-definition lists to unfold are in the
  scratch (`D1_reach.out`): `final` reaches 289 derivation defs, `mct_p2` 60.
* **Diagnosis of the earlier `a₂` vs `a₂T` mismatch (resolved, item 3 below):** with
  `monotone_soundness` passed as an unfold target, simp reduced `ms forall_ax_vz` by smart
  unfolding — Meta ran the K-rule through the `Eq.mp` and recorded no proof; the `Eq.trans`
  chain therefore ended at `seqAllI [P] …` (`a₂T`) while the goal already showed the fully
  rewritten `seqMp …` (`a₂`), and the kernel had to close that definitional gap = re-run
  the K-rule = `std::bad_alloc`. Fixed by the 39 equation theorems + `implicitDefEqProofs :=
  false`.

## G-D1 — `le_R_pu_of_le_R` (3 `Eq.mpr` from one `canorm`) is LIVE.  (a) PASSES.

## The instrument, and the three things that had to be true for it to work

`mfi_push` is `simp (config := { implicitDefEqProofs := false }) (disch := mfi_disch) only
[mfi_memo, <the derivation's definitions>]`, then `kernel_rfl`. Each clause was forced by a
measured failure (2026-09-05, all on `pintro h; pforall; pexact h` over `le_R dxw Tq`, the
smallest derivation that fails without it):

1. **`transportTo`, not `transport`.** With plain `MRealizer.transport` the kernel's K-rule
   check compares `Ty.interpret X (wTy B).hat` with `… (wTy B').hat` *argument-first*, i.e.
   `B ≡ B'`, the formula before and after the normalisation — `std::bad_alloc`. Through
   the reduced hat type `τ` (a `Ty` constructor tree computed by the kernel's `whnf`,
   `tyNF`) every K-check is 0 ms (measured per node with `Kernel.isDefEq`). `Meta.reduce`
   does *not* reduce `wTy _` — the first version of the simproc handed the transport
   `τ := wTy B'` verbatim and nothing changed.
2. **The casts inside the closed kernel theorems must be reached.** `forall_imp_pull` (what
   `seq_allI` inserts once per hypothesis) contains `forall_ax_vz`, an `Eq.mp` along
   `(A.renameF (ext shift)).subst0 (var vz) = A`. Folded as `ms forall_imp_pull` the kernel
   K-checks that equation — linear, but through `le_Q_dec`/`cauchyfy` per hypothesis under
   a `∀` — `std::bad_alloc`. Hence `seqAllI`/`seqInduction` unfold at a literal `Δ`, the
   `*Comb`s unfold to their theorem, the theorems unfold, and `ms_forall_ax_vz` is the entry.
3. **Every step propositional.** `simp only [monotone_soundness]` reduces by *smart
   unfolding*: at `ms (Eq.mp e d)` Meta runs the K-rule through the cast once, records no
   proof, and the kernel — re-running the definitional step — dies at the same cast even with
   every entry in place (bisected node by node with `addDecl`: the failing node was a
   `congrArg` whose two endpoints differed by exactly that definitional gap). The 39
   equation theorems of `monotone_soundness` are in the set instead, and
   `implicitDefEqProofs := false` makes simp emit their instances; the same derivation then
   kernel-checks in milliseconds. `MRealizer.transport_rfl` is likewise kept **out** of the
   set (its implicit `B'` unifies with `B` at default transparency — the same comparison).

`mfi_disch` is `canorm`'s own normaliser, each stage under `try` (a stage that closes the
goal must not make the next fail with "no goals"); the `Eq.mpr` side condition `pack Δ B =
pack Δ' B'` is what `ms_eqmpr_congr` leaves when its `hB` is not in the term (the aux-theorem
`_proof_i` casts `canorm` emits) — proof irrelevance matches the pattern and the discharger
proves the equation the way `canorm` did.

`Elab.async` is off in this file: two 12 GB kernel reductions in parallel look like one OOM.
-/

set_option Elab.async false

namespace Metatheorems
namespace MonotoneMemoGates

open Formula ProofMode
open MonotoneLaneB (D qTy rT dxw Tq mr xs XM concT concT_pe concT_vf sq tail d2 dummy)
open TriangleBoundDemo (triCm)

-- ============================================================================
-- Tools
-- ============================================================================

/-- The discharger for the `Eq.mpr` side conditions `pack Δ B = pack Δ' B'`: the normaliser
that produced the cast (`canorm`), each stage under `try` — a stage that closes the goal must
not make the next one fail with "no goals". -/
macro "mfi_disch" : tactic => `(tactic| (try q_cons_norm; try canorm))

/-- **The pass.** `mfi_memo` with explicit proofs for every step (`implicitDefEqProofs :=
false` — a definitional step is one the kernel must re-run, and at a cast that is the K-rule
through the ℚ constants), the `Eq.mpr` side conditions discharged by `mfi_disch`. Extra
arguments are the derivation's own definitions to unfold. Never pass `monotone_soundness`
itself (see the header, item 3). -/
macro "mfi_push" : tactic =>
  `(tactic| simp (config := { implicitDefEqProofs := false }) (disch := mfi_disch)
      only [mfi_memo])
macro "mfi_push" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { implicitDefEqProofs := false }) (disch := mfi_disch)
      only [mfi_memo, $ts,*])

open Lean Meta Elab Tactic in
/-- Read-out of a goal's shape: for every `monotone_soundness … d` the head constant of `d`
(a non-empty list means the pass stopped somewhere); the number of cast nodes;
`transport`/`transportTo`/`seqInduction` occurrences (tree-counted); `numObjs`. -/
elab "mfi_report" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let rec visit (e : Expr) (acc : Std.HashMap String Nat × Nat) : Std.HashMap String Nat × Nat :=
    let acc :=
      match e.getAppFn with
      | .const fn _ =>
        if fn == ``Metatheorems.monotone_soundness && e.getAppNumArgs == 13 then
          let d := e.getAppArgs[12]!
          let hd := match d.getAppFn with
            | .const dn _ => dn.toString
            | .fvar _ => "fvar" | .mvar _ => "mvar" | .lam .. => "lam" | .letE .. => "let"
            | .proj .. => "proj" | _ => "other"
          (acc.1.insert hd ((acc.1.getD hd 0) + 1), acc.2)
        else if fn == ``Eq.mpr || fn == ``Eq.mp || fn == ``Eq.rec then (acc.1, acc.2 + 1)
        else if fn == ``Metatheorems.MRealizer.transport
            || fn == ``Metatheorems.MRealizer.transportTo
            || fn == ``Metatheorems.MRealizer.seqInduction || fn == ``cast then
          let hd := "@" ++ fn.toString
          (acc.1.insert hd ((acc.1.getD hd 0) + 1), acc.2)
        else acc
      | _ => acc
    match e with
    | .app f a => visit a (visit f acc)
    | .lam _ t b _ => visit b (visit t acc)
    | .forallE _ t b _ => visit b (visit t acc)
    | .letE _ t v b _ => visit b (visit v (visit t acc))
    | .mdata _ b => visit b acc
    | .proj _ _ b => visit b acc
    | _ => acc
  let (hs, c) := visit g ({}, 0)
  let n ← g.numObjs
  logInfo m!"mfi_report: numObjs = {n}; cast nodes = {c}; heads = {hs.toList}"

set_option linter.unusedTactic false

-- ============================================================================
-- G-D1 (a): the read-out that stalled Lane B — the counter transformer of `le_R_pu_of_le_R`
-- ============================================================================

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- The majorant of the default witness of `le_R dxw Tq`. -/
noncomputable def wdef : Ty.interpret (XM M) (wTy (le_R dxw Tq)).hat :=
  termMajorizer (triCm M h) (defaultWTerm (le_R dxw Tq)) 0 (xs M, ())

/-- The challenge: index `3` on the conclusion `le_R_pu dxw Tq`. -/
def cnt3 : Ty.interpret (XM M) (cTy (le_R_pu dxw Tq)).hat := ((3 : ℕ), ((), ()))

/-- Lane B's `d2c`, verbatim: the counter side of `le_R_pu_of_le_R dxw Tq` at challenge `3`,
first component of the `∃`-witness handed back to `le_R`. -/
noncomputable def d2c : ℕ :=
  (((mr M h d2).val 0 (xs M, ())).2 (wdef M h) (cnt3 M)).1.1

/-- **G-D1 (a).** The index passes through: `3`. Kernel ≈ 3.7 s (with the proof term). -/
theorem d2c_is_3 : (3 : ℕ) = d2c M h := by
  unfold d2c mr d2
  mfi_push [le_R_pu_of_le_R]
  kernel_rfl

theorem d2c_ne_4 : (4 : ℕ) ≠ d2c M h := by
  rw [← d2c_is_3 M h]; decide

end Model

-- ============================================================================
-- G-D1 (b): the premise-slot statement, the premise converted through BOTH conversions
-- ============================================================================

theorem concT_pu : concT.isPurelyUniversal = true := rfl

/-- `le_R_pu dxw Tq →ᶠ le_R dxw Tq` — 4167 constructors, 4 `Eq.mpr`. -/
def d1x : D [qTy] (le_R_pu dxw Tq →ᶠ le_R dxw Tq) := le_R_of_le_R_pu dxw Tq

/-- `∀n [d(x,w) ≤ T]ₙ → ∃v [d(x,w) ≤ T]ᵥ`, the premise consumed through `le_R_of_le_R_pu`,
`le_R_pu_of_le_R`, then instantiated at `sq` and generalised. -/
def puInner : D [qTy] (Formula.all Ty.nat concT →ᶠ Formula.ex Ty.nat concT) :=
  .syllogism d1x (.syllogism d2 tail)

def puInnerW : D [qTy] (Formula.weakenBy qTy dummy →ᶠ
    (Formula.all Ty.nat concT →ᶠ Formula.ex Ty.nat concT)) :=
  .mp puInner (.exportation .and_weak)

/-- `⊢ ∀q ( ∀n [d(x,w) ≤ T]ₙ → ∃v [d(x,w) ≤ T]ᵥ )`. -/
def puFinal : D [] (Formula.all qTy (Formula.all Ty.nat concT →ᶠ Formula.ex Ty.nat concT)) :=
  .mp .refl0 (.forall_rule puInnerW)

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- `x* = ((7,5),((5,5), λ_.1))`. -/
noncomputable def xs7 : Ty.interpret (XM M) qTy.hat :=
  (((7 : ℕ), (5 : ℕ)), (((5 : ℕ), (5 : ℕ)), fun _ => (1 : ℕ)))

/- -- WIP: G-D1 (b). With `d1x` (`le_R_of_le_R_pu`, 4167 constructors, `pobtain` = `pm_exE`,
`pinst`, 4 `Eq.mpr`) in the premise path this is a 12 GB `std::bad_alloc` at the first attempt
(2026-09-05); not yet localised — see the header, "State". The (a) read-out through
`le_R_pu_of_le_R` alone is live above.

theorem pu_U_5_5 : (901 : ℕ) = mfiU (triCm M h) (mr M h puFinal) (xs M) := by
  unfold mr puFinal puInnerW puInner d1x d2 tail
  mfi_push [le_R_of_le_R_pu, le_R_pu_of_le_R]
  kernel_rfl

theorem pu_V_5_5 : (901 : ℕ) = mfiV (triCm M h) (mr M h puFinal) (xs M) := by
  unfold mr puFinal puInnerW puInner d1x d2 tail
  mfi_push [le_R_of_le_R_pu, le_R_pu_of_le_R]
  kernel_rfl

theorem pu_phi_5_5 : (901 : ℕ) = (monotone_general_metatheorem_at_gen M.eqXInterp M.spremise
    (triCm M h) concT_pu concT_vf concT_pe concT_vf puFinal).val (xs M) := by
  unfold monotone_general_metatheorem_at_gen puFinal puInnerW puInner d1x d2 tail
  simp only [Subtype.val, coreBound]
  mfi_push [le_R_of_le_R_pu, le_R_pu_of_le_R]
  kernel_rfl

theorem pu_U_7_5 : (1273 : ℕ) = mfiU (triCm M h) (mr M h puFinal) (xs7 M) := by
  unfold mr puFinal puInnerW puInner d1x d2 tail
  mfi_push [le_R_of_le_R_pu, le_R_pu_of_le_R]
  kernel_rfl

theorem pu_U_5_5_ne_900 : (900 : ℕ) ≠ mfiU (triCm M h) (mr M h puFinal) (xs M) := by
  rw [← pu_U_5_5 M h]; decide
theorem pu_U_5_5_ne_902 : (902 : ℕ) ≠ mfiU (triCm M h) (mr M h puFinal) (xs M) := by
  rw [← pu_U_5_5 M h]; decide
theorem pu_U_7_5_ne_901 : (901 : ℕ) ≠ mfiU (triCm M h) (mr M h puFinal) (xs7 M) := by
  rw [← pu_U_7_5 M h]; decide
-/

end Model

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms d2c_is_3
#print axioms d2c_ne_4

end MonotoneMemoGates
end Metatheorems
