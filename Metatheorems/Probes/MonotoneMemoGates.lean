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
layer and the casts. This file runs the gates with the instrument `mfi_push` (below) +
`kernel_rfl` (`Probes/MonotoneLaneB.lean`).

**Result (state at wrap-up, 2026-09-05).** Lane D1 was stopped before G-D2/G-D3 (the
composition combinators cost ×5 per nested syllogism; the gates are to be re-run on top of a
sharing fix in `Dialectica/Monotone.lean`). G-D1 (a) passes (`d2c_is_3`: the counter transformer
of `le_R_pu_of_le_R`, a 12 GB `std::bad_alloc` in Lane B, returns `3`), and G-D1 (b) partly
passes (`d1c_is_3` for `le_R_of_le_R_pu`); the whole `pu_*` statement does not reduce and is
kept in the `-- WIP:` block below, out of the build. The instrument is `mfi_push`
(`simp … only [mfi_memo, …]`, then `kernel_rfl`). The `mfi_memo` entry list, the two
non-vacuity controls, the tested non-explanations, the next-step notes and the three things the
instrument needed are in the notes.

`Elab.async` is off in this file: two 12 GB kernel reductions in parallel look like one OOM.
-/

set_option Elab.async false

namespace Metatheorems
namespace MonotoneMemoGates

open Formula ProofMode
open MonotoneLaneB (D qTy rT dxw Tq mr xs XM concT concT_pe concT_vf sq tail d2 dummy)
open TriangleBoundDemo (triCm)

-- Tools

/-- The discharger for the `Eq.mpr` side conditions `pack Δ B = pack Δ' B'`: the normaliser
that produced the cast (`canorm`), each stage under its own `try` on its own line — `try a;
try b` is `try (a; try b)`, which skipped `canorm` whenever `q_cons_norm` failed — then
`pack`/`List.map` unfolding (a cast created across a `pintro`) and `Term.weaken`/`shift`
unfolding (`canorm` dissolves `shift` on the side it rewrote, and the other side still says
`weaken`). No reflexivity closer, deliberately: see the header. -/
macro "mfi_disch" : tactic =>
  `(tactic| (try q_cons_norm
             try canorm
             try simp only [ProofMode.pack, List.map, Term.weaken, Term.Renaming.shift]))

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

-- G-D1 (a): the read-out that stalled Lane B — the counter transformer of `le_R_pu_of_le_R`

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

-- G-D1 (b): `le_R_of_le_R_pu` — the other conversion, `pobtain`/`pinst`, 4 `Eq.mpr`

theorem concT_pu : concT.isPurelyUniversal = true := rfl

/-- `le_R_pu dxw Tq →ᶠ le_R dxw Tq` — 4167 constructors, 4 `Eq.mpr`. -/
def d1x : D [qTy] (le_R_pu dxw Tq →ᶠ le_R dxw Tq) := le_R_of_le_R_pu dxw Tq

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- The majorant of the default witness of `le_R_pu dxw Tq`. -/
noncomputable def wpu : Ty.interpret (XM M) (wTy (le_R_pu dxw Tq)).hat :=
  termMajorizer (triCm M h) (defaultWTerm (le_R_pu dxw Tq)) 0 (xs M, ())

/-- The majorant of the default counter of `le_R dxw Tq`. -/
noncomputable def cle : Ty.interpret (XM M) (cTy (le_R dxw Tq)).hat :=
  termMajorizer (triCm M h) (defaultCTerm (le_R dxw Tq)) 0 (xs M, ())

/-- The challenge on `le_R dxw Tq`: the `∃`-witness index `3`, the rest default. -/
noncomputable def cnt3le : Ty.interpret (XM M) (cTy (le_R dxw Tq)).hat :=
  (((3 : ℕ), (cle M h).1.2), ())

/-- The counter side of `le_R_of_le_R_pu dxw Tq` at challenge `3`: the index handed back to
`le_R_pu`. -/
noncomputable def d1c : ℕ :=
  (((mr M h d1x).val 0 (xs M, ())).2 (wpu M h) (cnt3le M h)).1

/-- **G-D1 (b), the conversion alone.** The index passes through `pobtain`/`pinst` and the
four casts: `3`. Kernel 23.8 s (open form); 13.5 s and 8.4 GB peak at the closed model
`WHyperbolicModel.ofNormed ℝ`. -/
theorem d1c_is_3 : (3 : ℕ) = d1c M h := by
  unfold d1c mr d1x
  mfi_push [le_R_of_le_R_pu]
  kernel_rfl

theorem d1c_ne_4 : (4 : ℕ) ≠ d1c M h := by
  rw [← d1c_is_3 M h]; decide

end Model

-- G-D1 (b), the whole statement — NOT reducing (12 GB), kept out of the build

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

/-- The other association of the same proof: `syllogism (syllogism d1x d2) tail`. Reduced once
in 22.3 s and panicked on the next run — at the memory cap, not below it. -/
def puInnerR : D [qTy] (Formula.all Ty.nat concT →ᶠ Formula.ex Ty.nat concT) :=
  .syllogism (.syllogism d1x d2) tail

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- `x* = ((7,5),((5,5), λ_.1))`. -/
noncomputable def xs7 : Ty.interpret (XM M) qTy.hat :=
  (((7 : ℕ), (5 : ℕ)), (((5 : ℕ), (5 : ℕ)), fun _ => (1 : ℕ)))

/- -- WIP: G-D1 (b), the whole statement. Every theorem below is a 12 GB `std::bad_alloc` /
`INTERNAL PANIC: out of memory` in the kernel's reduction of the value (2026-09-05), at the
open form and at the closed model alike; the push succeeds (18,437 objects, 40 casts, all
`transportTo`, no `monotone_soundness` head left) and the proof term alone kernel-checks in
0.25 s. See the header. Re-run unchanged after the sharing fix in `Dialectica/Monotone.lean`.

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

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms d2c_is_3
#print axioms d2c_ne_4
#print axioms d1c_is_3
#print axioms d1c_ne_4

end MonotoneMemoGates
end Metatheorems
