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

## STATE (wrap-up, 2026-09-05) — read this first if continuing

Lane D1 was stopped by the supervisor before G-D2/G-D3, because Lane C found that the
composition combinators of `Dialectica/Monotone.lean` (`MRealizer.syllogism` uses
`hAB.val n e` three times, unshared) cost ×5 per nested syllogism in the kernel; the gates are
to be re-run on top of a sharing fix in that file. Everything below is what the build shows.

### The `mfi_memo` entries (`Dialectica/MonotoneSeq.lean`)

Δ-generic, by structural recursion on the hypothesis context `Δ` (each holds at every `Δ`,
never traversing the sub-derivation): `ms_seq_of_thm`, `ms_seq_mp`, `ms_seq_id`,
`ms_seq_allI`, `ms_seq_induction`. Δ-uniform, no recursion needed (`subst h; rfl` / `rfl`):
`ms_seq_cast` (a `transport` along `congrArg (pack Δ) h`), `ms_seq_mono`. Cast entries:
`ms_eqmp_congr`, `ms_eqmpr_congr` (the formula equation is in the term), plus Lane B's
`monotone_soundness_eqmpr/_eqmp/_subst` tagged in, and the simproc `mfiTransportNF`
(`transport ↦ transportTo` at the kernel-normalised hat type). Exposure entries for casts inside
closed kernel theorems: `ms_forall_ax_vz`, `ms_ex_and_left`; the theorems
`forall_imp_pull/_push`, `exist_imp_pull`, `forall_mono`, `imp_mono_right`, `pair_h` unfold under
the set; `MRealizer.seqAllI_nil/_cons`, `seqInduction_nil/_cons`, `fipComb_eq`, `eipComb_eq`,
`fipushComb_eq`, `fmSComb_eq` unfold the Δ-recursive combinators at a literal `Δ`. One `rfl`
restatement per derived `seq_*`/`pm_*` (`ms_seq_intro` … `ms_pm_qfac`, 43 of them). The 39
equation theorems `monotone_soundness.eq_1 … eq_39` are in the set (never the unfold target —
header item 3 below). All entries are at `monotone_soundness`'s own axiom list
`[propext, Classical.choice, Quot.sound]` (the `#print axioms` block of `MonotoneSeq.lean`);
the Δ-recursive combinators `seqOfThm`/`seqMp`/`seqId`/`seqAllI`/`seqInduction` likewise.

### The two non-vacuity controls (type-correct, wrong right-hand sides; both FAIL)

1. `ms_seq_id` at `Δ = [A, A]`: claim `ms (seq_id (.hs .hz)) = MRealizer.seqId … .hz`
   (the two variables have the same type). `simp only [mfi_memo]; rfl` fails with
   `⊢ MRealizer.seqId eqxi spremise cm HVar.hz.hs = MRealizer.seqId eqxi spremise cm HVar.hz`
   — the entry transmits the variable index.
2. `ms_seq_of_thm` at `Δ = [A]`, `B := A`: claim `= MRealizer.seqOfThm cm [] (iComb cm A)`
   (same type as the real `seqOfThm [] (mp (ms h) (kComb A A))`). `rw [ms_seq_of_thm]; rfl`
   fails with `⊢ MRealizer.seqOfThm cm [A] (ms h) = MRealizer.seqOfThm cm [] (MRealizer.iComb cm A)`.

### G-D1 (a) PASSES — `d2c_is_3`

Lane B's stalling read-out verbatim: the counter transformer of `le_R_pu_of_le_R dxw Tq`
(650 constructors, 3 `Eq.mpr` from one `canorm`) fed the challenge index `3` returns `3`; on
Lane B it was a 12 GB `std::bad_alloc` (`MonotoneLaneB.lean`, finding 3). Kernel ≈ 3.7 s
including the proof term; `4` refuted (`d2c_ne_4`). Open form (`M`, `h` variables).

### G-D1 (b) — what reduces and what does not (all measured 2026-09-05, 12 GB cap)

* **`d1c_is_3` PASSES** (live below): the counter transformer of `le_R_of_le_R_pu dxw Tq` —
  4167 constructors, `pobtain` (`pm_exE`, so `ex_and_left`/`exist_imp_pull`), `pinst`, 4
  `Eq.mpr` — fed the `le_R` challenge `((3, default), ())` returns index `3`. Open form: kernel
  23.8 s. Closed model (`WHyperbolicModel.ofNormed ℝ`, no free variables): kernel 13.5 s,
  **peak RSS 8.4 GB** (sampled by `ps` every 2 s), `4` refuted. After `mfi_push` the goal has
  **no** `monotone_soundness` head left and every cast is a `transportTo` (`mfi_report`
  heads: `mp_form` ×4, `and_proj2` ×4 — cast-free theorems, folded on purpose — and 180
  `transportTo`); the simp proof term alone (`∃ x, x = …` closed by `⟨_, rfl⟩`) kernel-checks
  in 0.25 s. So the pass is complete on this derivation and the cost is the kernel's *value*
  reduction only.
* **The whole `pu_*` statement does NOT reduce** (kept in the `-- WIP:` block below, out of
  the build): `∀q (∀n [d(x,w) ≤ T]ₙ → ∃v [d(x,w) ≤ T]ᵥ)` with the premise consumed through
  `le_R_of_le_R_pu` **and** `le_R_pu_of_le_R`, then `tail` (`forall_ax sq ⟶ exist_ax sq`),
  under `forall_rule`/`and_weak`/`refl0` as `puFinal`. `U`, `V`, `Φ` at `x* = (5,5)` are
  12 GB `std::bad_alloc` / `INTERNAL PANIC: out of memory` in the kernel's reduction of the
  value, at the open form and at the closed model alike. The push itself succeeds (18,437
  objects, 40 cast nodes, all `transportTo`), and the proof term alone kernel-checks in 0.25 s.
  **Association-sensitive**: the same derivation with the inner syllogism re-associated —
  `syllogism (syllogism d1x d2) tail` instead of `syllogism d1x (syllogism d2 tail)` (identical
  after β) — kernel-checked `U = 901` once in 22.3 s (`D1_pu2` scratch) and panicked on the next
  run (`D1_pu`, 57 s), i.e. it sits at the memory cap; the other association panics every time.
  Both proof terms check in 0.25 s. This is the ×5-per-nested-syllogism cost Lane C found.
* **What does NOT explain it (each tested)**: (i) free variables — the closed model panics the
  same way; (ii) `kernel_rfl` vs `Kernel.whnf` — `Kernel.whnf` of the same value reaches the
  literal (23 s, `d1c`) where `Kernel.isDefEq (lit 3) e` panics, so the two kernel entry points
  differ in *memory*, not in what they can compute; `of_decide_eq_true (Eq.refl true)`
  (`Nat.decEq` route) panics too; (iii) a missing entry — no `monotone_soundness` head
  survives; (iv) a definitional gap in the proof term — it checks in 0.25 s.
* **Two instrument bugs found on the way, both fixed in `mfi_disch` below.** (1) `try a; try b`
  parses as `try (a; try b)`: when `q_cons_norm` failed, `canorm` was silently skipped, one
  side condition stayed open as a reflexive-looking `X = X'` (the two sides differ by
  `Term.rename shift` vs `Term.weaken`), the entry did not fire, and the raw `Eq.mpr` reached the
  kernel — that was *the* 12 GB OOM on `d1c` for most of the lane. One `try` per line. (2) Never
  close such a residual with `with_reducible rfl`: the kernel then has to decide `X ≡ X'` through
  the ℚ constants — a second 12 GB OOM, measured.
* **The `a₂` vs `a₂T` mismatch (resolved earlier in the lane, kept for the record)**: with
  `monotone_soundness` passed as an unfold target, simp reduced `ms forall_ax_vz` by smart
  unfolding (Meta ran the K-rule through the `Eq.mp` and recorded no proof), so the `Eq.trans`
  chain ended at `MRealizer.seqAllI [P] …` (`a₂T`) while the goal already showed the fully
  rewritten `MRealizer.seqMp …` (`a₂`); the kernel had to close that definitional gap = re-run
  the K-rule = `std::bad_alloc`. They first differ at the outermost head (`seqAllI` vs `seqMp`);
  the 39 equation theorems + `implicitDefEqProofs := false` remove the gap (header item 3).

### G-D2, G-D3: not attempted (stopped before them).

### Next step for a fresh agent (after Lane C's sharing fix in `Monotone.lean`)

Re-run the `-- WIP:` block below unchanged (`pu_U_5_5` first). If it still panics: the staged
route prototyped in the lane's scratch (`D1_stage.lean`, not committed) — `rfl` equations for the
applied projections of the outer combinators (`mfiU_eq`, `MRealizer.mp_val`,
`syllogism_val_fst/_snd`, `forallRule_val_fst/_snd`, `exportation_val_*`, `ofSRealizer_val`,
`tm_sAndWeak_fst`) rewritten with `implicitDefEqProofs := false`, then a tactic that reifies
the innermost first-order-typed sub-value (`Nat`/`Unit`/`×` after `Kernel.whnf` of its type) to
a literal by kernel deep-whnf, certifies `sub = lit` as its own `Eq.refl` aux theorem and
rewrites it in (reducible `kabstract`) — so each kernel call carries one stage. It ran two
trivial stages; the third candidate was still the whole value because the U read-out goes
through `and_weak`'s `termMajorizer` *as data* and the val-equations did not fire on
`↑(MRealizer.forallRule …)` — the remaining work is the matching of those equations (see the
`after val` goal in `D1_stage.log`: `(((↑(MRealizer.forallRule …`). Do **not** unfold
`MRealizer.*` with plain `simp only [MRealizer.syllogism, …]`: it unfolds (65k objects) and the
definitional steps it records then OOM the kernel.

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

`mfi_disch` is `canorm`'s own normaliser, each stage under its own `try` on its own line (a
stage that closes the goal must not make the next fail with "no goals"; and `try a; try b` on
one line is `try (a; try b)`), then `pack`/`List.map`/`Term.weaken`/`shift` unfolding; the
`Eq.mpr` side condition `pack Δ B = pack Δ' B'` is what `ms_eqmpr_congr` leaves when its
`hB` is not in the term (the aux-theorem `_proof_i` casts `canorm` emits) — proof irrelevance
matches the pattern and the discharger proves the equation the way `canorm` did. The `pack`
stage is for a cast created across a `pintro` (`le_R_of_le_R_pu`'s second `canorm`), whose
two sides are `pack Δ (B →ᶠ ⊥)` and `pack (B :: Δ) ⊥`: true by `pack`'s equations, invisible
to `canorm`. A side condition the discharger does not close must stay open (the entry then
does not fire and `mfi_report` shows the surviving cast) — never `rfl` it shut.

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
