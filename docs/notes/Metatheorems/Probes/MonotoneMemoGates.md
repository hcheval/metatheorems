# Probes/MonotoneMemoGates.lean

## module header

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
