# Probes/MonotoneLaneB.lean

## module header

**RESULT: MIXED, and sharper than pass/fail.** Three findings, each measured:

1. **The proof-mode layer is transparent to `monotone_soundness` — in the kernel.** A
   proof-mode derivation (`pmFinal`: `pforall`/`pintro`/`pinst`/`pexists`/`pexact`, i.e.
   `pm_allI`, `pm_intro`, `pm_inst`, `pm_exI`, `seq_id`; **449 constructors**, no `Eq.mpr`
   in its transitive closure) yields `U = V = 901` at `x* = (5,5)`, the *counter side*
   included, kernel-checked in **≈2.2 s** — and the same over the large `triB` matrix
   (`pmFinalBig`, 449 constructors, `U` 1.75 s, `V` 0.76 s), and through
   `monotone_general_metatheorem_at` (`Φ = 901`, 2.06 s). The term route never produced a
   counter-side numeral from any proof-mode derivation.
   **The instrument matters**: the same `U` by bare `rfl` (`Meta.isDefEq`) is a
   200 000-heartbeat `whnf` timeout whose profile is `Ty.casesOn ↦ 23488`, `Eq.rec ↦ 1331`,
   `termMajorizer ↦ 140`, `monotone_soundness ↦ 86` — type-level `Ty.interpret`
   recomputation with **no cache**, because the model `M`, `h` are free variables
   (`Meta.whnf` caches closed terms only). The kernel caches by structure. `kernel_rfl`
   below assigns `Eq.refl` and lets the kernel alone decide; its non-vacuity control is
   that the kernel **rejects** `900` (`e1_U_900`, run live: "(kernel) declaration type
   mismatch", 1.8 s).
2. **`dist_tri_chain` itself is unreachable by any numeric bound, structurally.** Its
   formula `le_R f g = ¬ lt_R g f` has `wTy = ((nat ×ₜ unit) →ₜ unit) ×ₜ ((nat ×ₜ unit) →ₜ
   unit →ₜ unit)`: every component is `unit`-valued, so no projection of its monotone
   realizer is a number, and a `unit`-valued `rfl` closes by structure eta without
   reducing anything. The brief's literal design (`finalA`: the chained inequality in the
   premise slot, *derived* by `dist_tri_chain` and weakened away) therefore reduces —
   `V = 901`, `U = 0` — **by laziness**: `whnf` never enters `dist_tri_chain`'s realizer,
   exactly as `TriangleBoundDemo.triUncUtB_is_zero` never entered `dist_tri`. Recorded, not
   claimed as a test of anything.
   The design that *does* route a number through the content is transitivity: premise
   `∀n [(d(x,y)+d(y,z))+d(z,w) ≤ T]ₙ`, conclusion `∃v [d(x,w) ≤ T]ᵥ`, via `dist_tri_chain`
   and `le_R_trans_core` (`final` below; it elaborates). There the counter of `le_R f g`
   **is** an index (`cTy (le_R f g) = (nat ×ₜ unit) ×ₜ unit`), and `U` is the index at which
   the premise inequality must be known — computed *through* `le_R_trans_core`'s engine.
3. **That design does not reduce, and the blocker is localised to one line of one lemma —
   not to the proof mode, not to induction, not to `le_R_trans_core`, not to
   `dist_tri_chain`.** The smallest piece, `le_R_pu_of_le_R` (`d2`: 650 constructors,
   DAG 622, five `pm_*`, **one `Eq.mpr` from `canorm`**), fed a challenge index `3` on
   its counter side:
   * kernel (`kernel_rfl`): **`std::bad_alloc` at the 12 GB cap after ≈1 min**;
   * `Meta` (`rfl`, `diagnostics.threshold 5`): timeout; profile `Eq.rec ↦ 187521`,
     `Term.rec ↦ 35530`, `Term.rename ↦ 30410`, `List.rec ↦ 13412`, `Var.rec ↦ 13381`,
     `Renaming.ext ↦ 12814`, `Term.subst ↦ 5045`, then **the ℚ constants being unfolded**
     — `Term.add ↦ 413`, `monus ↦ 248`, `pd ↦ 248`, `triag ↦ 205`, `sg_bar ↦ 156`,
     `inv_triag ↦ 105`, `fst_pair ↦ 81`, `le_Q_dec ↦ 35`, `rat_sign ↦ 26` … — with
     `monotone_soundness ↦ 38` (38 of 650 nodes reached).
   * the discriminating control: the **same script without `canorm`** does not elaborate —
     `pexact hn` is itself a `whnf` timeout (19.7 s). So the cast's two sides are not
     cheaply definitional: the equation is a `closed_subst` normalisation
     (`Term.subst`/`rename` through `cauchyfy`, the 1.8M-node delta expansion CLAUDE.md's
     "Build cost" section documents), which the lemma proves *without* computing. The
     kernel's K-rule reduction of `Eq.mpr` has to check the two formulas definitionally
     equal — i.e. **redo the computation the `closed_subst` lemma was written to avoid.**
   Nothing about the monotone interpretation is at fault: the profile is renaming and
   substitution traffic on the *formula indices*, before the recursion has done anything.
   The fix is not in this lane: an `Eq.mpr`-commutation lemma for `monotone_soundness`
   (the `syntactic_soundness_eqmpr` shape, `Probes/CombinatorLemmas.lean`) applied by
   `simp` with the equation *given*, or `canorm`-free proof-mode lemmas. Both are the
   Track A programme one level up.

## Sizes (`derivSizeA` = constructor count as a tree; `reportD` = pointer-identity DAG)

| derivation | tree | DAG | `Eq.mpr` in closure | note |
|---|---|---|---|---|
| `pmFinal` (E1) | 449 | see `#eval` | 0 | proof mode, matrix `u =₀ u` |
| `pmFinalBig` (E3) | 449 | see `#eval` | 0 | proof mode, matrix `triB` |
| `d2 = le_R_pu_of_le_R` | 650 | 622 | 1 (`canorm`) | the blocker |
| `d1 = le_R_of_le_R_pu` | 4167 | 3979 | 1 (`canorm`) | |
| `tr = le_R_trans_core` | — | — | 0 itself; many below | **OOM at 12 GB while being BUILT** |
| `chain = dist_tri_chain` | — | — | 0 itself | `#eval derivSizeA` OOM at 12 GB |

The OOMs are a fact about *strict runtime construction*: `Derivable`'s constructors store
their formulas, and the proof-mode combinators compute `Formula.substF`/`weakenBy` of
formulas containing `cauchyfy` at every node. The kernel is lazy and is not bound by this
(finding 1); it is bound by finding 3.

`walk` (the transitive constant walk) on `final`: **442** reachable definitions,
`pm_induction` in `leR_tail` and `pow2neg_Q_le_add_all`, raw `Derivable.induction` in the
ℕ-arithmetic lemmas, `Eq.mpr` in `le_R_pu_of_le_R`, `le_R_of_le_R_pu`, `leR_tail`,
`leR_le`, `leR_strict`, `le_R_all`, `le_R_of_all`, `le_R_add_mono_l_core` and every
`*_inst`/`*_nf` lemma.

## The stalling declarations (NOT in the file — a file of errors is not a green build)

    -- kernel: std::bad_alloc at 12 GB after ≈1 min
    noncomputable def d2c : ℕ :=
      (((mr M h d2).val 0 (xs M, ())).2 (wdef M h (le_R dxw Tq) (xs M, ())) (cnt3 M)).1.1
    theorem d2c_is_3 : (3 : ℕ) = d2c M h := by kernel_rfl

    -- Meta: (deterministic) timeout at `whnf`, profile in finding 3
    set_option diagnostics true in set_option diagnostics.threshold 5 in
    example : (3 : ℕ) = d2c M h := by unfold d2c; rfl

    -- the discriminating control: `le_R_pu_of_le_R`'s script without `canorm`
    def d2nc : D [qTy] (le_R dxw Tq →ᶠ le_R_pu dxw Tq) := by
      pmode; pintro h; pforall; pintro hn; papply h; pexists (.var .vz); pexact hn
    -- pexact: (deterministic) timeout at `whnf` (19.7 s)

    -- Meta `rfl` on E1's counter side (the kernel does it in 2.2 s):
    set_option diagnostics true in set_option diagnostics.threshold 5 in
    theorem e1_U_meta : (901 : ℕ) = mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
      have hval : … = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
      …  -- timeout at `whnf`; Ty.casesOn ↦ 23488, Eq.rec ↦ 1331, termMajorizer ↦ 140,
         -- monotone_soundness ↦ 86, Term.rename ↦ 66, MRealizer.syllogism ↦ 35

## Cost (kernel type-checking, `lake env lean -D profiler=true`, 2026-09-05, scratch runs;
## in the committed file the seven `kernel_rfl` theorems type-check in 0.7–1.7 s each)

| theorem | kernel |
|---|---|
| `e1_U` (proof mode, counter side, 449 constructors) | 2.22 s |
| `e1_U_900` control (rejected) | 1.76 s |
| `e3_U` (proof mode over `triB`) | 1.75 s |
| `e3_V` | 0.76 s |
| `e1_phi` (through `monotone_general_metatheorem_at`) | 2.06 s |
| `e2_U`, `e2_V` (`triFinal`, raw constructors, Meta `rfl` + `decide`) | ≈120–140 ms elab |
| `a_V` (`finalA`, lazy) | 170 ms elab |
| `a_U` (`finalA`, lazy; by `rfl` in the scratch) | 5.9 s Meta + 1.6 s kernel |
