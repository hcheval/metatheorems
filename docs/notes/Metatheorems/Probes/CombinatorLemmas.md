# Probes/CombinatorLemmas.lean

## module header

## The `pm_*` layer

`headStats` (a DAG walk over the elaborated term, never materialising sharing) lists the
constants `mct_p2` actually contains, transitively through `mct_body` and `mct_descent`:

    pm_enter pm_intro pm_have pm_mp pm_cut pm_inst pm_sym pm_trans pm_rw_at pm_andE₁ pm_andE₂
    pm_cases pm_exI pm_allE_here_cut pm_allI pm_induction seq_id
    qfer_at_nf qfer_no_premise_at_nf Eq.mpr

The `pm_*_eq` / `seq_*_eq` block below shows by `rfl` that all of these except **three** are
compositions of `seq_of_thm`/`seq_mp`/`seq_id` applied to kernel theorems:

1. **`pm_allI` = `seq_allI`** does not reduce to the primitives: it recurses on `Δ` with one
   `seq_mono forall_imp_pull` per hypothesis and a raw `.mp I_comb (.forall_rule …)` at the
   bottom. It *is* Δ-generic in the same sense `seq_mp` is, and `wit_seq_allI` below is the
   commutation lemma — the first use-site of `wall_wapp_sForallRule`.
2. **`pm_induction` = `seq_induction`** — out of scope here (CLAUDE.md Track A item 2).
3. **`Eq.mpr`**, which is not a `pm_*` at all: `anorm`/`anorm_ren`/`prw_norm` are `simp only`
   calls on a `SeqD` goal, so they rewrite the goal *formula* and leave an `Eq.mpr` node in the
   derivation term. `syntactic_soundness_eqmpr` handles it: with the formula equation
   `hB : B = B'` in hand the cast is transparent to `syntactic_soundness` (proof irrelevance
   turns the `Eq.mpr` into the identity once `hB` is substituted). The equation is exactly what
   the same `simp only` set proves at the formula level.

## Non-vacuity controls (run 2026-09-04, scratch files, all EXPECTED TO FAIL — 9/9 did)

Every proof here ends in `rfl` or a closing `simp only`, so the `conv`-without-closer trap
cannot occur; the controls check that the *statements* are not vacuous:

| control | change | outcome |
|---|---|---|
| W1 `capp_sForallRule` | `y.2` replaced by `defM` | `rfl` fails |
| W2 `capp_sExistRule`  | environment not extended by `w.1` | `rfl` fails |
| W3 `capp_sQfer`       | `w` replaced by the default witness | `rfl` fails |
| W4 `wall_wapp_sForallRule` | `x` dropped from the environment | `rfl` fails |
| W5 `wall_forall_imp_pull`  | `x` replaced by `defM` on the right | `rfl` fails |
| W6 `wit_seq_allI` at `Δ = [A₀]` | environment not extended by `x` | unsolved goal |
| I1 `capp_sExistRule`, I2 `capp_sForallRule` | no `termMajorizer_subst_gen` | unsolved goals |
| I3 `wall_forall_imp_pull` | no `wall_wapp_sForallRule` | unsolved goal |

Two further controls were run independently by the supervising session, not by the agent
that wrote this file, and both failed as required: `capp_sQfer` with the incoming witness
`w` replaced on the right by `defM` (the error exhibits the real LHS reading
`Ctx.lookupHat Var.vz.vs (y, w, e)`, so `w` really is transmitted), and `capp_sForallRule`
with `y.2` replaced by `defM`.

## What is NOT done

* **The counter side of `seq_allI`** (`cwit_seq_allI`, the analogue of `wit_seq_allI` for
  `capp`). Not attempted; `capp_sForallRule` is the leaf it would need and it is here.
* **Counter-side lemmas for `forall_ax_vz`/`forall_imp_pull`** — same remark.
* **`sInduction` / `seq_induction`** — out of scope by instruction. What a statement would
  have to look like, for the record: `seq_induction` at `A₀ :: Δ` inducts on
  `A' := A₀↑ →ᶠ A`, so the witness type at depth `k` is
  `wTy (A_k↑ →ᶠ … →ᶠ A₁↑ →ᶠ A)` — a *function* of the context. A Δ-generic lemma therefore
  cannot fix `A`; it must quantify over the family `A_Δ := pack (Δ.map (weakenBy nat)) A`
  and relate `wall (wit Δ (tm (ss (seq_induction base step))) as) k` to a `cm.precM`-driven
  recursion whose *base* is `wit Δ (tm (ss base)) as` and whose *step* is
  `wit Δ (tm (ss step)) as` applied at each stage — i.e. the same `Nat.rec` that `sInduction`
  builds, but with `wit Δ … as` pushed inside both arguments through the `seq_cast`
  (`syntactic_soundness_subst` here handles that cast) and the two `seq_mono`s
  (`forall_mono S_comb`, `forall_imp_push`, each needing its own witness lemma). The
  `Δ = []` case is `sInduction base step` directly. So the shape is "`wit` commutes with
  `Nat.rec`", indexed by the packed formula family; no code was written for it.

`CounterSideProbe.lean` is **not** imported either: it cannot be *built* under a 12 GB cap
(`INTERNAL PANIC: out of memory` inside its Stage B `example`), so its `capp`/`cfst`/`defM`
are re-declared here, definitionally identical, so the counter lemmas compose with its once
the two are merged. Building the chain also needed two one-token post-ι/κ-split fixes
(`@Derivable Empty FEmpty …` → `@Derivable Empty Empty FEmpty …`) in `BoundProbe.lean:84`
and `SeqMpBoundProbe.lean:109`, exactly the site class CLAUDE.md's split note predicts.
