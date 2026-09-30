# Probes/WExtBoundDemo.lean

## module header

**The design point that makes rungs 1, 3 and 4 expressible at all**: `eqAtType xTy s t` *is*
`eq_R (d(s,t)) 0ℝ` *is* `Formula.all Ty.nat <QF body>` — so the metatheorem's own `∀u` **is**
the Cauchy index of the base-type equality, and `Formula.all Ty.nat eqB… = eqAtType xTy …`
holds by `rfl` (`extB_all`, `extC_all`, `parB_all` below). That is `TriangleBoundDemo`'s trick
(there for `le_R_pu`) transposed to `=_X`, and it is what lets an *equality between points* sit
in the premise slot of a metatheorem whose premise variable ranges over `ℕ`.

## MEASURED (2026-09-07) — five findings

The `#eval NestingDepth.report` rows at the bottom of the file print the depths; the numerals
are the `kernel_rfl` theorems in the `Model` section. Everything below was run in this
worktree with `LEAN_NUM_THREADS=2` and the 12 GB `ulimit -v`, with two other lanes building.

1. **Rungs 1 and 2 reduce completely, both sides**, and the numbers move with the space
   majorant: `901` at `nx = 5`, `1273` at `nx = 7`, `900` refuted by `decide` in both cases.
2. **Rung 2 is the project's first bound mined through a space-theory `.premise`.** Every
   earlier space extraction (`TriangleBoundDemo`, `ContentExampleSpace`) consumes
   `Derivable.dist_tri`, a **free constructor**; `wAx` runs `monotone_soundness` through
   `WHyperbolic.W2_at`, whose derivation ends in `Derivable.premise WHyperbolic.W2` (see its
   histogram: `premise~1`) and whose body is a proof-mode script of four `pinst`/`znorm`
   rounds. Composition depth **8** — right at the wall the classical route hits — and it
   reduces in seconds. So neither `.premise` nor the `pm_*` layer is what stops extraction.
3. **Rung 3 splits by side, and the split is sharp.** `VextD = 901` (the witness side, through
   a derivation of depth **≥66** and 3.7 M tree nodes) is kernel-checked in **≈36 s**;
   `mfiU` on the *same* realizer is `std::bad_alloc` at 12 GB after **≈100 s**. That is the
   witness/counter sidedness the project measured for the term route (`ConjBoundDemo`'s `V`
   reduces while its `U` stalls) reproduced under MFI, on a real space theorem.
4. **Depth is not by itself the predictor it was taken to be.** `Probes/NestingDepth.lean`
   calibrates the MFI wall at composition depth ≈ 9 from the classical `syllogism` chain, and
   `wExt` at depth ≥66 nonetheless reduces on the witness side in 36 s. The ×5-per-level cost
   is charged on the **counter** side (`MRealizer.syllogism` uses `hAB` three times there and
   `hBC` twice); the witness side composes without duplication. So a depth figure bounds the
   counter side and says little about the witness side.
5. **What blocks rung 3's `U` is the ℝ order package, and the extensionality argument adds
   nothing to it.** This was checked rather than assumed, and the check corrected the guess.
   `dist_W_mono_left` — which `W_ext_left` merely composes with `mul_eq_zero_R_core`,
   `le_R_of_eq_R_core` and `eqX_of_dist_le_zero_imp` — is **itself** `dag 48141 / tree 105226 /
   DEPTH 38`, the same figures as `W_ext_left` (both budget-capped at 250 000 `Expr` nodes).
   So the depth is already there one rung below, inside `leRt = le_R_trans_core`, which
   `Probes/NestingDepth.lean` measures at depth ≥23 standing alone. By contrast `W2_at` — the
   (W2) axiom instantiated at four abstract terms, with no `≤ℝ` anywhere — is `dag 252 /
   tree 1478 / DEPTH 3`, and rung 2 built on it reduces. **The `≤ℝ` package is the cost, not
   `W`**: every W-hyperbolic statement phrased with `≤ℝ` inherits `le_R_trans_core`'s
   telescope, and every one phrased with `=ℝ` (i.e. (W2), (W3)) does not.

Reproduction of the negative measurement (it cannot live in the file — a file of errors is not
a green build). Paste into a scratch module importing this one:

```lean
theorem UextD : (0 : ℕ) = mfiU (triCm M h) (rExtD M h) (qs M 5 5 5) := by
  unfold mfiU rExtD
  mfi_push [wExtD, wrap, wrapW, extInnerD]
  kernel_rfl
```

`0` is only the first candidate; the value is unknown, because a `kernel_rfl` that OOMs
reports nothing about it. Nine candidates (`0`–`6`, `901`) were tried in one module and the
module died at 12 GB, so the failure is not a mis-guessed constant.

6. **`NestingDepth`'s depth does not discriminate *inside* the ℝ layer, and a conjecture made
   from it was refuted the same night.** The first draft of this header guessed that rung 4's
   depth of ≥62 came from `eq_R_trans_core`'s `eqR_tail`/`eqR_le`/`eqR_strict` squeeze, and
   proposed a squeeze-free `=ℝ`-transitivity as the fix. Measuring the components refutes it:

   | declaration | dag | tree | DEPTH | capped? |
   |---|---|---|---|---|
   | `WHyperbolic.W2_at` | 252 | 1478 | **3** | no |
   | `WHyperbolic.W4_at` | 491 | 2944 | **7** | no |
   | `le_R_antisymm_core` | 48124 | 61285 | ≥23 | yes |
   | `dist_nonneg` | 46734 | 71961 | ≥26 | yes |
   | `clamp01_congr_R` | 47952 | 61026 | ≥35 | yes |
   | `abs_sub_eq_zero_R` | 45305 | 128042 | ≥36 | yes |
   | `eq_R_trans_core` | 47885 | 110275 | ≥37 | yes |
   | `mul_eq_zero_R_core` | 45195 | 101685 | ≥37 | yes |
   | `WHyperbolic.dist_W_mono_left` | 48141 | 105226 | ≥38 | yes |

   `clamp01_congr_R` is a **slack-free single-index** lemma written in this same pass —
   `clamp01_Q_lip` and one `le_lt_Q_trans`, no estimate, no telescope — and it still reports
   ≥35. Every row that reaches the ℚ constants hits the walk's 250 000-`Expr` budget and lands
   in the same 23–38 band, so those figures are lower bounds produced by the *cap*, not
   measurements of the lemmas. The only discriminating rows are the uncapped ones, and they
   say what finding 5 says: the space axioms are cheap (3 and 7) and everything downstream of
   ℚ is not separable by this instrument.

   Consequence for the next lane: **do not pick an ℝ-layer target by its `NestingDepth`
   figure.** The empirical witness/counter split (finding 3) is the only signal currently
   available, and it is cheap to run — a `mfiV` and a `mfiU` at a non-trivial witness, ≈40 s
   and ≈100 s-to-OOM respectively.

## What this suggests for the next lane

The witness side is *not* where the wall is, at any depth reached here: both rung 3 and rung 4
give `901` in ~35 s through derivations of depth ≥66 and ≥62. Every failure measured tonight
is on the counter side, where `MRealizer.syllogism` re-evaluates `hAB` three times and `hBC`
twice per level. So the ×5-per-level sharing problem (`ARCHITECTURE.md` §14.7, Lane D1's memo
direction) is the whole remaining obstacle for space theorems — not induction, not the proof
mode, not `.premise`, not casts, and not the extensionality argument.

## Honest limits

Nothing here proves a *new* mathematical fact — the object-level content is
`WHyperbolicLemmas.lean`'s, and this file only wraps it in the metatheorem's shape and turns
the crank. What it establishes is which of those theorems the extraction machinery can
currently see through, and the ladder is arranged so that the answer is a rung number rather
than a yes/no.
