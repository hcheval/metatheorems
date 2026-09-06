/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Monotone
import Metatheorems.Probes.ConjBoundDemo

/-!
# Spike G0: the monotone functional interpretation on `acFinal`'s nine constructors

**"Spike"** is used here in the software sense: a deliberately throwaway prototype built to
answer one feasibility question fast — here, *does the monotone functional interpretation
clear the `and_contract` stall that blocked the term route?* Nine of the (then) 36
`Derivable` constructors were implemented, just enough to run `ConjBoundDemo.acFinal`, and the
rest fell back to the term route. It did clear it (`1709` in ≈207 ms where the term route was
a `whnf` timeout), and that result is why MFI was adopted. Elsewhere in the docs "the spike"
always means this file.

**STATUS (2026-09-05, Lane A): the recursion has moved into the library.** What this file
used to define — `MRealizer`, `MaxCompat`, the nine combinators, `monotone_spike`, `mfiU`/
`mfiV`, `maxT_comm`, `bezemMaxCompat` — now lives in `Metatheorems/Dialectica/Monotone.lean`
(`monotone_soundness`, every constructor, no fallback), `Metatheorems/Majorizability.lean`
(`MaxCompat`'s three facts are fields of `AbstractMajorizability`, discharged in
`bezemAbstract` from a `BaseMono` hypothesis) and `Metatheorems/StrongMajorizability.lean`
(`maxT_comm`). This file keeps its header as the record of the spike, and **re-runs its
gate against the library recursion** — same statements, same numbers, same normal forms —
so that nothing regressed in the move. The full-recursion gate G1 (`tFinalTwice`, a genuine
crossing `max`) is `Probes/MonotoneLaneA.lean`.

The header below is the spike's, kept verbatim for the record except where marked.

---

**Question.** `ConjBoundDemo.acFinal` is a 13-constructor derivation with one `and_contract`
whose counter-side bound `acUt_at_5_9` is a kernel `whnf` timeout (`Eq.rec ↦ 60474`,
`Term.rename ↦ 10504` — the kernel executing renamings over dependent indices on the way to
a 2,529-node term, `SizeProbe.lean`). Does computing a **majorant of the realizer by recursion
on the derivation**, as a semantic value at the hat type — Kohlenbach's monotone functional
interpretation, *Applied Proof Theory* Thm 9.1, pp. 141–145 — with the realizer itself only
existentially quantified, clear the stall?

**RESULT: THE GATE PASSES.** `mfi_acFinal_U_at_5_9 : 1709 = mfiU (triCm M h) (acSpike M h) (5,9)`
closes by `have hval : … = max (pairN …) 0 := rfl; rw [hval]; decide`, kernel-checked, at
`[propext, Classical.choice, Quot.sound]`, in **≈0.2 s of elaboration** (`rfl` ≈ 207 ms, `decide`
≈ 2 ms, kernel type-checking ≈ 40–70 ms; `set_option profiler true`, 2026-09-05) — against a
200 000-heartbeat `whnf` timeout for the same number on the term route. The witness side
`mfi_acFinal_V_at_5_9 = 1709` agrees with the term route's `cVtTwice_at_5_9`.

## The definition (`MRealizer`) — now `Metatheorems.MRealizer`

The statement mirrors `termMajorizer_maj` one level up, over the derivation. Three things
differ from the shape written in the task brief, each forced, none a simplification:

1. **The mixed hypothesis is `MajEnv`, not `SelfMajEnv`.** `SelfMajEnv am Γ e₁ e₂` relates
   two *hat* environments; the brief's `SelfMajEnv am Γ envstar env` with
   `env : Ctx.interpret X Γ` does not typecheck. `MajEnv am Γ envstar env` is the relation the
   content demands (it is what `termMajorizer_maj` uses).
2. **The existential is hoisted outside the environment quantifier** — `∃ x : env → 𝕎 A`,
   uniform in `env`, with correctness `∀ env y` and majorization `∀ envstar env, MajEnv → …`.
   This is exactly the book's `(+)`: `∃x (t* maj x ∧ ∀a,y A_D(x a, y, a))`, where `x` is one
   functional of the free variables `a`. The per-environment form
   `∀ envstar env, MajEnv → ∃ x, …` is **not closable at `forall_rule`**: the premise lives in
   context `ρ :: Γ`, the conclusion's realizer must be correct at *every* `z : ρ`, and the IH
   supplies realizers only at majorized `z` — and even with choice, a realizer chosen from one
   `z*`'s existential need not be majorized by `tstar (z'*, e)` for a second `z'* ≽ z`. The
   hoisted form needs no choice anywhere. `MRealizer.pointwise` derives the brief's shape from
   it, so nothing is lost.
3. **A self-majorization conjunct is carried**, exactly as `termMajorizer_maj` carries one:
   `arrow_intro`'s second clause (Lemma 17.80's self-majorization half) is what `forall_rule`
   needs to show the composed majorant is a majorant at an arrow type, and it is a statement
   about the majorant's monotonicity in its hat-environment, which the mixed clause cannot
   supply.

## The nine cases (the spike's), and the fallback it had

| constructor | strategy | majorant |
|---|---|---|
| `and_weak`, `forall_ax`, `exist_ax`, `refl0` | leaf (Howard, p. 142) | `termMajorizer cm (s…).val` |
| `mp` | composition (p. 144 case 5) | `t₂*.1 t₁*` |
| `syllogism` | composition | `(λx. bc.1 (ab.1 x), λx y. ab.2 x (bc.2 (ab.1 x) y))` |
| `exportation` | composition | currying of the sub-majorant |
| `forall_rule` | composition (p. 144 case 6) | `λxB z. (h*(z,e)).1 xB` …, via `arrow_intro` |
| **`and_contract`** | **p. 143 case 1** | `(λx.(x,x), λx y. maxT (cTy A) y.1 y.2)` |

The spike sent every other constructor to a fallback (the leaf strategy on the whole
sub-derivation). **The library recursion has no fallback**: see `Dialectica/Monotone.lean`'s
header for the strategy of each of the remaining constructors.

`and_contract` needs `maj ρ (maxT ρ a b) c` from `maj ρ a c` (or `b c`) plus self-majorization
of the other argument, and a `maxT` congruence for `selfMaj`, at every hat type. The abstract
`am.maj` has no `max`, so those three facts were packaged here as `MaxCompat am`; **they are
now the fields `maxT_maj_left`/`maxT_maj_right`/`maxT_selfMaj` of `AbstractMajorizability`**,
discharged in `bezemAbstract` from `maxT_bezemMaj_left` / `maxT_hatMaj` / `maxT_comm` and a
`BaseMono` hypothesis (which every instance already had).

## Gate: measured (spike, 2026-09-05; re-run against the library below)

Setting: `M : WHyperbolicModel`, `h : d(a, 0_X) ≤ 5`, majorants `TriangleBoundDemo.triCm M h`,
derivation `ConjBoundDemo.acFinal` (13 constructors, `derivSize_acFinal`), `x* = (5, 9)`.
`U`/`V` are read off the monotone realizer exactly as `extractUTerm`/`extractVTerm` read them
off the realizing term (`mfiU`/`mfiV`).

| theorem | value | normal form reached by `rfl` |
|---|---|---|
| `mfi_acFinal_U_at_5_9` (**the gate**) | `1709` | `max (pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)) 0` |
| `mfi_acFinal_V_at_5_9` | `1709` | `pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)` |
| `mfi_acFinal_U_at_5_1` | `349` | `max (pairN (2·((5+1)·2^(0+1))) (2^(0+1)−1)) 0` |
| `mfi_once_U_at_5_9` (`tFinalOnce`, no contraction) | `1709` | `pairN …` — **no `max`** |

**The `max` is `and_contract`'s and it is `max(1709, 0)`, not `max(1709, 1709)`.** The brief
expected the latter; the actual shape of `acFinal` is
`syllogism (syllogism and_contract and_weak) (syllogism (forall_ax s₁) (exist_ax s₁))`, so the
contraction's second copy of `∀u tB` is discarded by `and_weak`, whose counter majorant
supplies the *default* counter `(zeroM, ()) = (0, ())` for it. `maxT (nat ×ₜ unit) (1709,()) (0,())
= (max 1709 0, ())`. Same number, honestly different arithmetic; `tFinalOnce` shows the `max`
absent when the contraction is. Both are what the book's case 1 predicts for this derivation.

Non-vacuity: `mfi_acFinal_U_ne_1708`, `_ne_1710`, `_ne_zero` are the permanent refutations; the
live `1708` control (spike, 2026-09-05) failed at `decide` with the proposition exhibited, so
the `rfl` genuinely reduces (trap 12 excluded).
-/

namespace Metatheorems
namespace MonotoneSpike

open Formula
open TriangleBoundDemo (pTy triCm)
open ConjBoundDemo (tB acFinal tFinalOnce)

/-- Constructor count, copied from `SizeProbe.derivSize` (that file is not imported here). -/
def derivSizeSpike {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Nat
  | _, _, .mp a b          => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .syllogism a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .exportation a   => 1 + derivSizeSpike a
  | _, _, .importation a   => 1 + derivSizeSpike a
  | _, _, .expansion a     => 1 + derivSizeSpike a
  | _, _, .forall_rule a   => 1 + derivSizeSpike a
  | _, _, .exist_rule a    => 1 + derivSizeSpike a
  | _, _, .univ_gen a      => 1 + derivSizeSpike a
  | _, _, .qfer _ _ a      => 1 + derivSizeSpike a
  | _, _, .induction a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, _                => 1

/-- The scale of the gate: `acFinal` is thirteen constructors. -/
theorem derivSize_acFinal : derivSizeSpike acFinal = 13 := rfl

/-- The monotone realizer of `acFinal`, at the W-hyperbolic model with `d(a, 0_X) ≤ 5` —
now through the library's full recursion. -/
noncomputable def acSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) acFinal

/-- The same for the contraction-free control `tFinalOnce`. -/
noncomputable def onceSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) tFinalOnce

/-- **THE GATE (re-run).** The counter-side bound of `acFinal` — the one that is a `whnf`
timeout on the term route (`ConjBoundDemo.acUt_at_5_9`) — through the library's monotone
interpretation. -/
theorem mfi_acFinal_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The witness side of the same derivation, agreeing with `cVtTwice_at_5_9`'s term-route
value. -/
theorem mfi_acFinal_V_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The bound moves with `x*`: at `(5,1)` it is `349`, `s₁`'s majorant there
(`ConjBoundDemo.witM1_at_5_1`). -/
theorem mfi_acFinal_U_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The contraction-free control `tFinalOnce` through the same interpretation: the same
`1709`, and — visibly in the `hval` normal form — **no `max`**. -/
theorem mfi_once_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- Permanent refutation controls: the gate value is exact from below and above. -/
theorem mfi_acFinal_U_ne_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

theorem mfi_acFinal_U_ne_1710 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1710 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

/-- The `U` is not `0` — the premise is consulted. -/
theorem mfi_acFinal_U_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms derivSize_acFinal
#print axioms mfi_acFinal_U_at_5_9
#print axioms mfi_acFinal_V_at_5_9
#print axioms mfi_acFinal_U_at_5_1
#print axioms mfi_once_U_at_5_9
#print axioms mfi_acFinal_U_ne_1708
#print axioms mfi_acFinal_U_ne_1710
#print axioms mfi_acFinal_U_ne_zero

end MonotoneSpike
end Metatheorems
