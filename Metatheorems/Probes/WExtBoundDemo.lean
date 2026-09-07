/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.ContentExampleSpace
import Metatheorems.Probes.NestingDepth
import Metatheorems.WHyperbolicLemmas

/-!
# Bound extraction from the W-hyperbolic library — a ladder, and where it stops

`Metatheorems/WHyperbolicLemmas.lean` derives theorems *about* W-hyperbolic spaces
(nonexpansiveness, the geodesic estimates, and — since this pass — **extensionality of `W`**).
None of them is in metatheorem shape: they are purely universal, with no `∃`. This file builds
statements *around* them in the shape `∀q (∀u B₀ → ∃v C₀)`, exactly as
`Probes/TriangleBoundDemo.lean` does around `Derivable.dist_tri` and
`Probes/ContentExampleSpace.lean` around the same, and runs the **monotone** route
(`monotone_soundness` → `mfiU`/`mfiV`, then `monotone_general_metatheorem_at`) on each.

Everything is at an **arbitrary** `WHyperbolicModel M` with `d(a, 0_X) ≤ 5` — `M` and the
bound `h` stay free variables, so every numeral below holds of every W-hyperbolic space.
The evaluator is `mfi_push` + `kernel_rfl` throughout; bare `rfl` is the wrong instrument at a
space (no `whnf` cache with free model variables — `MonotoneLaneB`'s finding).

## The ladder, and the result

`q = ((x, x'), (y, λ))`, so `q* = ((nx, nx'), (ny, r*))`. `λ̃` is `clamp01 λ`.

| rung | premise `∀u B₀` | conclusion `∃v C₀` | the proof | depth | `V` | `U` |
|---|---|---|---|---|---|---|
| 1 `wDir` | `W(x,y,λ̃) =_X W(x',y,λ̃)` | the same, at some `v` | `forall_ax D₀` ⟶ `exist_ax D₀` | **3** | **901** / **1273** | **901** |
| 2 `wAx` | unused | `∃v` (W2)'s body at `v` | `W2_at` (the axiom at abstract terms, via the proof mode) | **8** | **901** / **1273** | **0** |
| 3 `wExt` / `wExtD` | `x =_X x'` | `W(x,y,λ̃) =_X W(x',y,λ̃)` at some `v` | **`W_ext_left`** | **≥66** | **901** (36 s) | **OOM** |
| 4 `wExtP` / `wExtPD` | `λ =ℝ μ` | `W(x,y,λ̃) =_X W(x,y,μ̃)` at some `v` | **`W_ext_param`** | **≥62** | **901** (35 s) | not run |

Rung 3 is the one with content: premise and conclusion are *different formulas*, the premise
is genuinely consumed (it is `W_ext_left`'s only hypothesis), and `U` is the precision at
which `d(x,x') =ℝ 0ℝ` has to be known for the conclusion to hold at precision `v`.

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
-/

set_option Elab.async false
set_option linter.unusedTactic false

namespace Metatheorems
namespace WExtBoundDemo

open Formula ProofMode
open TriangleBoundDemo (triCm)
open MonotoneLaneA (derivSizeA)

-- ============================================================================
-- Types, context, projections
-- ============================================================================

/-- `q = ((x, x'), (y, λ))`. -/
abbrev qTy : Ty MetricSpace.ι := (xTy ×ₜ xTy) ×ₜ (xTy ×ₜ rTy)

abbrev K0 : Ctx MetricSpace.ι := [qTy]
abbrev K1 : Ctx MetricSpace.ι := Ty.nat :: K0

abbrev DS (Γ : Ctx MetricSpace.ι) (A : Formula WHyperbolic.F Γ) :=
  @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
    WHyperbolic.Premises Γ A

abbrev x0 : Term WHyperbolic.F K0 xTy := Term.fst (Term.fst (.var .vz))
abbrev x1 : Term WHyperbolic.F K0 xTy := Term.snd (Term.fst (.var .vz))
abbrev y0 : Term WHyperbolic.F K0 xTy := Term.fst (Term.snd (.var .vz))
abbrev l0 : Term WHyperbolic.F K0 rTy := Term.snd (Term.snd (.var .vz))

/-- A second parameter, taken as `λ` again — rung 4 needs two codes and the context has one,
so `μ := λ` is used; the statement is still the extensionality *implication*, whose premise
`λ =ℝ μ` is then derivable, which is exactly why rung 4 measures the derivation and not the
hypothesis. -/
abbrev m0 : Term WHyperbolic.F K0 rTy := Term.snd (Term.snd (.var .vz))

abbrev cl0 : Term WHyperbolic.F K0 (realTy MetricSpace.ι) := .app Term.clamp01 l0

abbrev W0 : Term WHyperbolic.F K0 xTy := Term.app3 (Term.func ()) x0 y0 cl0
abbrev W1' : Term WHyperbolic.F K0 xTy := Term.app3 (Term.func ()) x1 y0 cl0

-- ============================================================================
-- The quantifier-free bodies
-- ============================================================================

/-- **The quantifier-free body of `f =ℝ g` at the bound index `x₀`.** `eq_R f g` is
`Formula.all Ty.nat (eqBody f g)` by construction, so `Formula.all Ty.nat (eqBody f g)` and
`eq_R f g` are the *same expression* — which is what lets a base-type equality be the
metatheorem's `∀u B₀`. -/
def eqBody {Γ : Ctx MetricSpace.ι} (f g : Term WHyperbolic.F Γ (realTy MetricSpace.ι)) :
    Formula WHyperbolic.F (Ty.nat :: Γ) :=
  Formula.eq0
    (Term.app2 Term.lt_Q_dec
      (Term.app Term.abs_Q
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))))
      (Term.app Term.pow2neg_Q (.var .vz)))
    Term.zero

theorem eqBody_all {Γ : Ctx MetricSpace.ι}
    (f g : Term WHyperbolic.F Γ (realTy MetricSpace.ι)) :
    Formula.all Ty.nat (eqBody f g) = eq_R f g := rfl

theorem eqBody_qf {Γ : Ctx MetricSpace.ι}
    (f g : Term WHyperbolic.F Γ (realTy MetricSpace.ι)) : (eqBody f g).isQF = true := rfl
theorem eqBody_vf {Γ : Ctx MetricSpace.ι}
    (f g : Term WHyperbolic.F Γ (realTy MetricSpace.ι)) : (eqBody f g).isVFree = true := rfl

/-- `d(x, x')` — the distance the premise of rung 3 says is `0ℝ`. -/
def dXX : Term WHyperbolic.F K0 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x0 x1
/-- `d(W(x,y,λ̃), W(x',y,λ̃))` — the distance the conclusion of rung 3 says is `0ℝ`. -/
def dWW : Term WHyperbolic.F K0 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) W0 W1'

/-- `∀u (premise body) = x =_X x'`, on the nose. -/
theorem extB_all : Formula.all Ty.nat (eqBody dXX Term.zero_R) = eqAtType xTy x0 x1 := rfl
/-- `∀v (conclusion body) = W(x,y,λ̃) =_X W(x',y,λ̃)`, on the nose. -/
theorem extC_all : Formula.all Ty.nat (eqBody dWW Term.zero_R) = eqAtType xTy W0 W1' := rfl

-- ============================================================================
-- Rung 1: assume the conclusion, exhibit it — the plumbing, with a `W` matrix
-- ============================================================================

/-- The witness: the space's own number `⌈d(x,x')⌉₀`, as in `ContentExampleSpace.D0`. Its
majorant is what `U` and `V` report — `distMajorant nx nx' 0 = pairN (2·((nx+nx')·2), 1)`,
i.e. `901` at `(5,5)` and `1273` at `(7,5)`, the numbers `Probes/TriangleBoundDemo.lean`
already calibrated. -/
abbrev D0 : Term WHyperbolic.F K0 Ty.nat := Term.app dXX Term.zero

def dirInner : DS K0 (Formula.all Ty.nat (eqBody dWW Term.zero_R) →ᶠ
    Formula.ex Ty.nat (eqBody dWW Term.zero_R)) :=
  Derivable.syllogism (Derivable.forall_ax (A := eqBody dWW Term.zero_R) D0)
    (Derivable.exist_ax D0 (eqBody dWW Term.zero_R))

-- ============================================================================
-- Rung 2: the conclusion is (W2) at abstract terms — a proof-mode axiom instance
-- ============================================================================

/-- (W2)'s right-hand side at `μ := λ`: `|λ̃ −ℝ λ̃|ℝ ·ℝ d(x,y)`. -/
def w2rhs : Term WHyperbolic.F K0 (realTy MetricSpace.ι) :=
  Term.app2 Term.mul_R
    (.app Term.abs_R (Term.app2 Term.sub_R cl0 (.app Term.clamp01 m0)))
    (Term.app2 (Term.dist ()) x0 y0)

def w2lhs : Term WHyperbolic.F K0 (realTy MetricSpace.ι) :=
  Term.app2 (Term.dist ())
    (Term.app3 (Term.func ()) x0 y0 cl0)
    (Term.app3 (Term.func ()) x0 y0 (.app Term.clamp01 m0))

/-- (W2) at the four projections, as the `∀`-formula whose body the conclusion instantiates. -/
def w2thm : DS K0 (Formula.all Ty.nat (eqBody w2lhs w2rhs)) :=
  WHyperbolic.W2_at x0 y0 l0 m0

def axInner : DS K0 (Formula.all Ty.nat (eqBody dWW Term.zero_R) →ᶠ
    Formula.ex Ty.nat (eqBody w2lhs w2rhs)) :=
  Derivable.mp
    (Derivable.mp (Derivable.mp w2thm (Derivable.forall_ax D0))
      (Derivable.exist_ax D0 (eqBody w2lhs w2rhs)))
    K_comb

-- ============================================================================
-- Rung 3: `W_ext_left` — the premise is `x =_X x'`, the conclusion is about `W`
-- ============================================================================

/-- **The rung with content.** `W_ext_left` turns the premise `x =_X x'` — which *is*
`∀u B₀` — into `W(x,y,λ̃) =_X W(x',y,λ̃)`, of which the conclusion asks for one index. So `U`
is the precision at which the hypothesis must be known and `V` the precision the conclusion is
delivered at. -/
def extInner : DS K0 (Formula.all Ty.nat (eqBody dXX Term.zero_R) →ᶠ
    Formula.ex Ty.nat (eqBody dWW Term.zero_R)) :=
  Derivable.syllogism (WHyperbolic.W_ext_left x0 x1 y0 l0)
    (Derivable.syllogism (Derivable.forall_ax (A := eqBody dWW Term.zero_R) Term.zero)
      (Derivable.exist_ax Term.zero (eqBody dWW Term.zero_R)))

/-- The same at the **non-trivial** witness `⌈d(x,x')⌉₀`, so that `V` is `901` rather than `0`
and cannot be produced without evaluating a majorant. -/
def extInnerD : DS K0 (Formula.all Ty.nat (eqBody dXX Term.zero_R) →ᶠ
    Formula.ex Ty.nat (eqBody dWW Term.zero_R)) :=
  Derivable.syllogism (WHyperbolic.W_ext_left x0 x1 y0 l0)
    (Derivable.syllogism (Derivable.forall_ax (A := eqBody dWW Term.zero_R) D0)
      (Derivable.exist_ax D0 (eqBody dWW Term.zero_R)))

-- ============================================================================
-- Rung 4: `W_ext_param` — the premise is `λ =ℝ μ`
-- ============================================================================

def dWWp : Term WHyperbolic.F K0 (realTy MetricSpace.ι) :=
  Term.app2 (Term.dist ())
    (Term.app3 (Term.func ()) x0 y0 cl0)
    (Term.app3 (Term.func ()) x0 y0 (.app Term.clamp01 m0))

theorem parB_all : Formula.all Ty.nat (eqBody l0 m0) = eq_R l0 m0 := rfl

def parInner : DS K0 (Formula.all Ty.nat (eqBody l0 m0) →ᶠ
    Formula.ex Ty.nat (eqBody dWWp Term.zero_R)) :=
  Derivable.syllogism (WHyperbolic.W_ext_param x0 y0 l0 m0)
    (Derivable.syllogism (Derivable.forall_ax (A := eqBody dWWp Term.zero_R) Term.zero)
      (Derivable.exist_ax Term.zero (eqBody dWWp Term.zero_R)))

/-- The same at the non-trivial witness `⌈d(x,x')⌉₀`. -/
def parInnerD : DS K0 (Formula.all Ty.nat (eqBody l0 m0) →ᶠ
    Formula.ex Ty.nat (eqBody dWWp Term.zero_R)) :=
  Derivable.syllogism (WHyperbolic.W_ext_param x0 y0 l0 m0)
    (Derivable.syllogism (Derivable.forall_ax (A := eqBody dWWp Term.zero_R) D0)
      (Derivable.exist_ax D0 (eqBody dWWp Term.zero_R)))

-- ============================================================================
-- Metatheorem shape
-- ============================================================================

def wDummy : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) := Formula.eq0 Term.zero Term.zero

def wrapW {B C : Formula WHyperbolic.F K1}
    (d : DS K0 (Formula.all Ty.nat B →ᶠ Formula.ex Ty.nat C)) :
    DS K0 (Formula.weakenBy qTy wDummy →ᶠ
      (Formula.all Ty.nat B →ᶠ Formula.ex Ty.nat C)) :=
  Derivable.mp d (Derivable.exportation Derivable.and_weak)

def wrap {B C : Formula WHyperbolic.F K1}
    (d : DS K0 (Formula.all Ty.nat B →ᶠ Formula.ex Ty.nat C)) :
    DS [] (Formula.all qTy (Formula.all Ty.nat B →ᶠ Formula.ex Ty.nat C)) :=
  Derivable.mp (Derivable.refl0 (t := Term.zero)) (Derivable.forall_rule (wrapW d))

def wDir := wrap dirInner
def wAx := wrap axInner
def wExt := wrap extInner
def wExtD := wrap extInnerD
def wExtP := wrap parInner
def wExtPD := wrap parInnerD

-- ============================================================================
-- The numerals, at an arbitrary W-hyperbolic model with `d(a, 0_X) ≤ 5`
-- ============================================================================

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

noncomputable def rDir : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat (eqBody dWW Term.zero_R) →ᶠ
      Formula.ex Ty.nat (eqBody dWW Term.zero_R))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) wDir

abbrev XM := fun (_ : Unit) => M.carrier

/-- `q* = ((nx, nx'), (ny, r*))` with `r* = λn. n+1`. -/
def qs (nx nx' ny : ℕ) : Ty.interpret (XM M) qTy.hat :=
  ((nx, nx'), (ny, fun (n : ℕ) => n + 1))

macro "pushDirV" : tactic =>
  `(tactic| (unfold mfiV rDir
             mfi_push [wDir, wrap, wrapW, dirInner]))
macro "pushDirU" : tactic =>
  `(tactic| (unfold mfiU rDir
             mfi_push [wDir, wrap, wrapW, dirInner]))

/-! ### Rung 1 -/

theorem Vdir : (901 : ℕ) = mfiV (triCm M h) (rDir M h) (qs M 5 5 5) := by
  pushDirV
  kernel_rfl

theorem Udir : (901 : ℕ) = mfiU (triCm M h) (rDir M h) (qs M 5 5 5) := by
  pushDirU
  kernel_rfl

/-- …and it moves with the space majorant of `x`: `1273` at `nx = 7`. -/
theorem Vdirb : (1273 : ℕ) = mfiV (triCm M h) (rDir M h) (qs M 7 5 5) := by
  pushDirV
  kernel_rfl

theorem Vdir_ne_900 : (900 : ℕ) ≠ mfiV (triCm M h) (rDir M h) (qs M 5 5 5) := by
  rw [← Vdir M h]; decide

theorem Vdirb_ne_901 : (901 : ℕ) ≠ mfiV (triCm M h) (rDir M h) (qs M 7 5 5) := by
  rw [← Vdirb M h]; decide

/-! ### Rung 2: the conclusion is (W2) itself, instantiated through the proof mode

`W2_at` is a **proof-mode** derivation (four `pinst`/`znorm` rounds) that ends in
`Derivable.premise WHyperbolic.W2` — so unlike every earlier space extraction in the project
(`TriangleBoundDemo`, `ContentExampleSpace`), which consume the *free* constructor
`Derivable.dist_tri`, this one runs `monotone_soundness` through a real `.premise` of a space
theory and through the `pm_*` layer. `U = 0` (the premise formula is weakened away by
`K_comb`); `V` is the majorant of the witness `⌈d(x,x')⌉₀`, i.e. the same `901`/`1273`. -/

noncomputable def rAx : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat (eqBody dWW Term.zero_R) →ᶠ
      Formula.ex Ty.nat (eqBody w2lhs w2rhs))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) wAx

macro "pushAxV" : tactic =>
  `(tactic| (unfold mfiV rAx
             mfi_push [wAx, wrap, wrapW, axInner, w2thm]))
macro "pushAxU" : tactic =>
  `(tactic| (unfold mfiU rAx
             mfi_push [wAx, wrap, wrapW, axInner, w2thm]))

theorem Vax : (901 : ℕ) = mfiV (triCm M h) (rAx M h) (qs M 5 5 5) := by
  pushAxV
  kernel_rfl

theorem Vaxb : (1273 : ℕ) = mfiV (triCm M h) (rAx M h) (qs M 7 5 5) := by
  pushAxV
  kernel_rfl

theorem Uax : (0 : ℕ) = mfiU (triCm M h) (rAx M h) (qs M 5 5 5) := by
  pushAxU
  kernel_rfl

theorem Vax_ne_900 : (900 : ℕ) ≠ mfiV (triCm M h) (rAx M h) (qs M 5 5 5) := by
  rw [← Vax M h]; decide

/-! ### Rung 3: `W_ext_left` — witness side only

`W_ext_left` is a composition-**depth 66** derivation of 3.7 M tree nodes (the histogram at
the bottom of this file). The witness side goes through it in seconds; the counter side does
not go through it at all. See this file's header for the numbers and the reproduction
snippet. -/

noncomputable def rExt : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat (eqBody dXX Term.zero_R) →ᶠ
      Formula.ex Ty.nat (eqBody dWW Term.zero_R))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) wExt

noncomputable def rExtD : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat (eqBody dXX Term.zero_R) →ᶠ
      Formula.ex Ty.nat (eqBody dWW Term.zero_R))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) wExtD

/-- The witness `0`: `V = 0`. **On its own this proves nothing** — a `V` of `0` at a witness
whose majorant is `0` is exactly the laziness `Probes/MonotoneLaneB.lean` records for
`dist_tri_chain`. It is kept as the control for the next theorem. -/
theorem Vext : (0 : ℕ) = mfiV (triCm M h) (rExt M h) (qs M 5 5 5) := by
  unfold mfiV rExt
  mfi_push [wExt, wrap, wrapW, extInner]
  kernel_rfl

/-- **The non-vacuous one**: at the witness `⌈d(x,x')⌉₀` the same derivation gives `901`, the
majorant `distMajorant 5 5 0`. So the kernel really evaluates a majorant through
`W_ext_left`; `Vext` above is not what is being reported here. ≈36 s of kernel time. -/
theorem VextD : (901 : ℕ) = mfiV (triCm M h) (rExtD M h) (qs M 5 5 5) := by
  unfold mfiV rExtD
  mfi_push [wExtD, wrap, wrapW, extInnerD]
  kernel_rfl

theorem VextD_ne_900 : (900 : ℕ) ≠ mfiV (triCm M h) (rExtD M h) (qs M 5 5 5) := by
  rw [← VextD M h]; decide

/-! ### Rung 4: `W_ext_param` — witness side only

Same picture as rung 3, through the *parameter* case, which uses (W2) and the three new `=ℝ`
facts (`clamp01_congr_R`, `abs_sub_eq_zero_R`, `mul_zero_l_R`) and **no** `le_R_trans_core`.
Composition depth ≥62; `V` at the non-trivial witness is `901` in ≈35 s. -/

noncomputable def rExtPD : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat (eqBody l0 m0) →ᶠ
      Formula.ex Ty.nat (eqBody dWWp Term.zero_R))) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) wExtPD

theorem VextPD : (901 : ℕ) = mfiV (triCm M h) (rExtPD M h) (qs M 5 5 5) := by
  unfold mfiV rExtPD
  mfi_push [wExtPD, wrap, wrapW, parInnerD]
  kernel_rfl

theorem VextPD_ne_900 : (900 : ℕ) ≠ mfiV (triCm M h) (rExtPD M h) (qs M 5 5 5) := by
  rw [← VextPD M h]; decide

end Model

-- ============================================================================
-- Depth measurements — the predictor for the rungs that do not reduce
-- ============================================================================

#eval derivSizeA wDir

#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WHyperbolic.W_ext_left
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WHyperbolic.W_ext_param
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WHyperbolic.W2_at
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WExtBoundDemo.wDir
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WExtBoundDemo.wAx
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WExtBoundDemo.wExt
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WExtBoundDemo.wExtP
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WHyperbolic.dist_W_mono_left
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.WHyperbolic.W4_at
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.eq_R_trans_core
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.le_R_antisymm_core
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.dist_nonneg
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.mul_eq_zero_R_core
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.clamp01_congr_R
#eval show Lean.MetaM Unit from NestingDepth.report ``Metatheorems.abs_sub_eq_zero_R

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms extB_all
#print axioms extC_all
#print axioms wDir
#print axioms wAx
#print axioms wExt
#print axioms wExtD
#print axioms wExtP
#print axioms wExtPD

end WExtBoundDemo
end Metatheorems
