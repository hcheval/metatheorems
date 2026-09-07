/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Hilbert
import Metatheorems.MonotoneMetatheoremClassical
import Metatheorems.ProofMode.RealMCT
import Metatheorems.Probes.MonotoneLaneA
import Metatheorems.Probes.MonotoneLaneB
import Metatheorems.Probes.TermPrintDemo
import Metatheorems.Probes.LemBoundDemo
import Metatheorems.Probes.MonotoneMemoGates

/-!
# A guided walkthrough — one file, four sections, for a talk

Everything here is either **written in this file** or **restated from a probe with its proof
term**, so every number below is checked by this module's own build. Nothing is quoted.

The running example is fixed once, in §1, and used unchanged by §1 and §2, so the two
extraction routes are compared on *the same statement, the same model, the same majorants and
the same `x*`*.

| § | shows | reduces to a numeral? |
|---|---|---|
| 1 | statement at a space, proof-mode derivation, `#hilbert`, term route, printed realizer | yes — from the raw-constructor derivation |
| 2 | the same numeral through the monotone functional interpretation, plus contraction | yes — including from the **proof-mode** derivation |
| 3 | ℝ-MCT end to end: statement, derivation, bound, Mathlib metastability | **no** — types and axioms only |
| 4 | the classical entry point | **no** — type and axioms only |

The honest summary is in `docs/RESULTS.md`; the questions a proof-mining audience asks are in
`docs/QA.md`.

**How to check this file.** `Demo` is not a `lean_lib` in `lakefile.toml`, so this module is
not reachable from `Probes.lean` (`import Demo.Walkthrough` fails with "unknown module prefix
'Demo'"); build it directly:

    scripts/lean.sh <repo>/Demo/Walkthrough.lean

It elaborates with **no errors and no warnings**, and prints, in order: the two `#hilbert`
step counts, the rendered realizer of §1e, the four `#check`s of §3–§4, and the `#print axioms`
block at the end. To fold it into `lake build Probes`, add `[[lean_lib]] name = "Demo"` to
`lakefile.toml` and the import line noted at the bottom of `Probes.lean`.
-/

namespace Metatheorems
namespace Demo

open Formula
open TriangleBoundDemo (pTy triB triWit triCm triFinal triB_pu triB_vf triB_pe triB_qf)

/-! ============================================================================
# §1. A statement at a space, proved twice, and mined once

## The statement

    ∀p^(X ×ₜ X) ( ∀n [ d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z) ]ₙ  →  ∃v [ … ]ᵥ )

with `x := π₁ p`, `z := π₂ p`. `triB` is the *quantifier-free body* of `d(x,z) ≤ℝ d(x,0_X) +ℝ
d(0_X,z)` read at one Cauchy index; `TriangleBoundDemo.triAll_eq` proves, by `rfl`, that
`∀n triB` is on the nose the formula `Derivable.dist_tri` concludes. So the metatheorem's own
premise variable `u` **is** the precision index of the triangle inequality, and the extracted
`U` says *how precisely the space axiom has to be known*.

`X` is the carrier of an arbitrary W-hyperbolic space (`WHyperbolic.lean`; every real normed
space is one, `Instances.lean`). `M` and the bound `h : d(a,0_X) ≤ 5` stay **variables**
throughout, so every numeral below holds of every such model.
============================================================================ -/

/-- Derivations over the W-hyperbolic signature, at `Allowed.extended`. -/
abbrev WD (Γ : Ctx MetricSpace.ι) (A : Formula WHyperbolic.F Γ) :=
  @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
    WHyperbolic.Premises Γ A

/-- **The statement**, spelled out. `abbrev`, so the metatheorems' unifiers see through it. -/
abbrev stmt : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) :=
  Formula.all pTy (Formula.all Ty.nat triB →ᶠ Formula.ex Ty.nat triB)

/-! ## 1a. The proof, in the proof mode

Six tactic lines. `pmode` opens the hypothesis context (`Seq Δ B` is *definitionally*
`Derivable … (pack Δ B)`, so this costs nothing and there is nothing to verify about it);
`pforall` introduces `p`; `pintro h` assumes the triangle inequality; `pinst h triWit`
instantiates it at the witness term `s(p) := (d(x,z)) 0`; `pexists`/`pexact` close.

The premise is **consumed**, not weakened away — that is what makes the extracted `U`
informative rather than `0` (contrast `TriangleBoundDemo.triUncUtB_is_zero`, which is the same
formula proved by weakening `triB` in). -/
def proofMode : WD [] stmt := by
  pmode
  pforall
  pintro h
  pinst h triWit with h1
  pexists triWit
  pexact h1

/-! ## 1b. The same statement from raw `Derivable` constructors

`TriangleBoundDemo.triFinal`: `forall_ax s` (instantiate the premise) composed by `syllogism`
with `exist_ax s` (generalise), then `forall_rule` over a dummy premise. Raw constructors, no
proof mode. This is the derivation the *term* route can still handle (§1d). -/
example : WD [] stmt := triFinal

/-! ## 1c. `#hilbert`: the proof term IS the Hilbert derivation

`Derivable` is `Type`-valued, so a proof in this development is a term whose head constructors
are the inference rules of the object logic. `#hilbert` walks it and writes the numbered
listing, in Markdown and LaTeX. Sharing is preserved: every distinct subproof is numbered
once and cited by line number afterwards, which is what a paper proof does anyway.

Look at `Demo/hilbert/triFinal.md` (**9** numbered steps, everything expanded — the `all`
modifier) beside `Demo/hilbert/proofMode.md` (**7** steps: the same statement via the proof
mode, with the `pm_*` tactic lemmas cited by name rather than expanded, which is the only
tenable default since every `pintro` is itself a derivation). The step counts are printed by
the two commands below when this file is elaborated. -/
#hilbert triFinal all to "Demo/hilbert/triFinal"
#hilbert proofMode to "Demo/hilbert/proofMode"

/-! ## 1d. Through the metatheorem — the bound is a `def`, not an `∃`

`syntactic_general_metatheorem_at_gen` is Kohlenbach 17.52 in the `_gen` (arbitrary purely
universal premise / purely existential conclusion) form, returning a `Subtype`: `Φ` is
**data**. The four side conditions are `rfl`. -/
section TermRoute
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- The bound, extracted from the raw-constructor derivation. -/
noncomputable def phiTerm :
    { Φ : Ty.interpret (fun () => M.carrier) pTy.hat → Nat //
      ∀ (x : Ty.interpret (fun () => M.carrier) pTy)
        (x_star : Ty.interpret (fun () => M.carrier) pTy.hat),
        M.abstractMajorizability.toRel.maj pTy x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si triB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si triB (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen M.eqXInterp M.spremise (triCm M h)
    triB_pu triB_vf triB_pe triB_vf triFinal

set_option linter.unusedTactic false

/-- **The numeral.** At `x* = (5,5)` the bound is the literal `901` — kernel-checked, not
`#eval`ed. (`901 = (5+5)° read at index 0 = pairN 40 1 = triagN 41 + 40`.) -/
theorem phiTerm_at_5_5 : (901 : ℕ) = (phiTerm M h).val ((5 : ℕ), (5 : ℕ)) := by
  have hval : (phiTerm M h).val ((5 : ℕ), (5 : ℕ))
      = Nat.max (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]
  decide

/-- **The refutation control.** `902` is provably *not* the value, so the `rfl` above really
reduced and the number is exact rather than an upper estimate. -/
theorem phiTerm_ne_902 : (902 : ℕ) ≠ (phiTerm M h).val ((5 : ℕ), (5 : ℕ)) := by
  rw [← phiTerm_at_5_5 M h]; decide

/-- **The bound moves with `x*`.** The premise bound alone (`U`, i.e. the precision the
triangle inequality is needed at) is `1273` at `(7,5)` — a `U` supplied by a default path
could not depend on `x*` at all. -/
theorem u_at_7_5 :
    (1273 : ℕ) = closedMajorizer (triCm M h) (TriangleBoundDemo.triUt M) ((7 : ℕ), (5 : ℕ)) :=
  TriangleBoundDemo.triUt_at_7_5 M h

end TermRoute

/-! ## 1e. The extracted realizer, printed

`extractTerm` is `syntactic_soundness` with the model deleted — the realizing term depends on
the *derivation tree alone*, so it is an ordinary computable `Term` even at a space (every
model here routes through Mathlib `ℝ` and is `noncomputable`).

`TermPretty` renders it. `summary` reports: tree size; DAG size (distinct subterms — an
**upper** bound on achievable sharing, since de Bruijn indices are context-relative and an open
subterm cannot be hoisted); the `let`-bindings actually emitted; and the **written size**, which
is the honest figure for "can a human read this". `Demo/../term-print-out/realizers.md` has the
full listings. -/

/-- The realizer of `triFinal`, as a printable tree (`TermPrintDemo.rTri`). -/
def realizerTri : TermPretty.RTerm := TermPrintDemo.rTri

/-- 413 nodes, kernel-checked. -/
theorem realizerTri_size : realizerTri.size = 413 := TermPrintDemo.rTri_size

#eval IO.println (TermPretty.summary "triFinal " realizerTri)
#eval IO.println (TermPretty.render realizerTri)

/-! ============================================================================
# §2. The same bound through the MONOTONE functional interpretation

Kohlenbach *Applied Proof Theory* Ch. 9, Thm 9.1: instead of building the Dialectica realizer
and then majorizing it, compute a **majorant** of the realizer directly by recursion on the
derivation, leaving the realizer itself existential. Because `Ty.hat` sends every base type to
`nat`, the majorant is a plain Lean value built from `ℕ`/`unit`/`×`/`→` — **no `Term` on the
bound path**, hence no `weaken`, no `rename`, no dependent casts to reduce.

`monotone_general_metatheorem_at` has the *same statement* as `syntactic_general_metatheorem_at`;
only the internal object changes.

Two things this buys, both demonstrated below.
============================================================================ -/

section MonotoneRoute
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- The monotone realizer of the **proof-mode** derivation of §1a. -/
noncomputable def mr : MRealizer (triCm M h) stmt :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) proofMode

/-! `kernel_rfl` (from `Probes/MonotoneLaneB.lean`) assigns `Eq.refl` and lets the **kernel**
decide the equation. That is the right instrument at a space: `Meta.isDefEq` has no `whnf`
cache on terms with free variables (`M`, `h`) and recomputes `Ty.interpret` at every step,
where the kernel caches by structure. Its non-vacuity control is `mfi_U_ne_900` below, which
`decide` *refutes*. -/

/-- **The premise bound `U`, from the PROOF-MODE derivation, counter side included** — `901`,
in a couple of seconds of kernel time (`Probes/MonotoneLaneB.lean` times the identical
`e3_U` at 1.75 s). The term route has never produced a counter-side numeral from any
proof-mode derivation. -/
theorem mfi_U : (901 : ℕ) = mfiU (triCm M h) (mr M h) ((5 : ℕ), (5 : ℕ)) := by kernel_rfl

/-- The witness bound `V`, same derivation. -/
theorem mfi_V : (901 : ℕ) = mfiV (triCm M h) (mr M h) ((5 : ℕ), (5 : ℕ)) := by kernel_rfl

/-- **`Φ` through the monotone metatheorem itself** — the same `901` §1d got through the term
route from the raw-constructor derivation. Same statement, same model, same majorants, same
`x*`; two routes, one number. -/
theorem mfi_phi : (901 : ℕ) = (monotone_general_metatheorem_at M.eqXInterp M.spremise
    (triCm M h) triB_qf triB_vf triB_qf triB_vf proofMode).val ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

theorem mfi_U_ne_900 : (900 : ℕ) ≠ mfiU (triCm M h) (mr M h) ((5 : ℕ), (5 : ℕ)) := by
  rw [← mfi_U M h]; decide

theorem mfi_U_at_7_5 : (1273 : ℕ) = mfiU (triCm M h) (mr M h) ((7 : ℕ), (5 : ℕ)) := by
  kernel_rfl

/-! ## 2b. Contraction — the one thing the term route cannot do

A premise used **twice at different terms** forces `U` to be a genuine `max` of two
majorants. On the term route a single `and_contract` at the premise formula is a `whnf`
timeout (`Probes/ConjBoundDemo.lean`: six variants isolate it — not matrix size, not numeral
magnitude, not the duplicating plumbing, just the one rule). Under the monotone interpretation
contraction *is* a `max` (Kohlenbach p. 143, case 1) and it evaluates.

`ConjBoundDemo.tFinalTwice` instantiates its premise at `s₁ = (d x z) 0` and `s₂ = (d x 0_X) 0`.
The two majorants **cross over**, so the `max` is doing real work: at `x* = (5,9)` the first
wins, at `(5,1)` the second does. A `U` following either instantiation alone would be a
visibly different function. -/

/-- `max(1709, 901) = 1709` at `x* = (5,9)`. -/
theorem contraction_at_5_9 :
    (1709 : ℕ) = mfiU (triCm M h) (MonotoneLaneA.twiceM M h) ((5 : ℕ), (9 : ℕ)) :=
  MonotoneLaneA.g1_U_at_5_9 M h

/-- `max(901, 349) = 901` at `x* = (5,1)` — the **other** instantiation now wins. -/
theorem contraction_at_5_1 :
    (901 : ℕ) = mfiU (triCm M h) (MonotoneLaneA.twiceM M h) ((5 : ℕ), (1 : ℕ)) :=
  MonotoneLaneA.g1_U_at_5_1 M h

/-- The control that makes the crossover a fact and not a coincidence: `349` — what a `U`
following `s₁` alone would report at `(5,1)` — is refuted. -/
theorem contraction_not_one_sided :
    (349 : ℕ) ≠ mfiU (triCm M h) (MonotoneLaneA.twiceM M h) ((5 : ℕ), (1 : ℕ)) :=
  MonotoneLaneA.g1_U_at_5_1_ne_349 M h

end MonotoneRoute

/-! ============================================================================
# §3. ℝ-MCT, end to end — statement, derivation, bound, and Mathlib

The monotone convergence theorem for a nonincreasing `[0,1]`-valued real sequence, in
**metastable** (no-counterexample) form, is the project's one derivation with real
mathematical content: 655 lines of proof-mode script over the encoded reals.

    ∀ x^{(ℕ→ℝ) × ((ℕ→ℕ) × ℕ)} ( ∀u B(u,x) → ∃v C(v,x) )      a := π₁x, g := π₁π₂x, k := π₂π₂x

    B(u,x) := ∀n ( a(n+1) ≤ℝ a n  ∧  0ℝ ≤ℝ a n  ∧  a n ≤ℝ 1ℝ )   each read at Cauchy index u
    C(v,x) := |a v −ℝ a(v + g v)|ℝ  ≤  ⟨2^{-(k+1)}⟩ℝ            at the fixed index k+2

`B` is purely universal and **not** quantifier-free, so this needs the `_gen` metatheorem —
it is Kohlenbach's `B∀`/`C∃`, not the QF special case.

Three facts to look at, in order.
============================================================================ -/

/-! **(a) The statement** is a closed `Formula`, and its side conditions hold by `rfl`. -/
#check @RealMCT.rmStatement
example : (RealMCT.rmB (F := WHyperbolic.F)).isPurelyUniversal = true := rfl
example : (RealMCT.rmB (F := WHyperbolic.F)).isQF = false := rfl
example : (RealMCT.rmC (F := WHyperbolic.F)).isPurelyExistential = true := rfl

/-! **(b) The derivation.** `real_mct_p2 : Derivable F al Premises rmStatement` at *every*
`Allowed` — no excluded middle and no Markov. The window dichotomy is `qf_lem` on the
quantifier-free conclusion matrix, i.e. a decidable rational comparison, which is exactly
Kohlenbach's point about metastability: the ineffectivity of MCT lives in the *Cauchy*
statement, not in the metastable one. The price of taking the dichotomy on a QF matrix is a
budget of `2^{k+1}` windows against the book's `2^k` — a factor 2 in the exponent, recorded in
`ProofMode/RealMCT.lean`'s header. -/
#check @ProofMode.real_mct_p2

/-! **(c) The bound exists as data** — `rmBound` applied to that derivation. -/
#check @ProofMode.real_mct_bound_p2

/-! **(d) …and it means what it should on Mathlib `ℝ`.** `real_mct_of_bound` composes the
metatheorem with the semantic bridge: for every antitone `[0,1]`-valued sequence of *codes*
majorized by `x*`, there is `v ≤ Φ x*` with `|a v − a (v + g v)| < 1/2^k` in Mathlib's reals.
That is `Reference/MCT.lean`'s `metastable`, with `Φ` extracted rather than assumed. -/
#check @RealMCT.real_mct_of_bound

/-! ### What does NOT happen here: a number

`Φ` for ℝ-MCT is **named and type-checked, never evaluated**, and the same is true of ℕ-MCT
(`Probes/MonotoneMCT.lean`'s `mctPhi`). Two blockers, both measured and both named in
`ARCHITECTURE.md` §14.7:

1. **`Eq.mpr` casts buried under the proof-mode layer.** A `closed_subst`-style normalisation
   lemma proves a formula equation *without* computing it; the kernel's K-rule reduction of the
   resulting cast has to redo exactly that computation. Lane D1 (`Dialectica/MonotoneSeq.lean`)
   clears this where the casts can be reached — see the two numerals in §3b below.
2. **The composition combinators re-evaluate their sub-majorants.** `MRealizer.syllogism` uses
   its first argument three times and its second twice, and neither the kernel nor the compiled
   evaluator shares them: ≈×5 per nested syllogism, which dies at depth ≈8. That is the
   Dialectica exponential in its last hiding place, and it applies to every route equally.

Neither is about the monotone interpretation, the proof mode, induction, or formula size —
each of those was tested and cleared (`Probes/MonotoneLaneB.lean`, `Probes/MonotoneMCT.lean`).

### §3b. How far the real-analysis lemmas *do* reduce

The counter transformer of two genuine `≤ℝ` conversion lemmas, fed a challenge index, returns
an index — through 650 and 4167 `Derivable` constructors of ℝ-layer proof-mode script with
`Eq.mpr` casts in them. On the term route both were 12 GB `std::bad_alloc`. -/

#check @MonotoneMemoGates.d2c_is_3   -- `le_R_pu_of_le_R`, 650 constructors  ↦ 3
#check @MonotoneMemoGates.d1c_is_3   -- `le_R_of_le_R_pu`, 4167 constructors ↦ 3

/-! ============================================================================
# §4. The classical entry point

`syntactic_general_metatheorem_classical_at` takes a derivation at `Allowed.classical` — with
`Derivable.lem` available — and routes it `prenexify` → negative translation → `nn_all_nn` →
Dialectica → majorants, returning `Φ` as data with the *same* statement as the intuitionistic
version.

Applied once, below, to `LemBoundDemo.lFinalLem`: the smallest statement in the metatheorem's
shape whose proof genuinely uses excluded middle. (Note the design constraint: `qf_lem` derives
`A ∨ᶠ ¬ᶠA` for quantifier-free `A` with **no** `Derivable.lem` at all, so a case split on the
matrix is free and says nothing about classicality. The minimal honest instance is LEM at the
Π₁ *premise* `∀u B₀`, which is what `lFinalLem` does.)
============================================================================ -/

open LemBoundDemo (lXE lFE lSiE lEqxiE lPremE lSpremiseE lNts lB0 lC0
  lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem lCmE)

/-- **The classical metatheorem, applied.** Type-checks; `Φ` is data. -/
noncomputable def classicalBound :
    { Φ : Ty.interpret lXE Ty.nat.hat → Nat //
      ∀ (x : Ty.interpret lXE Ty.nat) (x_star : Ty.interpret lXE Ty.nat.hat),
        (bezemAbstractEmpty lSiE).toRel.maj Ty.nat x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret lSiE lB0 (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret lSiE lC0 (v, (x, ())) } :=
  syntactic_general_metatheorem_classical_at lEqxiE lNts lSpremiseE lCmE
    lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem

/-! The monotone classical entry point has the same statement, and fuses the negative
translation into the interpretation so `negTrans_sound`'s output is never built. It also
removes the NT-stability side condition entirely. -/
#check @monotone_general_metatheorem_classical_at

/-! ### What does NOT happen here either: a number

`classicalBound.val 5` does not reduce, on **either** route, and the cause is not excluded
middle. `LemBoundDemo`'s `lFinalExt` and `lFinalNoLem` are the *same derivation term at two
`Allowed` values*; the extended one yields `U = 0`, `V = 5` by bare `rfl`
(`LemBoundDemo.lUtExt_at_5` / `lVtExt_at_5`, restated below), and the classical one is
unreachable. What dominates is the classical *plumbing*: `prenexify` alone is 347 constructors
with 134 nested `syllogism`s, and each classical syllogism costs ≈×5 in the counter-side
fan-out — the §3 blocker 2 again. Excluded middle itself is 4,376 constructors of 89,556. -/

/-- The intuitionistic control, same statement: `U = 0` (the premise is not consulted). -/
theorem control_U : (0 : ℕ) = closedMajorizer lCmE LemBoundDemo.lUtExt (5 : ℕ) :=
  LemBoundDemo.lUtExt_at_5

/-- …and `V = 5`. -/
theorem control_V : (5 : ℕ) = closedMajorizer lCmE LemBoundDemo.lVtExt (5 : ℕ) :=
  LemBoundDemo.lVtExt_at_5

/-! ============================================================================
# Axiom hygiene — the project's claims, checked

Expected: object-level derivations `[propext, Quot.sound]`; anything mentioning a model,
Mathlib `ℝ`, or Markov's principle `[propext, Classical.choice, Quot.sound]`. `sorryAx` must
never appear. (`Metatheorems/Headline.lean` does this for every headline declaration.)
============================================================================ -/

#print axioms proofMode
#print axioms phiTerm_at_5_5
#print axioms phiTerm_ne_902
#print axioms u_at_7_5
#print axioms realizerTri_size
#print axioms mfi_U
#print axioms mfi_V
#print axioms mfi_phi
#print axioms mfi_U_ne_900
#print axioms mfi_U_at_7_5
#print axioms contraction_at_5_9
#print axioms contraction_at_5_1
#print axioms contraction_not_one_sided
#print axioms ProofMode.real_mct_p2
#print axioms ProofMode.real_mct_bound_p2
#print axioms RealMCT.real_mct_of_bound
#print axioms classicalBound
#print axioms control_U
#print axioms control_V

end Demo
end Metatheorems
