/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems
import Metatheorems.Hilbert
import Metatheorems.Probes.ContentExampleNat

/-!
# The live walkthrough — scroll from the top, one part at a time

A Lean 4 formalization of **WE-HA^{ω,X}** (Kohlenbach's weakly extensional Heyting arithmetic
in all finite types over an abstract space `X`), Gödel's **Dialectica** interpretation, and the
proof-mining **metatheorems** that turn a proof into a bound.

Six parts, in the order they are meant to be shown:

| § | what is on the screen | costs |
|---|---|---|
| 1 | the proof mode, on a purely logical statement — first contact | instant |
| 2 | the same tactics at a **metric space**: the chained triangle inequality | ~2 s |
| 3 | …and at a **W-hyperbolic space**: extensionality of the convex combination `W` | ~1 s |
| 4 | the **same theorem as §1 from bare `Derivable` constructors** — the contrast | instant |
| 5 | `#hilbert`: what those six tactic lines actually *denote* | ~2 s |
| 6 | **extraction** — two proofs by induction, one linear bound, one exponential | see below |

**Every extraction in §6 is written twice**: once here, commented out, ready to be
uncommented and run on stage with its measured wall-clock time beside it; and once,
uncommented and kernel-checked on every build, in `Metatheorems/Probes/DemoChecks.lean`
(which imports *this* file, so the derivations checked there are literally the ones below —
commented code cannot rot into a lie).

## How to build it

    scripts/build.sh Demo        -- this file
    scripts/build.sh Probes      -- this file plus DemoChecks, which verifies §6

`Demo` is a `lean_lib` but is **not** in `defaultTargets`, so a plain `lake build` is
unaffected.

## Two things to say out loud, because a number on a slide invites the wrong reading

* The bounds below are **magnitudes**, deliberately. Anything routed through this project's
  ℚ/ℝ encoding comes out as a Cantor **pairing code** (`pairN a b = triagN (a+b) + a`), and
  comparing two such codes compares encoded rationals, not sizes. §6 stays at `ι = Empty`,
  where every value is a plain natural number.
* The claim this project defends is **verified mechanical extraction**, not competitive
  bounds. Kohlenbach's own tool is the monotone functional interpretation applied by hand with
  simplification at every step; a machine that never simplifies pays for it.
-/

namespace Metatheorems
namespace Demo

open Formula ProofMode

/-! ============================================================================
# §1. First contact: the proof mode on pure logic

`Derivable F al Premises A` is a **`Type`**: a proof is a term whose head constructors are the
inference rules of the object logic. That makes the object logic a first-class citizen — but a
Hilbert system has no deduction theorem, so writing anything by hand is combinator soup (§4).

The proof mode supplies the deduction theorem. `Seq Δ B` is *definitionally*
`Derivable … (pack Δ B)`, where `pack` folds the hypothesis list `Δ` into a chain of `→ᶠ`, so
`pintro` costs nothing and there is **nothing to verify about the proof mode**: a buggy tactic
can only fail to elaborate. There is no soundness theorem for it and there does not need to be.

The statement below is composition of implications — `(A → B) → (B → C) → (A → C)` — in the
*object* language. `→ᶠ` is object implication; `A`, `B`, `C` are arbitrary object formulas over
an arbitrary signature, so nothing about arithmetic, spaces or the real numbers is involved.
============================================================================ -/

section PureLogic

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}
variable {Γ : Ctx ι} {A B C : Formula F Γ}

/-- **Composition of implications**, in the object logic:
`⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)`.

Five tactic lines. `pmode` opens the hypothesis context; each `pintro` moves an antecedent
into it; `papply h in ha with h1` is forward reasoning — apply the hypothesis `h` to the
hypothesis `ha`, naming the result `h1`; `pexact` closes.

Read on screen, this is an ordinary natural-deduction proof. What it *is* is a term of an
inductive type whose constructors are Hilbert axioms — §5 prints it. -/
def compose_pm : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := by
  pmode
  pintro hAB
  pintro hBC
  pintro ha
  papply hAB in ha with hb
  papply hBC in hb with hc
  pexact hc

/-- The same tactics, one step shorter: contraction, `⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B`.
Kept because it is the cheapest possible `#hilbert` target in §5 — abstract formulas, so no
arithmetic constant can enter the rendering and the listing measures the *proof-mode layer*
rather than the size of the formulas in it. -/
def contract_pm : Derivable F al Premises ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) := by
  pmode
  pintro h
  pintro ha
  papply h in ha with h1
  papply h1 in ha with h2
  pexact h2

end PureLogic

/-! ============================================================================
# §2. The same tactics at a metric space

The metric is **structural**: `Term.dist i` is a term former, not a signature constant, and
equality at a base type is *defined* — `s =_X t` **is** `d(s,t) =ℝ 0ℝ`, where `=ℝ` is a formula
about the encoded reals (a `∀n` over a quantifier-free rational comparison). So the
pseudometric axioms are free `Derivable` constructors — `dist_self`, `dist_comm`, `dist_tri` —
and everything below holds in **every** `Derivable F al Premises`, at every `Allowed`: no
excluded middle, no Markov, no premise set.

The theorem is the chained triangle inequality. It is the project's first *derived*
object-level theorem about a space: everything else said about metric, W-hyperbolic, CAT(0) or
normed spaces is an axiom, a model fact, or a statement about the encoding.

It was **impossible until the `≤ℝ` order package existed**. `Derivable.dist_tri` delivers its
conclusion in the purely universal form `le_R_pu`, and for a long time the `≤ℝ` API was
conversions only — no transitivity, no monotonicity. Chaining two triangle inequalities is the
smallest thing you cannot do without them, which is why four complete space towers derived
nothing at all.
============================================================================ -/

section MetricSpace

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}

/-- **The chained triangle inequality**:
`⊢ d(x,w) ≤ℝ (d(x,y) +ℝ d(y,z)) +ℝ d(z,w)`.

`papplym` applies a *kernel* theorem to the object-level goal, `psplit` splits the
`∧ᶠ`-antecedent it leaves, `pthm` discharges a leaf with a closed derivation. Two uses of the
`dist_tri` constructor, one transitivity, one additive monotonicity, one re-association.

(Adapted from `Metatheorems.dist_tri_chain` in `BaseEquality.lean`.) -/
def demo_dist_tri_chain {Γ : Ctx ι} (i : ι) (x y z w : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (le_R (Term.app2 (Term.dist i) x w)
        (Term.app2 Term.add_R
          (Term.app2 Term.add_R
            (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))
          (Term.app2 (Term.dist i) z w))) :=
  let dxy : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x y
  let dyz : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y z
  let dzw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) z w
  let dyw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y w
  let dxw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x w
  let rassoc : Term F Γ (realTy ι) := Term.app2 Term.add_R dxy (Term.app2 Term.add_R dyz dzw)
  let lassoc : Term F Γ (realTy ι) := Term.app2 Term.add_R (Term.app2 Term.add_R dxy dyz) dzw
  by
  pmode
  papplym (le_R_trans_core dxw rassoc lassoc)
  psplit
  · papplym (le_R_trans_core dxw (Term.app2 Term.add_R dxy dyw) rassoc)
    psplit
    · -- `d(x,w) ≤ℝ d(x,y) +ℝ d(y,w)` — the constructor, converted out of `le_R_pu`
      pthm (Derivable.mp (Derivable.dist_tri i x y w)
        (le_R_of_le_R_pu dxw (Term.app2 Term.add_R dxy dyw)))
    · -- `d(y,w) ≤ℝ d(y,z) +ℝ d(z,w)`, under `d(x,y) +ℝ ·`
      papplym (le_R_add_mono_l_core dxy dyw (Term.app2 Term.add_R dyz dzw))
      pthm (Derivable.mp (Derivable.dist_tri i y z w)
        (le_R_of_le_R_pu dyw (Term.app2 Term.add_R dyz dzw)))
  · -- re-associate: `a +ℝ (b +ℝ c) =ℝ (a +ℝ b) +ℝ c`
    papplym (le_R_of_eq_R_core rassoc lassoc)
    pthm (Derivable.mp (add_assoc_R_core dxy dyz dzw) (eq_R_sym_core lassoc rassoc))

/-- **The reverse triangle inequality**, the other orientation:
`⊢ d(y,z) −ℝ d(x,z) ≤ℝ d(x,y)`.

Seven lines. `Metatheorems.dist_rev_tri` at `(y,x,z)` gives it with `d(y,x)` on the right;
`dist_comm` — again a free constructor — turns that into `d(x,y)`.

`Probes/RevTriangleDemo.lean` reads this back through `MetricModel.soundness` in an
*arbitrary* Mathlib `MetricSpace` as `M.d a c − M.d b c ≤ M.d a b`: the first time a *derived*
object-level theorem was checked in a model, rather than an axiom being discharged into one. -/
def demo_dist_rev_tri {Γ : Ctx ι} (i : ι) (x y z : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.sub_R
              (Term.app2 (Term.dist i) y z) (Term.app2 (Term.dist i) x z))
            (Term.app2 (Term.dist i) x y)) :=
  let dyx : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y x
  let dxy : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x y
  let s : Term F Γ (realTy ι) :=
    Term.app2 Term.sub_R (Term.app2 (Term.dist i) y z) (Term.app2 (Term.dist i) x z)
  by
  pmode
  papply (le_R_trans_core s dyx dxy)
  psplit
  · pthm (dist_rev_tri i y x z)
  · papply (le_R_of_eq_R_core dyx dxy)
    pthm (Derivable.dist_comm i y x)

end MetricSpace

/-! ============================================================================
# §3. …and at a W-hyperbolic space

A W-hyperbolic space is a metric space with a convex-combination operation
`W(x,y,λ)` for `λ ∈ [0,1]`, satisfying (W1)–(W4). Here `ι = Unit` (one base type `X`) and the
signature has exactly **one** constant, `W : X →ₜ X →ₜ ℝ →ₜ X`; the four axioms are the
project's first non-empty `Premises`, and `WHyperbolicModel.axiomsHold` discharges all four in
any Mathlib-level model, so the metatheorems for this space take no axioms argument.

`λ ∈ [0,1]` is a quantifier over a *subset* of type 1, which the metatheorem cannot take. The
standard move is Kohlenbach's: a retraction `λ̃ = clamp01 λ` under which **every** `f : ℕ → ℕ`
codes an element of `[0,1]`. That is why `W`'s third argument is written `clamp01 l`
everywhere below, and it is what makes the majorant of `W` independent of `λ`.

## Why extensionality has to be *derived*

The ambient system is **weakly** extensional: `WE-HA^{ω,X}` has only quantifier-free
extensionality (`Derivable.qfer`), and full extensionality is deliberately unavailable — it is
exactly what would break the metatheorems. So adding a constant `W` to the signature is only
legitimate if `W`'s extensionality follows from the space's own axioms. For W-hyperbolic
spaces it does, and the proof below is that derivation: (W4) supplies the two carrier
arguments, (W2) the parameter.

The mechanism is worth stating once, because it is what makes the proof short: `s =_X t`
**is** `d(s,t) =ℝ 0ℝ`, so a nonexpansiveness bound `d(W…, W…) ≤ℝ c ·ℝ d(s,t)` collapses as
soon as the product does — and a product with a known-zero factor needs no order theory about
`·ℝ` at all.
============================================================================ -/

section WHyperbolicSpace

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **Full extensionality of `W`**:

    x =_X x'  ∧  y =_X y'  ∧  λ =ℝ μ   →   W(x,y,λ̃) =_X W(x',y',μ̃)

Stated as an object-level implication from the conjunction, so it is a *theorem of the
theory*, not a derived rule. The three one-argument cases (`W_ext_left`, `W_ext_right`,
`W_ext_param`, each ~5 lines in `WHyperbolicLemmas.lean`) chained by transitivity of base-type
equality. `pdestruct` takes the conjunction apart; `∧ᶠ` is left-associative, so the hypothesis
is `(x =_X x' ∧ y =_X y') ∧ λ =ℝ μ`.

(Adapted from `Metatheorems.WHyperbolic.W_ext`.) -/
def demo_W_ext (x x' y y' : Term WHyperbolic.F Γ xTy) (l m : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy x x' ∧ᶠ eqAtType xTy y y' ∧ᶠ eq_R l m →ᶠ
        eqAtType xTy
          (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
          (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 m))) := by
  pmode
  pintro hyp
  pdestruct hyp with hxy hl
  pdestruct hxy with hx hy
  papplym (eqAtType_trans_base ()
    (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
    (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 l))
    (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 m)))
  psplit
  · papplym (eqAtType_trans_base ()
      (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
      (Term.app3 WHyperbolic.W x' y (.app Term.clamp01 l))
      (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 l)))
    psplit
    · papplym (WHyperbolic.W_ext_left x x' y l)
      pexact hx
    · papplym (WHyperbolic.W_ext_right x' y y' l)
      pexact hy
  · papplym (WHyperbolic.W_ext_param x' y' l m)
    pexact hl

end WHyperbolicSpace

/-! ============================================================================
# §4. The same theorem as §1, from bare `Derivable` constructors

This is the contrast. `compose_pm` (§1) and `compose_raw` (here) prove **the same formula**.
One is five tactic lines; the other is what a Hilbert system actually offers.

There is no `syllogism` *axiom* — `Derivable.syllogism` is a **rule**, so it cannot be
discharged into the object implication. What is available is: conjunction weakening
(`and_weak`), permutation (`and_perm`), contraction (`and_contract`), and the two structural
rules `exportation : (A ∧ᶠ B →ᶠ C) → (A →ᶠ B →ᶠ C)` and `importation`, its converse. Every
step below is one of those.

`pair_h` and `eval_h` are Lean-level helpers from `PropositionalLemmas.lean` — themselves
built from exactly these constructors, no tactics — that build `H →ᶠ X ∧ᶠ Y` from `H →ᶠ X`
and `H →ᶠ Y`, and `H →ᶠ B` from `H →ᶠ (A →ᶠ B)` and `H →ᶠ A`. Without them the same proof is
about thirty `let`s.

**This is not a straw man.** Raw-constructor derivations are what §6 mines: they are 145
constructors where the proof-mode form of the same argument is 42,747, and on the current
evidence the proof mode is a *liability* for extraction, not the route to it. §1–§3 are how
mathematics gets written; §4 is what the extractor prefers to read. Reconciling the two is
open work.
============================================================================ -/

section RawHilbert

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}
variable {Γ : Ctx ι} {A B C : Formula F Γ}

/-- **Composition of implications, from raw constructors**:
`⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)` — the same formula `compose_pm` proves in §1.

Write `H := ((A→B) ∧ᶠ (B→C)) ∧ᶠ A` for the fully importated antecedent. Project the three
components out of it with `and_weak`/`and_perm`, apply twice, then `exportation` twice to
peel `H` back into a chain of implications. -/
def compose_raw : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) :=
  -- `H := ((A →ᶠ B) ∧ᶠ (B →ᶠ C)) ∧ᶠ A`, since `∧ᶠ` is left-associative.
  let getAB : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ (A →ᶠ B)) :=
    .syllogism .and_weak .and_weak
  let getBC : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ (B →ᶠ C)) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let getA : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ A) :=
    .syllogism .and_perm .and_weak
  let getB := eval_h getAB getA            -- H →ᶠ B
  let getC := eval_h getBC getB            -- H →ᶠ C
  .exportation (.exportation getC)

/-- The two really are the same theorem — Lean checks it by `rfl` on the *statement*, not on
the two proof terms, which are wildly different objects. -/
example : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := compose_raw
example : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := compose_pm

end RawHilbert

/-! ============================================================================
# §5. `#hilbert`: what those tactic lines denote

`Derivable` is `Type`-valued, so a proof in this development *is* a proof tree in the object
logic. `#hilbert` walks that term and writes the numbered Hilbert listing, in Markdown and
LaTeX. Sharing is preserved: each distinct subproof is numbered once and cited by line number
afterwards, which is what a paper proof does anyway.

`depth n` says how many definition levels of the proof-mode layer to expand before citing what
remains by name; `keeping g` never expands `g` whatever else is said; `all` expands the
propositional combinators too. (Note `unfolding *` does **not** exist — the parser takes
identifiers.)

**The size is the argument for having a proof mode.** Five tactic lines of §1 denote:

| invocation | steps | wall |
|---|---|---|
| `contract_pm` (depth 0) | 12 | 66 ms |
| `contract_pm depth 2` | 54 | 0.24 s |
| `contract_pm depth 4` | 117 | 1.3 s |
| `contract_pm depth 6` and `depth 10` | **120** — a fixed point | 1.1 s |
| `contract_pm all depth 10` | **1844** raw-axiom steps | 15.3 s |

The fixed point at 120 is a genuine Hilbert derivation: 30 modus ponens, 24 `S`, 20
`weaken_intro_h`, 4 `I`, 2 `K`, and no `ProofMode` name anywhere. With `all` the combinators
expand too and the same proof is 1844 steps.

Those figures are from `Probes/HilbertDepth.lean`, which also records the ceiling on a *real*
derivation and what causes it: on `ProofMode.mct_descent` (112 steps of ℕ-MCT), `depth 1` is a
heartbeat timeout, and `keeping seq_id` — that one constant, hypothesis lookup, which recurses
on the context through `HVar.rec` with a dependent cast per level — turns it into **1766 steps
in 18.5 s**. Depth 3 does not exist at any `keeping` tried. The wall at the top is the
*delaborator*, not the traversal.

The commands below regenerate `Demo/hilbert/`. Absolute paths: `#hilbert … to` resolves
relative to the process's working directory, which is not this file's.
============================================================================ -/

#hilbert contract_pm
  to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/contract_pm_d0"
#hilbert contract_pm depth 4
  to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/contract_pm_d4"
#hilbert compose_pm
  to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/compose_pm_d0"
#hilbert compose_raw
  to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/compose_raw"

-- The fixed point, and the fully expanded 1844-step listing — uncomment to run live
-- (≈1.1 s and ≈15.3 s respectively; the second is too slow to sit in the build):
-- #hilbert contract_pm depth 10
--   to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/contract_pm_d10"
-- #hilbert contract_pm all depth 10
--   to "/home/horatiu/LeanMisc/metatheorems/.worktrees/demo-lane/Demo/hilbert/contract_pm_all"
--   ⟹ 120 steps, then 1844. Five tactic lines; 1844 applications of Hilbert axioms.

/-! ============================================================================
# §6. Extraction — the centrepiece

## What the metatheorem says

For a statement in the shape

    ∀x^ρ ( ∀u^ℕ B₀(u,x)  →  ∃v^ℕ C₀(v,x) )

with `B₀`, `C₀` quantifier-free and ∨-free, the metatheorem produces a **computable functional
`Φ`** such that, in every model, for every `x` majorized by `x*`:

    (∀u ≤ Φ x*. B₀)  →  ∃v ≤ Φ x*. C₀

`Φ = max U V`, where `V` bounds the existential witness and `U` bounds *how far into the
premise `∀u B₀` the proof reaches*. Both are extracted from the derivation. `Φ` is **data**:
`monotone_general_metatheorem_at` returns a `Subtype`, not an `∃`, so the bound is a `def` a
tactic can evaluate.

The route used here is the **monotone** functional interpretation (Kohlenbach, *Applied Proof
Theory*, Ch. 9, Thm 9.1): rather than build the Dialectica realizer and then majorize it,
compute a majorant of the realizer directly by recursion on the derivation, leaving the
realizer itself existential. Because `Ty.hat` sends every base type to `nat`, the majorant is a
plain Lean value built from `ℕ`/`unit`/`×`/`→` — no object-level `Term` on the bound path,
hence no `weaken`, no `rename`, no dependent casts for the kernel to reduce.

## The instrument

`kernel_rfl` (from `Probes/MonotoneLaneB.lean`) assigns `Eq.refl` and lets the **kernel** decide
the equation. That is the evaluator of record here, not `#eval` and not bare `rfl`: nothing
below rests on compiler trust. Every numeral also has a **refutation control** — a theorem that
the neighbouring value is *not* the bound — because a `rfl` that gets stuck and a `rfl` that
computes are otherwise indistinguishable from a green build.

## The thesis, in one sentence

**The bound mirrors the recursion in the proof.** Two derivations follow; both use the *same*
`Derivable.induction` rule. One has a linear bound and one an exponential one, and the
difference is visible in the proofs.
============================================================================ -/

open MonotoneMCT (cmE)
open TinyBoundDemo (tXE tFE tSiE tEqxiE tPremE tSpremiseE tB0 tC0)

/-! ## 6a. A proof whose witness is a projection ⟹ a LINEAR bound

Statement: `∀x ( ∀u (u =₀ u) → ∃v (v =₀ x) )`.

Proved by induction on `x`, with the witness at every step being the induction variable
itself. Nothing is built *from* the previous witness, so the primitive recursion that
Dialectica assigns to `Derivable.induction` has nothing to iterate. -/

/-- **The derivation.** `∀x (∀u (u =₀ u) → ∃v (v =₀ x))`, by `pinduction`; the witness is
`0` in the base case and `S x₀` in the step. 368 `Derivable` constructors.
(Restated from `Probes/MonotoneMCT.lean`'s `indFinal`.) -/
def linearInduction : @Derivable Empty Empty tFE Allowed.extended tPremE []
    (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) := by
  pmode
  pinduction
  · pintro h
    pexists Term.zero
    pthm Derivable.refl0
  · pforall
    pintro ih
    pintro h
    pexists (Term.app Term.succ (Term.var Var.vz))
    pthm Derivable.refl0

/-- The monotone realizer of it — an ordinary `def`, elaborates instantly. -/
def linearR : MRealizer cmE
    (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) :=
  monotone_soundness tEqxiE tSpremiseE cmE linearInduction

/-- Majorants of `x` to evaluate at. -/
def at5 : Ty.interpret tXE Ty.nat.hat := (5 : ℕ)
def at9 : Ty.interpret tXE Ty.nat.hat := (9 : ℕ)

-- Extraction — uncomment to run live (≈2 s of kernel time each):
--
-- theorem lin_V_5 : (5 : ℕ) = mfiV cmE linearR at5 := by kernel_rfl
-- theorem lin_V_9 : (9 : ℕ) = mfiV cmE linearR at9 := by kernel_rfl
-- theorem lin_U_5 : (0 : ℕ) = mfiU cmE linearR at5 := by kernel_rfl
-- theorem lin_V_5_ne_4 : (4 : ℕ) ≠ mfiV cmE linearR at5 := by rw [← lin_V_5]; decide
--
--   ⟹ V(k) = k. Linear, and it moves with the input. U = 0 because the premise
--     `∀u (u =₀ u)` is never consulted — nothing is read out of it at any step.

/-! ## 6b. A proof whose witness is built from the previous one ⟹ an EXPONENTIAL bound

Statement (`ρ := nat ×ₜ (nat →ₜ nat)`, `x = (k, f)`):

    ∀x ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f k =₀ v ) )

*If `f` doubles at every step, then `f k` is bounded* — and the metatheorem's `v ≤ Φ x*` is
that bound.

Same induction rule. But now the step case takes the witness `w` the induction hypothesis
supplies and returns `w +ᵗ w`:

```lean
    def inner3 : D G2 (C2 ∧ᶠ E2f →ᶠ Formula.weakenBy Ty.nat R1) :=
      Derivable.syllogism
        (pair_h and_proj2 (Derivable.syllogism and_proj1 cong2))
        (Derivable.syllogism Derivable.trans0
          (Derivable.exist_ax (Term.app2 Term.add v2 v2) CS3))
    --                        ^^^^^^^^^^^^^^^^^^^^^^^^^^ the new witness, `v +ᵗ v`
```

Dialectica interprets `Derivable.induction` as primitive recursion (`MRealizer.induction` =
`cm.precM` = `recMaj`, Kohlenbach's `t^M`). A witness built *from* the previous witness makes
that recursion iterate, and the doubling in the proof comes out as an exponential in the bound.

Two things that make this a demonstration rather than an anecdote. The premise is genuinely
**consumed** — `forall_ax k` instantiates `∀u B₀` at `u := k`, once per step, so `U` reports a
property of the proof and not a default. And **no witness term written by hand mentions
`Term.prec`**: the surface-recursor ban (`ProofMode/Linter.lean`) is enforced, so the iteration
in the bound is produced by the extraction, not smuggled into the derivation. -/

/-- **The derivation.** 145 raw `Derivable` constructors, built in
`Probes/ContentExampleNat.lean` from `induction`, `forall_ax`, `exist_ax`, `exist_rule`,
`syllogism`, `exportation` and one quantifier-free extensionality step — no proof mode at all.
Its fifteen named pieces are worth scrolling through in that file; the one that matters is
`inner3`, quoted above. -/
def doubling := ContentExampleNat.eFinal

/-- Its monotone realizer. -/
def doublingR := ContentExampleNat.rE

/-- `x* = (k*, λn. n+1)`, so the majorant of `f` at `0` is `1`. -/
def xs (k : ℕ) : Ty.interpret tXE ContentExampleNat.sTy.hat := ContentExampleNat.xs k
/-- `x* = (k*, λn. n+3)` — the *other* component of the majorant, so `f*(0) = 3`. -/
def ys (k : ℕ) : Ty.interpret tXE ContentExampleNat.sTy.hat := ContentExampleNat.ys k

-- Extraction, the witness side — uncomment to run live
-- (≈1 s at k*=0, ≈2 s at k*=3, ≈3 s at k*=5):
--
-- theorem exp_V_0 : (1 : ℕ) = mfiV cmE doublingR (xs 0) := by kernel_rfl
-- theorem exp_V_3 : (8 : ℕ) = mfiV cmE doublingR (xs 3) := by kernel_rfl
-- theorem exp_V_5 : (32 : ℕ) = mfiV cmE doublingR (xs 5) := by kernel_rfl
-- theorem exp_V_3_ne_7 : (7 : ℕ) ≠ mfiV cmE doublingR (xs 3) := by rw [← exp_V_3]; decide
--
--   ⟹ V(k*, f*) = 2^{k*} · f*(0). Exponential — and it is *tight*: 2^k·f(0) is exactly f k.

-- …and it tracks the function majorant, not only the index (≈1 s, ≈2 s):
--
-- theorem exp_V_ys_0 : (3 : ℕ) = mfiV cmE doublingR (ys 0) := by kernel_rfl
-- theorem exp_V_ys_2 : (12 : ℕ) = mfiV cmE doublingR (ys 2) := by kernel_rfl
--
--   ⟹ f*(0) = 3 triples every value: 2^2 · 3 = 12, not the 4 that f*(0) = 1 would give.

-- The premise side — U is NOT a copy of V, and it is sharp (≈1–3 s each):
--
-- theorem exp_U_0 : (0 : ℕ) = mfiU cmE doublingR (xs 0) := by kernel_rfl
-- theorem exp_U_2 : (1 : ℕ) = mfiU cmE doublingR (xs 2) := by kernel_rfl
-- theorem exp_U_3 : (2 : ℕ) = mfiU cmE doublingR (xs 3) := by kernel_rfl
-- theorem exp_U_5 : (4 : ℕ) = mfiU cmE doublingR (xs 5) := by kernel_rfl
--
--   ⟹ U(k*) = k* − 1, exactly: the step at k consults ∀u B₀ at u := k, for k = 0 … k*−1.
--     "How far into the premise the proof reaches", as a genuine function of x*.

-- Φ, through the metatheorem itself (≈2 s, ≈4 s):
--
-- theorem exp_Phi_3 : (8 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
--     ContentExampleNat.eB_qf ContentExampleNat.eB_vf
--     ContentExampleNat.eC_qf ContentExampleNat.eC_vf doubling).val (xs 3) := by kernel_rfl
-- theorem exp_Phi_5 : (32 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
--     ContentExampleNat.eB_qf ContentExampleNat.eB_vf
--     ContentExampleNat.eC_qf ContentExampleNat.eC_vf doubling).val (xs 5) := by kernel_rfl
--
--   ⟹ Φ = max U V, from the metatheorem's own entry point rather than its two components.

/-! ## 6c. ⚠ THE CEILING — do not type `8` or more on stage

On this **same** 145-constructor derivation, with nothing else changed:

| `k*` | `V` | outcome |
|---|---|---|
| 5 | 32 | ≈3 s |
| **7** | **128** | kernel-checked, **≈9 s** |
| **8** | 256 | **`INTERNAL PANIC: out of memory` at the 12 GB cap** |

The ceiling is the **value**, not the derivation and not the proof: the majorant of the
object-level `Term.add` is a `prec` term, so `recMaj` iterates *value*-many times with nothing
shared. `k* = 7` is the last one that finishes.

    -- theorem exp_V_7 : (128 : ℕ) = mfiV cmE doublingR (xs 7) := by kernel_rfl   -- ≈9 s
    -- theorem exp_V_8 : (256 : ℕ) = mfiV cmE doublingR (xs 8) := by kernel_rfl   -- OOM

## 6d. What the two together show

Same rule, two proofs, two growth rates — and the growth rate is read off the *proof*, not the
theorem. That is the whole content of "a bound is a property of a proof". `ProofMode/MCT.lean`
and `ProofMode/MCTLazy.lean` are the same contrast at scale: two derivations of one ℕ-MCT
statement, one of which is constructive and one of which must be hand-translated.

## 6e. Where this stops, stated plainly

The derivations with real mathematical content — `ProofMode.real_mct_p2` (ℝ-MCT in metastable
form, 655 lines), `dist_tri_chain` of §2, `mct_p2` — have their `Φ` **named and type-checked,
never evaluated**. Two blockers, both measured, both in `ARCHITECTURE.md` §14.7, and neither of
them the monotone interpretation, the proof mode, induction, or formula size (each of those was
tested and cleared):

1. **`Eq.mpr` casts buried under the proof-mode layer.** A `closed_subst`-style normalisation
   lemma proves a formula equation *without* computing it; the kernel's K-rule reduction of the
   resulting cast has to redo exactly that computation.
2. **The composition combinators re-evaluate their sub-majorants.** `MRealizer.syllogism` uses
   its first argument three times and its second twice, and neither the kernel nor the compiled
   evaluator shares them — measured at ×3.7 per nesting level at depth 6, which dies around
   depth 8. That is the Dialectica exponential in its last hiding place, and it applies to
   every route equally, classical and intuitionistic alike.

Accuracy notes for anyone quoting this on a slide: `real_mct_p2` proves the **metastable**
statement, a bare `∃v` with no bound in it; and *the metastable form* needs no classical logic
(it holds at every `Allowed`) — which is not the same claim as "MCT needs no classical logic".
============================================================================ -/

#check @ProofMode.real_mct_p2
#check @ProofMode.real_mct_bound_p2
#check @RealMCT.real_mct_of_bound

/-! ============================================================================
# Axiom hygiene — the claims, checked

Expected: object-level derivations `[propext, Quot.sound]`; anything mentioning a model,
Mathlib `ℝ`, or Markov's principle `[propext, Classical.choice, Quot.sound]`. `sorryAx` must
never appear anywhere. (`Metatheorems/Headline.lean` does this for every headline declaration
in the project; `Probes/DemoChecks.lean` does it for the §6 numerals.)
============================================================================ -/

#print axioms compose_pm
#print axioms compose_raw
#print axioms demo_dist_tri_chain
#print axioms demo_dist_rev_tri
#print axioms demo_W_ext
#print axioms linearInduction
#print axioms doubling
#print axioms ProofMode.real_mct_p2

end Demo
end Metatheorems
