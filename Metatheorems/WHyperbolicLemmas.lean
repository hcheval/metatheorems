/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolic

/-!
# A library of derived theorems about W-hyperbolic spaces

Everything here is derived **in the object theory** from the four axioms (W1)–(W4) of
`WHyperbolic.lean` (through `.premise`, i.e. `WHyperbolic.W1`–`W4`) together with the free
`Derivable` constructors `dist_self`/`dist_comm`/`dist_tri` and the ℝ layer. Each theorem
holds in every `Derivable WHyperbolic.F al WHyperbolic.Premises` — at every `Allowed`, no LEM,
no Markov — and each is read back in an arbitrary `WHyperbolicModel` in
`Probes/WHyperbolicLemmasDemo.lean` through `WHyperbolicModel.soundness`.

`WHyperbolic.lean` already contains the first such theorem, `WHyperbolic.W_self`
(`W(x,x,λ̃) =_X x`). This file is the chain above it.

## The correspondence to Kohlenbach, *Applied Proof Theory*, §17.2

Kohlenbach (following Kirk, and Kohlenbach–Leuştean) states, for a W-hyperbolic space and
`λ ∈ [0,1]`:

* `d(x, W(x,y,λ)) = λ·d(x,y)` and `d(y, W(x,y,λ)) = (1−λ)·d(x,y)` — the *geodesic* property,
  i.e. `W(x,y,λ)` is the point of the segment `[x,y]` at fraction `λ`. He derives it from
  (W1) plus the triangle inequality: (W1) gives both `≤`, and the triangle inequality
  `d(x,y) ≤ d(x,W) + d(W,y)` forbids either from being strict.
* `W(x,y,0) = x`, `W(x,y,1) = y`, `W(x,x,λ) = x`.
* `d(W(x,y,λ), W(x,y,μ)) = |λ−μ|·d(x,y)` — that is (W2) itself.
* (W4) makes `W(·,·,λ)` nonexpansive in each argument separately.

## What is here

| name | statement | Kohlenbach |
|---|---|---|
| `W1_at` | (W1) at arbitrary terms, as `≤ℝ` | (W1) |
| `W4_at` | (W4) at arbitrary terms, as `≤ℝ` | (W4) |
| `dist_W_left` | `d(x, W(x,y,λ̃)) ≤ℝ λ̃ ·ℝ d(x,y)` | half of the geodesic property |
| `dist_W_right` | `d(y, W(x,y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)` | the other half |
| `dist_W_left_lower` | `d(x,y) −ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x) ≤ℝ d(x, W(x,y,λ̃))` | reverse inequality |
| `W_zero` | `W(x,y,0ℝ~) =_X x` | `W(x,y,0) = x` |
| `W_one` | `W(x,y,1ℝ~) =_X y` | `W(x,y,1) = y` |
| `dist_W_mono_right` | `d(W(x,y,λ̃), W(x,y',λ̃)) ≤ℝ λ̃ ·ℝ d(y,y')` | (W4), nonexpansive in `y` |
| `dist_W_mono_left` | `d(W(x,y,λ̃), W(x',y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(x,x')` | (W4), in `x` |

`λ̃` is `clamp01 λ` throughout — the object-level `[0,1]`-retraction, exactly as the axioms
of `WHyperbolic.lean` are stated. `0ℝ~` and `1ℝ~` above mean `clamp01 0ℝ` and `clamp01 1ℝ`;
the statements are at the clamped parameter because that is the only form the axioms speak
about, and `clamp01_eq_core` is what identifies them with `0ℝ`/`1ℝ`.

## The ℝ lemmas this needed, and the one that is missing

New here (generic, no `W` in sight — they belong in `RealNumbers/`, and are kept in this
file only so that no module below it is touched in this pass, exactly as `WHyperbolic.lean`
keeps `mul_eq_zero_R_core`):

* `mul_zero_l_R : f =ℝ 0ℝ →ᶠ f ·ℝ g =ℝ 0ℝ` — `mul_eq_zero_R_core` is stated for the *right*
  factor; this is `mul_comm_R_core` on top of it.
* `zero_add_le_R` / `zero_le_R_one` / `eqR_of_le_le` / `eqX_of_dist_le_zero` — one-line
  packagings of `add_zero_R_core`, `zero_lt_one_R`, `le_R_antisymm_core`, `dist_nonneg`.

**NOT DONE, and this is the honest boundary of the chain: the equality versions.**
Kohlenbach's `d(x, W(x,y,λ)) = λ·d(x,y)` and the (W2) corollary
`d(W(x,y,λ), W(x,y,μ)) ≤ d(x,y)` both need **multiplicative monotonicity of `≤ℝ`**,

    `0ℝ ≤ℝ f → g ≤ℝ g' → f ·ℝ g ≤ℝ f ·ℝ g'`,

and the ℝ layer does not have it — `RealNumbers/Order.lean` has only the *strict* product
fact `lt_mul_pos_R` (`0 <ℝ f → 0 <ℝ g → 0 <ℝ f ·ℝ g`), and `RealNumbers/Mul.lean` has the ring
identities but no order. Nor is it derivable from what is there: the natural route
`f ·ℝ g' =ℝ f ·ℝ (g +ℝ (g' −ℝ g)) =ℝ f ·ℝ g +ℝ f ·ℝ (g' −ℝ g)` needs an `=ℝ`-congruence for
`·ℝ` in its second argument, and *that* is again multiplicative monotonicity (the additive
congruence, by contrast, **is** derivable from `le_R_add_mono_*` plus `le_R_antisymm_core`,
which is why nothing additive is blocked). So it is a genuine new estimate in the
`cauchyfy` layer — of the shape of `mul_R_check` — and was not attempted here.

What that costs, precisely:

* `dist_W_left_lower` is proved and is exactly Kohlenbach's reverse inequality with the
  arithmetic left undone: its left-hand side is `d(x,y) −ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)`, which
  equals `λ̃ ·ℝ d(x,y)` by `distrib_R_core` **and** the missing congruence (to turn `d(y,x)`
  into `d(x,y)` under the product). With the congruence, `le_R_antisymm_core` against
  `dist_W_left` gives the equality with no further work.
* `dist_W_right` is stated with `d(y,x)`, not `d(x,y)`. `dist_comm` gives
  `d(y,x) =ℝ d(x,y)`, but there is no way to rewrite under `·ℝ` — same missing congruence.
  The statement is *not* weakened: it is what (W1) at `z := y` literally gives.
-/

namespace Metatheorems

open Formula

-- ============================================================================
-- Generic ℝ helpers (no `W`; they belong one layer down)
-- ============================================================================

section RHelpers

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **`f =ℝ 0ℝ →ᶠ f ·ℝ g =ℝ 0ℝ`** — the left-factor form of `mul_eq_zero_R_core`, obtained
from it by `mul_comm_R_core`. -/
def mul_zero_l_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f Term.zero_R →ᶠ eq_R (Term.app2 Term.mul_R f g) Term.zero_R) := by
  pmode
  pintro h
  papplym (eq_R_trans_core (Term.app2 Term.mul_R f g) (Term.app2 Term.mul_R g f) Term.zero_R)
  psplit
  · pthm (mul_comm_R_core f g)
  · papplym (mul_eq_zero_R_core g f)
    pexact h

/-- `0ℝ +ℝ f ≤ℝ f`. -/
def zero_add_le_R (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R (Term.app2 Term.add_R Term.zero_R f) f) :=
  leR_of_eq (eqRt (add_comm_R_core Term.zero_R f) (add_zero_R_core f))

/-- `f +ℝ 0ℝ ≤ℝ f`. -/
def add_zero_le_R (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R (Term.app2 Term.add_R f Term.zero_R) f) :=
  leR_of_eq (add_zero_R_core f)

/-- `0ℝ ≤ℝ 1ℝ`. -/
def zero_le_R_one :
    Derivable F al Premises (Γ := Γ) (le_R Term.zero_R Term.one_R) :=
  Derivable.mp zero_lt_one_R (lt_imp_le_R_core Term.zero_R Term.one_R)

/-- Antisymmetry, Lean-level. -/
def eqR_of_le_le {f g : Term F Γ (realTy ι)}
    (h1 : Derivable F al Premises (le_R f g)) (h2 : Derivable F al Premises (le_R g f)) :
    Derivable F al Premises (eq_R f g) :=
  Derivable.mp (Derivable.mp h2 (Derivable.mp h1 and_intro)) (le_R_antisymm_core f g)

/-- **`d(s,t) ≤ℝ 0ℝ` makes `s` and `t` equal at the base type.** `dist_nonneg` supplies the
other half and `le_R_antisymm_core` closes; `eqAtType (.base i) s t` *is* `d(s,t) =ℝ 0ℝ`. -/
def eqX_of_dist_le_zero {i : ι} (s t : Term F Γ (Ty.base i))
    (h : Derivable F al Premises (le_R (Term.app2 (Term.dist i) s t) Term.zero_R)) :
    Derivable F al Premises (eqAtType (Ty.base i) s t) :=
  eqR_of_le_le h (dist_nonneg i s t)

end RHelpers

namespace WHyperbolic

open Metatheorems.WHyperbolic (F d W)

-- ============================================================================
-- The axioms at arbitrary terms
-- ============================================================================

section AxiomsAt

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **(W1) at arbitrary terms**, and as a plain `≤ℝ` rather than the purely universal
`le_R_pu` the axiom is stated with:

    `d(z, W(x,y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(z,x) +ℝ λ̃ ·ℝ d(z,y)`.

This is the rung everything else in the file stands on: with it, every later theorem is
Lean-level composition of `Derivable.mp`s with the ℝ order package, and no further
proof-mode instantiation is needed. The proof is `WHyperbolic.W_self_core`'s opening,
factored out: four `pinst`/`znorm` rounds, `wfold` to bring the instance to the fully folded
weakening normal form, then `le_R_of_le_R_pu_nf`. -/
def W1_at (z x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ()) z
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
            (Term.app2 (Term.dist ()) z x))
          (Term.app2 Term.mul_R (.app Term.clamp01 l)
            (Term.app2 (Term.dist ()) z y)))) := by
  pmode
  pfrom w1 := WHyperbolic.W1
  simp only [WHyperbolic.ax_W1, le_R_pu, Term.app3]
  pinst w1 z with w2
  znorm
  pclear w1
  pinst w2 x with w3
  znorm
  pclear w2
  pinst w3 y with w4
  znorm
  pclear w3
  pinst w4 l with w5
  znorm
  pclear w4
  wfold
  papplym (le_R_of_le_R_pu_nf
    (Term.app2 (Term.dist ()) z (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
        (Term.app2 (Term.dist ()) z x))
      (Term.app2 Term.mul_R (.app Term.clamp01 l) (Term.app2 (Term.dist ()) z y)))
    (Term.app2 (Term.dist ()) z.weaken
      (Term.app3 (Term.func ()) x.weaken y.weaken (.app Term.clamp01 l.weaken)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l.weaken))
        (Term.app2 (Term.dist ()) z.weaken x.weaken))
      (Term.app2 Term.mul_R (.app Term.clamp01 l.weaken)
        (Term.app2 (Term.dist ()) z.weaken y.weaken)))
    (by simp only [Term.app2, Term.app3, weaken_app, dist_weaken, func_weaken, clamp01_weaken])
    (by simp only [Term.app2, weaken_app, dist_weaken, clamp01_weaken,
      sub_R_weaken, one_R_weaken'', add_R_weaken'', mul_R_weaken''])) in w5 with hle
  pexact hle

/-- **(W4) at arbitrary terms**, as a plain `≤ℝ`:

    `d(W(x,z,λ̃), W(y,w,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(x,y) +ℝ λ̃ ·ℝ d(z,w)`.

Same shape as `W1_at`, one binder more. -/
def W4_at (x y z w : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ())
          (Term.app3 (Term.func ()) x z (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) y w (.app Term.clamp01 l)))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
            (Term.app2 (Term.dist ()) x y))
          (Term.app2 Term.mul_R (.app Term.clamp01 l)
            (Term.app2 (Term.dist ()) z w)))) := by
  pmode
  pfrom w1 := WHyperbolic.W4
  simp only [WHyperbolic.ax_W4, le_R_pu, Term.app3]
  pinst w1 x with w2
  znorm
  pclear w1
  pinst w2 y with w3
  znorm
  pclear w2
  pinst w3 z with w4
  znorm
  pclear w3
  pinst w4 w with w5
  znorm
  pclear w4
  pinst w5 l with w6
  znorm
  pclear w5
  wfold
  papplym (le_R_of_le_R_pu_nf
    (Term.app2 (Term.dist ())
      (Term.app3 (Term.func ()) x z (.app Term.clamp01 l))
      (Term.app3 (Term.func ()) y w (.app Term.clamp01 l)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
        (Term.app2 (Term.dist ()) x y))
      (Term.app2 Term.mul_R (.app Term.clamp01 l) (Term.app2 (Term.dist ()) z w)))
    (Term.app2 (Term.dist ())
      (Term.app3 (Term.func ()) x.weaken z.weaken (.app Term.clamp01 l.weaken))
      (Term.app3 (Term.func ()) y.weaken w.weaken (.app Term.clamp01 l.weaken)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l.weaken))
        (Term.app2 (Term.dist ()) x.weaken y.weaken))
      (Term.app2 Term.mul_R (.app Term.clamp01 l.weaken)
        (Term.app2 (Term.dist ()) z.weaken w.weaken)))
    (by simp only [Term.app2, Term.app3, weaken_app, dist_weaken, func_weaken, clamp01_weaken])
    (by simp only [Term.app2, weaken_app, dist_weaken, clamp01_weaken,
      sub_R_weaken, one_R_weaken'', add_R_weaken'', mul_R_weaken''])) in w6 with hle
  pexact hle

end AxiomsAt

-- ============================================================================
-- The geodesic estimates
-- ============================================================================

section Geodesic

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **`d(x, W(x,y,λ̃)) ≤ℝ λ̃ ·ℝ d(x,y)`** — half of Kohlenbach's geodesic property.

(W1) at `z := x` gives `d(x,W) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(x,x) +ℝ λ̃ ·ℝ d(x,y)`, and `d(x,x) =ℝ 0ℝ`
(`dist_self`) kills the first summand through `mul_eq_zero_R_core`; `0ℝ +ℝ c ≤ℝ c` finishes.
No estimate is spent — every step is the ℝ order package. -/
def dist_W_left (x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ()) x
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))
        (Term.app2 Term.mul_R (.app Term.clamp01 l)
          (Term.app2 (Term.dist ()) x y))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let mu : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.sub_R Term.one_R cl
  let dxx : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 (Term.dist ()) x x
  let rhs : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.mul_R cl (Term.app2 (Term.dist ()) x y)
  -- `(1ℝ −ℝ λ̃) ·ℝ d(x,x) =ℝ 0ℝ`
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R mu dxx) Term.zero_R) :=
    Derivable.mp (Derivable.dist_self () x) (mul_eq_zero_R_core mu dxx)
  leRt (W1_at x x y l)
    (leRt (leR_mono_r rhs (leR_of_eq hz)) (zero_add_le_R rhs))

/-- **`d(y, W(x,y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)`** — the other half.

(W1) at `z := y`, with `d(y,y) =ℝ 0ℝ` killing the *second* summand. The right-hand side
carries `d(y,x)`, not `d(x,y)`: that is what the axiom gives, and there is no
`=ℝ`-congruence for `·ℝ` to rewrite under (see the file header). -/
def dist_W_right (x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ()) y
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))
        (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
          (Term.app2 (Term.dist ()) y x))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let dyy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 (Term.dist ()) y y
  let lhs : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R cl)
      (Term.app2 (Term.dist ()) y x)
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R cl dyy) Term.zero_R) :=
    Derivable.mp (Derivable.dist_self () y) (mul_eq_zero_R_core cl dyy)
  leRt (W1_at y x y l)
    (leRt (leR_mono_l lhs (leR_of_eq hz)) (add_zero_le_R lhs))

/-- **`d(x,y) −ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x) ≤ℝ d(x, W(x,y,λ̃))`** — Kohlenbach's *reverse*
inequality, which is what forbids `dist_W_left` from being strict.

The triangle inequality `d(x,y) ≤ℝ d(x,W) +ℝ d(W,y)`, then `d(W,y) =ℝ d(y,W)` (`dist_comm`)
and `dist_W_right`, then `le_sub_R_of_le_add_core` to move the second summand across.

With multiplicative monotonicity of `≤ℝ` — the one ℝ fact this file lacks — the left-hand
side is `λ̃ ·ℝ d(x,y)` by `distrib_R_core`, and `le_R_antisymm_core` against `dist_W_left`
would give Kohlenbach's equality `d(x, W(x,y,λ̃)) =ℝ λ̃ ·ℝ d(x,y)`. -/
def dist_W_left_lower (x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 Term.sub_R (Term.app2 (Term.dist ()) x y)
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
            (Term.app2 (Term.dist ()) y x)))
        (Term.app2 (Term.dist ()) x
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let wp : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cl
  let dxy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x y
  let dxw : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x wp
  let dwy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) wp y
  let bnd : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R cl)
      (Term.app2 (Term.dist ()) y x)
  -- `d(x,y) ≤ℝ d(x,W) +ℝ d(W,y)`
  let htri : Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R dxy (Term.app2 Term.add_R dxw dwy)) :=
    Derivable.mp (Derivable.dist_tri () x wp y)
      (le_R_of_le_R_pu dxy (Term.app2 Term.add_R dxw dwy))
  -- `d(W,y) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)`
  let hwy : Derivable WHyperbolic.F a WHyperbolic.Premises (le_R dwy bnd) :=
    leRt (leR_of_eq (Derivable.dist_comm () wp y)) (dist_W_right x y l)
  Derivable.mp
    (leRt htri (leR_mono_l dxw hwy))
    (le_sub_R_of_le_add_core dxy dxw bnd)

end Geodesic

-- ============================================================================
-- The endpoints
-- ============================================================================

section Endpoints

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **`W(x,y,clamp01 0ℝ) =_X x`** — Kohlenbach's `W(x,y,0) = x`.

`dist_W_left` at `λ := 0ℝ` bounds `d(x,W)` by `clamp01 0ℝ ·ℝ d(x,y)`; `clamp01_eq_core` says
`clamp01 0ℝ =ℝ 0ℝ` (the retraction is the identity on `[0,1]`, and `0ℝ` is in it), so that
product is `=ℝ 0ℝ` by `mul_zero_l_R`. A distance bounded above by `0ℝ` and below by `0ℝ`
(`dist_nonneg`) is `0ℝ`, which *is* equality at the base type. -/
def W_zero (x y : Term WHyperbolic.F Γ xTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy
        (Term.app3 (Term.func ()) x y (.app Term.clamp01 Term.zero_R)) x) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 Term.zero_R
  let dxy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x y
  -- `clamp01 0ℝ =ℝ 0ℝ`
  let hcl : Derivable WHyperbolic.F a WHyperbolic.Premises (eq_R cl Term.zero_R) :=
    Derivable.mp zero_le_R_one
      (Derivable.mp (le_R_refl_core Term.zero_R) (clamp01_eq_core Term.zero_R))
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R cl dxy) Term.zero_R) :=
    Derivable.mp hcl (mul_zero_l_R cl dxy)
  Derivable.mp
    (eqX_of_dist_le_zero x (Term.app3 (Term.func ()) x y cl)
      (leRt (dist_W_left x y Term.zero_R) (leR_of_eq hz)))
    (eqAtType_sym_base () x (Term.app3 (Term.func ()) x y cl))

/-- **`W(x,y,clamp01 1ℝ) =_X y`** — Kohlenbach's `W(x,y,1) = y`.

`dist_W_right` at `λ := 1ℝ` bounds `d(y,W)` by `(1ℝ −ℝ clamp01 1ℝ) ·ℝ d(y,x)`, and
`1ℝ −ℝ clamp01 1ℝ =ℝ 0ℝ`: `≤ℝ 0ℝ` from `clamp01_eq_core` (`clamp01 1ℝ =ℝ 1ℝ`) through
`le_sub_R_of_le_add_core`, and `0ℝ ≤ℝ` from `clamp01_le_one_core` through
`sub_R_nonneg_of_le`. Note that this route never needs an `=ℝ`-congruence for `−ℝ`, which
does not exist either. -/
def W_one (x y : Term WHyperbolic.F Γ xTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy
        (Term.app3 (Term.func ()) x y (.app Term.clamp01 Term.one_R)) y) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 Term.one_R
  let mu : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.sub_R Term.one_R cl
  let dyx : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) y x
  -- `clamp01 1ℝ =ℝ 1ℝ`
  let hcl : Derivable WHyperbolic.F a WHyperbolic.Premises (eq_R cl Term.one_R) :=
    Derivable.mp (le_R_refl_core Term.one_R)
      (Derivable.mp zero_le_R_one (clamp01_eq_core Term.one_R))
  -- `1ℝ ≤ℝ 0ℝ +ℝ clamp01 1ℝ`, hence `1ℝ −ℝ clamp01 1ℝ ≤ℝ 0ℝ`
  let hle : Derivable WHyperbolic.F a WHyperbolic.Premises (le_R mu Term.zero_R) :=
    Derivable.mp
      (leRt (leR_of_eq (Derivable.mp hcl (eq_R_sym_core cl Term.one_R)))
        (le_R_zero_add cl))
      (le_sub_R_of_le_add_core Term.one_R Term.zero_R cl)
  -- `0ℝ ≤ℝ 1ℝ −ℝ clamp01 1ℝ`
  let hge : Derivable WHyperbolic.F a WHyperbolic.Premises (le_R Term.zero_R mu) :=
    Derivable.mp (clamp01_le_one_core Term.one_R)
      (sub_R_nonneg_of_le Term.one_R cl)
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R mu dyx) Term.zero_R) :=
    Derivable.mp (eqR_of_le_le hle hge) (mul_zero_l_R mu dyx)
  Derivable.mp
    (eqX_of_dist_le_zero y (Term.app3 (Term.func ()) x y cl)
      (leRt (dist_W_right x y Term.one_R) (leR_of_eq hz)))
    (eqAtType_sym_base () y (Term.app3 (Term.func ()) x y cl))

end Endpoints

-- ============================================================================
-- Nonexpansiveness, from (W4)
-- ============================================================================

section Nonexpansive

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **`d(W(x,y,λ̃), W(x,y',λ̃)) ≤ℝ λ̃ ·ℝ d(y,y')`** — `W(x,·,λ̃)` is `λ̃`-Lipschitz.

(W4) at `(x, x, y, y')` with `d(x,x) =ℝ 0ℝ`; same shape as `dist_W_left`. -/
def dist_W_mono_right (x y y' : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ())
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x y' (.app Term.clamp01 l)))
        (Term.app2 Term.mul_R (.app Term.clamp01 l)
          (Term.app2 (Term.dist ()) y y'))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let mu : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.sub_R Term.one_R cl
  let dxx : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x x
  let rhs : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.mul_R cl (Term.app2 (Term.dist ()) y y')
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R mu dxx) Term.zero_R) :=
    Derivable.mp (Derivable.dist_self () x) (mul_eq_zero_R_core mu dxx)
  leRt (W4_at x x y y' l)
    (leRt (leR_mono_r rhs (leR_of_eq hz)) (zero_add_le_R rhs))

/-- **`d(W(x,y,λ̃), W(x',y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(x,x')`** — `W(·,y,λ̃)` is
`(1−λ̃)`-Lipschitz. (W4) at `(x, x', y, y)` with `d(y,y) =ℝ 0ℝ`. -/
def dist_W_mono_left (x x' y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 (Term.dist ())
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x' y (.app Term.clamp01 l)))
        (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
          (Term.app2 (Term.dist ()) x x'))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let dyy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) y y
  let lhs : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R cl)
      (Term.app2 (Term.dist ()) x x')
  let hz : Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R (Term.app2 Term.mul_R cl dyy) Term.zero_R) :=
    Derivable.mp (Derivable.dist_self () y) (mul_eq_zero_R_core cl dyy)
  leRt (W4_at x x' y y l)
    (leRt (leR_mono_l lhs (leR_of_eq hz)) (add_zero_le_R lhs))

end Nonexpansive

end WHyperbolic

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms mul_zero_l_R
#print axioms eqX_of_dist_le_zero
#print axioms WHyperbolic.W1_at
#print axioms WHyperbolic.W4_at
#print axioms WHyperbolic.dist_W_left
#print axioms WHyperbolic.dist_W_right
#print axioms WHyperbolic.dist_W_left_lower
#print axioms WHyperbolic.W_zero
#print axioms WHyperbolic.W_one
#print axioms WHyperbolic.dist_W_mono_right
#print axioms WHyperbolic.dist_W_mono_left

end Metatheorems
