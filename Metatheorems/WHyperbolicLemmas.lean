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
| `W2_at` | `d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ \|λ̃ −ℝ μ̃\|ℝ ·ℝ d(x,y)` | (W2) |
| `W3_at` | `W(x,y,λ̃) =_X W(y,x, 1ℝ −ℝ λ̃)` | (W3) |
| `W4_at` | (W4) at arbitrary terms, as `≤ℝ` | (W4) |
| `dist_W_left` | `d(x, W(x,y,λ̃)) ≤ℝ λ̃ ·ℝ d(x,y)` | half of the geodesic property |
| `dist_W_right` | `d(y, W(x,y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)` | the other half |
| `dist_W_between` | the two added: `d(x,W) +ℝ d(W,y) ≤ℝ …` | geodesic, detour form |
| `dist_W_left_lower` | `d(x,y) −ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x) ≤ℝ d(x, W(x,y,λ̃))` | reverse inequality |
| `W_zero` | `W(x,y,0ℝ~) =_X x` | `W(x,y,0) = x` |
| `W_one` | `W(x,y,1ℝ~) =_X y` | `W(x,y,1) = y` |
| `dist_W_mono_right` | `d(W(x,y,λ̃), W(x,y',λ̃)) ≤ℝ λ̃ ·ℝ d(y,y')` | (W4), nonexpansive in `y` |
| `dist_W_mono_left` | `d(W(x,y,λ̃), W(x',y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃) ·ℝ d(x,x')` | (W4), in `x` |
| `W_ext_left` | `x =_X x' →ᶠ W(x,y,λ̃) =_X W(x',y,λ̃)` | extensionality, 1st argument |
| `W_ext_right` | `y =_X y' →ᶠ W(x,y,λ̃) =_X W(x,y',λ̃)` | extensionality, 2nd argument |
| `W_ext_param` | `λ =ℝ μ →ᶠ W(x,y,λ̃) =_X W(x,y,μ̃)` | extensionality, parameter |
| `W_ext` | all three at once | Kohlenbach §17.2 |

## Extensionality of `W`, and why it has to be *derived*

The ambient system is **weakly** extensional: `WE-HA^{ω,X}` has only quantifier-free
extensionality (`Derivable.qfer`), and full extensionality is deliberately unavailable — it is
what would break the metatheorems. So adding a constant `W` to the signature is only
legitimate if `W`'s extensionality follows from the *space's own axioms*. For W-hyperbolic
spaces it does, and `W_ext` is that derivation: the two carrier arguments come from (W4)
through `dist_W_mono_left`/`_right`, and the parameter from (W2) through `W2_at`. The three
one-argument cases are chained by `eqAtType_trans_base`; nothing outside
`WHyperbolic.W2`/`W4` is consulted.

The mechanism in each case is the same and is worth stating once: `s =_X t` **is**
`d(s,t) =ℝ 0ℝ`, so a nonexpansiveness bound `d(W…, W…) ≤ℝ c ·ℝ d(s,t)` collapses as soon as
the product does, and a product with a **known-zero factor** is `mul_eq_zero_R_core` /
`mul_zero_l_R` — no order-theoretic input about `·ℝ` at all. `dist_nonneg` supplies the other
side and `le_R_antisymm_core` closes.

**This is why the parameter case is *not* blocked by the missing lemma below**, which the
first version of this header predicted it would be. (W2) puts the parameter difference in the
**left** factor, `d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ |λ̃ −ℝ μ̃|ℝ ·ℝ d(x,y)`, and rewriting a factor
*to `0ℝ`* is a special case of the congruence that is already available. What is missing is
rewriting a factor by an **arbitrary** `=ℝ`.

Three generic `=ℝ` facts were needed and are proved here (`abs_eq_zero_R`, `sub_eq_zero_R`,
`clamp01_congr_R`, and the composite `abs_sub_eq_zero_R`). All are slack-free or better:
`cauchyfy` evaluates on `|·|ℝ`, `−ℝ` and `clamp01`, so each goal is a ℚ identity at a single
index. Their proper home is `RealNumbers/`; they are kept here for the reason stated below.

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
`d(W(x,y,λ), W(x,y,μ)) ≤ d(x,y)` need an `=ℝ`-**congruence** for `·ℝ`,

    `mul_congr_r_R :  g =ℝ g' →ᶠ f ·ℝ g =ℝ f ·ℝ g'`,

which the ℝ layer does not have — `RealNumbers/Order.lean` has only the *strict* product fact
`lt_mul_pos_R` (`0 <ℝ f → 0 <ℝ g → 0 <ℝ f ·ℝ g`), and `RealNumbers/Mul.lean` has the ring
identities (`mul_comm_R`, `mul_assoc_R`, `distrib_R`, `mul_one_R`) but nothing that rewrites a
factor. The additive congruence, by contrast, **is** derivable from `le_R_add_mono_*` plus
`le_R_antisymm_core`, which is why nothing additive is blocked.

**Two things about that missing statement are easy to get wrong, so they are spelled out:**

1. **What is missing is the congruence, not multiplicative monotonicity
   (`0ℝ ≤ℝ f → g ≤ℝ g' → f ·ℝ g ≤ℝ f ·ℝ g'`).** Naming monotonicity and then arguing that the
   congruence "is again multiplicative monotonicity" is backwards: the
   congruence is strictly weaker (it is monotonicity's two-sided instance, with no sign
   hypothesis and no sign case split), it is what both stalled statements actually consume,
   and it is what should be attempted first. Monotonicity additionally needs a four-way case
   split on the signs of `f̂(N)` and `ĝ(N) −ℚ ĝ'(N)`; the congruence needs none, because there
   `|ĝ(N) −ℚ ĝ'(N)|` is itself small and `|f̂(N)|` only has to be *bounded*.

2. **It is not "of the shape of `mul_R_check`" and it does not need a new telescope.** The
   accounting, done: with `b₁ = f(0)+g(0)+2`, `cauchyfy_mul_R` reads the goal at index
   `p = x₀+1+b₁`, and relocating both factors to a common far index `N` costs at most
   `(⟨f(0)⟩+⟨g(0)⟩+2) ·ℚ 2^{-p}` per side — the two existing move lemmas `mul_move_le` /
   `mul_move_le_l` with `cauchyfy_shift_le` and `cauchyfy_mag_le`, exactly as in
   `mul_assoc_est`. The residual `|f̂(N)| ·ℚ |ĝ(N) −ℚ ĝ'(N)|` is bounded by
   `(⟨f(0)⟩+1) ·ℚ 2^{-(N-1)}` from the hypothesis, and `N` is **free**, so it can be made
   smaller than any fixed budget.

   Whether that closes depends on one dyadic constant. `mag_dyadic_le` spends `c+1` exponent
   units on a magnitude `⟨c⟩+1` (via `⟨c⟩+1 ≤ ⟨2^{c+1}⟩`), and four independent applications
   of it consume the whole budget `2^{-x₀} = 4 ·ℚ 2^{-(x₀+2)}` with nothing left for the
   residual. Bounding the two moves of one side **together** — `⟨f(0)⟩+⟨g(0)⟩+2 ≤ ⟨2^{f(0)+g(0)+1}⟩`,
   i.e. the sharper `c+1 ≤ 2^c` in place of `c+1 ≤ 2^{c+1}` (true at every `c`, including
   `c = 0`) — gives `2^{-(x₀+2)}` per side instead of `2^{-(x₀+1)}`, hence `2^{-(x₀+1)}` for
   the two sides and `2^{-(x₀+1)}` left over for the residual. So there **is** a factor of 2 of
   slack, and no Archimedean squeeze (`eqR_tail`/`eqR_le`/`eqR_strict`) is needed — unlike
   `eq_R_trans` and `le_R_trans_core`, which are genuinely tight.

   The recipe, for whoever picks it up: one new dyadic lemma (`mag_dyadic_le` with `c` in
   place of `c+1`, resting on `c+1 ≤ 2^c` at the encoded level), one combined two-move bound
   per side, and a five-term `abs_Q_triangle` chain. Everything else is already in
   `RealNumbers/Mul.lean` and `RealNumbers/Bounds.lean`. Estimated at a day, not a night; not
   attempted here.

What that costs, precisely:

* `dist_W_left_lower` is proved and is exactly Kohlenbach's reverse inequality with the
  arithmetic left undone: its left-hand side is `d(x,y) −ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)`, which
  equals `λ̃ ·ℝ d(x,y)` by `distrib_R_core` **and** the missing congruence (to turn `d(y,x)`
  into `d(x,y)` under the product). With the congruence, `le_R_antisymm_core` against
  `dist_W_left` gives the equality with no further work.
* `dist_W_right` is stated with `d(y,x)`, not `d(x,y)`. `dist_comm` gives
  `d(y,x) =ℝ d(x,y)`, but there is no way to rewrite under `·ℝ` — same missing congruence.
  The statement is *not* weakened: it is what (W1) at `z := y` literally gives.
* `Probes/WHyperbolicLemmasDemo.lean` measures the gap exactly:
  `dist_W_left_eq_in_model` derives Kohlenbach's equality `d(x, W(x,y,λ)) = λ·d(x,y)` in an
  arbitrary `WHyperbolicModel` from `dist_W_left` and `dist_W_left_lower` — the whole
  remaining step is one `nlinarith` over `M.d_comm` on Mathlib `ℝ`. So the mathematics of
  the chain is complete; what is missing is one lemma of the ℝ *encoding*.
* Neither is there anything above `W3_at`: transporting `W(x,y,λ̃) =_X W(y,x,1ℝ −ℝ λ̃)`
  into another `d(·,·)` needs `Derivable.qfer` at `σ := realTy`, where `eqAtType` is
  pointwise `=₀` on codes — strictly stronger than `=ℝ`, with no bridge in the ℝ layer.

## Cost

`Metatheorems.WHyperbolicLemmas` elaborates in **13–16 s**, `Probes.WHyperbolicLemmasDemo`
in **14 s**. The four `W*_at` are the only proof-mode scripts in the file (four or five
`pinst`/`znorm` rounds each); everything above them is Lean-level `Derivable.mp` composition
with the ℝ order package, which is what keeps the cost flat as the chain grows.
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

/-- `eqX_of_dist_le_zero` as an **object-level implication**, which is what a derivation built
by `.syllogism` chaining needs. `eqAtType (.base i) s t` *is* `d(s,t) =ℝ 0ℝ`, so the type
ascription below is a definitional unfolding and no cast appears. -/
def eqX_of_dist_le_zero_imp {i : ι} (s t : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (le_R (Term.app2 (Term.dist i) s t) Term.zero_R →ᶠ eqAtType (Ty.base i) s t) :=
  .syllogism (pair_h I_comb (weaken_intro_h (dist_nonneg i s t)))
    (le_R_antisymm_core (Term.app2 (Term.dist i) s t) Term.zero_R)

-- ── Three `=ℝ` facts the extensionality of `W` needs ────────────────────────
--
-- All three are slack-free or better, and none is an estimate in the `leR_strict` sense:
-- every `cauchyfy` involved evaluates (`cauchyfy_abs_R`, `cauchyfy_sub_R`,
-- `cauchyfy_clamp01`), so each goal is a ℚ identity at a single index. Contrast the
-- multiplicative facts of the file header, where `mul_R`'s index shift depends on the
-- arguments and the two sides are read at *different* indices.

/-- **`w =ℝ 0ℝ →ᶠ |w|ℝ =ℝ 0ℝ`.** `cauchyfy` is the identity on `|w|ℝ`, so the goal at index
`n` is `‖|ŵ(n+1)|ℚ −ℚ 0ℚ‖ℚ <ℚ 2^{-n}` and the hypothesis at the *same* index is
`|ŵ(n+1) −ℚ 0ℚ|ℚ <ℚ 2^{-n}`; `abs_Q_abs_Q` and `sub_Q_zero_Q` identify the two left-hand
sides. Nothing moves index, so there is no budget to account for. -/
def abs_eq_zero_R (w : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R w Term.zero_R →ᶠ eq_R (.app Term.abs_R w) Term.zero_R) := by
  pmode
  pintro h
  pforall
  simp only [abs_R_app_weaken, zero_R_weaken]
  pspecialize h with h1
  canorm
  prw (cauchyfy_zero_R (.app .succ (.var .vz)))
  prw (cauchyfy_zero_R (.app .succ (.var .vz))) in h1 with h2
  prw (cauchyfy_abs_R w.weaken (.app .succ (.var .vz)))
  papplym (lt_Q_congr
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))) Term.zero_Q))
    (.app Term.pow2neg_Q (.var .vz))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (.app Term.abs_Q (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz))))
      Term.zero_Q))
    (.app Term.pow2neg_Q (.var .vz))
    (eqQtrans
      (abs_Q_congr (sub_Q_zero_Q
        (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))
      (eqQtrans
        (eqQsym (abs_Q_abs_Q
          (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))
        (eqQsym (abs_Q_congr (sub_Q_zero_Q
          (.app Term.abs_Q
            (Term.app2 Term.cauchyfy w.weaken (.app .succ (.var .vz)))))))))
    (eq_Q_refl_inst (.app Term.pow2neg_Q (.var .vz))))
  pexact h2

/-- The one ℚ identity `sub_eq_zero_R` needs: `|a −ℚ b|ℚ =ℚ |(a +ℚ (−ℚ b)) −ℚ 0ℚ|ℚ`. -/
private def subZeroEq (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q a b))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.add_Q a (.app Term.neg_Q b)) Term.zero_Q))) :=
  abs_Q_congr
    (eqQtrans (sub_Q_eq_add_neg a b)
      (eqQsym (sub_Q_zero_Q (Term.app2 Term.add_Q a (.app Term.neg_Q b)))))

/-- **`f =ℝ g →ᶠ f −ℝ g =ℝ 0ℝ`.** `sub_R` shifts by one (`cauchyfy_sub_R`), so the goal at
index `n` speaks about index `n+2` while the hypothesis read at `n+1` bounds the same
difference by `2^{-(n+1)}` — half the budget. Factor 2 of slack; no telescope. -/
def sub_eq_zero_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f g →ᶠ eq_R (Term.app2 Term.sub_R f g) Term.zero_R) := by
  pmode
  pintro h
  pforall
  simp only [sub_R_app_weaken, zero_R_weaken]
  pinst h (.app .succ (.var .vz)) with h1
  canorm
  prw (cauchyfy_zero_R (.app .succ (.var .vz)))
  prw (cauchyfy_sub_R f.weaken g.weaken (.app .succ (.var .vz)))
  papplym (lt_le_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (.app Term.neg_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
      Term.zero_Q))
    (.app Term.pow2neg_Q (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · papplym (lt_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (.app Term.neg_Q
            (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
        Term.zero_Q))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (subZeroEq
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
      (eq_Q_refl_inst (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
    pexact h1
  · pthm (pow2neg_Q_le_succ (.var .vz))

/-- **`clamp01` respects `=ℝ`**: `f =ℝ g →ᶠ clamp01 f =ℝ clamp01 g`.

`clamp01_Q_lip` — `clamp01_Q` is 1-Lipschitz — transfers the bound verbatim at the same
index, exactly as it transfers the Cauchy rate in `clamp01_check`. No budget is spent. -/
def clamp01_congr_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f g →ᶠ eq_R (.app Term.clamp01 f) (.app Term.clamp01 g)) := by
  pmode
  pintro h
  pforall
  simp only [clamp01_app_weaken]
  pspecialize h with h1
  canorm
  prw (cauchyfy_clamp01 f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_clamp01 g.weaken (.app .succ (.var .vz)))
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (.app Term.clamp01_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz))))
      (.app Term.clamp01_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))))
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pthm (clamp01_Q_lip
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
  · pexact h1

/-- **`f =ℝ g →ᶠ |f −ℝ g|ℝ =ℝ 0ℝ`** — `sub_eq_zero_R` then `abs_eq_zero_R`. This is the
form the `λ` case of `W`'s extensionality consumes: (W2) puts `|λ̃ −ℝ μ̃|ℝ` in the *left*
factor of a product, where `mul_zero_l_R` applies. -/
def abs_sub_eq_zero_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f g →ᶠ eq_R (.app Term.abs_R (Term.app2 Term.sub_R f g)) Term.zero_R) :=
  .syllogism (sub_eq_zero_R f g) (abs_eq_zero_R (Term.app2 Term.sub_R f g))

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

/-- **(W2) at arbitrary terms**:

    `d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ |λ̃ −ℝ μ̃|ℝ ·ℝ d(x,y)`.

This one needs no `le_R_pu` conversion — the axiom is already an `=ℝ` — so after the four
`pinst`/`znorm` rounds the instance and the goal are brought to the *same* weakening normal
form by `wfold` (both are `Formula.all Ty.nat` over a body mentioning `f.weaken`), and
`pexact` closes. That is why `W1_at` needs `le_R_of_le_R_pu_nf` and this does not: there the
goal is the folded `le_R`, here it is the axiom's own shape. -/
def W2_at (x y : Term WHyperbolic.F Γ xTy) (l m : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R
        (Term.app2 (Term.dist ())
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 m)))
        (Term.app2 Term.mul_R
          (.app Term.abs_R
            (Term.app2 Term.sub_R (.app Term.clamp01 l) (.app Term.clamp01 m)))
          (Term.app2 (Term.dist ()) x y))) := by
  pmode
  pfrom w1 := WHyperbolic.W2
  simp only [WHyperbolic.ax_W2, eq_R, Term.app3]
  pinst w1 x with w2
  znorm
  pclear w1
  pinst w2 y with w3
  znorm
  pclear w2
  pinst w3 l with w4
  znorm
  pclear w3
  pinst w4 m with w5
  znorm
  pclear w4
  wfold
  pexact w5

/-- **(W3) at arbitrary terms**: `W(x,y,λ̃) =_X W(y,x, 1ℝ −ℝ λ̃)`.

Base-type equality is `d(·,·) =ℝ 0ℝ`, so this is again the axiom's own shape and `pexact`
closes after `wfold`. The chain has no corollary of (W3) above it: `W(x,y,λ̃) =_X …` cannot
be pushed inside another `d(·,·)` without extensionality of `d` in a base-type argument
w.r.t. `=_X`, and `Derivable.qfer` is stated for `eqAtType` at the *substituted* type — at
`realTy` that is pointwise `=₀`, strictly stronger than `=ℝ`, and no bridge from the one to
the other exists in the ℝ layer. -/
def W3_at (x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy
        (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
        (Term.app3 (Term.func ()) y x
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l)))) := by
  pmode
  pfrom w1 := WHyperbolic.W3
  simp only [WHyperbolic.ax_W3, eqAtType, eq_R, Term.app3]
  pinst w1 x with w2
  znorm
  pclear w1
  pinst w2 y with w3
  znorm
  pclear w2
  pinst w3 l with w4
  znorm
  pclear w3
  wfold
  pexact w4

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

/-- **`d(x, W(x,y,λ̃)) +ℝ d(W(x,y,λ̃), y) ≤ℝ λ̃ ·ℝ d(x,y) +ℝ (1ℝ −ℝ λ̃) ·ℝ d(y,x)`** — the
two geodesic estimates added.

Together with the triangle inequality `d(x,y) ≤ℝ d(x, W) +ℝ d(W, y)` (which is what
`dist_W_left_lower` uses) this is Kohlenbach's observation that the point `W(x,y,λ̃)` sits on
a geodesic: the detour through it costs nothing. The right-hand side is `d(x,y)` once the
missing multiplicative facts are available; as it stands it is the sum of the two bounds,
`le_R_add_mono_core` applied to `dist_W_left` and `dist_W_right` (the latter after
`dist_comm` turns `d(W,y)` into `d(y,W)`). -/
def dist_W_between (x y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R
        (Term.app2 Term.add_R
          (Term.app2 (Term.dist ()) x
            (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)))
          (Term.app2 (Term.dist ())
            (Term.app3 (Term.func ()) x y (.app Term.clamp01 l)) y))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R (.app Term.clamp01 l)
            (Term.app2 (Term.dist ()) x y))
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
            (Term.app2 (Term.dist ()) y x)))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let wp : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cl
  let hwy : Derivable WHyperbolic.F a WHyperbolic.Premises
      (le_R (Term.app2 (Term.dist ()) wp y)
        (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R cl)
          (Term.app2 (Term.dist ()) y x))) :=
    leRt (leR_of_eq (Derivable.dist_comm () wp y)) (dist_W_right x y l)
  Derivable.mp
    (Derivable.mp hwy (Derivable.mp (dist_W_left x y l) and_intro))
    (le_R_add_mono_core _ _ _ _)

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

-- ============================================================================
-- Extensionality of `W`
-- ============================================================================

section Extensionality

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **`x =_X x' →ᶠ W(x,y,λ̃) =_X W(x',y,λ̃)`** — extensionality of `W` in its first argument.

Nonexpansiveness (`dist_W_mono_left`, i.e. (W4)) bounds `d(W(x,y,λ̃), W(x',y,λ̃))` by
`(1ℝ −ℝ λ̃) ·ℝ d(x,x')`, and `d(x,x') =ℝ 0ℝ` — which is exactly what `x =_X x'` *is* —
collapses that product through `mul_eq_zero_R_core`. A distance bounded above by `0ℝ` and
below by `dist_nonneg` is `0ℝ`, i.e. the two points are equal at the base type. -/
def W_ext_left (x x' y : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy x x' →ᶠ
        eqAtType xTy
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x' y (.app Term.clamp01 l))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let mu : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    Term.app2 Term.sub_R Term.one_R cl
  let dxx : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x x'
  let mid : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 Term.mul_R mu dxx
  let wl : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cl
  let wr : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x' y cl
  let dW : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) wl wr
  .syllogism (mul_eq_zero_R_core mu dxx)
    (.syllogism (le_R_of_eq_R_core mid Term.zero_R)
      (.syllogism (pair_h (weaken_intro_h (dist_W_mono_left x x' y l)) I_comb)
        (.syllogism (le_R_trans_core dW mid Term.zero_R)
          (eqX_of_dist_le_zero_imp wl wr))))

/-- **`y =_X y' →ᶠ W(x,y,λ̃) =_X W(x,y',λ̃)`** — the same argument on the other side, through
`dist_W_mono_right`; the surviving factor is `λ̃` instead of `1ℝ −ℝ λ̃`. -/
def W_ext_right (x y y' : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy y y' →ᶠ
        eqAtType xTy
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x y' (.app Term.clamp01 l))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let dyy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) y y'
  let mid : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 Term.mul_R cl dyy
  let wl : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cl
  let wr : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y' cl
  let dW : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) wl wr
  .syllogism (mul_eq_zero_R_core cl dyy)
    (.syllogism (le_R_of_eq_R_core mid Term.zero_R)
      (.syllogism (pair_h (weaken_intro_h (dist_W_mono_right x y y' l)) I_comb)
        (.syllogism (le_R_trans_core dW mid Term.zero_R)
          (eqX_of_dist_le_zero_imp wl wr))))

/-- **`λ =ℝ μ →ᶠ W(x,y,λ̃) =_X W(x,y,μ̃)`** — extensionality of `W` in the **parameter**.

This is the case the file header predicted would need multiplicative monotonicity, and it
does not, for a reason worth stating: (W2) puts the parameter difference in the **left**
factor, `d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ |λ̃ −ℝ μ̃|ℝ ·ℝ d(x,y)`, and killing a product whose *known*
factor is `0ℝ` is `mul_zero_l_R` — a special case of the congruence, not the congruence
itself. What is missing is the ability to rewrite a factor by an arbitrary `=ℝ`; here the
factor is rewritten to `0ℝ`, and `0ℝ ·ℝ c =ℝ 0ℝ` needs no monotonicity at all.

The chain is `clamp01_congr_R` (the retraction respects `=ℝ`), `abs_sub_eq_zero_R`,
`mul_zero_l_R`, and `eq_R_trans_core` against (W2). -/
def W_ext_param (x y : Term WHyperbolic.F Γ xTy) (l m : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eq_R l m →ᶠ
        eqAtType xTy
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 m))) :=
  let cl : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 l
  let cm : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := .app Term.clamp01 m
  let df : Term WHyperbolic.F Γ (realTy MetricSpace.ι) :=
    .app Term.abs_R (Term.app2 Term.sub_R cl cm)
  let dxy : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x y
  let prod : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 Term.mul_R df dxy
  let wl : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cl
  let wr : Term WHyperbolic.F Γ xTy := Term.app3 (Term.func ()) x y cm
  let dW : Term WHyperbolic.F Γ (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) wl wr
  .syllogism (clamp01_congr_R l m)
    (.syllogism (abs_sub_eq_zero_R cl cm)
      (.syllogism (mul_zero_l_R df dxy)
        (.syllogism (pair_h (weaken_intro_h (W2_at x y l m)) I_comb)
          (eq_R_trans_core dW prod Term.zero_R))))

/-- **Full extensionality of `W`**:

    x =_X x' → y =_X y' → λ =ℝ μ → W(x,y,λ̃) =_X W(x',y',μ̃).

The three one-argument cases chained by `eqAtType_trans_base`. Stated as an object-level
implication from the conjunction, so it is a *theorem of the theory*, not a derived rule.

**Why this is worth having.** The ambient system is *weakly* extensional: `WE-HA^{ω,X}` has
only quantifier-free extensionality (`Derivable.qfer`), and full extensionality is
deliberately absent — it is what would break the metatheorems. So a new space constant is
only legitimate if its extensionality follows from the space's own axioms rather than being
assumed. For `W` it does, and this is that derivation: (W4) supplies the two carrier
arguments and (W2) the parameter. Nothing here is a `.premise` beyond `WHyperbolic.W2` and
`WHyperbolic.W4` themselves. -/
def W_ext (x x' y y' : Term WHyperbolic.F Γ xTy) (l m : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy x x' ∧ᶠ eqAtType xTy y y' ∧ᶠ eq_R l m →ᶠ
        eqAtType xTy
          (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
          (Term.app3 (Term.func ()) x' y' (.app Term.clamp01 m))) := by
  pmode
  pintro hyp
  -- `∧ᶠ` is left-associative, so the conjunction is `(x =_X x' ∧ y =_X y') ∧ λ =ℝ μ`
  pdestruct hyp with hxy hl
  pdestruct hxy with hx hy
  papplym (eqAtType_trans_base ()
    (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
    (Term.app3 (Term.func ()) x' y' (.app Term.clamp01 l))
    (Term.app3 (Term.func ()) x' y' (.app Term.clamp01 m)))
  psplit
  · papplym (eqAtType_trans_base ()
      (Term.app3 (Term.func ()) x y (.app Term.clamp01 l))
      (Term.app3 (Term.func ()) x' y (.app Term.clamp01 l))
      (Term.app3 (Term.func ()) x' y' (.app Term.clamp01 l)))
    psplit
    · papplym (W_ext_left x x' y l)
      pexact hx
    · papplym (W_ext_right x' y y' l)
      pexact hy
  · papplym (W_ext_param x' y' l m)
    pexact hl

end Extensionality

end WHyperbolic

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms mul_zero_l_R
#print axioms eqX_of_dist_le_zero
#print axioms WHyperbolic.W1_at
#print axioms WHyperbolic.W2_at
#print axioms WHyperbolic.W3_at
#print axioms WHyperbolic.W4_at
#print axioms WHyperbolic.dist_W_left
#print axioms WHyperbolic.dist_W_between
#print axioms WHyperbolic.dist_W_right
#print axioms WHyperbolic.dist_W_left_lower
#print axioms WHyperbolic.W_zero
#print axioms WHyperbolic.W_one
#print axioms WHyperbolic.dist_W_mono_right
#print axioms WHyperbolic.dist_W_mono_left
#print axioms abs_eq_zero_R
#print axioms sub_eq_zero_R
#print axioms clamp01_congr_R
#print axioms abs_sub_eq_zero_R
#print axioms WHyperbolic.W_ext_left
#print axioms WHyperbolic.W_ext_right
#print axioms WHyperbolic.W_ext_param
#print axioms WHyperbolic.W_ext

end Metatheorems
