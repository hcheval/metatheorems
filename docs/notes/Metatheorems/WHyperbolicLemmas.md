# WHyperbolicLemmas.lean

## module header

### The correspondence to Kohlenbach, *Applied Proof Theory*, §17.2

Kohlenbach (following Kirk, and Kohlenbach–Leuştean) states, for a W-hyperbolic space and
`λ ∈ [0,1]`:

* `d(x, W(x,y,λ)) = λ·d(x,y)` and `d(y, W(x,y,λ)) = (1−λ)·d(x,y)` — the *geodesic* property,
  i.e. `W(x,y,λ)` is the point of the segment `[x,y]` at fraction `λ`. He derives it from
  (W1) plus the triangle inequality: (W1) gives both `≤`, and the triangle inequality
  `d(x,y) ≤ d(x,W) + d(W,y)` forbids either from being strict.
* `W(x,y,0) = x`, `W(x,y,1) = y`, `W(x,x,λ) = x`.
* `d(W(x,y,λ), W(x,y,μ)) = |λ−μ|·d(x,y)` — that is (W2) itself.
* (W4) makes `W(·,·,λ)` nonexpansive in each argument separately.

### Extensionality of `W`, and why it has to be *derived*

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

### The ℝ lemmas this needed, and the one that is missing

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

### Cost

`Metatheorems.WHyperbolicLemmas` elaborates in **13–16 s**, `Probes.WHyperbolicLemmasDemo`
in **14 s**. The four `W*_at` are the only proof-mode scripts in the file (four or five
`pinst`/`znorm` rounds each); everything above them is Lean-level `Derivable.mp` composition
with the ℝ order package, which is what keeps the cost flat as the chain grows.

## `W3_at`

The chain has no corollary of (W3) above it: `W(x,y,λ̃) =_X …` cannot
be pushed inside another `d(·,·)` without extensionality of `d` in a base-type argument
w.r.t. `=_X`, and `Derivable.qfer` is stated for `eqAtType` at the *substituted* type — at
`realTy` that is pointwise `=₀`, strictly stronger than `=ℝ`, and no bridge from the one to
the other exists in the ℝ layer.

## `dist_W_left_lower`

With multiplicative monotonicity of `≤ℝ` — the one ℝ fact this file lacks — the left-hand
side is `λ̃ ·ℝ d(x,y)` by `distrib_R_core`, and `le_R_antisymm_core` against `dist_W_left`
would give Kohlenbach's equality `d(x, W(x,y,λ̃)) =ℝ λ̃ ·ℝ d(x,y)`.

## `dist_W_between`

Together with the triangle inequality `d(x,y) ≤ℝ d(x, W) +ℝ d(W, y)` (which is what
`dist_W_left_lower` uses) this is Kohlenbach's observation that the point `W(x,y,λ̃)` sits on
a geodesic: the detour through it costs nothing. The right-hand side is `d(x,y)` once the
missing multiplicative facts are available; as it stands it is the sum of the two bounds,
`le_R_add_mono_core` applied to `dist_W_left` and `dist_W_right` (the latter after
`dist_comm` turns `d(W,y)` into `d(y,W)`).

## `W_ext_param`

This is the case the file header predicted would need multiplicative monotonicity, and it
does not, for a reason worth stating: (W2) puts the parameter difference in the **left**
factor, `d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ |λ̃ −ℝ μ̃|ℝ ·ℝ d(x,y)`, and killing a product whose *known*
factor is `0ℝ` is `mul_zero_l_R` — a special case of the congruence, not the congruence
itself. What is missing is the ability to rewrite a factor by an arbitrary `=ℝ`; here the
factor is rewritten to `0ℝ`, and `0ℝ ·ℝ c =ℝ 0ℝ` needs no monotonicity at all.

## `W_ext`

**Why this is worth having.** The ambient system is *weakly* extensional: `WE-HA^{ω,X}` has
only quantifier-free extensionality (`Derivable.qfer`), and full extensionality is
deliberately absent — it is what would break the metatheorems. So a new space constant is
only legitimate if its extensionality follows from the space's own axioms rather than being
assumed. For `W` it does, and this is that derivation: (W4) supplies the two carrier
arguments and (W2) the parameter. Nothing here is a `.premise` beyond `WHyperbolic.W2` and
`WHyperbolic.W4` themselves.
