# RealNumbers/Mul.lean

## Multiplicative monoid (section comment)

`mul_comm_R` is PROVED, further down the file: it needs `cauchyfy_congr`, which is an
induction on the `cauchyfy` recursion and so sits with the rest of that theory.
`mul_assoc_R` and `distrib_R` are proved at the BOTTOM of the file: they need
`mul_R_check`/`cauchyfy_mul_R` (below) and the `Bounds.lean` assembly layer.

`mul_one_R` is PROVED, at the bottom of the file: it needs `mul_R_apply` (below) and the
symbolic-shift telescope `cauchyfy_shift_le` (`Estimates.lean`).

## `mul_comm_R` (section comment)

Unlike `add_R`, `mul_R` is **not** known to be Cauchy — there is no `mul_R_check`, and
supplying one is the majorization argument of REALS_PLAN §1 — so `cauchyfy` cannot be
evaluated away on either side. This is where `cauchyfy_congr` earns its keep: the two raw
sequences are pointwise `=_ℚ`, and that is enough.

The one wrinkle `add_R` does not have is that `mul_R`'s index depends on its arguments:
`mul_R f g (n) = f̂(n +ℕ b) ·ℚ ĝ(n +ℕ b)` with `b = f(0) +ℕ g(0) +ℕ 2`, so swapping the
arguments swaps the two summands inside `b`. `Arithmetic.add_comm` repairs that at ℕ,
underneath `cauchyfy`, before `mul_Q_comm_inst` is spent.

## `mul_R_check`: the product of two reals is provably Cauchy (section comment)

REALS_PLAN §1's majorization argument, cashed. The raw sequence is
`M(k) = f̂(k+b) ·ℚ ĝ(k+b)` with `b = f(0) + g(0) + 2`, and one step costs

    |M(k) − M(k+1)| ≤ |f̂(k+b) − f̂(k+b+1)|·|ĝ(k+b)| + |ĝ(k+b) − ĝ(k+b+1)|·|f̂(k+b+1)|
                    ≤ (Bg + Bf) · 2^{-(k+b+1)}   with  B· = ⟨·(0)⟩ + 1
                    = ⟨b⟩ · 2^{-(k+b+1)}  <  ⟨2^b⟩ · 2^{-(k+b+1)}  =  2^{-(k+1)}

— the code-dominates magnitude bound (`cauchyfy_mag_le`) making the operand bounds
`⟨f(0)⟩+1`, `⟨g(0)⟩+1`, encode arithmetic collecting them into `⟨b⟩`, and the strict step
`b < 2^b` (`succ_succ_le_exp2_succ`) buying the strictness the check demands. This is why
`b` has the shape it does.

## `mul_one_R` (section comment)

Unlike `mul_comm_R`, this one *can* discharge the outer `cauchyfy`: `mul_R f 1ℝ` is
pointwise `=ℚ` to `f̂(· +ℕ b)`, which is Cauchy, and `lt_Q_dec`'s decision is `=ℚ`-invariant
(that is what `lt_Q_congr` supplies), so `cauchyfy_id` applies.  What is left is

    |f̂(n+1+b) −ℚ f̂(n+1)|  <ℚ  2^{-n},        b = f(0) +ℕ 1ℚ-code +ℕ 2

with `b` **symbolic** — a telescope of symbolically many `cauchyfy` steps, which is exactly
`cauchyfy_shift_le`.  It is not a slack argument: `2^{-(n+1)} <ℚ 2^{-n}` is the only slack
there is, and it is spent on the last step.

`b` is spelled out at every occurrence rather than named: a named wrapper would hide it
from `prw` and from the `=₀` congruences (REALS_PLAN §0.1).

## `mul_assoc_R` (section comment)

With `cauchyfy_mul_R` the outer cauchyfication *evaluates* on both sides, and the two
sides read `f̂, ĝ, ĥ` at different composite indices. The estimate moves each side onto
the common triple product at the index `N = s + b₁ + b₂ + b₃ + b₄` in **four** moves —
two per side, each an instance of `mul_move_le` (one factor takes a `cauchyfy_shift_le`
telescope, the other is bounded by `cauchyfy_mag_le`'s `⟨·(0)⟩+1`) — and there the two
sides agree by `mul_Q_assoc_inst` exactly. Each move costs at most `2^{-(x₀+2)}`
(`mag_dyadic_le`: the index `b` paid for the magnitude, by construction of `mul_R`), the
first strictly (`mag_dyadic_lt`, from `b+1 < 2^b`), so the four together stay strictly
below the budget `2^{-x₀} = 4·2^{-(x₀+2)}`.

## `distrib_R` (section comment)

Same architecture as `mul_assoc_R`, with one asymmetry: the right-hand side is a *sum*
of products, so its two `cauchyfy_shift_le` moves sit inside `add_Q` and cost a bare
`2^{-(x₀+2)}` each (`abs_Q_sub_add_split`) — no magnitude, no dyadic conversion. The
left side pays the two magnitude-weighted moves, the first strictly. The key exact step
is `distrib_Q_inst` at the common index `N`, after `cauchyfy_add_R` has evaluated the
sum both where it is an operand (left) and where it is the outer operation (right).
