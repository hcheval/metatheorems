# The real-number layer: what it needs, in dependency order

Status of `Metatheorems/RealNumbers.lean` as of 2026-08-31. Not in the build.

CLAUDE.md calls this a "skeleton". That undersells it: **every operation is already
defined** — `cauchyfy`, `zero_R`, `one_R`, `embed_nat_R`, `neg_R`, `add_R`, `sub_R`,
`mul_R`, `abs_R`, `eq_R`, `lt_R`, `le_R`, `le_R_pu`, `round_nat` — together with their
closed-substitution lemmas, `eq_R_isPurelyUniversal`, `eq_R_substF`, and the `le_R_pu`
pair. The encoding exists and, as far as this note could check, is correct.

All 20 sorries are the ordered-field/Archimedean package. None of them is blocked on the
encoding. They are blocked on two bodies of missing theory, named in §3.

## 1. The encoding is sound — including the bit that looks wrong

`mul_R` bounds its operands by `b = f(0) +ℕ g(0) +ℕ 2`, i.e. it adds raw *codes*, not
magnitudes. This reads as a type confusion and a future reader will flag it as a bug. It
is not one:

- `pair(a,b) = triag(a+b) +ℕ a`, so `pair(a,b) ≥ a` — a code dominates its own `j₁`.
- `j₁(code) = 2·num`, so `code ≥ 2·num ≥ num ≥ num/den = |value|`.
- `cauchyfy f 0 = f 0` (the recursion's base case is `pair(f 0, 0)`), so `f(0)` is `f̂(0)`.
- `2^b ≥ b+1 ≥ f(0) + g(0) + 2`, which is the bound multiplication actually needs.

So the code majorizes the magnitude for free. **Do not "fix" this.**

## 2. The structural fact that drives everything

`eq_R f g` is *not* an equation. It is

```
∀n. |cauchyfy(f)(n+1) −_ℚ cauchyfy(g)(n+1)|_ℚ  <_ℚ  ⟨2^{-n}⟩_ℚ
```

Two consequences, both load-bearing:

**(a) Every real axiom bottoms out in ℚ *order* reasoning, not ℚ algebra.** Even
`add_comm_R` — an ostensibly algebraic statement — ends at `0_ℚ <_ℚ ⟨2^{-n}⟩_ℚ`. This is
why the ℚ order sorries (`lt_Q_add`, `lt_Q_trans`, `lt_Q_mul_pos`, `lt_Q_trichotomy`)
matter more to the reals than the ℚ algebra ones do.

**(b) `eq_R` re-cauchyfies both sides.** The two sides of a real equation are compared
*after* `cauchyfy`, and `cauchyfy` takes its argument as a **function**. So proving
`f =_ℝ g` from a pointwise ℚ identity requires pushing that identity underneath a
function-typed argument position.

That sounds like it needs extensionality, which WE-HA^ω does not have. It does not.
QF-ER's hole type `ρ` is arbitrary, and `eqAtType EqX (nat →ₜ nat) f g` unfolds to
`∀x. f x =₀ g x` — pointwise equality is exactly the arrow-type instance of QF-ER. So:

```
from   ∀x. (add_R f g) x =₀ (add_R g f) x                    -- pointwise, from add_Q_comm
QF-ER at ρ = nat →ₜ nat, hole r = cauchyfy (·) (n+1)
get    cauchyfy(add_R f g)(n+1) =₀ cauchyfy(add_R g f)(n+1)
```

This is available *because* `prw` was generalised to take the pattern type from the rule
rather than hardcoding `Ty.nat` (the Stage C work; `Probes/RwBase.lean` is its regression
test). That generalisation was done for base types and its value here was not foreseen.

**Caveat, and the first thing to do:** `RwBase.lean` exercises pattern type `Ty.base ()`.
Pattern type `nat →ₜ nat` goes through the same code path but has **never been tested**.
Write that probe before planning around it.

## 3. The two missing bodies of theory

### 3.1 `cauchyfy` has no lemmas at all — zero

This is the larger gap and the one nobody has started. Needed, roughly in order:

| lemma | statement | used by |
|---|---|---|
| `cauchyfy_zero` | `f̂(0) =₀ f(0)` | the `mul_R` bound; everything |
| `cauchyfy_congr` | pointwise `f =₀ g` ⟹ pointwise `f̂ =₀ ĝ` | Class A below (via QF-ER, §2b) |
| `cauchyfy_cauchy` | `f̂` satisfies the Cauchy condition, for any `f` | Class C |
| `cauchyfy_id_on_cauchy` | `f` Cauchy ⟹ `f̂(n) =₀ f(n)` | `add_zero_R`, `mul_one_R` |
| `cauchyfy_const` | the constant sequences `0_ℝ`, `1_ℝ` are fixed by `cauchyfy` | Class B |

`cauchyfy` is defined by `prec` over a `pair(value, violation_flag)` state, so these are
induction proofs. `seq_induction` (`ProofMode/Induction.lean`) is the tool.

### 3.2 The ℚ order toolkit — partly built, and gated on ℕ

Missing entirely, and needed by the reals:

- `abs_Q` triangle inequality `|a +_ℚ b|_ℚ ≤_ℚ |a|_ℚ +_ℚ |b|_ℚ`
- `≤_ℚ` transitivity and additive monotonicity (`le_Q` is defined but has no theory)
- ~~`pow2neg_Q` halving~~ — **done**, `pow2neg_Q_halve` (`2ff23eb`)
- ~~`pow2neg_Q` positivity~~ — **done**, `zero_lt_pow2neg_Q` (`e5a62c1`)
- `|a −_ℚ b|_ℚ =_ℚ |b −_ℚ a|_ℚ` — for `eq_R_sym`

Also landed on the way (2026-08-31): `add_Q` and `eq_Q` component lemmas, `lt_Q`/`le_Q`
characterised in both directions via the difference's sign bit and numerator, `exp2`
theory (it had none), and `lt_Q_of_eq_Q_diff` / `le_Q_of_eq_Q_diff`.

### 3.3 The real blocker is one level lower: ℕ truncated subtraction against `mul`

All four ℚ order sorries reduce, via `lt_Q_of_eq_Q_diff`, to `add_Q` abelian-group
identities — so **`add_Q_right_congr` is the gateway, not `lt_Q_add`**. And that in turn
needs two ℕ facts that exist nowhere in the development:

- `(x ∸ y) · k =₀ x·k ∸ y·k` — for `add_Q`'s opposite-sign numerator branch `|na·dc − nc·da|`
- `geq` invariance under scaling by a positive, `sg_bar((v·k) ∸ (u·k)) =₀ sg_bar(v ∸ u)` —
  because the opposite-sign *sign* branch is `ite(geq(na·dc, nc·da), sa, sc)`, which
  `eq_Q c d` must preserve

`Arithmetic.lean` has `monus_zero/succ/cancel/self/zero_l/succ_l/eq_zero_antisym/disjunct`
and nothing relating `monus` to `mul`; there is no `geq` theory at all. Route:
`monus_monus` (induction on `c`) → `pd_mul` (induction on `m`, via `monus_cancel`) →
`monus_mul_distrib` (induction on `y`), plus `sg_bar_mul_succ` from `mul_eq_zero_iff`.

**The dependency chain is therefore: ℕ `monus`×`mul` → `add_Q_right_congr` → ℚ order →
`RealNumbers.lean`.** Everything in §4 and §5 sits above it.

## 4. The 20 axioms, classified by what they actually need

**Class A — the two sides are pointwise-identical.** Reduce to a ℚ identity, then QF-ER at
`nat →ₜ nat` (§2b), then `0_ℚ <_ℚ 2^{-n}`. Cheapest; do these first.

- `add_comm_R` — from `add_Q_comm` (proved)
- `mul_comm_R` — from `mul_Q_comm` plus `add` commutativity at ℕ to equate the bounds
- `eq_R_refl` — needs only `0_ℚ <_ℚ 2^{-n}`
- `eq_R_sym` — plus `|a−b|_ℚ =_ℚ |b−a|_ℚ`

**Class B — needs `cauchyfy` theory but no approximation.**

- `add_zero_R`, `mul_one_R` — `cauchyfy_const` + `cauchyfy_id_on_cauchy`
- `add_neg_R` — plus `a +_ℚ neg_Q a =_ℚ 0_ℚ`
- `zero_lt_one_R` — arithmetic on constants; probably the single easiest in the file

**Class C — genuine approximation; needs the triangle inequality and `pow2neg` halving.**
The two sides are *different sequences* that merely converge together, because the shift
amounts (`add_R` uses `n+1`) and bounds (`mul_R` uses `n+b`) differ between the groupings.

- `add_assoc_R`, `mul_assoc_R`, `distrib_R`
- `eq_R_trans`, `add_eq_zero_R`, `le_zero_eq_zero_R`

**Class D — order.** Each lifts fairly directly from its ℚ counterpart, so each is gated
on that ℚ sorry.

- `lt_irrefl_R` ← `lt_Q_irrefl` (proved — so this one is available now)
- `lt_trans_R` ← `lt_Q_trans`
- `lt_add_R` ← `lt_Q_add`
- `lt_mul_pos_R` ← `lt_Q_mul_pos`
- `archimedean_R` — the odd one out: needs `round_nat`/`embed_nat_R` and a bound on `f̂(0)`
  from §1's majorization argument. Self-contained, and the only place `round_nat` is used.

## 5. Recommended order

1. The `nat →ₜ nat` pattern-type probe for `prw` (§2 caveat). Small, and everything
   downstream assumes it.
2. `pow2neg_Q` positivity, then Class A. This gets four axioms and proves the §2b
   technique works end to end.
3. `lt_irrefl_R` — already unblocked.
4. `cauchyfy` theory (§3.1), then Class B.
5. The ℚ order sorries (§3.2), then Class D.
6. The triangle inequality, then Class C.

`distrib_R` and `mul_assoc_R` are the last two and the hardest; they need both bodies of
theory at once.

## 6. Open question not settled here

`le_R` is `¬(g <_ℝ f)`, which is *not* syntactically purely universal, so `le_R_pu` exists
as a hand-written Π₁⁰ alternative. Nothing yet proves the two are interderivable, and the
metric-space axioms will need whichever one `AdmissibleEqX` can consume. Decide which is
canonical before `MetricSpaces.lean` is started, rather than after.
