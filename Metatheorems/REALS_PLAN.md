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

### 3.2 The ℚ order toolkit — strict order DONE, `≤` side still missing

**`RationalNumbers.lean` reached zero sorries on 2026-08-31.** ℚ is an Archimedean ordered
field, provably. What that gives the reals:

- ✅ `lt_Q_trans`, `lt_Q_add`, `lt_Q_mul_pos`, `lt_Q_trichotomy`, `lt_Q_irrefl`
- ✅ `zero_lt_pow2neg_Q`, `pow2neg_Q_halve` — the two `2^{-n}` facts every real axiom needs
- ✅ `add_Q_assoc`, `mul_Q_assoc`, `distrib_Q`, `add_Q_congr`, `mul_Q_congr`, `neg_Q_add_Q`
- ✅ `eq_Q_of_signed_cross` — `eq_Q` from cross-multiplied signed parts with *mismatched*
  denominators. Built for `distrib_Q`; it is the general bridge the reals will want, since
  `add_R`/`mul_R` produce different denominators on the two sides of an equation.
- ✅ `lt_Q_of_eq_Q_diff` / `le_Q_of_eq_Q_diff`, the `lt_Q`/`le_Q` characterisations, `exp2`
  theory, and the ℕ `monus`×`mul` layer of §3.3.

Still missing, verified 2026-08-31, and all four are needed by the reals:

- `|a −_ℚ b|_ℚ =_ℚ |b −_ℚ a|_ℚ` — needed by `eq_R_sym`, so **even Class A is not fully clear**
- `≤_ℚ` transitivity and additive monotonicity (`le_Q` is defined; only `le_Q_refl` exists)
- `abs_Q` triangle inequality `|a +_ℚ b|_ℚ ≤_ℚ |a|_ℚ +_ℚ |b|_ℚ` — needs the two above

These should now be cheap: the `eq_Q` chaining toolkit (`eqQtrans`, `eqQsym`, `addQr`, `addQl`,
`sub_Q_eq_add_neg`), the `posN`/`negN` signed-numerator route, and `eq_Q_of_signed_cross` all
exist. Nothing here needs new ℕ theory.

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

## 5. Recommended order (revised 2026-08-31, after ℚ reached zero sorries)

1. **The `nat →ₜ nat` pattern-type probe for `prw`** (§2 caveat). Small, and *everything*
   downstream assumes it. If it fails, that is a tactic-level fix to make before any real-number
   work, not something to route around.
2. **Four small ℚ lemmas**: `abs_diff_Q_comm`, `le_Q_trans`, `le_Q_add`, then `abs_Q_triangle`.
   All four are listed in §3.2 as missing; none needs new ℕ theory.
3. **Class A + `lt_irrefl_R`** — five axioms. The first end-to-end evidence that the §2b
   technique (pointwise ℚ identity → QF-ER at arrow type → `0 <ℚ 2^{-n}`) actually works.
4. **`cauchyfy` theory** (§3.1) — the real unknown, and the largest remaining gap: the file has
   exactly one `cauchyfy` theorem and it is `closed_subst`. Induction over a `prec` with a
   `pair(value, flag)` state; `ProofMode/Induction.lean`'s `seq_induction` is the tool.
5. **Class B**, then **Class D** (each now unblocked, its ℚ counterpart being proved).
6. **Class C** last — needs the triangle inequality *and* `cauchyfy` theory at once.

Status counts, verified 2026-08-31: `RealNumbers.lean` has **20** sorries (all axioms; the
encoding is complete). `RationalNumbers.lean` has **0**. The only sorry in the build is
`general_metatheorem_classical`, which is out of scope.

`distrib_R` and `mul_assoc_R` are the last two and the hardest; they need both bodies of
theory at once.

## 6. Open question not settled here

`le_R` is `¬(g <_ℝ f)`, which is *not* syntactically purely universal, so `le_R_pu` exists
as a hand-written Π₁⁰ alternative. Nothing yet proves the two are interderivable, and the
metric-space axioms will need whichever one `AdmissibleEqX` can consume. Decide which is
canonical before `MetricSpaces.lean` is started, rather than after.
