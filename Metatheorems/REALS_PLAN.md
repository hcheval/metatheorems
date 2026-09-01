# The real-number layer: what it needs, in dependency order

> **Revision 2026-09-01 — read §0 first. Three of this note's claims are wrong.**

## 0. What the 2026-09-01 session established

`RealNumbers.lean` is now **in the build** (`Metatheorems.lean` imports it), so its `sorry`s
are visible and its breakage is a build failure.

**There are 19 ordered-field axioms, not 20.** Count them: `add_comm_R`, `add_assoc_R`,
`add_zero_R`, `add_neg_R`, `mul_comm_R`, `mul_assoc_R`, `mul_one_R`, `distrib_R`,
`lt_irrefl_R`, `lt_trans_R`, `lt_add_R`, `lt_mul_pos_R`, `zero_lt_one_R`, `archimedean_R`,
`eq_R_refl`, `eq_R_sym`, `eq_R_trans`, `add_eq_zero_R`, `le_zero_eq_zero_R`. The "20" in §5
below was never checked.

**Proved (4/19), `#print axioms` = `[propext, Quot.sound]` in-file:**
`eq_R_refl`, `eq_R_sym`, `lt_irrefl_R`, `zero_lt_one_R`.

### 0.1 The `prw` arrow-type probe passed — with one limit

`Metatheorems/Probes/RwArrow.lean` (in the build) exercises `prw` at pattern type
`nat →ₜ nat`, in both the folded `eqAtType` spelling and the unfolded `∀x. f x =₀ g x` one.
All three cases work unchanged. §2's caveat is discharged.

**But `prwby` at an arrow type is impossible, not merely unimplemented.** `prwby` instantiates
QF-ER's premise `A₀` with the hypothesis's own formula and discharges `A₀.isQF = true` by
`rfl`; at an arrow type that formula is a `Formula.all`, so it is not quantifier-free. Checked:
the error is `(eqAtType EqX (nat →ₜ nat) f g).isQF is not definitionally equal to true`.
Function-typed rewriting is available from **closed** rules only.

There is a second, sharper limit that cost time to find: **`prw` finds its pattern by
descending through `Term.app`/`app2`/`app3` nodes only** (`scanTerm`'s match), so any named
wrapper hides its contents from the rewrite. `Term.cauchy_check_at f n`, or a `def cVal f n :=
.app fst_pair (cauchyState f n)`, are opaque to it. Formula statements that `prw` must see
inside have to be spelled out. This is why `RealNumbers.lean` has no `cVal`/`cFlag`
abbreviations.

### 0.2 §4's "Class A — the two sides are pointwise-identical" is **wrong**

`add_Q_comm` and `mul_Q_comm` are `eq_Q` statements, not `=₀` statements: the ℚ encoding does
not commute on the nose (the sign field of `add_Q x y` is `ite(geq a b, s₁, s₂)` and of
`add_Q y x` is `ite(geq b a, s₂, s₁)`, which differ when `a =₀ b`; they agree only because the
numerator is then `0` and `rat_encode` ignores the sign there). So the two sides of
`add_comm_R` are pointwise **`eq_Q`**, and §2b's technique — pointwise `=₀`, then QF-ER at
`nat →ₜ nat` — does not apply to them.

`add_comm_R` and `mul_comm_R` therefore need **one of**:

- `add_Q_comm_nat : add_Q x y =₀ add_Q y x` at the *code* level (true; needs the `geq`
  trichotomy and a "`rat_encode` ignores the sign when the numerator is 0" lemma — neither
  exists), or
- an `eq_Q`-level congruence for `cauchyfy`: pointwise `f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n`. This is
  *now* within reach (§0.3 supplies the invariant), but is an induction carrying an
  object-level hypothesis, so it needs `seq_induction` and the weakened-hypothesis plumbing.

Only `eq_R_refl` and `eq_R_sym` were genuinely Class A, and both are done.

### 0.3 `cauchyfy` is open — the invariant and the Cauchy property are proved

This was the plan's declared main risk. It is real work but it is **not** an obstruction.
`RealNumbers.lean` now has:

| lemma | statement |
|---|---|
| `Term.cauchyBase/cauchyStep/cauchyState` | the recursion, named, so it can be talked about |
| `cauchyfy_unfold` | `cauchyfy f n =₀ fst_pair (cauchyState f n)` — the one beta step |
| `cauchyState_zero/succ` | `rec_zero`/`rec_succ` at this recursion |
| `cauchyState_succ_unfold` | the step with both state components exposed |
| `cauchyState_frozen` | flag set ⟹ the state does not move |
| `cauchyState_advance` | flag clear ∧ check passes ⟹ next state is `pair(f(n+1), 0)` |
| `cauchyState_trip` | flag clear ∧ check fails ⟹ value freezes, flag sets |
| **`cauchy_inv`** | **the invariant**: at every `n`, either flag `= 0` and value `=₀ f n`, or flag `= 1` |
| **`cauchyState_cauchy`** | **`\|f̂(n) −ℚ f̂(n+1)\|ℚ <ℚ 2^{-(n+1)}` for *any* `f`** |
| `cauchyState_id_of_cauchy`, `cauchyfy_id` | `f̂(n) =₀ f(n)` when the check passes everywhere |
| `cauchyfy_zero` | `f̂(0) =₀ f(0)` |
| `cauchyfy_zero_R`, `cauchyfy_one_R` | the constant sequences are fixed |

The invariant is what makes any of it possible: without it nothing pins the flag to `{0,1}`,
and `ite_nat` on anything else computes garbage. Every step above went through the proof mode
essentially first try; the expensive part was the four `subst0`/`substVar0` normal-form lemmas
(`invF_subst0`, `invF_substVar0`, `idF_subst0`, `idF_substVar0`), which need
`Term.weaken_subst_ext`, `Term.weaken_var` and `subst_subst0_map_weaken` with `Term.weaken`
left **folded** — unfolding `Term.weaken` to `Term.rename` stops `weaken_subst_ext` firing.

### 0.4 §4's Class D — "each lifts fairly directly from its ℚ counterpart" — is **wrong**

`lt_R f g` is `∃n. ĝ(n+1) −ℚ f̂(n+1) ≥ℚ 2^{-n}`. Transitivity has to combine two witnesses at
*different* indices, which needs the Cauchy property of `cauchyfy` to move between them, and
`lt_add_R`/`lt_mul_pos_R` need the same. Only `lt_irrefl_R` was direct (done). Class D belongs
with Class C.

### 0.5 `eq_R_trans` is much harder than "triangle inequality + halving"

The bound in `eq_R` is exactly tight — `2^{-n} = 2·2^{-(n+1)}` — so no route through
"|f̂−ĝ| + |ĝ−ĥ| at a common index" closes: every such estimate overshoots by exactly one
dyadic step, at *every* choice of index. Worked out:

    |f̂(n+1) − ĥ(n+1)| ≤ |f̂(n+1) − f̂(m)| + |f̂(m) − ĝ(m)| + |ĝ(m) − ĥ(m)| + |ĥ(m) − ĥ(n+1)|
                      <  (2^{-(n+1)} − 2^{-m}) + 2^{-(m-1)} + 2^{-(m-1)} + (2^{-(n+1)} − 2^{-m})
                      =  2^{-n} + 2^{-(m-1)}        -- over, for every m

The statement *is* true, and the proof that works keeps the first Cauchy step **strict** and
carries its slack:

    |f̂(n+1) − ĥ(n+1)| ≤ |f̂(n+1)−f̂(n+2)|  +  |f̂(n+2)−f̂(m)|  +  |f̂(m)−ĥ(m)|
                        + |ĥ(m)−ĥ(n+2)|   +  |ĥ(n+2)−ĥ(n+1)|
                      <  2^{-(n+2)} + (2^{-(n+2)} − 2^{-m}) + 2^{-(m-1)}
                        + (2^{-(n+2)} − 2^{-m}) + 2^{-(n+2)}   =  2^{-n}

with the two outer terms strict and the rest `≤`. That needs, none of which exists:

1. `abs_Q_triangle` (`|a +ℚ b| ≤ℚ |a| +ℚ |b|`), `le_Q_trans`, `le_Q_add` — §3.2's three
   remaining items;
2. a **mixed** `<`/`≤` addition lemma (`a <ℚ A`, `b ≤ℚ B` ⟹ `a +ℚ b <ℚ A +ℚ B`);
3. an **unbounded telescoping induction**: `|f̂(p) − f̂(p+k)| ≤ℚ 2^{-p} − 2^{-(p+k)}`, by
   induction on `k`, on top of `cauchyState_cauchy`;
4. the exact dyadic identities `4·2^{-(n+2)} =ℚ 2^{-n}` and `2^{-p} − 2^{-(p+k)}` telescoping.

Item 3 is a second `cauchyfy`-scale induction. Everything in Class C — and `lt_trans_R`,
`lt_add_R`, `add_zero_R`, `mul_one_R` — sits on it, because those all compare two *different*
sequences that merely converge together. **This, not `cauchyfy`, is the real remaining
project.**

### 0.6 One statement-level change was made

The 19 axioms now take `(adm : AdmissibleEqX EqX)`, as every ℚ theorem already does. Nothing
else about any statement changed.

### 0.7 Revised work order

1. `abs_Q_triangle`, `le_Q_trans`, `le_Q_add`, and the mixed `<`/`≤` addition lemma (§3.2 plus
   one). All four are ℚ-level and unblocked.
2. The telescoping induction `|f̂(p) − f̂(p+k)| ≤ℚ 2^{-p} − 2^{-(p+k)}` (§0.5 item 3).
3. `eq_R_trans` — with 1 and 2 it is assembly, and it completes `AdmissibleEqX` for
   `MetricSpaces.lean` (`eq_R_refl`/`eq_R_sym` are done).
4. `cauchyfy_congr_eqQ` (§0.2), then `add_comm_R` and `mul_comm_R`.
5. The rest of Class C and Class D, which all reuse 1–2.
6. `archimedean_R` last; it is the only one that is genuinely self-contained
   (`round_nat` + the §1 majorization argument) and could be done at any time.

---

*Original note, 2026-08-31, follows. §2's caveat is discharged (§0.1); §4's Class A and Class D
classifications are wrong (§0.2, §0.4); §5's count of 20 is wrong (§0).*


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
