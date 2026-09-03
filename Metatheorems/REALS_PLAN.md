# The real-number layer: what it needs, in dependency order

> **Revision 2026-09-01 — read §0 first. Three of this note's claims are wrong.**
>
> **Revision 2026-09-02 — §0.02 and §0.03 are the newest state (the additive package and the
> `<_ℝ` shift). §0.6 is SUPERSEDED (`AdmissibleEqX` no longer exists) and §0.5 item 3 was
> superseded rather than built; both now say so in place.**
>
> **Revision 2026-09-03 — §0.2 is now the newest state: `add_comm_R` and `mul_comm_R` are
> PROVED, and its own "blocked on `seq_induction`" verdict is retracted there with the reason.
> §0.7's work order items 4 (and its framing of 1–3) are overtaken accordingly.**

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

> **Running total, 2026-09-03 (end of `reals-mul`): 16 proved.** The four above, plus
> `eq_R_trans` and `add_eq_zero_R` (§0.05), `le_zero_eq_zero_R` (§0.05(c), in its *repaired*
> form), `add_zero_R` / `add_assoc_R` / `add_neg_R` (§0.02), **`add_comm_R` / `mul_comm_R`**
> (§0.2), **`mul_one_R`** (§0.22), and — §0.23 — **`abs_R_bound`, `mul_assoc_R`,
> `distrib_R`** (via `mul_R_check`: `mul_R f g` is provably Cauchy). **The ring structure of
> `=_ℝ` is now complete.** Still open: `lt_trans_R`, `lt_add_R`, `lt_mul_pos_R`,
> `archimedean_R`, `approx_R`, `cauchy_complete_R`. The `RealNumbers/` modules carry **6**
> sorried declarations, verified by name after a completed `lake build` (`lt_add_R`,
> `lt_mul_pos_R`, `archimedean_R`, `lt_trans_R_core`, `approx_R`, `cauchy_complete_R`).

### 0.02 The additive package, 2026-09-02 (branch `reals-additive`)

**`add_zero_R`, `add_assoc_R`, `add_neg_R` are proved**, all `[propext, Quot.sound]`.
`RealNumbers.lean` is at **12** sorried declarations. Four findings, in decreasing order of
importance.

**(a) The `eqR_le` engine did NOT generalise, and did not need to.** §0.05's telescoping
machinery is for *tight* statements only. `add_zero_R` and `add_assoc_R` are not tight:
the two sides are the same sum read at indices differing by a fixed number of `cauchyfy`
steps, each costing `2^{-(index+1)}` against a budget of `2^{-n}`, so `cauchyfy_cauchy` alone
closes them with a factor of two (resp. four) to spare. `add_neg_R` has *no* estimate at all —
the sum is `eq_Q`-zero outright. So the engine was neither reused nor re-run; the right
question turned out to be "is this statement tight?", and only `eq_R_trans` in the additive
package is. What *would* be worth packaging, if a tight additive statement ever appears, is
`eqR_strict` plus the two `cauchyfy_unfold` rewrites — i.e. `eqR_hyp f h →ᶠ eq_R f h` — which
is `eq_R_trans_core`'s last four lines.

**(b) `add_neg_R` needed a genuinely new piece: `cauchyfy_neg`.** `neg_R f = λn. neg_Q (f n)`
applies to the **raw** `f`, so nothing related `(neg_R f)^` to `f̂`, and `f` is an arbitrary
`ℕ → ℕ` so `cauchyfy_id` does not apply either. What works is that the two recursions run in
lockstep *on the nose*:

    state(neg_R f, n)  =₀  pair( neg_Q (fst_pair (state(f, n))), snd_pair (state(f, n)) )

— same flag, negated value, at every index (`cauchyState_neg`, by `pinduction`, three cases
mirroring `cauchy_inv`'s). The value half is bookkeeping. The flag half is the content: the
Cauchy check is taken on the *raw* sequences and `|neg_Q a −ℚ neg_Q b|ℚ` is only `eq_Q`-equal
to `|a −ℚ b|ℚ`, so the flags agree only because `lt_Q_dec`'s **decision** is `eq_Q`-invariant.
`sg_bar_congr_iff` (new) is the bridge — it turns the two-way implication `lt_Q_congr` supplies
into the `=₀` equality of `sg_bar` values that `cauchyState_advance`/`_trip` demand.

**This is §0.2's blocker in a special case, and it went through.** §0.2 says `add_comm_R` /
`mul_comm_R` need "an `eq_Q`-level congruence for `cauchyfy`… an induction carrying an
object-level hypothesis, so it needs `seq_induction`". That is right *in general*; but when
the two sequences are related by a **fixed ℚ-operation** rather than by an assumed pointwise
`eq_Q`, the induction hypothesis is a plain `=₀` equation and ordinary `pinduction` suffices.
`cauchyState_neg` is 60 lines. Whether `add_comm_R` can be reached the same way — via a
`cauchyState_congr` for a fixed operation rather than a hypothesis — was not tested, but the
route is no longer obviously closed.

**Tested 2026-09-03: it transfers, and more than that.** `cauchyState_congr` /
`cauchyfy_congr` are proved in full generality — the pointwise `=ℚ` hypothesis is a *Lean-level
schema*, so ordinary `pinduction` suffices even without a fixed operation — and
`cauchyState_neg` is now the special case `v := neg_R u`. `mul_comm_R` is what spends them;
`add_comm_R` turned out not to need them at all. See §0.2.

**(c) `prw` at a goal containing `Term.add_R` bit exactly as predicted**, three times. All
three proofs go through a `_gen` companion taking the composed real as an abstract Lean
parameter, following `add_eq_zero_R_gen`. Two new `=₀` congruences, `addQ_l_nat` and
`addQ_r_nat` (the mirror of `RationalNumbers.lean`'s private `add_Q_congr_r_nat`), assemble
the `cauchyfy_add_R` chains *outside* the proof mode so no `prw` ever sees `add_R`.

**(d) A named `Formula` definition hides itself from `canorm`.** `canorm` normalises
substitutions with `simp only`, which does not unfold a `def`, so an abbreviation like
`negF f : Formula F (Ty.nat :: Γ)` makes `pinduction`'s own bookkeeping fail with
"the pattern does not occur in the goal". The lockstep claim is therefore written out at both
its occurrences. This is the `Formula`-level twin of §0.1's "a named wrapper hides its
contents from `prw`", and `cauchy_inv`'s `invF` avoids it only because it uses raw
`.induction` with hand-written `subst0`/`substVar0` lemmas rather than `pinduction`.

### 0.03 `lt_trans_R`: the estimate is proved, the assembly is blocked on the proof mode

**`lt_shift1`, `lt_shift`, `lt_shift_at` are proved** (`[propext, Quot.sound]`).
**`lt_trans_R` is still `sorryAx`**, through a new `lt_trans_R_core`.

§0.4 is right that `lt_trans_R` must combine two witnesses at different indices, and the
device is that a `<_ℝ` witness at `n` is a witness at every later index *with the bound
shrinking at exactly the dyadic rate*:

    2^{-n} ≤ℚ D(n)  ⟹  2^{-(n+k)} ≤ℚ D(n+k),        D(p) := ĝ(p+1) −ℚ f̂(p+1)

`lt_shift1` is one step: `D(n) −ℚ D(n+1)` is `(ĝ(n+1) −ℚ ĝ(n+2)) +ℚ (f̂(n+2) −ℚ f̂(n+1))`, both
parts below `2^{-(n+2)}` *strictly* by `cauchyfy_cauchy` and `le_Q_self_abs` (which is what
turns a bound on `|·|` into the directed bound actually needed), so the sum is strictly below
`2^{-(n+1)}` and one `lt_Q_add_cancel` finishes. `lt_shift` iterates it by induction on `k`,
the index bookkeeping being `add_succ` against `add_succ_l` exactly as in `eqR_tail`.

**With that, transitivity needs no `max`**: shift the first witness by `n₂` and the second by
`n₁`, both land at `n₁ +ℕ n₂`, and there `(ĥ −ℚ ĝ) +ℚ (ĝ −ℚ f̂) = ĥ −ℚ f̂` by
`sub_Q_trans_split`; only one of the two shifted bounds is spent as a bound, the other through
`0ℚ ≤ℚ 2^{-m} ≤ℚ ĥ −ℚ ĝ`, so the dyadic scale does not double.

**What blocks it is `pobtain`, not arithmetic.** `lt_R f g ∧ᶠ lt_R g h` needs two nested
`pobtain`s, and `pm_exE` maps `Formula.weakenBy ρ` over the whole hypothesis context — so the
witness obtained *first* ends up wrapped in a bare `Formula.weakenBy`. `canorm` does not
normalise that: `q_cons_norm` handles `renameF (Renaming.ext …)`, which is why the
*second*-obtained witness comes out clean, but nothing handles the bare wrapper. And
`ProofMode/Pretty.lean` **hides** it, so the hypothesis and the goal print identically while
being different terms — with `pp.explicit` the tell is that the hypothesis's context prints as
`nat :: Γ` inside a sequent over `nat :: nat :: Γ`. `pexact` / `papplym … in h` on it then run
`isDefEq` on two stuck terms containing `Term.cauchyfy` and exhaust the heartbeat budget.
A display-assisted trap, in the same family as metaprogramming trap 11 in CLAUDE.md.

Note that `ProofMode/MCTLazy.lean` never nests `pobtain`s, and reaches earlier hypotheses only
through `pinst`/`pfrom` — `pinst` whnf's through `weakenBy`, `pexact` does not. Three ways out
are written up at `lt_trans_R_core`, along with the complete script, kept verbatim.

**`lt_add_R` is harder than `lt_trans_R` and was not attempted.** The same shift lands the
hypothesis at index `m+2` (`add_R`'s extra shift), where `D(m+2) > 2^{-(m+1)}` — short of the
required `2^{-m}` by exactly a factor of two, *at every `m`*, and the estimate
`D_p ≥ 2^{-(p-1)}` is the fixed point of the drift recursion so bootstrapping does not improve
it. The witness has to depend on `f` through the Cauchy slack at the hypothesis's own index,
`d := 2^{-(n+2)} −ℚ |ĝ(n+1) −ℚ ĝ(n+2)|`, exactly as in §0.8's analysis of `approx_R`; so
`lt_add_R` and `approx_R` are one job, and `pow2neg_rat_den_le` is the Archimedean step both
need.

### 0.05 Class C, 2026-09-02: `eq_R_trans` and `add_eq_zero_R` are proved

Both `#print axioms`-clean (`[propext, Quot.sound]`). `RealNumbers.lean` is at **16** sorries.
Three corrections to §0.5 and §0.8 below, in decreasing order of importance.

**(a) §0.5's refined five-term split does not close either.** Its display drops one of the two
middle terms: routing `f̂(m) → ĝ(m) → ĥ(m)` costs `2^{-(m-1)} + 2^{-(m-1)} = 2^{-(m-2)}`, not
`2^{-(m-1)}`. Redone honestly the sum is `2^{-n} + 2^{-(m-1)}` — over, for every `m`, exactly
as the crude bound is. **No finite split closes**, because the semantic proof spends
`|f̂(p) − F| < 2^{-p}` *strictly*, and strictness at a limit is not available at any finite
index.

**What works instead** (`RealNumbers.lean`, `cauchy_pair_step` → `eqR_tail` → `eqR_le` →
`eqR_strict`): prove the non-strict `≤` first and spend one extra strict step on top of it.

| step | statement |
|---|---|
| `cauchy_pair_step` | `X_q <ℚ 2^{-q} +ℚ X_{q+1}` — two strict `cauchyfy` steps, `2^{-(q+1)}` each |
| `eqR_tail` | `∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}` — induction on `k`, one round per step |
| `eqR_le` | `∀p. X_{p+1} ≤ℚ 2^{-p}` — Archimedean squeeze over all `k` |
| `eqR_strict` | `∀n. X_{n+1} <ℚ 2^{-n}` — one more strict step on top of the `≤` |

`eqR_le` is the whole trick: `<` for every `k` gives `≤`, and `eqR_strict` buys the `<` back
with a *fresh* strict step that was not spent in the telescope. `pow2neg_rat_den_le` supplies
the index for the squeeze, and needs `pow2neg_Q_le_add_r` (new) to be usable.

The telescoping estimate §0.5 item 3 asks for was **not** built. `eqR_tail` is the same
induction in a form that never mentions `f̂(p) − f̂(p+k)`: it carries the *whole* estimate
`X_{p+1} <ℚ 2^{-p} + 2^{-(p+k)}` through the induction, so no separate sum lemma is needed.

**(b) The reverse triangle inequality was not needed.** HANDOFF and §0.8 item 1 both name
`| |a| −ℚ |b| | ≤ℚ |a −ℚ b|` as the load-bearing missing piece for Class C. It is not: nothing
in `eq_R_trans` or `add_eq_zero_R` uses it. It is still missing, and still needed by
`approx_R` (to license `cauchyfy_id` on `A := |D|`). Do not budget it against Class C.

**(c) `le_zero_eq_zero_R` is FALSE as stated** and is left sorried with a counterexample in
its doc comment. `f ≤_ℝ g ∧ g =_ℝ 0 → f =_ℝ 0` fails at `f := λn.⟨−1⟩_ℚ`, `g := 0_ℝ`: nothing
bounds `f` from *below*. The statement `MetricSpaces.admissibleEqX.eqx_trans` needs carries
`0_ℝ ≤_ℝ f` as a third hypothesis, and that in turn has to be derived from the pseudo-metric
premises (`0 =_ℝ d(x,x) ≤_ℝ d(x,y) +_ℝ d(y,x)`). That is a metric-layer design decision, not
an estimate.

**New in `RationalNumbers.lean`** (all `[propext, Quot.sound]`): `lt_Q_add_inst`,
`lt_Q_add_l`, `le_Q_add_l`, `lt_Q_add_both`, `add_Q_sub_cancel`, **`eq_Q_imp_le_Q`**,
`lt_Q_trichotomy_inst`, **`le_Q_or_lt_Q`**, `pow2neg_Q_lt_succ`, `pow2neg_Q_le_succ`,
`pow2neg_Q_le_add(_all,_r)`, **`abs_Q_sub_triangle`**, `abs_Q_sub_add_split`, and the
`q_ord_norm` / `q_cons_norm` substitution normalisers.

`eq_Q_imp_le_Q` is the one to remember: without it `lt_Q_trichotomy` cannot be used to *prove*
a `≤_ℚ` at all — its middle case hands you an `eq_Q` and there was no way to spend it. It has
to go through the private hypothesis-level `eq_Q` calculus (`eqQhtrans`/`eqQhconst`/
`addQl_imp`), which is why it lives in `RationalNumbers.lean` and not above it.

**One cost note.** `prw` must not be pointed at a goal containing `Term.add_R`: the QF-ER
normal forms it discharges by `rfl` push a substitution through that constant, and it times
out on heartbeats. `add_eq_zero_R_gen` takes the sum as an abstract Lean-level parameter `u`
for exactly this reason. This is the CLAUDE.md build-cost pathology in a new place.

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

### 0.2 §4's "Class A — the two sides are pointwise-identical" is **wrong** — but the
### commutativity axioms are **PROVED** (2026-09-03)

**Verdict, 2026-09-03: `add_comm_R` and `mul_comm_R` are both closed**, `[propext,
Quot.sound]`, along with the general `cauchyfy_congr` this note called out of reach. Two
things this section got right and one it got wrong; the wrong one was the blocker.

**Right, and still true.** `add_Q_comm` and `mul_Q_comm` are `eq_Q` statements, not `=₀`
statements: the ℚ encoding does not commute on the nose (the sign field of `add_Q x y` is
`ite(geq a b, s₁, s₂)` and of `add_Q y x` is `ite(geq b a, s₂, s₁)`, which differ when
`a =₀ b`; they agree only because the numerator is then `0` and `rat_encode` ignores the sign
there). So the two sides are pointwise `eq_Q`, and §2b's technique — pointwise `=₀`, then
QF-ER at `nat →ₜ nat` — does not apply.

**Right.** `add_Q_comm_nat` at the code level was never built and is not needed.

**Wrong, twice over.**

**(a) `add_comm_R` needs no `cauchyfy` congruence at all.** The section assumes the two
sequences must be pushed through the outer `cauchyfy` that `eq_R` applies. They need not be:
`add_R f g` is *provably Cauchy* (`add_R_check`, proved for `add_zero_R`), so `cauchyfy_add_R`
**evaluates** that cauchyfication on both sides before they are ever compared. What is left is
`|(A +ℚ B) −ℚ (B +ℚ A)| <ℚ 2^{-n}` at fixed rationals, which `add_Q_comm_inst` makes
`eq_Q`-zero. `add_comm_R_gen` is fifteen lines and contains no estimate and no induction. The
whole difficulty was located in the wrong place: it is not that ℚ fails to commute on the
nose, it is whether the outer `cauchyfy` can be discharged, and for `+ℝ` it can.

**(b) The general congruence does not need `seq_induction` either.** `cauchyfy_congr`
(pointwise `f k =ℚ g k` ⟹ `f̂ n =ℚ ĝ n`) is proved by **plain `pinduction`**. The pointwise
hypothesis is taken as a **Lean-level schema** — `∀ x : Term F (nat :: Γ) nat, Derivable …
(eq_Q (u.weaken x) (v.weaken x))` — not as an object-level `∀`, so it is available at whatever
index each case of the induction asks for and nothing is carried through the induction but the
invariant. That is exactly what `cauchyfy_neg` did (§0.02(b)) and the route transfers verbatim;
`cauchyState_neg` is now visibly the special case `v := neg_R u` in which the value halves
agree on the nose.

The invariant is a **conjunction**, and that is the one genuine generalisation over
`cauchyfy_neg`:

    eq_Q (fst (cauchyState u n)) (fst (cauchyState v n))
      ∧ᶠ  snd (cauchyState u n) =₀ snd (cauchyState v n)

— values up to `=ℚ`, **flags on the nose**, because `cauchyState_advance`/`_trip` branch on
the flags. `check_sg_congr` (the generic `neg_check_sg`) keeps the flags in step and is the
only step that is not bookkeeping; it is still `sg_bar_congr_iff` that does the work.

**`mul_comm_R` is where the congruence is actually spent**, because there was then no
`mul_R_check` — supplying one is §1's majorization argument (since done: §0.23) — so
`cauchyfy` could not be evaluated away on either side. The extra wrinkle over `+ℝ` is that `mul_R`'s index depends on
its arguments (`b = f(0) +ℕ g(0) +ℕ 2`), so the swap permutes the summands inside `b`;
`Arithmetic.add_comm` repairs that at ℕ, underneath `cauchyfy`, before `mul_Q_comm_inst` is
spent (`mul_R_pointwise_comm`).

**New and reusable**: `check_sg_congr`, `cauchyState_congr`, `cauchyfy_congr`,
`eq_R_of_cauchyfy_eqQ` (pointwise `=ℚ` at every cauchyfied index ⟹ `=ℝ`, on abstract reals so
no `prw` sees a composed real), `mul_R_apply`, `mul_R_weaken` / `mul_R_app_weaken`,
`cauchyfy_idx_nat`, `mulQ_l_nat` / `mulQ_r_nat`, `eqQ_of_nat_eq`, `mul_R_pointwise_comm`.

One mechanical note, paid for once: **`prwby` needs an equation**, so a conjunction goal must
be `psplit` *before* the state equations are rewritten in, not after — the opposite order to
`cauchyState_neg`, whose goal is a single equation.

Only `eq_R_refl` and `eq_R_sym` were genuinely Class A; Class A as a class does not exist.

### 0.21 Triage of `mul_one_R`, 2026-09-03 — **not** slack-only; do not budget it as small

> **Superseded by §0.22 the same day: `mul_one_R` is PROVED, and this triage was correct in
> every particular. Kept because it is the worked example of "not tight ⇏ no new induction".**

Worked out but **not attempted**, and the reason is worth recording because it contradicts the
natural guess that `mul_one_R` is the `add_zero_R` of the multiplicative side.

With `1̂ℝ = 1ℚ` (`cauchyfy_one_R`) and a `mul_Q q 1ℚ =ℚ q`, the raw sequence is pointwise
`(f ·ℝ 1ℝ)(x) =ℚ f̂(x +ℕ b)` with `b = f(0) +ℕ 1ℚ-code +ℕ 2`. That sequence *is* Cauchy —
`|f̂(x+b) − f̂(x+1+b)| <ℚ 2^{-(x+b+1)} ≤ℚ 2^{-(x+1)}` by `cauchyState_cauchy` plus
`pow2neg_Q_le_add` — and `lt_Q_congr` carries the check across the `=ℚ`, so `cauchyfy_id`
applies and the outer cauchyfication *can* be evaluated, as for `+ℝ`. So far, easy.

What is left is **not** a fixed-shift comparison:

    |f̂(n+1+b) −ℚ f̂(n+1)|  <ℚ  2^{-n},        b symbolic

`b` depends on `f`, so this is a telescope of *symbolically many* steps, not the one or two
that `add_zero_R` / `add_assoc_R` spend. It needs the unbounded induction

    ∀k ∀p.  |f̂(p) −ℚ f̂(p+k)|  +ℚ  2^{-(p+k)}  ≤ℚ  2^{-p}

(the remaining slack has to be carried, or the step has none: base `k = 0` is `0 +ℚ 2^{-p} ≤ 2^{-p}`; the step
splits off `|f̂(p+k) − f̂(p+k+1)| <ℚ 2^{-(p+k+1)}` and uses `2^{-(p+k)} = 2·2^{-(p+k+1)}`).
This is §0.5 item 3 in the form that really is needed — and it is *not* what `eqR_tail`
proves: `eqR_tail` carries its estimate inside the `eqR_hyp f h` two-sequence setting and
never mentions `f̂(p) − f̂(p+k)`.

So the honest classification is: `mul_one_R` has a factor of two of slack, but is gated on a
new `cauchyfy`-scale induction. `distrib_R` and `mul_assoc_R` are gated on the same one, plus
`mul_R_check`. The tightness question (§0.02(a)) is the right one, but "not tight" does not
imply "no new induction".

### 0.22 The symbolic-shift telescope, and `mul_one_R` — DONE 2026-09-03 (`reals-telescope`)

§0.21's triage was right in every detail, including the shape of the induction it asked for.
Both landed, `[propext, Quot.sound]`, and `mul_one_R` fell out of the telescope with no
surprises.

**The form that worked is the `+ℚ` one**, exactly as §0.21 wrote it (`Estimates.lean`,
`cauchyfy_tele`):

    ∀k ∀p.  |f̂(p) −ℚ f̂(p+k)|  +ℚ  2^{-(p+k)}  ≤ℚ  2^{-p}

The `−ℚ` form §0.5 item 3 asked for (`|f̂(p) − f̂(p+k)| ≤ℚ 2^{-p} −ℚ 2^{-(p+k)}`) was **not
attempted**, and should not be: the two are equivalent, but the difference form needs a
`sub_Q` cancellation at every step of the induction, while the `+ℚ` form is `le_Q_add_both`
and `add_Q_assoc_inst` bookkeeping and nothing else. The whole induction is 130 lines and
went through on the second try; the first failure was a *typing* slip (`f.weaken.weaken` in
the base case, where after `pinduction`'s `k := 0` substitution the context is `nat :: Γ` and
only one `weaken` typechecks), not a mathematical one.

Note that carrying the slack is what makes the step free rather than merely cheap:
`2^{-(p+k)} = 2^{-(p+k+1)} +ℚ 2^{-(p+k+1)}` (`pow2neg_Q_halve`), one half funds the new
`cauchyfy_cauchy` step and the other becomes the next round's slack. **Nothing is spent**, so
the conclusion stays `≤ℚ 2^{-p}` for every `k` — unlike `eqR_tail`, which spends a step per
round and therefore needs the Archimedean squeeze of `eqR_le` afterwards. That is the
structural difference between the two inductions, and it is why this one needs no squeeze.

Three lemmas, all in `Estimates.lean`:

| lemma | statement |
|---|---|
| `cauchyfy_tele` | `∀k ∀p. \|f̂(p) −ℚ f̂(p+k)\| +ℚ 2^{-(p+k)} ≤ℚ 2^{-p}` |
| `cauchyfy_tele_at f p k` | the same at explicit `p`, `k` |
| `cauchyfy_shift_le f p k` | `\|f̂(p) −ℚ f̂(p +ℕ k)\| ≤ℚ 2^{-p}` — the slack dropped, which is all the callers want |

plus two private ℚ steps, `tele_base_eq` (`e =ℚ \|a −ℚ a\| +ℚ e`) and `tele_carry_eq`
(`(D +ℚ 2^{-(m+1)}) +ℚ 2^{-(m+1)} =ℚ D +ℚ 2^{-m}`). Factoring those out was not cosmetic: as
inline arguments to `papplym` they made the failure mode unreadable — a `papplym` whose term
fails to elaborate reports `_inhabitedExprDummy` and then **panics inside the pretty-printer**
(`index out of bounds`, with a C stack trace), so the actual type error is never shown. Keep
`papplym` arguments small enough that a type error surfaces at the argument.

**`mul_one_R` then fell out**, in `Mul.lean`, with one new mechanical piece and nothing else:

- `mul_one_R_apply f x` — `(f ·ℝ 1ℝ)(x) =ℚ f̂(x +ℕ b)`, `b = f(0) +ℕ 1ℝ(0) +ℕ 2`. Only `=ℚ`:
  `mul_Q q 1ℚ` is not `q` on the nose. Needs a new `mul_Q_one_inst` (the `∀`-version existed).
- `mul_one_R_check f` — the Cauchy check, which is where §0.21's claim that the outer
  `cauchyfy` *can* be discharged is cashed. The check goal **is** a `lt_Q`, so `lt_Q_congr`
  carries the pointwise `=ℚ` across it directly; no `sg_bar_congr_iff` detour is needed (that
  is only for `=₀` goals about the state, as in `cauchyState_neg`).
- `cauchyfy_mul_one_R` — `cauchyfy_id` applied to the above.
- `mul_one_R_gen f u bw hu` — `u =ℝ f` whenever `û(n+1) =ℚ f̂((n+1) +ℕ bw)`. The composed real
  is a Lean parameter for the usual reason (`prw` must not see `Term.mul_R`), and **the shift
  is taken directly in context `nat :: Γ`** rather than as `b.weaken`, which avoids needing a
  weakening lemma for `b` at all.

The estimate itself is two lines: `cauchyfy_shift_le f (n+1) b` gives `≤ℚ 2^{-(n+1)}` and
`pow2neg_Q_lt_succ n` buys the strict `<ℚ 2^{-n}`. Index arithmetic never needed `prw` — every
`add (succ k) b` ↔ `succ (add k b)` move went through `le_Q_congr`/`lt_Q_congr` with
`add_succ_l` lifted by `cauchyfy_idx_nat` and a new `pow2neg_idx_nat`.

**Not attempted, deliberately:** `distrib_R` and `mul_assoc_R`. They are gated on the same
telescope, which now exists, *plus* `mul_R_check` — §1's majorization argument — and that is a
separate job. `lt_trans_R`, `lt_add_R`, `approx_R` were out of scope per §0.03 / §0.4.
**Done the next session — see §0.23.**

### 0.23 The multiplicative package — DONE 2026-09-03 (`reals-mul`)

**`abs_R_bound`, `mul_R_check`, `mul_assoc_R`, `distrib_R` all closed**, `[propext,
Quot.sound]`, in that order — and the prescribed chain `abs_R_bound → mul_R_check →
{mul_assoc_R, distrib_R}` was exactly the right decomposition, with one refinement: the
shared nugget is one level below `abs_R_bound`, at the single-code fact
**`abs_le_encode : |c|_ℚ ≤_ℚ ⟨c⟩_ℚ`** (a ℚ-code dominates the magnitude it encodes), which
both `abs_R_bound` and the magnitude bound `cauchyfy_mag_le` (`|ŵ(y)| ≤ ⟨w 0⟩+1`, any `w`)
consume. Two new modules: `RealNumbers/QBounds.lean` (pure ℚ/ℕ, beside `Defs`) and
`RealNumbers/Bounds.lean` (the cauchyfy-level magnitude layer, beside `Estimates`).

**The code-dominates chain** (`QBounds.lean`): `rat_num z = div2(j₁ z + isOdd (j₁ z)) ≤ j₁ z
≤ z ≤ z · rat_den z`, then the `le_Q_of_cross` criterion. Two findings worth keeping:

- **`div2_double` did not need re-deriving from the state machine** (it is `private` in
  `RationalNumbers.lean`): the public roundtrip `rat_num_rat_encode` already contains the
  analysis, and `rat_num (pair (2m) 0) = div2 (2m + isOdd 2m)` unfolds to it. The same trick
  killed every other private dependence except tiny `isEven` computations, re-derived in ~40
  lines with `pinduction` (`isEven_add_self` etc.).
- The exact bound `div2 (j + isOdd j) ≤ j` needs the **existential** parity split
  `∀j ∃m. j = m+m ∨ j = S(m+m)` (`double_or_succ`, a `pinduction` with `pexists`/`pcases`) —
  `isEven_cases`' Boolean disjunction cannot supply the witness.

**`mul_R_check`** is the paper estimate with the strictness moved: the two factor moves are
spent as `≤` (not the strict `cauchyfy_cauchy`), and strictness is bought at the *encode*
step `⟨b⟩ <_ℚ ⟨2^b⟩` from `b+1 ≤ 2^b` (`succ_succ_le_exp2_succ`, a 3-line `pinduction`).
The collection `(⟨f0⟩+1)+(⟨g0⟩+1) =_ℚ ⟨b⟩` needs `encode_succ`/`encode_add` — same-sign
`add_Q` is *not* relational, `addQ_num_same` computes it — and the dyadic cancellation
`⟨2^e⟩·2^{-(e+m)} =_ℚ 2^{-m}` (`encode_pow2_mul`, on `exp2_add`).

**`mul_assoc_R`/`distrib_R`: four moves onto a common index, then exact.** With
`cauchyfy_mul_R` (= `cauchyfy_id` on `mul_R_check`) the outer cauchyfication evaluates on
both sides; each side then travels to the triple product at the one index
`N = s + b₁ + b₂ + b₃ + b₄` in two moves of the form `|a·r − a'·r| ≤ B·P`
(`mul_move_le`: the moving factor takes a `cauchyfy_shift_le` telescope from its own base,
the resident factor is bounded by `cauchyfy_mag_le`), and at `N` the two sides agree by
`mul_Q_assoc_inst` / `distrib_Q_inst` **exactly** — no fifth comparison. Each move costs
`≤ 2^{-(x₀+2)}` (`mag_dyadic_le`: `mul_R`'s own `b` pays for the resident magnitude — that
is what the `b` in the index is *for*), one move strictly (`mag_dyadic_lt`), and
`4·2^{-(x₀+2)} = 2^{-x₀}` is the budget with nothing to spare: the estimate is **exactly
tight up to the single encode-strictness**, sharper than §0.21 anticipated. `distrib_R`'s
one asymmetry: its right side is a *sum* of products, so its two moves sit inside `add_Q`
(`abs_Q_sub_add_split`) and cost a bare `2^{-(x₀+2)}` each with no magnitude at all — but
mind `add_R`'s `+1` shift, which puts the right side's summand indices at `s+1`, not `s`
(forgetting it was the one build error of the session).

**Method note.** Unlike every earlier `_gen`-style proof, *no proof-mode `prw` appears
anywhere* in these four: everything is Lean-level `qtrans`/`eqQtrans`/`Derivable.mp` chains
over congruence lemmas, so composed reals (`mul_R`, `add_R`) sit in the statements freely —
the delta-expansion trap is a `prw`/subst phenomenon, not a term-size one. The two entry
points `le_R_of_bound` and the new `eq_R_of_lt_bound` (`Bounds.lean`) fold a pointwise
`lt_Q` bound at context `nat :: Γ` into `≤_ℝ` / `=_ℝ`, with `simp only [mul_R_app_weaken]`
as the only tactic step.

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
3. ~~an **unbounded telescoping induction**: `|f̂(p) − f̂(p+k)| ≤ℚ 2^{-p} − 2^{-(p+k)}`, by
   induction on `k`, on top of `cauchyState_cauchy`~~ — **SUPERSEDED, and never built. Do not
   build it.** `eqR_tail` (§0.05) is the same induction in a form that never mentions the
   difference `f̂(p) − f̂(p+k)`: it carries the *whole* estimate `X_{p+1} <ℚ 2^{-p} + 2^{-(p+k)}`
   through, so no separate sum lemma is needed and `eq_R_trans` is closed without this. The
   refined form that keeps one step's slack out of the sum is still open and is what
   `approx_R` and `lt_add_R` need (§0.03, §0.8 item 2) — but that is a *different* statement
   from the one written here;
4. the exact dyadic identities `4·2^{-(n+2)} =ℚ 2^{-n}` and `2^{-p} − 2^{-(p+k)}` telescoping.

Item 3 is a second `cauchyfy`-scale induction. Everything in Class C — and `lt_trans_R`,
`lt_add_R`, `add_zero_R`, `mul_one_R` — sits on it, because those all compare two *different*
sequences that merely converge together. **This, not `cauchyfy`, is the real remaining
project.**

### 0.6 One statement-level change was made — ⚠ SUPERSEDED, do not act on this

This section used to read: *"The 19 axioms now take `(adm : AdmissibleEqX EqX)`, as every ℚ
theorem already does."*

**`AdmissibleEqX` was DELETED on 2026-09-02**, later the same day, along with `Derivable`'s
`EqX` index. Base-type equality is now *defined* — `eqAtType (.base i) s t ≡ eq_R (dist i s t)
0ℝ` — the pseudometric axioms are Π⁰₁ constructors `Derivable.dist_self` / `dist_comm` /
`dist_tri`, and refl/sym/trans at base types are theorems in `BaseEquality.lean`. **No axiom in
`RealNumbers.lean` takes an `adm` parameter.** Check the signatures in the file, not this note.
See CLAUDE.md's design table ("Base-type equality") and ARCHITECTURE.md §1, §8.

### 0.65 The ℚ layer as of 2026-09-01 (end of the `approx-r` session)

The four items §0.7 lists as step 1 are **done**, plus three that were not on the list:

| lemma | statement |
|---|---|
| `le_Q_zero_parts` / `le_Q_zero_of_parts` | `0 ≤_ℚ p` ⟺ `negN p =₀ 0` |
| `addQ_negN_zero` | the negative part of a sum of non-negatives vanishes |
| `le_Q_zero_add`, `lt_Q_zero_add_le` | `≤`+`≤` and `<`+`≤` at `0_ℚ` |
| `le_Q_to_zero_sub`, `le_Q_of_zero_sub`, `le_Q_zero_congr` | `≤_ℚ` in difference form |
| `le_Q_add`, `sub_Q_add_split`, `le_Q_add_both` | additive monotonicity, one- and two-sided |
| **`lt_le_Q_add`** | **the mixed `<`/`≤` addition lemma** |
| `le_Q_trans`, `lt_le_Q_trans`, `le_lt_Q_trans` | the three transitivity combinations |
| `monus_add_self`, `monus_le_of_eq_add`, `monus_le_trans`, `add_le_mono` | ℕ order in `monus` form |
| `one_le_exp2`, **`exp2_ge_self`** | `1 ≤ 2^n`, `n ≤ 2^n` |
| **`le_Q_of_cross`** | `≤_ℚ` from an ℕ inequality between signed cross products |
| **`pow2neg_rat_den_le`** | `0 <_ℚ q →ᶠ ⟨2^{-rat_den q}⟩_ℚ ≤_ℚ q` — the Archimedean index |
| `rat_num_add_Q_le`, **`abs_Q_triangle`** | `\|a +_ℚ b\|_ℚ ≤_ℚ \|a\|_ℚ +_ℚ \|b\|_ℚ` |

`le_Q_of_cross` is the one to remember: it is the `≤_ℚ` counterpart of `eq_Q_of_signed_cross`,
and it turns a ℚ order goal into ordinary ℕ arithmetic with no `sub_Q` in it. `abs_Q_triangle`
and `pow2neg_rat_den_le` are both two-thirds bookkeeping on top of it.

The ℕ order lemmas sit in `RationalNumbers.lean` rather than `Arithmetic.lean`, where they
belong by subject: `Arithmetic.lean` is below `ProofMode` in the import graph, and in Hilbert
style they are a page each.

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

### 0.8 `approx_R` (Kohlenbach Lemma 4.2) — worked out, 2026-09-01

Not proved. But the arithmetic is settled and one missing ingredient that §0.7 does not list
has been built. The finding that matters: **`approx_R` as stated needs an Archimedean modulus,
because it is stated with `<_ℝ` rather than `≤_ℝ`.**

**What the goal reduces to.** With `c := λn. f̂(k)` and `D := f −_ℝ c`, `A := |D|_ℝ`, and
`B := ⟨2^{-k}⟩_ℝ`:

| step | value |
|---|---|
| `D(n)` | `f̂(n+1) −_ℚ f̂(k)` (`add_R` shifts by 1; `ĉ` is the constant) |
| `D` is Cauchy | `\|D(n) − D(n+1)\| = \|f̂(n+1) − f̂(n+2)\| < 2^{-(n+2)} < 2^{-(n+1)}`, so `D̂ = D` |
| `A(n)` | `\|D(n)\|_ℚ`, and `A` is Cauchy too, so `Â = A` |
| `B̂(n+1)` | `2^{-k}` |

`lt_R A B` is `∃n. B̂(n+1) −_ℚ Â(n+1) ≥_ℚ 2^{-n}`, so the goal is

    ∃n.  2^{-k} −_ℚ |f̂(n+2) −_ℚ f̂(k)|  ≥_ℚ  2^{-n}.

**The crude telescoping bound is short by a factor of 4, at every `n`.** Summing
`cauchyState_cauchy` from `k` to `n+1` gives `|f̂(n+2) − f̂(k)| < 2^{-k} − 2^{-(n+2)}`, i.e. a
margin of `2^{-(n+2)}` where `2^{-n}` is wanted. Enlarging `n` does not help: both sides shrink
together. This is the same tightness as §0.5, and no rearrangement of the telescope fixes it.

**The witness must therefore depend on `f`, and it does — through the slack at index `k`.**
Let `d := 2^{-(k+1)} −_ℚ |f̂(k) −_ℚ f̂(k+1)|`, which is positive *for every `f`* by
`cauchyState_cauchy` (the Cauchy check is strict). Keeping that one step's slack out of the
telescope,

    |f̂(n+2) − f̂(k)|  <  2^{-k} − d − 2^{-(n+2)},

so any `n` with `2^{-n} ≤_ℚ d` (and `n ≥ k`) works. Hence

    **witness  n := max(k, rat_den d)**,

a closed term of the object language — `Derivable`'s `∃`-introduction takes an arbitrary
witness term, so this is expressible.

**Proved on 2026-09-01, and it is the piece §0.7 omits:**
`pow2neg_rat_den_le : 0 <_ℚ q →ᶠ ⟨2^{-rat_den q}⟩_ℚ ≤_ℚ q`. A positive rational's own
denominator field is an index at which the dyadic scale has already fallen below it
(`q = p/D` with `p ≥ 1`, and `D ≤ 2^D ≤ p·2^D`). With it, `le_Q_of_cross`, the ℕ order lemmas,
and the `≤_ℚ` toolkit, everything in the *witness* half of the lemma is available.

**Still missing, all of it estimate work:**

1. ~~`abs_Q_triangle`~~ — **proved 2026-09-01**, via `le_Q_of_cross` + `rat_num_add_Q_le`
   (`num(a+b) ≤ num a·den b + num b·den a`, the only place the sign cases are taken). What
   remains here is the **reverse** triangle inequality `| |a| − |b| | ≤_ℚ |a − b|`, which is
   what makes `A = |D|` Cauchy, i.e. what licenses `cauchyfy_id` on `A`; §0.7 did not list it.
   The usual route needs `z ≤_ℚ |z|`, `−|z| ≤_ℚ z` and `(−c ≤ z ∧ z ≤ c) → |z| ≤ c`, none of
   which exists.
2. The telescoping induction of §0.5 item 3, in the refined form that keeps the `k`-th step's
   slack out of the sum.
3. `cauchyfy_const` for an *arbitrary* constant sequence (only `zero_R`/`one_R` are done), and
   the `add_R`/`sub_R`/`abs_R` unfolding lemmas, plus `cauchyfy_id` applied to `D` and to `A`.
4. Assembly, including `max` case analysis to get `n ≥ k`.

**One statement-level observation.** With `le_R` in place of `lt_R` the lemma is Π₁⁰ and needs
*no* witness at all: `¬∃n(…)` follows from the crude bound alone, since the difference is
negative and `2^{-n}` is positive. The entire Archimedean-modulus content of `approx_R` comes
from the `<_ℝ` spelling. Worth checking against Kohlenbach p. 80 before investing in item 2:
if the book says `≤_ℝ`, the lemma is a fraction of the work and items 1–3 shrink accordingly.

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
(Proved 2026-09-03: `abs_le_encode` in `RealNumbers/QBounds.lean` is exactly this argument,
and `mul_R_check`/`abs_R_bound` cash it. See §0.23.)

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
