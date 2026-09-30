# ProofMode/RealMCT.lean

## module header

### The argument, and where it comes from

**The book** (Kohlenbach, *Applied Proof Theory*, §2.3, Prop. 2.26–2.27, pp. 30–32; the
no-counterexample interpretation of the Cauchy property of a nonincreasing sequence in
`[0,1]`): with `g̃(n) := n + g(n)`, *assume every window `[g̃^i(0), g̃^{i+1}(0)]`, `i ≤ 2^k`,
drops by at least `2^{-k}`; then `a_0 − a_{g̃^{2^k+1}(0)} ≥ (2^k+1)·2^{-k} > 1`, a
contradiction, so some window `i ≤ 2^k` drops by `< 2^{-k}`; monotonicity turns the drop into
`|a_i − a_j| < 2^{-k}` on the window, and `Φ(g,k) := g̃^{(2^k)}(0)` bounds its left end.*
`Reference/MCT.lean` is the same argument on Mathlib (`descent`: `N` bad windows lose `N·ε`;
`metastable`: with `N := 2^k + 1` that exceeds `1`).

**Here** the counting is done *constructively*, exactly as `ProofMode/MCT.lean` does it for
ℕ-MCT: a budget induction rather than a reductio. Write `ε := ⟨2^{-(k+1)}⟩ℝ` and
`q_j := ⟨j ·ℚ 2^{-(k+1)}⟩ℝ`; the descent formula (`real_mct_descent`) is

    A(j)  ≡  (∀u B)  →  ∀m ( a m ≤ℝ q_j  →  ∃n C(n) ).

* **The window lemma** (`real_mct_window`), the one step of the book's argument: for every
  `m`, either `C(m)` holds — `n := m` is the witness — or the window at `m` is *bad*, and
  then `a(m+g m) +ℝ ε ≤ℝ a m` together with `0ℝ ≤ℝ a(m+g m)`. The dichotomy is
  `qf_lem` on `C(m)`; the bad case is `MCTLemmas.window_drop`: `¬C(m)` is, by
  `qf_double_neg_elim` and `cauchyfy_const`, the rational fact
  `2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ 2^{-(k+1)}`, which `const_le_R_of_sample` (through
  `approx_le_R_core`, Lemma 4.2 in `≤` form) lifts to `ε ≤ℝ |a m −ℝ a(m+gm)|ℝ`; antitonicity
  (`antitone_chain_R`, from the premise) makes the difference nonnegative, so
  `|w|ℝ ≤ℝ w` and the drop follows by monotonicity and `g +ℝ (f −ℝ g) ≤ℝ f`.
* **Base `j = 0`**: `a m ≤ℝ q_0 ≤ℝ 0ℝ`; a bad window would give `0 +ℝ ε ≤ℝ a(m+gm) +ℝ ε ≤ℝ
  a m ≤ℝ 0ℝ`, i.e. `ε ≤ℝ 0ℝ`, which is literally `¬(0ℝ <ℝ ε)` and `zero_lt_pow2neg_R` refutes
  it. (The book's contradiction, localised to the window that would overdraw the budget.)
* **Step `j → j+1`**: `a m ≤ℝ q_{j+1} ≤ℝ q_j +ℝ ε` (`budget_succ_R`: `(j+1)·e =ℚ j·e + e`), so
  a bad window gives `a(m+gm) +ℝ ε ≤ℝ q_j +ℝ ε`, cancel `ε` (`le_R_add_cancel_r_core`,
  algebraically), and the induction hypothesis applies at `m + g m`.
* **Closing** (`real_mct_body`): `A(2^{k+1})` at `m := 0`, since `a 0 ≤ℝ 1ℝ ≤ℝ q_{2^{k+1}}`
  (`budget_top_Q`: `⟨2^{k+1}⟩ ·ℚ 2^{-(k+1)} =ℚ 1`, from `encode_pow2_mul`).

### Where the factor 2 enters

The book's budget is `2^k` windows of drop `2^{-k}`. Ours is `2^{k+1}` windows of drop
`2^{-(k+1)}`, because the dichotomy is taken on the *quantifier-free* `C(m)` — a rational
comparison at the single index `k+3` — rather than on the real statement `D ≤ℝ 2^{-k}`. A
window that fails `C(m)` is only known to have `D̂(k+3) ≥ 3·2^{-(k+2)}`, hence real drop
`> 5·2^{-(k+3)}`, and the dyadic budget unit under `5/8` is `2^{-(k+1)}` (`docs/REAL_MCT.md` §1,
§6). The price of a constructive, `Allowed.extended` derivation is therefore one extra
iteration of `m ↦ m + g m` in the exponent — `Φ ≈ g̃^{(2^{k+1})}(0)` against the book's
`g̃^{(2^k)}(0)` — and the `2^k + 1` of `Reference/MCT.lean` is a third bookkeeping (its
`descent` is non-strict; `Reference/MCTBridge.lean` §4–5).

### Where the encoding forced a choice

* **The conclusion is read at index `k+2` with slack `2^{-(k+1)}`** — fixed by the statement,
  not here; `C(m)` is one `forall_ax` away from `D ≤ℝ ε`, and the *bad* branch consumes it
  as a rational inequality at index `k+3` (`leIdx_dne`), then `cauchyfy_const` evaluates the
  constant's cauchyfication.
* **The budget is a rational code**, `mul_Q (encode_nat_Q j) (pow2neg_Q (k+1))`, not a real
  product: `mul_R` carries an index shift and an estimate; the code needs three ℚ identities
  (`budget_zero_Q`, `budget_succ_Q`, `budget_top_Q`) and no estimate.
* **`add_R`'s `+1` shift** never surfaces: every `≤ℝ` fact used is either from `LeOrder.lean`
  (where the shift was paid) or a constant comparison (`const_R_le_add`, slack-free).
* **ℕ-equalities under `a ⬝ (·)`** cannot be rewritten by `prw` inside a `le_R`; the antitone
  chain uses `le_R_app_congr_l` (unpack the `¬∃`, `prwby` in the QF witness).
* **`0ℝ`/`1ℝ` are constant reals** (`zero_R_eq_const`, `one_R_eq_const`), so `q_0 ≤ℝ 0ℝ` and
  `1ℝ ≤ℝ q_{2^{k+1}}` are instances of `const_R_mono`.

### Mechanics worth recording

* **The premise is consumed *before* it is weakened.** `real_mct_window` is stated
  `(∀u B) →ᶠ ∀m (…)`, applied to `H` in the context where `H` was introduced, and only then
  is `∀m` opened; the per-`m` statement is recovered by `pinst hw x₀`. A `weakenBy`-wrapped
  hypothesis and a freshly elaborated lemma instance differ in the *placement* of the
  renamings around the opaque parameters `a`, `g`, `k` (`rename (ext shift) (weaken a)` vs
  `weaken (weaken a)`), which are not definitionally equal, so `rmnorm` pushes every
  `weakenBy`/`renameF` to the leaves and folds them (`rename_ext_weaken`), and instantiation
  at a bound variable is `pinst h xₖ` rather than `pspecialize`.
* **`leIdx` stays folded.** `leIdx_substF`/`leIdx_renameF`/`leIdx_weakenBy` keep the matrix
  as `leIdx f g m` under substitution, so the delta-expansion of `cauchyfy`/`le_Q_dec`
  (CLAUDE.md "Build cost") is never approached: only the *arguments* are normalised.

### What the extraction will see (qualitative; no `derivSize`, no evaluation here)

The derivation tree is `mct_p2`'s: one `pinduction` (→ `sInduction`), one `qf_lem` per
window (inside the induction step *and* the base, since both use `real_mct_window`), and per
window one `antitone_chain_R` instance (itself an induction), one `window_drop` (which calls
`const_le_R_of_sample` → `approx_le_R_core` → `cauchyfy_shift_le` → `cauchyfy_tele`, another
induction, plus `abs_R_le_self_of_nonneg`, `sub_R_nonneg_of_le`, `add_sub_cancel_le_R_core`,
each a chain of `le_R_trans_core`, which contains the `leR_*` telescope — an induction each
time it is invoked). `le_R_trans_core` is used 9 times in the window/step/base scripts and
∼25 times inside the lemmas; `le_R_add_mono_{l,r}_core` 8 times; `le_R_of_eq_R_core` ∼20
times in the algebraic chains. The realizer's DAG is therefore dominated by copies of the
`≤ℝ`-transitivity telescope; the *iteration* `m ↦ m + g m` appears exactly once, at the
`pinst ih1 (x₁ +ᵗ g ⬝ x₁)` of the step — as in `mct_p2`.
