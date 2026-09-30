# RealMCTStatement.lean

## module header

`MCTStatement.lean` is **ℕ**-MCT: values are naturals, order is `x ∸ y =₀ 0`, the conclusion
is *exact* equality `a v =₀ a (v + g v)`, and the budget is a natural `K`. `Reference/MCT.lean`
is **ℝ**-MCT on Mathlib: antitone in `[0,1]`, conclusion `|a i − a j| ≤ 2^{-k}`. This file is
ℝ-MCT *inside the object logic*, over the encoded reals (`realTy ι = nat →ₜ nat`, Cauchy
sequences of ℚ-codes with the fixed modulus `2^{-n}`).

### The statement — design of each part

* **`x` packs the three parameters with `Ty.prod`**: `a := fst x : ℕ → ℝ` the sequence,
  `g := fst (snd x) : ℕ → ℕ` the counterfunction, `k := snd (snd x) : ℕ` the precision.
  No Cantor pairing and no `mctTy`-style fusion into one functional (`MCTStatement.lean`
  predates products and reads `a`, `g`, `K` off `h ⌜0⌝`, `h ⌜1⌝`, `h ⌜2⌝ ⌜0⌝`). Products
  never move the type level — `degree (.prod ρ τ) = max ρ.degree τ.degree` — so `ρ` has
  degree 2, that of `ℕ → ℝ`. The hat type is
  `ρ.hat = (ℕ → ℕ → ℕ) ×ₜ ((ℕ → ℕ) ×ₜ ℕ)`, so `x* = (a*, (g*, k*))`.

* **The premise `∀u B` says `a` is antitone and lies in `[0,1]`, with `u` the Cauchy
  index** — the `TriangleBoundDemo` design. `le_R_pu f g` (`Terms/Real.lean`) is literally
  `Formula.all Ty.nat (leIdx f.weaken g.weaken (.var .vz))` where `leIdx f g m` is its
  quantifier-free body at index `m` (`all_leIdx_eq`, by `rfl`). `B` is

      B(u, x)  :=  ∀n ( leIdx (a(n+1)) (a n) u  ∧  leIdx 0ℝ (a n) u  ∧  leIdx (a n) 1ℝ u )

  so `∀u B` is `∀u ∀n (…)`, which is the three `le_R_pu` statements `∀n (a(n+1) ≤ℝ a n)`,
  `∀n (0ℝ ≤ℝ a n)`, `∀n (a n ≤ℝ 1ℝ)` with the two quantifier blocks swapped and the
  three Cauchy indices identified. **One `∀u` block carries all three conditions, and no
  product type is needed inside `B`**: the sequence index `n` is bound by `B`'s own inner
  `∀n`, and the Cauchy index is shared — `le_R_pu`'s `∀n` is a "for every precision" and
  identifying the three precisions loses nothing. `B` is purely universal (`.all` over a
  conjunction of QF formulas — `isPurelyUniversal` is closed under `∧`) and ∨-free.
  Consequently the extracted `U` bounds **the precision to which antitonicity and
  `0 ≤ a ≤ 1` must be known** — a genuinely proof-mining-shaped quantity (the hypotheses
  need only hold up to `2^{-U}`), and the same reading `TriangleBoundDemo` gave its `U`.
  The alternative packing — `u` the sequence index, the Cauchy index inside — would make `U`
  bound how far into the sequence the hypotheses are consulted; both are legitimate, this one
  is what is built, and `docs/REAL_MCT.md` §1 records the trade.

* **The conclusion `∃v C` is the metastability statement with explicit slack at a fixed
  index** — the one genuine design step in the statement. The real-number statement
  `|a v −ℝ a (v + g v)|ℝ ≤ℝ 2^{-k}` is Π⁰₁ (`le_R_pu` is `∀n …`), so `∃v (…)` would be
  Σ⁰₂ and fits neither our metatheorem nor Kohlenbach 17.52, whose `C∃` is an ∃-formula.
  Because every encoded real carries the fixed modulus `2^{-n}`, one rational comparison at
  one index suffices, and the choice of index and slack is forced by two accountings:

      C(v, x)  :=  leIdx  |a v −ℝ a (v + g v)|ℝ   ⟨2^{-(k+1)}⟩ℝ   (k+2)

  i.e. the QF body of `le_R_pu D c` at index `m := k+2`, with `D` the window difference and
  `c := const_R (pow2neg_Q (k+1))` the constant real `2^{-(k+1)}`. Written out it is
  `¬( 2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ ĉ(k+3) )`, and since `ĉ ≡ 2^{-(k+1)}` (a constant code passes
  every check, `cauchyfy_const`) it says **`D̂(k+3) <ℚ 3·2^{-(k+2)}`** — the cauchyfied
  window difference, read at index `k+3`, is below `3·2^{-(k+2)}` as a rational.

  - *Why it implies the real statement* (`rmC_implies`, proved below in every model):
    `|D̂(k+3) − codeReal D| < 2^{-(k+3)}` (`abs_qval_cauchyfyN_sub_codeReal_lt`), so
    `codeReal D < 3·2^{-(k+2)} + 2^{-(k+3)} = 7·2^{-(k+3)} < 2^{-k}`. The conclusion
    `|a v − a(v+g v)| < 2^{-k}` is *strict*, with `2^{-(k+3)}` to spare.
  - *Why this index and this slack, and not `k` and `2^{-k}` directly*: the conclusion must
    be *one `forall_ax` away* from a real inequality `D ≤ℝ c` the derivation produces,
    exactly as `TriangleBoundDemo` reads its `C` off `dist_tri`: `le_R_pu_of_le_R` then
    `forall_ax (k+2)` yields `C` verbatim, with no ℚ arithmetic at the end and no `cauchyfy`
    step spent. Reading `D ≤ℝ c` at index `m` gives `D̂(m+1) < c + 2^{-m}` — a *strict*
    bound with positive slack — so a non-strict target `D̂(j) ≤ℚ t` is unreachable and the
    target has to be the strict `D̂(k+3) <ℚ c + 2^{-(k+2)}`; that is the tightness
    discipline of CLAUDE.md's ℝ section applied to the statement rather than to a proof.
    The two free parameters are then pinned by the descent proof (`docs/REAL_MCT.md` §3): a
    window that *fails* `C` has `D̂(k+3) ≥ 3·2^{-(k+2)}`, hence a real drop
    `> 3·2^{-(k+2)} − 2^{-(k+3)} = 5·2^{-(k+3)} > 2^{-(k+1)}`, so the budget unit is
    `2^{-(k+1)}` and `a 0 ≤ 1` allows `2^{k+1}` bad windows. With `c = 2^{-(k+2)}` instead the
    drop is only guaranteed `> 2^{-(k+2)}` and the budget doubles to `2^{k+2}`; with
    `c = 2^{-k}` the good window would no longer certify `< 2^{-k}`. `c = 2^{-(k+1)}` at
    index `k+2` is the dyadic choice that keeps both, at the cost of a factor `2` over the
    sharp `2^k` (`Reference/MCTBridge.lean`).
  - It is QF, so `isPurelyExistential` and ∨-free hold trivially, and the metatheorem's own
    `∃v` is the only existential: no inner `∃c` block is needed.

  The other natural conclusion — the *drop* form `a v ≤ℝ a(v + g v) +ℝ 2^{-k}`, which is
  what the descent literally produces and which involves no `neg_R` — is equivalent to the
  absolute-value form under antitonicity. The `|·|` form is what is used here, and the only
  cost was one semantic lemma (`codeReal_negR`, below) that did not exist.

### What the extracted `Φ` would bound

`Φ : ρ.hat → ℕ`, `Φ(a*, g*, k*)`, bounds both `u` (the precision at which the premise is
consulted) and `v` (the left end of the good window). Uniformity, and its limit here:

* `k* ≥ k` and `g* ≽ g` (pointwise dominant and monotone) are the expected dependences; the
  bound `Reference/MCT.lean` computes by hand, `(shift g)^[2^k + 1] 0`, depends on exactly
  these.
* **`a*` is NOT `λn.1`, and cannot be, for the sequence as quantified here.** Majorization at
  `ℕ → ℝ = ℕ → ℕ → ℕ` is Bezem's: `a* n m ≥ a n m` pointwise plus monotonicity of `a*`.
  A code of a real in `[0,1]` is *not* bounded by the real's size — `codeReal_zero_code_unbounded`
  below exhibits codes of `0` with `f 0` arbitrarily large — so the premise `0 ≤ a ≤ 1`
  bounds `codeReal (a n)`, not the numbers `a n m`. Nor does `clamp01` help:
  `clamp01_Q` is the identity on codes of rationals strictly inside `(0,1)`, so
  `clamp01 f` has codes as large as `f̂`'s. Kohlenbach's uniformity comes from the *rounded*
  representative `(·)◦` (Def. 17.7): every real in `[0,b]` has a representative dominated by
  the single fixed function `Mmaj b` — `Rounding.roundR_le₁_Mmaj` at `b = 1`, with
  `Mmaj_mono` for the monotonicity half. That gives `a* := λn. Mmaj 1`, independent of `a`,
  **provided the statement quantifies over `a` through an object-level rounding term**,
  `a ↦ λn. (a n)◦`, which does not yet exist (`Term.round_nat` embeds naturals only). Adding
  it — a bounded search `max k ≤ 2^{n+1} [k/2^{n+1} ≤ℚ x(n+1)]` by `prec`, with `x◦ =ℝ x` for
  `x ∈ [0,1]` — is the one ingredient standing between this statement and a `Φ(g*, k)`
  independent of `a`. Until then `Φ` depends on `a*`, honestly.

## the classical example (docstring)

Note that `ProofMode.real_mct_p2` is *not* such a derivation: the **metastable** form of ℝ-MCT
needs no excluded middle and no Markov, so it is derivable at every `Allowed` and goes through
the extended entry point above. (The *Cauchy* form is the one that needs classical logic —
that is Kohlenbach's point about metastability, and it is reproduced here.) This shape check
is for a client that genuinely is classical, such as a proof that assumes no good window
exists and derives strict drops.
