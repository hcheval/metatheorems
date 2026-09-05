# ℝ-MCT — statement, bridge, and the derivation plan

2026-09-05, branch `real-mct`. Companion to `Metatheorems/RealMCTStatement.lean` (the statement,
in the build) and `Reference/MCTBridge.lean` (the `K := 2^k` bridge, Mathlib-level, not built).
This file is the **plan for the derivation**, which is deliberately *not* written yet. Read
CLAUDE.md's Track A item 4 and Track D first; this closes D4's "one genuine design step" and
A4's "bridge that is nowhere written", and leaves the derivation itself as the next job.

Everything under §§1–2 and §6 is checked by Lean. §§3–5 and §7 are prose: a plan, with every
claim about an existing lemma made by name so it can be checked, and every missing lemma
listed with the shape the plan needs.

## 0. What exists, in one table

| piece | where | status |
|---|---|---|
| the statement `rmStatement : ∀x(∀u B → ∃v C)` | `RealMCTStatement.lean` | in the build, side conditions by `rfl` |
| fits `syntactic_general_metatheorem_at_gen` / `_classical_gen` | same, `rmBound` + two `example`s | elaborates with `prf` as a binder |
| premise ⇔ `codeReal ∘ a` antitone in `[0,1]` | `rmB_all_iff` | proved, every model |
| conclusion ⇒ `\|a v − a(v+g v)\| < 2^{-k}` | `rmC_implies` | proved, every model |
| the assembled reading (`Reference/MCT.lean`'s `metastable` with `Φ` extracted) | `real_mct_of_bound` | proved, from any derivation |
| `neg_R` on raw codes: `codeReal (neg ∘ g) = −codeReal g` | `codeReal_negR`, `codeReal_subR_all` | proved (was only for check-passing codes) |
| no uniform majorant on raw codes of `[0,1]` | `codeReal_zero_code_unbounded` | proved |
| `K := 2^k` bridge, off-by-one located | `Reference/MCTBridge.lean` | checks with `lake env lean` |
| the derivation | — | **not started**; plan below |

## 1. The statement, and the two packing choices

    ∀ x^{(ℕ→ℝ) ×ₜ ((ℕ→ℕ) ×ₜ ℕ)} ( ∀u B(u,x) → ∃v C(v,x) )

    a := fst x,  g := fst (snd x),  k := snd (snd x)

    B(u,x) := ∀n ( leIdx (a(n+1)) (a n) u  ∧  leIdx 0ℝ (a n) u  ∧  leIdx (a n) 1ℝ u )
    C(v,x) := leIdx |a v −ℝ a(v + g v)|ℝ  ⟨2^{-(k+1)}⟩ℝ  (k+2)

where `leIdx f g m` is the quantifier-free body of `le_R_pu f g` at index `m`
(`all_leIdx_eq : Formula.all nat (leIdx f.weaken g.weaken (var vz)) = le_R_pu f g`, by `rfl`).

**Parameters.** Packed with `Ty.prod`, no Cantor pairing, no `mctTy`-style fusion. `ρ` has
degree 2 (that of `ℕ → ℝ`); `ρ.hat = (ℕ→ℕ→ℕ) ×ₜ ((ℕ→ℕ) ×ₜ ℕ)`, so `x* = (a*, (g*, k*))`.

**Premise: `u` is the Cauchy index** (the `TriangleBoundDemo` design, as the brief asked).
`∀u ∀n (…)` is the three `le_R_pu` statements with their `∀`-blocks swapped past `∀n` and the
three Cauchy indices identified. One `∀u` block carries all three conditions and **no product
type is needed inside `B`** — `n` is bound by `B`'s own inner `∀n`. Consequence: the extracted
`U` bounds *the precision to which the hypotheses must be known*. The alternative packing —
`u` the sequence index, the Cauchy index inside — makes `U` bound *how far into the sequence
the proof looks*, which is the ℕ-MCT reading (`mctB₀` has `u` as the sequence index). Both are
legitimate; the trade is: with `u` the Cauchy index, instantiating the premise at a sequence
index `m` inside a derivation costs a quantifier swap first (§3, step P0), whereas with `u` the
sequence index the premise is consumed exactly as `mct_p2` consumes `mctB₀` — but then
antitonicity would have to be *Π⁰₁ inside the block* and `B` would still be a ∀-formula, so
nothing is gained on the metatheorem side. The statement as committed keeps the brief's
choice; switching is a two-line change to `rmB` plus a rerun of `rmB_all_iff`.

**Conclusion: explicit slack at a fixed index** — CLAUDE.md D4's "one genuine design step".
`|D| ≤ℝ 2^{-k}` is Π⁰₁, so `∃v(…)` would be Σ⁰₂; neither our `_gen` metatheorem nor
Kohlenbach 17.52 takes it. Because the encoded reals carry the fixed modulus `2^{-n}`, one
rational comparison at one index says enough. `C` reads: `D̂(k+3) <ℚ 3·2^{-(k+2)}` (the
constant code `⟨2^{-(k+1)}⟩` is its own cauchyfication). Why exactly this:

* `C` must be *one `forall_ax` away* from a real inequality `D ≤ℝ c` the derivation produces
  (`le_R_pu_of_le_R`, then `forall_ax (k+2)`), with no ℚ arithmetic at the end. Reading
  `D ≤ℝ c` at index `m` gives the *strict* `D̂(m+1) <ℚ c + 2^{-m}`, so the target must be
  strict with positive slack — a non-strict `D̂(j) ≤ℚ t` is unreachable. Tightness triage,
  applied to the statement.
* The remaining freedom (`c`, `m`) is pinned by the descent proof (§3): a window that *fails*
  `C` has `D̂(k+3) ≥ 3·2^{-(k+2)}`, hence real drop `> 5·2^{-(k+3)} > 2^{-(k+1)}`; a window that
  passes has real drop `< 7·2^{-(k+3)} < 2^{-k}`. So the budget unit is `2^{-(k+1)}` and
  `a 0 ≤ 1` allows `2^{k+1}` bad windows. With `c = 2^{-(k+2)}` the budget doubles; with
  `c = 2^{-k}` the good window no longer certifies `< 2^{-k}`.
* It is QF, so the metatheorem's own `∃v` is the only existential.

The *drop* form `a v ≤ℝ a(v + g v) +ℝ 2^{-k}` (no `neg_R`) is what the descent literally
produces and is equivalent under antitonicity; the brief asked for `|·|`, and the only cost was
`codeReal_negR` on raw codes, now proved.

## 2. What `Φ` bounds, and the uniformity gap

`Φ(a*, g*, k*)` bounds `u` and `v`. `k* ≥ k` and `g* ≽ g` are the expected dependences.
**`a*` is not `λn.1`, and cannot be for the sequence as quantified.** Bezem majorization at
`ℕ → ℝ = ℕ → ℕ → ℕ` is pointwise on the *codes*; codes of reals in `[0,1]` are unbounded
(`codeReal_zero_code_unbounded`: `0` has codes with `f 0 > N` for every `N`). `clamp01` does
not help — `clamp01_Q` is the identity on codes of rationals strictly inside `(0,1)`, so a
clamped code is as large as the original. Kohlenbach's uniformity comes from the *rounded*
representative `(·)◦` (Def. 17.7): `Rounding.roundR_le₁_Mmaj` at `b = 1` + `Mmaj_mono` say
every real in `[0,1]` has a representative dominated by the single fixed `Mmaj 1`. To use it,
the statement must quantify over `a` through an **object-level rounding term**
`a ↦ λn. (a n)◦` — a bounded search `max j ≤ 2^{n+1} [j/2^{n+1} ≤ℚ x(n+1)]` by `prec`, with
`x◦ =ℝ x` on `[0,1]` — which does not exist (`Term.round_nat` embeds naturals only). That term
is the one missing ingredient between this statement and a `Φ(g*, k)` independent of `a`; it
is ordinary ℚ-layer work and belongs in `Terms/Real.lean` + `RealNumbers/`. Until then `Φ`
depends on `a*`, honestly, and the statement is still correct and still a metatheorem input.

## 3. The derivation plan — P2ℝ, the dichotomy proof (constructive)

The shape is `mct_p2`'s (`ProofMode/MCT.lean`): a budget induction on the number of drops,
with the dichotomy taken on the **quantifier-free conclusion matrix itself** via `qf_lem`, so
that no `Derivable.lem` is used and the derivation is at `Allowed.extended` — exactly as p₂ is
for ℕ-MCT. Write `ε := ⟨2^{-(k+1)}⟩ℝ = const_R (pow2neg_Q (k+1))` and `Cm := rmC.subst0 m`
("the window at `m` is good").

**Descent formula**, by `pinduction` on `j` carrying the premise `H := ∀u B`:

    A(j) ≡ H → ∀m ( a m ≤ℝ ⟨j ·ℚ 2^{-(k+1)}⟩ℝ → ∃n Cn )

(The budget is a *rational constant* `const_R (mul_Q (encode_nat_Q j) (pow2neg_Q (k+1)))`, not
`embed_nat_R j ·ℝ ε`: `mul_R`'s index shift buys nothing here and costs an estimate.)

* **P0. Premise unpacking** (FOL only): from `H = ∀u ∀n (…)` get, for each `n`,
  `le_R_pu (a(n+1)) (a n)`, `le_R_pu 0ℝ (a n)`, `le_R_pu (a n) 1ℝ` — a quantifier swap
  (`forall_rule`/`forall_ax`, `and_proj`s) — then `le_R_of_le_R_pu` (exists) to the `le_R`
  form every ℝ lemma uses. **Missing**: the swap lemma, trivial.
* **P1. Antitone chain, real**: `∀m i, a(m+i) ≤ℝ a m`. Induction on `i` with
  `le_R_trans_core` (exists), carrying the one-step hypothesis through `pinduction` — the
  hypothesis-dependent-induction pattern CLAUDE.md records for `cauchy_complete_R`. The ℕ
  version is `ProofMode/Arith.antitone_chain`. **Missing** (`antitone_chain_R`).
* **P2. Base `j = 0`**: `a m ≤ℝ ⟨0⟩ℝ`. With `0 ≤ℝ a(m+g m) ≤ℝ a m` (P0, P1):
  `w := a m −ℝ a(m+gm) ≤ℝ a m ≤ℝ 0` via `le_sub_R_of_le_add_core` (exists) from
  `a m ≤ℝ a m +ℝ a(m+gm)` (`le_R_add_mono_l_core` + `add_zero_R_core` + `le_R_congr`, all
  exist); `−w =ℝ a(m+gm) −ℝ a m ≤ℝ 0` (`neg_sub_R_core`, exists); so `|w|ℝ ≤ℝ 0ℝ`
  (`abs_R_le_of_le_le_core`, exists) `≤ℝ ε` (**missing** M7: `0ℝ ≤ℝ ⟨q⟩` from `0 ≤ℚ q`),
  hence `D ≤ℝ ε`, `le_R_pu_of_le_R`, `forall_ax (k+2)` gives `Cm`, `exist_ax m`.
* **P3. Step `j → j+1`**: `a m ≤ℝ ⟨(j+1)·2^{-(k+1)}⟩`. Split `Cm ∨ᶠ ¬ᶠCm` by
  `qf_lem (rfl)` — `(rmC.subst0 m).isQF = true` by `rfl` since substitution preserves the
  `imp (eq0 _ _) bot` shape. Good branch: `exist_ax m`. Bad branch:
  1. `¬ᶠCm` is `¬¬(2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ 2^{-(k+1)})`; `qf_double_neg_elim` (exists) gives
     the ℚ fact, and ℚ arithmetic (`add_Q`/`sub_Q` lemmas, exist) gives
     `3·2^{-(k+2)} ≤ℚ D̂(k+3)`.
  2. Lift to ℝ: `⟨3·2^{-(k+2)}⟩ ≤ℝ ⟨D̂(k+3)⟩` (**missing** M1 `const_R_mono`), and
     `approx_R` (exists: `|D −ℝ ⟨D̂(n)⟩| <ℝ ⟨2^{-n}⟩`) at `n := k+3`, unpacked to
     `⟨D̂(k+3)⟩ ≤ℝ D +ℝ ⟨2^{-(k+3)}⟩` (**missing** M3 — check `bound_of_abs_sub_le_const`,
     which is the ℚ-index form, and `abs_R_le_of_le_le_core`, which is the converse
     direction; the needed direction `|f −ℝ g| ≤ℝ v → g ≤ℝ f +ℝ v` is not written).
  3. `⟨3·2^{-(k+2)}⟩ −ℝ ⟨2^{-(k+3)}⟩ ≤ℝ D` (`le_sub_R_of_le_add_core`, exists), and the
     left side `=ℝ ⟨5·2^{-(k+3)}⟩ ≥ℝ ⟨2^{-(k+1)}⟩` (**missing** M2 `const_R_sub`/`const_R_add`
     + M1), so `ε ≤ℝ |w|ℝ` with `w := a m −ℝ a(m+gm)`.
  4. `|w|ℝ ≤ℝ w` since `0ℝ ≤ℝ w` (P1): **missing** M4 `abs_R_le_self_of_nonneg`, from
     `abs_R_le_of_le_le_core` and `−w ≤ℝ 0 ≤ℝ w` (**missing** M4a `neg_R_nonpos_of_nonneg`).
     (Do *not* go through `|w| =ℝ w`: that is tight — the drift `|ŵ| − ŵ` is `2^{-(n-1)}`
     against `eq_R`'s `2^{-n}` — and would need the `eqR` engine. `≤ℝ` is slack-free.)
  5. Hence `ε ≤ℝ a m −ℝ a(m+gm)`, so `a(m+gm) +ℝ ε ≤ℝ a(m+gm) +ℝ (a m −ℝ a(m+gm))`
     (`le_R_add_mono_l_core`) `≤ℝ a m` (**missing** M5 `add_sub_cancel_le_R_core :
     a +ℝ (b −ℝ a) ≤ℝ b`, pure ring rearrangement over `add_comm_R_core`, `add_assoc_R_core`,
     `add_neg_R_core`, `add_zero_R_core`, `le_R_of_eq_R_core` — no estimate)
     `≤ℝ ⟨(j+1)·2^{-(k+1)}⟩ =ℝ ⟨j·2^{-(k+1)}⟩ +ℝ ε` (M2 + ℚ `distrib_Q`/`mul_Q_one`).
  6. Cancel `ε` on the right: **missing** M5' `le_R_add_cancel_r_core : f +ℝ h ≤ℝ g +ℝ h →
     f ≤ℝ g`. Do it *algebraically*, not by estimate: `f ≤ℝ (f+h)+(−h) ≤ℝ (g+h)+(−h) ≤ℝ g`
     with `le_R_add_mono_r_core` and `add_neg_cancel_le_R_core` (both exist) plus the reverse
     cancellation `f ≤ℝ (f+h)+(−h)` (an `=ℝ` fact). A direct estimate is tight (reading the
     hypothesis at `n+1` and moving three indices overshoots by `2^{-(n+2)}`), exactly the
     situation CLAUDE.md's reverse-triangle note warns about.
  7. Now `a(m+gm) ≤ℝ ⟨j·2^{-(k+1)}⟩`: apply the induction hypothesis at `m + g m`.
* **P4. Closing**: `A(2^{k+1})` at `m := 0`, since `a 0 ≤ℝ 1ℝ =ℝ ⟨2^{k+1} ·ℚ 2^{-(k+1)}⟩`
  (ℚ: `pow2neg_Q_mul`/`encode_pow2_mul`, exist; M2 for the constant). Then fuse `a, g, k` into
  `x` by `pforall` + `pthm`, as `mct_p2` does with `x₀ ⬝ ⌜0⌝` etc.

**Nothing in P0–P4 is classical.** `qf_lem` and `qf_double_neg_elim` are derivable for QF
formulas; every ℝ lemma is stated for arbitrary `al`; `approx_R` is `[propext, Quot.sound]`.
So P2ℝ is an `Allowed.extended` derivation and goes through `syntactic_general_metatheorem_at_gen`
(the *extended* entry point) — the same conclusion CLAUDE.md D-4.2 reached for `mct_p2`. D4's
expectation that ℝ-MCT is "the first genuine client of the classical metatheorem" holds for
the *textbook* proof, not for this one; see §4.

**The two mechanical risks**, both known families:

* `Cm = rmC.subst0 m` inside the proof mode. `pinst`/`anorm` push `subst` through
  `cauchyfy`, `le_Q_dec`, `sub_Q`, `abs_R`, `sub_R`, `const_R` — the delta-expansion trap
  (CLAUDE.md "Build cost"). The `closed_subst` set covers all of them (`Defs.lean`:
  `add_R`, `neg_R`, `abs_R`, `cauchyfy`, …; `const_R_subst` in `Approx.lean`), so `qnorm`-style
  normalisation should stop at the constants. `ConjBoundDemo`'s "two instantiation terms in one
  formula" wall is an *extraction* (`whnf`) phenomenon, not a proof-mode one — but `rmC` at two
  different `m`s in one sequent (the IH at `m + g m` and the goal at `m`) is exactly that
  shape, so expect to name `Cm` through an abbreviation and rewrite with `le_R_substF`-style
  lemmas rather than let `anorm` unfold. Budget a day for this, as CLAUDE.md's ℝ notes do.
* The `weakenBy`/`Formula.weakenBy` display-hiding traps around `pm_exE`/`pinst` (trap 12):
  run `rnorm` after every `pinst`, per the `cauchy_complete_R` note.

## 4. The classical route — P1ℝ — and where the classical content sits

The textbook proof (`Reference/MCT.lean`, `cauchy`) takes an infimum: not available. The
Kohlenbach-style classical proof is P2ℝ with the dichotomy taken on the **real** statement:

    a m ≤ℝ a(m+gm) +ℝ ε   ∨   ¬(a m ≤ℝ a(m+gm) +ℝ ε)

i.e. `Derivable.lem` at a Π⁰₁ formula (`le_R` is `¬∃`), equivalently LEM at the Σ⁰₁
`ε <ℝ a m −ℝ a(m+gm)` — one instance per descent step, inside `∀m`. The negative branch is
`¬¬(lt_R …)`; under `Allowed.classical` that is again LEM (no `Derivable.markov` needed; under
`extended` it *would* be Markov, whose QF-body condition `lt_R`'s matrix satisfies — that is
how `mct_p1`'s hand translation works, CLAUDE.md D-1/D-4.2). The good branch then yields
`D ≤ℝ ε` as a real inequality and `Cm` by one `forall_ax`, with the same P2/P4 as above but
**no** `approx_R` step 2–4: the ε-management of §3 is precisely what replaces the LEM.

So: the classical content is *isolated to the dichotomy*, one Σ⁰₁-LEM per descent step; the
`pby_contra` discipline puts it there and nowhere else (the headline `∃n` is produced by
`exist_ax` with an explicit witness in both branches, never by contradiction). P1ℝ is the
genuine first client of `syntactic_general_metatheorem_classical_gen` — with the caveat that
`Probes/LemBoundDemo.lean` shows the classical route does not currently reduce to a numeral
even on a 12-constructor derivation (`negTrans_sound` inflates 363 → 84,905 constructors), so
P1ℝ is a *derivability* target, and P2ℝ + the MFI (`Probes/MonotoneSpike.lean`) is the route
to a number.

## 5. Missing ℝ lemmas — the complete list

All are "assembly of paid estimates" in CLAUDE.md's sense; none needs the `eqR`/`leR`
telescope. Names are proposals.

| # | statement | route | needed by |
|---|---|---|---|
| M1 | `const_R_mono : p ≤ℚ q → ⟨p⟩ℝ ≤ℝ ⟨q⟩ℝ` (and `<` variant) | `le_R_of_bound` + `cauchyfy_const`; slack-free | P3.2, P3.3, P4 |
| M2 | `const_R_add : ⟨p⟩+ℝ⟨q⟩ =ℝ ⟨p+ℚq⟩`, `const_R_sub`, `const_R_congr : p =ℚ q → ⟨p⟩ =ℝ ⟨q⟩` | `eq_R_of_cauchyfy_eqQ` + `cauchyfy_add_R`/`cauchyfy_sub_R`/`cauchyfy_const`; on the nose at every index | P3.3, P3.5, P4 |
| M3 | `le_add_of_abs_sub_lt : \|f −ℝ g\|ℝ <ℝ v → g ≤ℝ f +ℝ v` | index-wise from `lt_R` witness, or via `bound_of_abs_sub_le_const`'s ℚ form + `le_R_of_all`; check `abs_R_le_of_le_le_core`'s file for a converse | P3.2 |
| M4 | `abs_R_le_self_of_nonneg : 0ℝ ≤ℝ w → \|w\|ℝ ≤ℝ w` | `abs_R_le_of_le_le_core` + M4a | P3.4 |
| M4a | `neg_R_nonpos_of_nonneg : 0ℝ ≤ℝ w → −ℝw ≤ℝ 0ℝ` | `le_R_of_bound` + `cauchyfy_neg` + `cauchyfy_zero_R`; slack-free | M4 |
| M5 | `add_sub_cancel_le_R_core : a +ℝ (b −ℝ a) ≤ℝ b` and its reverse | ring identities + `le_R_of_eq_R_core`; no estimate | P3.5 |
| M5' | `le_R_add_cancel_r_core : f +ℝ h ≤ℝ g +ℝ h → f ≤ℝ g` | algebraic (§3 P3.6), **not** a direct estimate (tight) | P3.6 |
| M6 | `antitone_chain_R` | `pinduction` carrying the hypothesis, `le_R_trans_core` | P1 |
| M7 | `zero_le_const_R : 0ℚ ≤ℚ q → 0ℝ ≤ℝ ⟨q⟩ℝ` | instance of M1 (`zero_R` is `const_R zero_Q` up to a weaken) | P2 |
| M8 | the premise quantifier swap (FOL) | `forall_rule`/`forall_ax` | P0 |

Existing and load-bearing, by name: `le_R_of_le_R_pu`, `le_R_pu_of_le_R`, `le_R_all`,
`le_R_of_all`, `le_R_of_bound`, `le_R_trans_core`, `le_R_congr`, `le_R_add_mono_l_core`,
`le_R_add_mono_r_core`, `le_sub_R_of_le_add_core`, `add_neg_cancel_le_R_core`,
`neg_sub_R_core`, `sub_R_eq_add_neg_R_core`, `abs_R_le_of_le_le_core`, `le_R_of_eq_R_core`,
`approx_R`/`approx_R_core`, `const_R`/`const_R_apply`/`const_R_check`/`const_R_subst`,
`cauchyfy_const`, `cauchyfy_sub_R`, `cauchyfy_abs_R`, `eq_R_of_cauchyfy_eqQ`,
`add_zero_R_core`, `add_comm_R_core`, `add_assoc_R_core`, `add_neg_R_core`, `qf_lem`,
`qf_double_neg_elim`, `le_Q_or_lt_Q`, `pow2neg_Q_mul`, `encode_pow2_mul`, `distrib_Q`.

## 6. The bridge to ℕ-MCT (`Reference/MCTBridge.lean`)

The precise sense in which "an antitone `[0,1]`-sequence dropping by `2^{-k}` at most `2^k`
times is the ℕ-MCT descent with budget `K`": coarsen `b n := ⌊a n · 2^k⌋₊`. Then `b` is
antitone with `b 0 ≤ 2^k` (**this is `K := 2^k`**), equal floors give `|a i − a j| < 2^{-k}`
strictly, and ℕ-MCT's bound `Φℕ K g = (shift g)^[K] 0` transports to `(shift g)^[2^k] 0`.

**The literal identification with `Reference/MCT.lean`'s `Φ k g = (shift g)^[2^k+1] 0` is
false by one iterate** (`Φℕ_lt_Φ_const_one`: `2^k` vs `2^k+1` for `g ≡ 1`). The reference's
`+1` is slack in its own proof — its `descent` is non-strict, so it needs one extra window to
contradict `a ∈ [0,1]`. The exact accounting, for `g ≡ 1` (all proved):

| statement | sharp bound on the first good `n` |
|---|---|
| ℕ-MCT, budget `K` | `K` (attained by `K − n`) |
| ℝ-MCT, `\|a i − a j\| < 2^{-k}` — what `rmC` delivers | `2^k` (attained by `(2^k − n)/2^k`) |
| ℝ-MCT, `\|a i − a j\| ≤ 2^{-k}` | `2^k − 1` (`metastable_le_sharp`, strict descent) |
| `Reference/MCT.lean`'s `Φ` | `2^k + 1` |

So the ℕ-bridge bound is *exactly* the sharp bound for the strict conclusion, which is the one
the object-level statement produces. The P2ℝ descent of §3 has budget `2^{k+1}` — a factor `2`
above sharp — because its QF dichotomy certifies a good window at `< 7·2^{-(k+3)}` and a bad one
at `> 5·2^{-(k+3)}`, and the budget unit `2^{-(k+1)}` is the dyadic that fits under `5/8`.

## 7. Size and extraction prospects — qualitative only

Do not run `derivSize` on any of this (it OOMs on the 15-line `le_R_of_all`; CLAUDE.md,
reverse-triangle note). Qualitatively: P2ℝ's *skeleton* is `mct_p2`'s ~40-line script, but each
leaf that was a `monus` fact in ℕ-MCT is here an ℝ-layer lemma (`le_R_trans_core`, `approx_R`,
M1–M7), each of which is itself a proof-mode script over `cauchyfy` estimates, with the ℚ layer
underneath. The derivation is therefore one-to-two orders above anything extracted so far, and
`sInduction` (Track A item 2) is on its path in the same place it is on `mct_p2`'s. The route
to a numeral is not term extraction but the monotone interpretation (`Probes/MonotoneSpike.lean`,
ARCHITECTURE.md §14) — and even there, `Φ` will come out as a `2^{k+1}`-fold iteration of
`m ↦ m + g* m` dressed in whatever the majorants of the ℝ-layer lemmas contribute, which is
where CLAUDE.md A5's "astronomical, structurally" applies. The mathematically meaningful
comparison is against `Φℕ (2^{k+1}) g` from §6, not against the reference's `Φ`.
