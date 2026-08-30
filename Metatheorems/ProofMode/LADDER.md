# Working up to a real proof

The tactic table in `PARITY.md` says the moves exist. It does not say the mode survives a
real derivation, and MCT is too big a jump from `add_comm` to learn anything from failing at.
So: a ladder, each rung a proof that is actually wanted, each one harder than the last in a
*named* way.

The rungs are not invented. From rung 4 on they are `HANDOFF.md` §3 A0 — the shared lemmas
both MCT derivations need — so climbing the ladder *is* the Track A work, done in the mode
instead of by hand.

| | proof | what is new | where |
|---|---|---|---|
| 1 | `add_comm` | one induction; rewriting by a closed rule and by the hypothesis | `Arith.lean` ✅ |
| 2 | `add_assoc` | three variables; a rule mentioning an outer term *and* the bound variable together | `Arith.lean` ✅ |
| 3 | `0 ∸ y = 0` | the first monus fact; a non-equational finish (`pthm pd_zero`) | `Arith.lean` ✅ |
| 4 | monus transitivity: `x ∸ y = 0 → y ∸ z = 0 → x ∸ z = 0` | **case analysis inside an induction**, and **rewriting inside hypotheses** | `Arith.lean` ✅ |
| 5 | the antitone chain: `∀i, a(m+i) ∸ a m = 0` | induction *with a premise in the context*, and a function parameter `a` rather than a variable | `Arith.lean` ✅ |
| 6a | `y ∸ x = 0 → ¬(x =₀ y) → S y ∸ x = 0` | strictness from `≤` plus `≠`; a new induction, rung-4 sized | `Arith.lean` ✅ |
| 6b | the strict-drop step | composition rather than proof: no induction of its own | `Arith.lean` ✅ |
| 7 | ℕ-MCT, proof p₂ (dichotomy) | the whole thing: `qf_lem` case split, budget descent as induction on `K`, a headline `∃` | `ProofMode/MCT.lean` ✅ |

## What each rung is actually testing

Rungs 1–3 test *rewriting*, and they passed. Rung 3 in particular is the first proof that
does not end in `prefl`, so the mode has to hand off to a kernel theorem cleanly.

Rung 4 is the first real test of the **propositional** tactics inside an arithmetic proof —
so far `pcases`, `pclassic` and `pdestruct` have only been exercised on abstract `A`, `B`.
It is also the first proof whose *shape* is not "induct and rewrite".

Rung 5 is the first with a hypothesis that survives the induction, which is what the context
peeling in `Induction.lean` was built for and has only been unit-tested.

Rung 6 introduces negation, and rung 7 is the demo.

## Rung 4, and what it forced

This is the first proof that is not "induct and rewrite", and the first that is *not* also in
`Arithmetic.lean` — it is `HANDOFF.md` §3 A0's first shared lemma, so it is Track A work.

Mid-proof the state reads as the mathematics, which is the whole point:

    ⟪Γ, x₀ : nat, x₁ : nat, x₂ : nat⟫
          ih : ↑ᶜ↑ᶜ(∀ᶠ x₃ : nat, ∀ᶠ x₄ : nat, x₀ ∸ᵗ x₃ =₀ 0 →ᶠ x₃ ∸ᵗ x₄ =₀ 0 →ᶠ x₀ ∸ᵗ x₄ =₀ 0)
          h1 : S x₀ ∸ᵗ x₁ =₀ 0
          h2 : x₁ ∸ᵗ x₂ =₀ 0
          hyn : x₁ =₀ 0 →ᶠ ⊥ᶠ
          ────────────────────
          S x₀ ∸ᵗ x₂ =₀ 0

The `y ≠ 0` branch needs `y = S(pd y)` **rewritten into `h1` and `h2`**, so `monus_succ_l` can
strip the successors and the induction hypothesis can apply. `prw`/`prwby` were goal-directed
only, so this forced `prw e in h with k` and `prwby h in k with m`.

That is not a gap in the object logic: the congruence QF-ER supplies is exactly what a
hypothesis rewrite needs, applied forwards. The hypothesis is threaded between the two
sides' congruences by transitivity. Worth noting the matching-logic proof mode does not have
this either — `mlRewrite`/`mlRewriteBy` are goal-directed there, and only
`mlApplyMeta … in "H"` and `mlSymmetry in "H"` act on hypotheses.

## Rung 5, and the sharp edge it exposed — now fixed

Done, and it uses rung 4 — the antitone chain is monus transitivity applied along the
sequence. It needed object-level *application* to be writable, so `f ⬝ a` now parses as well
as prints, and the weakening coercion had to chain, since a parameter used under two binders
needs two weakenings and a single-step instance does not compose on its own.

**The sharp edge.** Instantiating a **weakened** `∀`-hypothesis at a **compound** term left

    Term.subst (fun v => subst0_map t (ext shift (ext shift v))) a

which `anorm` could not finish. The composite is an *anonymous* function, so it matches none
of the named rewrite rules; it can still be pushed structurally down to the variables, where
it beta-reduces, but at an **opaque** leaf — a term parameter rather than a variable or a
constant — there is nothing to push into, and collapsing it needs `subst_id` under a `funext`,
which is not a rewrite. Rung 5 dodged it by putting the premise *inside* the quantifiers so it
is never weakened; that does not scale, and MCT fuses `a`, `g` and `K` into one parameter
instantiated at compound terms constantly.

**The fix — `Term.Subst.cons`.** Every composite that actually arises has one shape: *put `t`
at variable 0, rename the rest by `r`*. Name it (`Subst.lean`), and it is closed under the
compositions that occur, with `Renaming.comp` absorbing the tower of weakenings:

    subst_subst0_map_rename_ext :  (u.rename (ext r)).subst (subst0_map t) = u.subst (cons t r)
    subst_cons_rename_ext       :  (u.rename (ext r')).subst (cons t r)
                                     = u.subst (cons t (comp r r'))
    subst_cons_weaken           :  (u.weaken).subst (cons t r) = u.rename r      -- the leaf rule

The last is the point: because `cons` is a *named constructor* rather than a lambda, it fires
on an opaque `u`. Under binders the substitution becomes `Subst.ext (cons t r)`, where the
existing `weaken_subst_ext` already applies; the formula-level counterparts are in
`Language.lean`, and `anorm` runs the whole set as `anorm_cons` before and after its main pass.

This was the same wall the `q_norm` tactic in `RationalNumbers.lean` was built against.
`antitone_chain_premise_outside` is the regression test: rung 5 restated with the
premise outside the quantifiers, so `hmono` is weakened twice and then instantiated at
`m + i` over the opaque parameter `a`. It did not typecheck before; it does now.

If a shape shows up later that `cons` does not cover, that is the signal a full
sigma-calculus/autosubst layer is genuinely needed — and this is its first constructor, not
work thrown away.

## Rung 6, and what it forced

Both halves are done. 6a (`monus_succ_of_ne`) is rung 4's shape — split on whether `x` is
zero, kill the zero branch with `succ_ne_zero`, replace `x` by `S (pd x)` so `monus_succ_l`
strips a successor — with one thing new: the *disequality* has to be transported down to the
predecessor too. 6b (`strict_drop`) is the first rung that is composed rather than proved:
6a plus `monus_trans` plus one cancellation, no induction of its own.

**What 6a forced was a limit, not a fix.** Two spellings failed to elaborate:

    phave hne2 : ¬ᶠ(pdᵗ x₁ =₀ x₀)
    papplym (succ_congr_imp (s := pdᵗ x₁) (t := x₀))

both with `x₀: the context has only 0 named variable(s)`. The `xₖ` tokens read their de
Bruijn index off the context of the *expected type*, and in both of these the expected type
is still a metavariable when the argument is elaborated — a user-written formula handed to
`phave`, and an implicit argument supplied by name ahead of the `(Γ := …)` injection
`elabRuleInCtx` performs. Neither is hard to work around, and the proof reads better for it
(the disequality became a goal after `papply` rather than a `phave`, and the successor
congruence became two `prwby`s), but it is a real edge: **`xₖ` needs the context to be known
at the point the token is elaborated.** Worth fixing properly before rung 7 if it recurs —
`phave` already has the goal's `Γ` in hand and could pin it the way `elabRuleInCtx` does.

## Why rung 6 was split in two

The strict-drop step is "from `x ∸ (K+1) = 0`, `y ∸ x = 0` and `¬(x =₀ y)` conclude
`y ∸ K = 0`". Given `S y ∸ x = 0` the rest is two moves — `monus_trans` against
`x ∸ S K = 0`, then `monus_succ_l` — both already available.

But `S y ∸ x = 0`, that is *`y ≤ x` and `y ≠ x` give `y < x`*, is not in `Arithmetic.lean`
and does not follow from what is there. `monus_disjunct` on `(S y, x)` does not close it: the
branch `x ∸ S y = 0` is consistent with the premises (it is the case `x = S y`, where the
goal happens to hold anyway), so it needs its own induction, of about rung 4's size.

So rung 6 is two rungs. 6a is a genuinely new arithmetic fact and belongs in
`Arithmetic.lean`'s vocabulary whether or not it is proved as a script.

## Rung 7 — the demo

`Metatheorems/ProofMode/MCT.lean`. `mct_p2 : Derivable F EqX al Premises (Γ := []) mctStatement`,
`#print axioms` clean, and `mct_bound_p2` composes it with the extraction — so the hypothesis
`MCTStatement.lean` left open ("given a derivation of `mctStatement` …") is discharged.

The proof is the budget descent, by induction on `k`:

    A(k)  ≡  (∀u B₀ u)  →  ∀m (a m ≤ k → ∃n (a n = a (n + g n)))

At `k = 0` boundedness pins `a m = 0` and antitonicity pins `a (m + g m) = 0`, so `m` is
itself flat. At `k+1`, either the window at `m` is flat — take `n := m` — or it is not, and
then `a (m + g m) < a m ≤ k+1`, so the induction hypothesis applies at `m + g m`. The
statement follows at `k := K`, `m := 0`.

It is built from rungs 5, 6a and 6b exactly as `HANDOFF.md` §3 A0 predicted: `antitone_chain`
supplies `a (m + i) ≤ a m`, `strict_drop` turns "flat fails" into "the budget drops". A0 was
the claim that the shared lemmas make the second derivation cheap; the descent is ~50 lines of
script.

The proof is done over *three separate parameters* `a`, `g`, `K` and specialised to the fused
`h` only in `mct_p2`. Fusing is an encoding decision — one majorant covering all three — and
the mathematics does not need to know about it.

**What rung 7 forced.** Three fixes, all of them context-plumbing:

- **`phave` re-elaborated its formula** as a named argument to `pm_cut`, where `pm_cut`'s own
  `Γ` was still a metavariable. Now it elaborates once, against the goal's context, and hands
  the *expression* on. This was the rung-6a limit; it also fixed the `papplym` failure there,
  which turned out to be downstream of it.
- **`pfrom` did not pin the context** at all, so a lemma over an outer-context parameter could
  not be brought in under a binder. It now uses `elabRuleInCtx` like `pthm`, and the parameter
  weakens by coercion.
- **`xₖ` now postpones** instead of failing when the context is still unknown. Lean does not
  always propagate an expected type into an argument before elaborating it — `x₀ ⬝ t` is the
  case that bit, where `Term.app`'s context is fixed only once the whole application meets its
  expected type.

Plus one addition to the substitution vocabulary: `pspecialize` leaves a bare *renaming* under
a binder rather than a substitution, and a renaming under a binder is a `Subst.cons` too. One
rewrite (`anorm_ren`) brings it into the normal form. It is deliberately *not* part of `anorm`:
converting a renaming before an enclosing `subst0` has absorbed it produces a
substitution-after-substitution, which is outside the vocabulary — the one place where the
`cons` calculus is not confluent under naive rewriting, and worth knowing.

## The rule for the ladder

A rung is done when the script compiles with no `sorry` **and** mentions no internal
machinery: no `Term.weaken`, no `Var.vz`, no `(Γ := …)`, no `Formula.subst0`. Every rung so
far has forced a fix to make that true:

- **rung 2** forced `prw` to pin the rule's context, so a rule can mention `x₀` and a term
  from the outer context in the same argument list;
- **rung 3** forced the closed-substitution lemmas for `monus` and friends out of
  `RationalNumbers.lean` into `Arithmetic.lean`, where `anorm` can reach them;
- **rung 4** forced four. `prwby` no longer requires the hypothesis context to be a single
  quantifier-free formula — the congruence is a *closed* theorem applied to the hypothesis, so
  the rest of the context can be anything, an induction hypothesis included. `anorm` learned
  to step through `Subst.ext`, which is what a goal under *nested* binders is made of.
  `pthm` / `papplym` got the same context pinning `prw` has. And rewriting gained its
  hypothesis-directed form, `prw … in h with k`.

That is the point of going slowly: each rung buys a fix the next one needs, and none of these
would have surfaced from more abstract tests.
