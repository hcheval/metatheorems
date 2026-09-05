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

## Past the ladder — A3, the lazy proof

`Metatheorems/ProofMode/MCTLazy.lean`. `mct_p1` derives the *same* `mctStatement` the way one
proves it on paper: assume no flat window, conclude the value drops strictly at every point,
iterate to fit `K + 1` drops under `a 0 ≤ K`, contradiction. `#print axioms` clean.

The reductio is applied **only** to the headline `∃n (a n =₀ a (n + g n))`, whose matrix is QF
and ∨-free — so its classical content is exactly `¬¬∃n(qf) → ∃n(qf)`, and `pby_contra`, which
refuses any other shape, is what enforces that. Nothing else in the proof is classical;
`Allowed.extended` has `lem := false` and the derivation lives there. That is D-1's
hand-translation, and the tactic's refusal message is the discipline made mechanical.

Three more arithmetic facts, all short inductions, and all wanted by *this* proof rather than
p₂: `succ_monus_self` (`S x ∸ x = 1`, the contradiction it bottoms out in), `monus_add_self_l`
(`y ≤ x + y`), `add_monus_add` (`≤` survives a common addend).

**The divergence, stated carefully.** p₁'s descent `∀k ∃m (a m + k ≤ a 0)` is an induction
whose *witness* is built by applying `m ↦ m + g m` once per step — the node where
`g`-iteration is manufactured. p₂'s induction carries no existential in its conclusion; its
`∃` is discharged inside each branch. That is a structural difference in the two derivation
trees, and it is what A5's tracer is meant to display. What is **not** established here is
that the extracted *terms* differ: that is a computation, and it needs a concrete
interpretation to run in. Both extractions exist and typecheck; comparing them is A4's
remaining half.

**What A3 forced.** One fix, and it was a regression I had introduced: `pthm` was pinning the
goal's formula *before* trying an open elaboration, and on a statement this size that
unification diverges — a stack overflow, not a timeout. The order is now the other way round,
so the pinning is a fallback that only runs when the open attempt fails. It still buys what it
was added for (`qf_lem rfl` in `MCT.lean` has a formula to check against) and no longer costs
anything on large goals.

Also worth recording: `mct_extract_p1` needs its result type **written out**. Inferring it
means normalising the Dialectica interpretation of the whole derivation, and p₁'s is large
enough that the elaborator does not get there. Stating the type is the fix; raising
`maxHeartbeats` is not.

## Rung 8 — unified apply (2026-09-05)

Not a proof; a tactic. `papply h` and `papplym e` were two elabs sharing one defect: each
elaborated the rule, counted its antecedents by walking `Formula.imp` with `whnfD` +
`isDefEq` **inside `withoutModifyingState`**, threw the assignments away, and then handed
the user's *syntax* back to `refine pm_mp (pm_have $eStx) ?_` to be elaborated and unified a
second time. Now there is one `papply term`: a bare identifier that names a hypothesis is
the hypothesis, anything else is a kernel theorem; `papplym e` is a macro for `papply e`;
the two forward forms `papply h in k with m` / `papplym e in h with k` and `pthm` are
untouched.

**As implemented.** The theorem is elaborated once by `elabRuleInCtx`, *open* — `Γ` pinned,
the formula a metavariable, exactly `pthm`'s first attempt; pinning first is what diverged
on `mct_p1` (above). Only if that fails is it retried against the goal's formula behind
0, 1, 2, 3 antecedent placeholders (the `rfl`-side-condition case). The conclusion is then
unified with the goal in the live metavariable context — `withReducible` first, default
transparency as the fallback — peeling one arrow per failure (arrows exposed as written,
then by `whnfR`, then by `whnfD`). The `pm_mp` chain is built as an `Expr` with the goal's
`ι κ F a Premises Γ ns Δ` read off the `SeqD` application and the antecedents as
synthetic-opaque goals; no `exprToSyntax`, no second elaboration. A `_` the conclusion does
not determine is left as a trailing goal, as Lean's `apply` does, and is fixed by whatever
proves the antecedent mentioning it (`PapplyDemo.trans_midpoint`).

**What it bought, measured** (`Probes/PapplyDemo.lean`):

- The rung-6a spelling `papplym (succ_congr_imp (s := pdᵗ x₁) (t := x₀))` elaborates. Its
  recorded failure, `x₀: the context has 0 named variable(s)`, came from the *second*
  elaboration — the `refine` re-elaborated the raw syntax with no `Γ` pinned, so the tokens
  resolved against the outer context. The first, pinned elaboration had always succeeded.
- `papply (lt_Q_add_both _ _ _ _)` reads all four terms off the goal. Retrofitted at three
  sites in `RealNumbers/Cauchyfy.lean` (`add_R_check`: `le_lt_Q_trans`, `lt_Q_congr`,
  `lt_Q_add_both`), 47 lines of spelled-out terms removed for 9 added (three of them
  comments); `add_R_check` stays `[propext, Quot.sound]`. Note that `_` placeholders *also* worked under the old
  tactic — `refine`'s second unification found them — so the gain there is one elaboration
  instead of two, not new expressiveness; the named-argument-with-tokens case is the one that
  was genuinely closed.
- The error path no longer indexes `etyArgs`: the message is built from the inferred type's
  last argument. The panic in trap 12 was the pre-split 6-argument `Derivable` read at
  `[6]!`; after the split it was in bounds by coincidence, and the two ill-formed-argument
  probes already gave readable messages at `10104d9`.

**Transparency per site**, via `-D pm.papply.trace=true` on the seven measured files (93
applications traced; the forward forms and `pthm` are not traced): 72 matched at
**reducible**, 14 at **default**, 0 needed a pinned elaboration, 3 needed `whnfD` to expose
an arrow. Every default match is one of two shapes: a goal spelled out as
`eq0 (lt_Q_dec …) 0` against a rule concluding `lt_Q …` (`BaseEquality`, `LeOrder`,
`Cauchyfy` — the `prw`-must-see-inside convention forces the spelled-out form), or a
`weakenBy`/`¬ᶠ`-wrapped hypothesis (`MCTLazy`'s `N`, `snz1`; `Arith`'s `ihB`). Every goal
containing `Term.cauchyfy` matched at reducible, so the default fallback never walks into
the recursor on a successful match. On a *failing* match it still would — the fallback is
the old behaviour, not a fix for trap 12.

**Timings**, `lake env lean` per file, best of two, same 12 GB cap, another agent building
on the same 15 GB machine throughout:

| file | before | after | |
|---|---|---|---|
| `ProofMode/MCT.lean` | 6.43 s | 6.40 s | 0 theorem-path sites; all `papply … in` |
| `ProofMode/MCTLazy.lean` | 7.59 s | 8.50 s | **+12%**, see below |
| `ProofMode/Arith.lean` | 5.61 s | 5.52 s | |
| `BaseEquality.lean` | 2.96 s | 2.41 s | −19% |
| `RealNumbers/LeOrder.lean` | 3.18 s | 2.62 s | −18% |
| `RealNumbers/Cauchyfy.lean` (pre-retrofit source) | 4.61 s | 4.25 s | −8% |
| `RealNumbers/Cauchyfy.lean` (retrofitted) | — | 4.12 s | |

`MCTLazy` has exactly two changed sites (`papply N`, `papply snz1`, both hypotheses, one
antecedent), so a stable 0.9 s from the tactic is implausible; a controlled A/B — the same
file with the old elab inlined as `papply_old` at those two sites, six interleaved pairs in
the same build state — gave new **7.88 / 9.2 s** (min / median, one 20.5 s outlier) against
old **8.18 / 8.5 s**. The minimum favours the new tactic by 4%, the median disfavours it by
8%, and a run-to-run spread of 7.9–20.5 s on an unchanged file says the machine, not the
tactic, is what was measured. The per-site work is the old work plus one failing
`withReducible` `isDefEq` and one `whnfR` for the default-match sites; no fallback to the
old path was warranted on this evidence, and none was added. Re-time on a quiet machine
before reading the +12% as real.

**What was not done.** `papply … in k with m` and `papplym … in h with k` still go through
`refine`/`pexact` syntax, unchanged. The `?m.54` metavariables in the "does not conclude the
goal" message are the rule's undetermined implicits, printed as such. The 16-arrow cap on
the walk is inherited.

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

## Rough edges, deliberately left

Recorded rather than fixed. Everything below was hit while writing the proofs above, and none
of it blocks anything — but each cost a debugging round, so it should cost the next person
zero.

**`anorm` is hand-placed, and there are two of them.** Every `pinduction`, `pinst` and
`pexists` leaves substitution bookkeeping that the script has to clear by calling `anorm`
explicitly, and you have to know when `anorm_ren` is the one you want (see the non-confluence
above). That is not a bug, it is the tax the mode has not yet paid off: `anorm` generalises
the hand-written `_nf` lemmas of `Arithmetic.lean` rather than removing the need for them.

It got worse in proportion to proof size — MCT calls it about thirty times. The two ways out
are for each tactic to normalise its own output, or for `anorm`'s rewrite set to become
confluent enough to run as a closure. Both are design work, not patches, and the second
subsumes the `anorm`/`anorm_ren` split.

Two smaller ones. `anorm` errors with "simp made no progress" when there is nothing to
normalise, so a script cannot call it defensively — which is exactly what you want to do when
you do not know whether the previous move left a substitution behind. And it does not report
what it *failed* to normalise, so a stuck goal has to be read by eye.

**`⬝` takes both operands at `max` precedence.** It is declared

```lean
syntax:max term:max " ⬝ " term:max : term      -- Pretty.lean
```

so each side must be an *atom* or parenthesized — a Lean-level application on either side does
not fit, and the whole `⬝`-expression sits at `max` too, so it happily becomes the head of an
application instead:

```lean
(x₀ ⬝ (Term.ofNat 2)) ⬝ (Term.ofNat 0)      -- correct: parens at every step
x₀ ⬝ Term.ofNat 0                            -- parses as (x₀ ⬝ Term.ofNat) 0
```

The failure mode is a type error some distance from the real problem, because the mis-parse
still elaborates far enough to produce one. `mct_p2` and `mct_p1` both hit it. Declaring it at
an ordinary level — `infixl:70` — would let applications sit on either side unparenthesized,
but it touches every existing use, so it is left alone for now.

**`prw` does not descend every term former.** `scanTerm` walks `Term.app`, `app2` and `app3`.
Anything else — a `lam` body, and the pair formers if `syntactic-witnesses` ever lands — is
treated as a leaf, so a rewrite inside one silently finds nothing rather than failing. Not
unsoundness; a coverage gap that reads as "the rule did not match".
