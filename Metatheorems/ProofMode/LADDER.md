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
| 4 | monus transitivity: `x ∸ y = 0 → y ∸ z = 0 → x ∸ z = 0` | **case analysis inside an induction** — the first proof needing `pcases`/`pclassic` and a zero-or-successor split | — |
| 5 | the antitone chain: `∀i, a(m+i) ∸ a m = 0` | induction *with a premise in the context*, and a function parameter `a` rather than a variable | — |
| 6 | the strict-drop step | a negated hypothesis; the first use of `pby_contra` in anger | — |
| 7 | ℕ-MCT, proof p₂ (dichotomy) | the whole thing: `qf_lem` case split, budget descent as induction on `K`, a headline `∃` closed by `pbound` | — |

## What each rung is actually testing

Rungs 1–3 test *rewriting*, and they passed. Rung 3 in particular is the first proof that
does not end in `prefl`, so the mode has to hand off to a kernel theorem cleanly.

Rung 4 is the first real test of the **propositional** tactics inside an arithmetic proof —
so far `pcases`, `pclassic` and `pdestruct` have only been exercised on abstract `A`, `B`.
It is also the first proof whose *shape* is not "induct and rewrite".

Rung 5 is the first with a hypothesis that survives the induction, which is what the context
peeling in `Induction.lean` was built for and has only been unit-tested.

Rung 6 introduces negation, and rung 7 is the demo.

## The rule for the ladder

A rung is done when the script compiles with no `sorry` **and** mentions no internal
machinery: no `Term.weaken`, no `Var.vz`, no `(Γ := …)`, no `Formula.subst0`. Every rung so
far has forced a fix to make that true — rung 2 forced `prw` to pin the rule's context so a
rule could mention `x₀` and an outer term at once; rung 3 forced the closed-substitution
lemmas for `monus` and friends out of `RationalNumbers.lean` and into `Arithmetic.lean`
where `anorm` can reach them. That is the point of going slowly: each rung buys a fix that
the next one needs.
