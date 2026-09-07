# The proof mode — tactic reference

The kernel of this development is `Derivable F allowed Premises A`, a Hilbert-style inductive
with no notion of a hypothesis context: `A →ᶠ B →ᶠ C` is one formula, and there is no deduction
theorem to appeal to. The proof mode supplies the missing bookkeeping.

`Seq Δ B` is *definitionally* `Derivable F a Premises (pack Δ B)`, where `pack` is the chain of
`→ᶠ`s; `SeqD ns F a Premises Δ B` is a `@[reducible]` wrapper that additionally carries a list
of display names for the hypotheses. So a sequent **is** a derivation, the names are display
data, and there is nothing to trust in the tactic layer: a bug in a tactic can only fail to
elaborate. Every tactic emits a `refine` against a lemma proved in `ProofMode/Tactics.lean`,
which is built from `ProofMode/Packing.lean`, which is built from `Derivable`.

Tactics are prefixed `p` throughout, to keep them clear of Lean's own `intro`, `cases`, ….

**How to read this file.** Each entry gives the syntax, what it does, and the file it is
defined in. Where a docstring in the source says more, it says so.

---

## Contents

1. [Entering and leaving the mode](#1-entering-and-leaving-the-mode)
2. [Closing a goal](#2-closing-a-goal)
3. [Implication and forward reasoning](#3-implication-and-forward-reasoning)
4. [Conjunction, disjunction, falsity](#4-conjunction-disjunction-falsity)
5. [Quantifiers](#5-quantifiers)
6. [Equational reasoning](#6-equational-reasoning)
7. [Rewriting — `prw` and `prwby`](#7-rewriting--prw-and-prwby)
8. [Induction](#8-induction)
9. [Context surgery](#9-context-surgery)
10. [Classical and semi-classical principles](#10-classical-and-semi-classical-principles)
11. [Normalisation](#11-normalisation-anorm-qnorm-pnorm)
12. [Notation](#12-notation)
13. [Rendering a derivation — `#hilbert`](#13-rendering-a-derivation--hilbert)
14. [Things that trip people up](#14-things-that-trip-people-up)

---

## 1. Entering and leaving the mode

| tactic | effect |
|---|---|
| `pmode` | Enter the mode from a kernel goal `Derivable … A`, giving the sequent `⊢ A` with an empty hypothesis context. Free — `Seq` is definitionally `Derivable`. |
| `pin_system h` | Prove the goal in a weaker system, justified by `h : Allowed.le a' a`. |

A theorem is *stated* as an ordinary `Derivable` and *proved* as a script:

```lean
def add_comm (x : Term F Γ Ty.nat) :
    Derivable F al Premises (Formula.all Ty.nat (Formula.eq0 (x +ᵗ x₀) (x₀ +ᵗ x))) := by
  pmode
  pinduction
  …
```

Leaving the mode is not a tactic: when the last goal closes, the term produced *is* the
`Derivable` value. `pthm` and `papply` are the doors in the other direction — they let a script
consume an existing kernel theorem.

*(`ProofMode/Tactics.lean`.)*

## 2. Closing a goal

| tactic | effect |
|---|---|
| `pexact h` | Close the goal with the hypothesis named `h`. |
| `passumption` | Close the goal with whichever hypothesis matches; tries each in turn. |
| `pthm e` | Close the goal with a kernel theorem `e`. The theorem is elaborated *in the goal's context*, so it may mention `x₀` and friends. |
| `pcontradiction h` | Finish from `h : ⊥ᶠ`. (`pexfalso; pexact h`.) |
| `pfail "…"` | Fail with exactly this message and no goal state appended. Useful inside tactic combinators. |
| `pside` | Discharge a side condition (`allowed` flags, `isQF`, `isVFree`): `rfl`, then `assumption`, then `decide`. Rules leave these as named holes rather than `(by …)` arguments, because at the time such an argument would be elaborated the matrix is still a metavariable. |

`pexact` is the only tactic in the file that inspects the goal, and it does so only to turn a
*name* into the de Bruijn index that `HVar` wants.

*(`ProofMode/Tactics.lean`.)*

## 3. Implication and forward reasoning

| tactic | effect |
|---|---|
| `pintro h k …` | Introduce implications, naming each new hypothesis. |
| `papply h` | `h` an implicational hypothesis: use it, leaving its antecedents as goals in order. |
| `papply e` | `e` a kernel theorem: same, applied to the goal. Anything that is not a bare hypothesis name is elaborated as a theorem. |
| `papplym e` | Old name for `papply e`; kept so that existing scripts do not change. |
| `papply h in k with m` | Forward: apply the implicational hypothesis `h` to the hypothesis `k`, adding the conclusion as `m`. |
| `papplym e in h with k` | Forward with a kernel theorem. |
| `pdestruct_imp h with k` | Use an implicational hypothesis in two goals: prove its antecedent in the first, continue with its conclusion named `k` in the second. |
| `phave h : A` | Prove `A` in a side goal and keep it as the hypothesis `h`. The formula is user-written, so the surface-recursor ban applies to the terms in it. |
| `pfrom h := e` | Add the kernel theorem `e` to the context under the name `h`. |
| `prevert` / `prevert h` | Move the most recent (or a named) hypothesis back into the goal. A named one is walked to the top by adjacent exchanges first. |

`papply` is worth knowing in detail. The theorem is elaborated **once**, with the goal's `Γ`
pinned but its formula left as a metavariable, and its conclusion is then unified with the goal
in the live metavariable context. Consequences:

* Implicit arguments and `_` placeholders are read off the goal, so
  `papply succ_congr_imp` needs no `(s := …) (t := …)`, and `papply (lt_Q_add_both _ _ _ _)`
  determines all four terms from the goal.
* A placeholder the conclusion does not determine becomes a trailing goal, as with Lean's
  `apply`.
* The conclusion is matched at **reducible** transparency first and at default only as a
  fallback, so a goal containing `Term.cauchyfy` is matched structurally rather than by
  unfolding it. Set `-D pm.papply.trace=true` to log which route and which transparency each
  call site took.

*(`ProofMode/Tactics.lean`.)*

## 4. Conjunction, disjunction, falsity

| tactic | effect |
|---|---|
| `psplit` | Split a conjunctive goal into two. |
| `pand_left` / `pand_right` | Weaken the goal to a conjunction containing it; the other conjunct is left as a metavariable for whatever closes the branch. |
| `pdestruct h with x y` | Split the conjunction proved by `h` into two named hypotheses. |
| `pconj h k with m` | Conjoin two hypotheses into one, named `m`. |
| `pleft` / `pright` | Choose a disjunct of a disjunctive goal. |
| `pcases h with hl \| hr` | Case analysis on the disjunction proved by `h`, naming the hypothesis in each branch. |
| `pexfalso` | Replace the goal by `⊥ᶠ`. |

*(`ProofMode/Tactics.lean`.)*

## 5. Quantifiers

| tactic | effect |
|---|---|
| `pforall` | Introduce a `∀`. The whole hypothesis context weakens; the display names do not change. |
| `pspecialize` | Instantiate a weakened `∀`-**goal** at the bound variable. |
| `pspecialize h with k` | Instantiate a weakened `∀`-**hypothesis** at the bound variable, naming the result `k`. This is how a `∀`-hypothesis is used after `pforall`. |
| `pinst h t with k` | Instantiate the `∀`-hypothesis `h` at the term `t`, naming the result `k`. `t` is a surface term, so the recursor ban applies. |
| `pexists t` | Supply the witness `t` for an `∃` goal, subject to the surface-recursor ban. |
| `pexists! t` | The same **without** the ban. The escape hatch is deliberately a distinct, greppable spelling; using it at a headline `∃` invalidates the extraction claim. |
| `pbound t` | Supply a witness at a *headline* `∃`. Behaves like `pexists`; it records at the call site that this is the position the metatheorem's bound occupies. |
| `pobtain h with x` | Consume the `∃` proved by `h`, naming the body `x`. |
| `pqfac h with k` | Apply quantifier-free choice to the `∀∃`-hypothesis `h`, naming the resulting choice-function statement `k`. |

The **surface-recursor ban** (`ProofMode/Linter.lean`) refuses a user-written term that applies
the primitive recursor `Term.prec` directly, at `pexists`, `pbound`, `pinst`, `ptrans` and
`phave`. The reason: iteration is what extraction is supposed to *produce*, so writing the
iteration by hand makes the extraction vacuous. Using a named constant that happens to be
defined by `prec` is fine; applying the recursor in the surface syntax is not.

*(`ProofMode/Tactics.lean`.)*

## 6. Equational reasoning

| tactic | effect |
|---|---|
| `prefl` | Reflexivity of `=₀`. |
| `psym` | Symmetry, on the goal. |
| `psym in h with k` | Flip the equational hypothesis `h`, keeping the flipped form as `k`. |
| `ptrans t` | Transitivity as a *step*: name the midpoint `t` and get the two halves as goals — a `calc` step. `t` is a surface term, so the recursor ban applies. |

*(`ProofMode/Tactics.lean`.)*

## 7. Rewriting — `prw` and `prwby`

There is no general `rw` for the object logic, and there cannot be one: the system is *weakly*
extensional, so equals may not be substituted for equals inside an arbitrary formula. What
there is instead is **QF-ER**:

> from `s =₀ t` conclude `r[s] =₀ r[t]`, for any term abstraction `r`

— congruence for *terms*, which is all an equational rewrite needs. Both tactics are built on
that: given the goal's side `L` and the pattern `s`, one traversal produces the abstraction `r`
(occurrences of `s` replaced by the bound variable, every other leaf weakened) and the rewritten
side at once.

| tactic | effect |
|---|---|
| `prw e` | Rewrite the goal with the **closed equation** `e : s =₀ t`, on both sides, the way `rw` does. Available in **any** hypothesis context, since a closed equation needs no premise. |
| `prw e at n` | Rewrite only the `n`-th occurrence, numbered from 1, left to right **across the whole goal**. |
| `prwby h` | Rewrite the goal with the **hypothesis** `h : s =₀ t`. |
| `prwby h at n` | The same, at one occurrence. |
| `prw e in h with k` | Rewrite *inside* the equational hypothesis `h`, naming the result `k`. |
| `prwby h in k with m` | Rewrite inside hypothesis `k` using the equation `h`, naming the result `m`. |
| `prw_norm` | The `simp only` that normalises the `subst0` round-trips the two tactics generate. Theory-independent; the only non-structural step is undoing a weakening. You rarely call it directly. |

The split between the two is forced, not stylistic. Rewriting by a closed equation goes through
`qfer_no_premise`. Rewriting by a hypothesis needs the premise form of QF-ER, whose premise must
be quantifier-free and ∨-free — but the premise is the *equation itself*, not the hypothesis
context, so the surrounding context may contain anything at all, including a non-quantifier-free
induction hypothesis.

A worked example, the object-level `x + y = y + x`, which reads like the textbook proof:

```lean
pmode
pinduction
· anorm                       -- x + 0 = 0 + x
  prw (add_zero_r x)
  prw (add_zero_l x)
  prefl
· pforall
  pintro ih
  anorm                       -- x + Sy = S(x + y) = S(y + x) = Sy + x
  prw (add_succ _ _)
  prw (add_succ_l _ _)
  prwby ih
  prefl
```

**Two restrictions to know before reaching for these.** See
[§14](#14-things-that-trip-people-up) — they are the two most common causes of a confusing
failure.

*(`ProofMode/Rewrite.lean`.)*

## 8. Induction

| tactic | effect |
|---|---|
| `pinduction` | Induction on `ℕ`, base case first, then the step. The hypothesis context is carried through: the underlying `seq_induction` strengthens the induction formula by the context, so the induction hypothesis is available *together with* everything already assumed. |

The goals `pinduction` leaves carry substitutions (`A.subst0 0`, and `∀n (A → A[Sn])`), which
have to be normalised before they are recognisable — that is what `anorm` is for, and why it
appears immediately after `pinduction` in every script above.

*(`ProofMode/Tactics.lean`, `ProofMode/Induction.lean`.)*

## 9. Context surgery

| tactic | effect |
|---|---|
| `pclear h` | Drop a hypothesis, wherever it sits in the context. |
| `pswap h with k` | Exchange two **adjacent** hypotheses. Non-adjacent exchanges compose from these; the primitive rule is the adjacent one. |
| `prename h into k` | Rename a hypothesis. Names are display data, so this proves nothing — it is the identity. |
| `prevert` / `prevert h` | See [§3](#3-implication-and-forward-reasoning). |

*(`ProofMode/Tactics.lean`.)*

## 10. Classical and semi-classical principles

Each is refused — **before** anything is applied to the goal — if the corresponding `Allowed`
flag is not set, or if the goal is not of the right shape.

| tactic | effect | requires |
|---|---|---|
| `pclassic A with h k` | Case split on `A ∨ᶠ ¬ᶠA`, naming the hypothesis in each branch. | `allowed.lem` |
| `pby_contra h` | Prove an `∃` over a quantifier-free, ∨-free matrix by contradiction: the goal becomes `⊥ᶠ` with `h` the negated `∃`. This *is* Markov's rule. | `allowed.markov`, and the matrix `isQF` and `isVFree` |
| `pqfac h with k` | Quantifier-free choice; see [§5](#5-quantifiers). | `allowed.qfac`, and the matrix `isQF` and `isVFree` |

`pby_contra`'s refusal messages ask "is this proof translated?" on purpose. A hand-translated
classical proof's classical content is exactly `¬¬∃n(qf) → ∃n(qf)`, so a goal of the wrong
shape means the translation has not been done.

Note that a case split on a *quantifier-free* formula does **not** need any of this:
`Arithmetic.qf_lem` derives `A ∨ᶠ ¬ᶠA` for quantifier-free `A` from the base system, with no
`Derivable.lem` at all.

*(`ProofMode/Tactics.lean`.)*

## 11. Normalisation — `anorm`, `qnorm`, `pnorm`

De Bruijn substitution bookkeeping is what a proof-mode script actually spends its lines on.
Three normalisers handle it.

| tactic | when |
|---|---|
| `anorm` | After `pinduction` and after `pinst`. Normalises the `subst0`/`substF` composites those leave, with the same rewrite set the hand-written proofs in `Arithmetic.lean` spell out one `_nf` lemma at a time. |
| `anorm_ren` | After `pspecialize`. Instantiating a weakened `∀` at the bound variable performs no substitution, only a weakening under a binder; one extra rewrite brings that into the same normal form and then `anorm` finishes. |
| `anorm_cons` | The `Term.Subst.cons` step alone; `anorm` runs it before and after its main pass. Rarely called directly. |
| `qnorm` / `qnorm [h₁, h₂]` | The substitution-normalising `simp only` for goals over the ℚ/ℝ constants: push `subst`/`subst0` through the application spine and leave the closed constants alone, with the `closed_subst` simp set folded in so the goal need not name any constant. The bracketed form adds lemmas at the front — in practice the local `let` abbreviations a goal is stated in terms of. Defined in `Arithmetic.lean`, not in `ProofMode/`. |
| `pnorm` | Clears the bookkeeping left when a weakening meets a substitution — most often after supplying a just-obtained witness back to an `∃`. |

**`anorm` and `anorm_ren` are not confluent against each other and must be chosen by hand.**
Turning a renaming into a `Subst.cons` *before* an enclosing `subst0` has absorbed it produces a
substitution-after-substitution, which is outside the vocabulary the rewrite set knows. Use
`anorm_ren` only when the renaming stands alone.

*(`ProofMode/Arith.lean`; `qnorm` in `Metatheorems/Arithmetic.lean`.)*

## 12. Notation

The mode prints and parses object-level syntax, so a term can be copied out of a goal and
pasted into a script.

| notation | means | defined in |
|---|---|---|
| `x₀ … x₅` | the de Bruijn variable at that position, resolved against the goal's context — these **parse as well as print** | `ProofMode/Pretty.lean` |
| `f ⬝ a` | object-level application, `Term.app f a` | `ProofMode/Pretty.lean` |
| `∀ᶠ x : ρ, A`, `∃ᶠ x : ρ, A`, `λᶠ x : ρ, t`, `R[t]` | object quantifiers, abstraction, recursor | `ProofMode/Pretty.lean` |
| `a +ᵗ b`, `a *ᵗ b`, `a ∸ᵗ b`, `S t`, `pdᵗ t` | object arithmetic | `ProofMode/Arith.lean` |
| `→ᶠ ∧ᶠ ∨ᶠ ¬ᶠ ↔ᶠ ⊥ᶠ`, `→ₜ` | formula connectives and the type arrow | `Language.lean`, `TypeSystem.lean` |
| `s =₀ t` for `Formula.eq0 s t` | scoped, so it needs the `Pretty` namespace open | `ProofMode/Pretty.lean` |

The goal itself is displayed as a named-hypothesis box by a delaborator on `SeqD`
(`ProofMode/Display.lean`).

Note that `ProofMode/Arith.lean` declares `S` and `+ᵗ` as *global* notation, so importing it
below the ℝ layer breaks unrelated files that bind `S` themselves.

## 13. Rendering a derivation — `#hilbert`

`Metatheorems/Hilbert.lean` provides a command that turns any `Derivable` value into a numbered
Hilbert-style derivation, written to Markdown and LaTeX.

```
#hilbert foo
#hilbert foo all
#hilbert foo unfolding g h
#hilbert foo keeping g
#hilbert foo depth 2
#hilbert foo to "out/foo"
```

* bare — cite every non-constructor by name;
* `all` — expand everything outside the proof-mode layer;
* `unfolding g h` — expand just `g` and `h`;
* `depth n` — expand the proof-mode layer `n` levels deep, citing it below that;
* `keeping g` — never expand `g`, whatever the rest says; `keeping` wins over `unfolding`, over
  `all` and over `depth`;
* `to "path"` — output base name, with no extension: both `.md` and `.tex` are written. The
  default is `hilbert-out/<qualified_name>`.

The modifiers are independent and compose. `Hilbert.lean` is not imported by the umbrella; see
`Probes/HilbertDemo.lean` for a worked use.

## 14. Things that trip people up

**`prw` finds its pattern by descending application spines only.** It walks `Term.app`,
`Term.app2` and `Term.app3` and nothing else, so a **named wrapper hides its contents from the
rewrite**: if a formula is stated through an abbreviation, `prw` reports "the pattern does not
occur" even though it plainly does. Spell the formula out where `prw` must see inside it. (The
same is true of `pinduction` against a named `Formula` definition — `simp only` will not unfold
a `def`.)

**`prw` needs its pattern present at that moment, so scripts are order-sensitive.** Fire the
rewrite that *creates* a subterm before the one that consumes it. The error message prints both
the pattern and the goal, so this is cheap to diagnose.

**`prwby` cannot work at an arrow pattern type; `prw` can.** `prwby` discharges QF-ER's
`A₀.isQF = true` side condition by `rfl`, and `eqAtType` at an arrow type is a `∀`, so the check
fails by construction. This is not a limitation that will be lifted. `prw` at pattern type
`nat →ₜ nat` does work.

**The mode *is* the deduction theorem — use it instead of hand-rolling QF-ER.** To apply a
congruence under a hypothesis, the move is

```lean
pmode; pintro h; prwby h; prefl
```

and not a hand-written `s =₀ t →ᶠ r[s] =₀ r[t]` twin composed with `.syllogism`. Before
hand-rolling any QF-ER application, check `ProofMode/Rewrite.lean` for a tactic that already
emits it.

**A proof-mode tactic bug never shows up as unsoundness.** `Seq` and `SeqD` are definitionally
`Derivable`, so a bug can only produce a confusing error about the goal or about an identifier.
When an error blames something that is plainly in scope, suspect the tactic layer and reproduce
with a control — the same term, differently bound — before working around it.

**Several failures are caused by a term difference the pretty-printer conceals**, so that the
two sides print identically and the error blames something else. Suspect this whenever a
`pexact` or `papply` on an obviously correct hypothesis fails, and especially when it fails as a
*heartbeat timeout* rather than as a type error — unification on two stuck terms containing
`Term.cauchyfy` exhausts the budget instead of reporting a mismatch. Known members of the
family: an `mdata` node left by a plain `have` (fixed in the tactics, but the symptom "the goal
is not a proof-mode sequent" is the tell); a `Formula.weakenBy` introduced by `pobtain`, visible
only under `pp.explicit`; and a folded `Term.weaken` around an application spine, which the `⬝`
notation prints straight through. Never work around any of these by raising `maxHeartbeats` —
the limit is what surfaces the bug.

---

## Where the rest is written down

* `Metatheorems/ProofMode/LADDER.md` — how the mode was built, rung by rung, what each step
  forced, and the two known debts (`Term.Subst.cons` is a deliberately partial substitution
  normal form; `anorm` and `anorm_ren` are non-confluent).
* `Metatheorems/ProofMode/PARITY.md` — the tactic set compared with the matching-logic proof
  mode it is modelled on.
* `Metatheorems/ProofMode/Examples.lean`, `ProofMode/Arith.lean` (namespace `ByScript`) — small
  scripts next to the raw-constructor proofs of the same statements.
* `Metatheorems/ProofMode/MCT.lean`, `MCTLazy.lean`, `RealMCT.lean` — the large scripts.
