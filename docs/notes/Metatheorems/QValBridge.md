# QValBridge.lean

## module header

`QVal.lean` defines `qval : ℕ → ℚ`, the rational denoted by a code, and its header says
explicitly that it does **not** connect `qval` to `Term.interpret` of `Term.rat_num`,
`Term.lt_Q_dec`, … This file is that connection, bottom-up.

### Method

For each **closed** constant `C : Term F Γ (nat →ₜ … →ₜ nat)` we prove a *function-level*
lemma

    Term.interpret si (Term.C (F := F) (Γ := Δ)) env = <Lean mirror>

— not an application-level one. Three reasons:

* the constants are closed, so the statement is environment-independent and is proved once;
* each proof unfolds **exactly one** constant and cites the already-proved lemmas for the
  rest. Never compose two unfoldings in one `simp`: `Term.add_Q` is 1,945 nodes as written
  and 1,880,329 fully reduced, so a `simp` that unfolds two layers at once will blow
  heartbeats;
* they chain: a function-level lemma fires as a rewrite on the *head* of an application
  spine, at any context and any environment, which is what lets the next stratum up unfold
  one level and finish.

The template is `interpret_pd_fun` in `Dialectica/Syntactic.lean`.

### Mirrors

Every mirror is chosen to be `omega`-friendly (truncated subtraction, `%`, `min`) rather
than a Lean `if`, so that the arithmetic side conditions of the strata above are discharged
automatically.

## Section 5: division by two

**`Term.div2` is misnamed**: it computes the ceiling `⌈n/2⌉ = (n+1)/2`, not the
floor. Its own docstring claims the state is `pair(div2 k, isEven k)`, but the
step adds `snd` *before* flipping the parity flag, so `div2 1 = 1`. Nothing
downstream is wrong — `Term.rat_num` is `div2 (j + isOdd j)`, and that is
`⌈j/2⌉` on the nose either way, which is what the encoding wants — but the
mirror below states the ceiling, because that is what the term computes.

## Section 9: the payoff — object-level constants denote the right rationals

These are the first statements in the project relating `Term.interpret` of a
ℚ-constant to `qval`. They are exactly what `QVal.lean`'s header said it did
not do.

## Section 10: interpretation congruence for `eq_R` / `le_R_pu`

These were developed in `Probes/SoundnessProbe.lean` and are hoisted here (not
into `Semantics.lean`) so that the core semantics file does not have to import
the whole ℚ/ℝ term layer. The probe keeps its own copies; it is not built.

## `le_Q_dec`, needed by `le_R_pu` (section doc)

An earlier scope note said `le_Q_dec` was not needed. That was **wrong**: `le_R_pu` — the
formula `Derivable.dist_tri` asserts, and hence what `EqXInterp.dist_tri_holds` must discharge
— is built on `le_Q_dec`, not `lt_Q_dec`.
