# Derivable.lean

## module header

Equality at a base type is no longer a parameter: it is *defined*, as
`eqAtType (.base i) s t ≡ d_i(s,t) =ℝ 0ℝ`, with `Term.dist` structural and the three
pseudometric axioms as constructors. See `EqAtType.lean` and ARCHITECTURE.md.

## `Formula.weakenBy_eq_substF`

`Formula.weakenBy` is what `pm_exE` maps over the hypothesis context, so a hypothesis
obtained by an earlier `pobtain` carries it while the goal carries hand-written
`.weaken`s. The two are equal but not syntactically so; this is the rewrite that closes
the gap, together with `Term.subst_shift_eq_weaken` for the terms inside.

## `Derivable.premise`

No condition on `A` here. The kernel does not care what shape a premise has; only
`negTrans_sound` does, and it asks for it itself (as NT-stability, which is weaker than
purely-universal). This constructor used to carry
`A.isPurelyUniversal = true ∧ Premises ⟨_, A⟩`; of the five sites that matched on it,
exactly one read the first component.

## `Derivable.pair_fst` / `pair_snd` / `pair_eta`

Product β/η-equality, for the primitive `mkPair`/`fst`/`snd`. Same family as `beta_eq`: the
two sides have definitionally equal interpretations, so every pass over `Derivable` handles
them with the line `beta_eq` uses. Without them `fst (mkPair a b) =_ρ a` was underivable —
the wall the classical route's `∃u∃v` collapse and `Probes/ConjBoundDemo.lean`'s nested
existentials both hit. Written out in `classical_to_prenex_extended`'s docstring
(`MetatheoremPrereqs.lean`).

## `Derivable.dist_self` / `dist_comm` / `dist_tri`

These are what make equality at a base type — `eqAtType (.base i) s t`, i.e.
`d_i(s,t) =ℝ 0ℝ` — an equivalence relation, *derivably*. They are all Π⁰₁, so their
Dialectica witness types are singletons and their soundness cases are the trivial
realizer plus the model's `distInterp` being a pseudometric. Keeping them Π⁰₁ is the
point: assuming symmetry of `=_X` directly would be an implication between Π⁰₁
formulas, whose realizer carries a genuine ℕ → ℕ counter-transformer. See ARCHITECTURE.md.

## `Derivable.qfer`

The document's QF-ER only requires QF, not ∨-free. We add `isVFree` because our Dialectica
proof (`dialectica_qfer`) needs `Subsingleton` on the counter type, which requires ∨-free. To
remove `hvf`, the Dialectica proof would need to first encode `A₀` as `qf_term A₀ =₀ 0`
(which IS ∨-free) via `qf_term_correct`.

## `Derivable.qfac`

The document's QF-AC only requires QF. We add `isVFree` because the NT proof uses Markov
(which requires ∨-free). To remove `hvf`, one would derive a general Markov for QF via the
decision function (`qf_term_correct`).

## `AdmissibleEqX` — deleted; where each of its conditions went

The structure bundled five conditions on an abstract base-type equality: `substF_nat`,
`eqx_refl`/`eqx_sym`/`eqx_trans`, `eqx_pu`. It was threaded as `adm` through ~2,700 call
sites, and it is gone because `EqX` is gone.

Where each condition went:

* `eqx_pu`     — a theorem, `eqAtType_base_isPurelyUniversal` in `EqAtType.lean`. `eq_R`
                 is `∀n. QF` by construction, so this is `rfl`.
* `substF_nat` — a theorem, from `eq_R_substF` plus `dist` being closed under
                 substitution (`Term.dist i` has no subterms).
* `eqx_refl`   — `dist_self`, instantiated.
* `eqx_sym`    — `dist_comm` + symmetry/transitivity of `eq_R`.
* `eqx_trans`  — `dist_tri` + `add_eq_zero_R` + non-negativity of `d`, itself derivable
                 from `dist_self`/`dist_tri`/`dist_comm`.

The last three are ordinary theorems now, provable *above* `Derivable.lean` where the ℝ layer
lives. That is the whole point of the restructuring: they used to be record fields that
had to be supplied before the arithmetic that proves them could run. See ARCHITECTURE.md.
