# NegTrans.lean

## module header (comment on the `import Metatheorems.ProofMode.Tactics` line)

`negTrans_iff_imp_pu` below is proved as a proof-mode script. That is the only reason this
file depends on the tactic layer; `ProofMode.Tactics` sits over `PureFOLLemmas` only, so
the dependency is acyclic (`ProofMode.MCT` reaches `NegTrans` through `MCTStatement`, but
`ProofMode.Tactics` reaches nothing here).

## `nn_all_nn`

Proof: apply `forall_rule` with the derivation (in context ρ :: Γ):
  `(¬¬(∀x.¬¬Q)).weaken → ¬¬Q`
obtained via `forall_ax (.var .vz)` (using `substF_renameF_id` to simplify the
substituted formula to `¬¬Q`) composed with `neg_neg_imp_rev + neg_neg_mp`.

Public, rather than `private` as it once was: `classical_to_prenex_extended` uses it as step
3, pushing the outer `¬¬` of `NT(∀x A)` inside the `∀`. That is decision D-1 of
`ARCHITECTURE.md` §12, and the only place the prenexified route needs it.

## `negTrans_qfer`

Working notes that sat in the proof, after `let fwd := …`:

    step1 gives A₀ → result. fwd gives result → NT(result) = ¬¬result.kurodaInner.
    So: A₀ → ¬¬result.kurodaInner. Then dnn_intro: ¬¬(A₀ → result.kurodaInner).
    But we need A₀ → result.kurodaInner first, then wrap in ¬¬.
    Actually: A₀ → result → result.kurodaInner (via negTrans_iff_pu backward... no, forward gives result → ¬¬result.ki)
    Hmm. fwd : result → ¬¬result.ki. So A₀ → ¬¬result.ki. Then neg_neg_imp_rev2: ¬¬(A₀ → result.ki).
    NT(A₀ → result) = ¬¬(A₀.ki → result.ki) = ¬¬(A₀ → result.ki) (since A₀ is QF).
    NT(A₀ → result) = ¬¬(A₀.ki → result.ki) = ¬¬(A₀ → result.ki) since A₀ is QF
    fwd : result → NT(result) = ¬¬result.ki
    So: A₀ → result → ¬¬result.ki. By neg_neg_imp_rev2: ¬¬(A₀ → result.ki).

## `NTStable`

This is the condition `negTrans_sound` actually needs, and the *only* thing anything ever
needed `isPurelyUniversal` on `Derivable.premise` for. It is strictly weaker than "every
premise is purely universal" — `negTrans_iff_imp_pu` shows an implication between two PU
formulas is NT-stable while not itself being PU.

## `ntStable_of_pu`

A purely-universal premise set is NT-stable — the old hypothesis, recovered as a lemma
rather than baked into the kernel.

## `negTrans_sound` (the `premise` case)

Premises: NT-stability is exactly what this case needs, and it is now supplied by the
caller instead of being carried on the constructor.
