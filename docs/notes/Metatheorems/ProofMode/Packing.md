# ProofMode/Packing.lean

## module header

### Deviation from the handoff, deliberate

The handoff specifies `pack Δ B := Δ.foldr (· →ᶠ ·) B`, under which the *head* of `Δ` is
the *outermost* antecedent. With that convention `Seq (A :: Δ) B` and `Seq Δ (A →ᶠ B)`
differ by a permutation of antecedents, so `intro` and `revert` each cost an exchange
lemma — contradicting the handoff's own "they are the identity".

Folding the other way — the head of `Δ` is the *innermost* antecedent, i.e. the most
recently introduced hypothesis — makes

    Seq (A :: Δ) B   and   Seq Δ (A →ᶠ B)

*definitionally equal*, so `seq_intro` and `seq_revert` really are `id`. That also makes
`HVar` indexing agree with the usual de Bruijn convention (index 0 = most recent). The
display layer reverses `Δ` for presentation; nothing else is affected.
