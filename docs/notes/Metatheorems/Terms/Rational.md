# Terms/Rational.lean

## module header

The `Term`-level encoding of ℚ, split out of `RationalNumbers.lean` so that it sits **below**
`eqAtType` and `Derivable` in the import order. See `Metatheorems/Terms/Arith.lean` for why.

Only the definitions moved. Every proof about them — including the `closed_subst` lemmas,
which need `Subst` — stays in `RationalNumbers.lean`, above `Derivable`.

## `Term.div2`

**The name says `⌊n/2⌋`; that is wrong — this computes `⌈n/2⌉`.**
`QValBridge.rec_div2_state` proves the true invariant,
`state k = pairN ((k+1)/2) (1 - k%2)`. The step adds `snd` *before* flipping the
parity flag, so the values run 0,1,1,2,2,… — `div2 1 = 1`, while `⌊1/2⌋ = 0`.

Nothing downstream is affected. `rat_num = div2 (j + isOdd j)` is `⌈j/2⌉` for both
parities, which is what the encoding wants, and `div2_zero` / `div2_double` hold of floor
and ceiling alike. The name is kept only because renaming it would churn every use.
