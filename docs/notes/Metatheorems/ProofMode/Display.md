# ProofMode/Display.lean

## module header

### Where names live

`Seq` has no names — the packaging kit sees positions, and that is the right invariant for
it (`HVar` is a de Bruijn index). Names are display data, so they are carried by a separate
*reducible* wrapper:

    SeqD names F a Premises Δ B  :=  Seq F a Premises Δ B

Being `@[reducible]`, every kit lemma applies through it by unification: the tactic layer
never has to translate between the two. Its job is only to keep `names` in step with `Δ`
when it changes one, and `names` never affects the proof term.

### Rendering (the layout rule)

Hypotheses are listed most-recent-*last*, which is the reverse of `Δ`'s own order (`Δ`'s
head is the most recent, see `Packing.lean`). That reversal is the whole reason the display
layer exists: it is the one place where the de Bruijn convention should not leak.

## `SeqD`

Reducible, hence interchangeable with `Seq` for every purpose except printing.

## the box syntax

The hypothesis lines are a grouped repetition *inside* this rule rather than a syntax
category of their own: a category would be run through the term parenthesizer, which cannot
know that juxtaposed `h : A` lines are unambiguous and so brackets them.
