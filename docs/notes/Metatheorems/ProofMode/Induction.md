# ProofMode/Induction.lean

## module header

Those two lemmas are the entire cost of the general rule, and they are the reason this is a
separate file from `Packing.lean`: everything there is pure combinator plumbing, whereas
this needs facts about de Bruijn substitution.

### Rule or axiom? Keep the rule. (Settled; do not reopen without new evidence.)

The two are interderivable, and `Derivable` could carry the axiom instead — you can even
derive the axiom from the rule with no kernel change, by inducting on
`A' n :≡ (A 0 ∧ᶠ ∀n(A n →ᶠ A (n+1))) →ᶠ A n`, i.e. the same context-strengthening as above but
paid **once**, at a closed statement schematic in `A`, rather than recursively over `Δ`. So the
paragraph above should not be read as an apology.

The reason to keep the rule is **extraction**, and it is Kohlenbach's own: he states the axiom
and then, for the soundness proof, says "let us use the equivalent induction rule". Realizing
the *axiom* means realizing an implication, whose Dialectica witness type has a second
component — a counter-transformer taking a counter for `∀n A n`, i.e. a pair `(n, counter)`,
back to a counter for the conjunction, which is the induction run backwards. The rule owes
none of that: its premises arrive as already-realized subderivations, not as antecedents. So
the axiom form would add work on the **counter side**, which is where composition's fan-out
lives and where extraction currently dies.

The one motivation that would have justified it is gone: `sInduction`'s Δ-generic obstacle
is a *term-route* problem, and under the monotone functional interpretation
it does not arise — `MRealizer.induction` is semantic, and a real `pinduction` derivation
extracts through it (`Probes/MonotoneMCT.lean`: `V(5) = 5`, `V(9) = 9`, `U = 0`, counter side
included). What remains open about induction is unaffected by rule-vs-axiom: `recMaj` iterates
value-many times without sharing, so a bound whose *value* is large is unreachable regardless
of packaging (`Probes/ContentExampleNat.lean`: `128` checks, `256` exhausts 12 GB).
