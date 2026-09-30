# Dialectica/MonotoneNDLeaves.lean

## module header

The fused recursion `monotone_nd_soundness` (`MonotoneND.lean`) applies a handful of closed
propositional combinators at every node of a classical derivation. On a representative
derivation (`LemBoundDemo.lFinalNoLem` prenexified, 363 constructors) the profile is: 134 `syllogism`
(each `neg_neg_mp` ×2, `K_comb`, `S_comb`, `neg_neg_imp_rev2`), 34 `exportation`, 30
`importation`, 11 `forall_rule` (each `neg_neg_mp`, `dnn_intro` ×2, `neg_neg_imp_rev`), 4
`expansion`, 2 `lem`, plus ~120 propositional axioms each wrapped in `dnn_intro`. Realizing
those combinators as leaves — `ofSRealizer ∘ syntactic_soundness`, i.e. the TERM route on a
fixed ~100-node Hilbert derivation, several times per node — is what made the classical
bound's kernel reduction a 12 GB `std::bad_alloc`. This module replaces them.

Each combinator is an `MRealizer cm <its formula>` whose **data** is an explicit λ-term at
the hat types and whose existential **realizer** is the same λ-term at the witness types —
written once, polymorphically in the four Lean types `WA CA WB CB` (`Ty.interpret` of a `wTy`
is definitionally the product/function type the clauses of `wTy` say), so the two coincide
syntactically and the majorization proof is purely structural. `maj_auto` below discharges
those: a *syntactic dispatcher* on the goal (`Prod.mk` → `prod_intro`, projection →
`prod_fst/snd`, `fun` → `arrow_intro` + intro, application → `app_compat`, `()` → `unit_maj`,
`maxT` → `maxT_selfMaj`), no search, no `isDefEq` beyond `assumption` at the leaves. The
`if`-realizers (`nnImpRevF`, `dnnLemF`) are the two combinators whose Hilbert proof uses a
hypothesis twice (contraction): the realizer branches on the decidable matrix, the majorant is
the `maxT` of the two branches — `MRealizer.andContract`'s pattern.

## `MRealizer.nnMpF`

The data is `nnMpFun`'s body written out as
a literal lambda: checked against the expected `Ty.interpret X (wTy …)` binder by binder, where
ascribing the polymorphic constant forces one wholesale defeq of two large types that, with
`A B` free (no `whnf` cache), re-unfolds `wTy`'s duplicated subterms exponentially.
