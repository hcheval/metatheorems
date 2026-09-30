# Dialectica/Monotone.lean

## module header

`monotone_soundness` computes, by recursion on a derivation, a **majorant of a Dialectica
realizer** as a semantic value at the hat type, with the realizer itself only existentially
quantified — the book's

    (+)  ∃x (t* maj x ∧ ∀a,y A_D(x a, y, a))

with `t*` the extracted datum and `x` a functional of the free variables `a`. The design and
the measurements behind it are in `ARCHITECTURE.md` §14 and `Probes/MonotoneSpike.lean`,
which first ran the recursion on nine constructors. This module completes it to every
constructor of `Derivable`, with no fallback.

### The statement (`MRealizer`)

`termMajorizer_maj`'s statement one level up, over the derivation:

* the majorant `tstar : ℕ → hat-env → hat-witness` is the data;
* `∃ x : env → 𝕎 A` — **hoisted outside the environment quantifier**, the book's `x a`
  exactly; the per-environment form is a corollary (`MRealizer.pointwise`) and is *not*
  closable at `forall_rule` (see the spike's header);
* `MajEnv` majorization of `x` by `tstar`, correctness of `x` at every counter, and
  self-majorization of `tstar` in its hat environment (what `arrow_intro`'s second clause
  needs).

### Strategy per constructor — the book's own division of labour (p. 142–144)

* **leaf** (Howard, p. 142) — `premise`, `or_weak`, `and_weak`, `and_perm`, `exfalso`,
  `forall_ax`, `exist_ax`, `succ_ne_zero`, `succ_inj`, `beta_eq`, `pair_fst/snd/eta`,
  `rec_zero`, `rec_succ`, `dist_self/comm/tri`, `refl0`, `sym0`, `trans0`, `markov`, `ip`,
  `ac`, `qfac`: `termMajorizer` of the axiom's own realizing term (`ofSRealizer`) — these
  are fixed-size combinators.
* **max** (p. 143, cases 1–3) — `and_contract`, `or_contract`, `or_perm`: `maxT` on the
  counter (resp. witness / flag); no matrix branching, no term.
* **composition, hand-written** (p. 144, cases 5–6) — `mp`, `syllogism`, `exportation`,
  `forall_rule`: the spike's, verbatim — the realizer's λ-term on the hat side, with
  `arrow_intro` discharged from the IH.
* **composition, via the usual λ-terms** (p. 144, case 6) — `importation`, `expansion`,
  `exist_rule`, `univ_gen`, `qfer`, `induction`: `termMajorizer` of the usual
  interpretation's combinator applied to a **variable** standing for the sub-realizer
  (`plug1`/`plug2`/`plugAll`); majorization is `termMajorizer_maj` with the sub-majorant in
  the environment.

The last row is the book's *"the monotone functional interpretation of the remaining
logical rules uses the λ-terms of the usual functional interpretation since they preserve
majorizability"* taken literally: the combinator is a fixed-size closed-shape `Term`, and
the sub-realizer enters it through `Ctx.lookupHat` of the environment, never as a term. So
the composed realizer term — the object whose `Term.weaken`/`Eq.rec` traffic stalled the
term route (`SizeProbe`) — is never built; only the per-node combinator is reduced, which is
the same cost class as the leaf cases.

**`induction`** is the book's `t^M` (p. 144 case 7): `termMajorizer` of `Term.prec` is
`cm.precM`, which in every instance in the tree is `recMaj` — the recursion with a running
`maxT`. It is obtained here by the last row, not by the leaf strategy on the whole
sub-derivation; the sub-realizers of base and step are variables. What it computes is `t^M`
already, so nothing has to be written by hand here — but note the practical ceiling this
carries: `recMaj` iterates *value*-many times without sharing, so a bound whose value is
large is expensive to reduce however small the derivation is (ARCHITECTURE §14.5).

## `MRealizer`

`cm` does not occur in the body: it is there to pin `am` (the relation the statement is about)
and because the leaf strategy reads its majorants — the same role it has in `termMajorizer`.

## `MRealizer.andContract`

This is the case that stalls the term route (`sAndContract`'s `matrixTerm`).
