# Dialectica/MonotoneND.lean

## module header

### Why a fused recursion, and the strategy per case

`negTrans_sound` (`NegTrans.lean`) is a derivation-to-derivation translation: at every node it
applies a fixed closed Hilbert combinator (`neg_neg_mp`, `neg_neg_imp_rev`, …, each ~50–200
constructors) and `dnn_intro`, so a 12-constructor classical derivation becomes 85,180
constructors and reducing `monotone_soundness` through that output is a 12 GB `std::bad_alloc`
in the kernel (measured in `Probes/ClassicalMfiProbe.lean`). The fix is to never build that
derivation: interpret the CLASSICAL derivation directly.

The recursion mirrors `negTrans_sound`'s match arm for arm. Per node:

* the **recursive calls** produce `MRealizer cm (subᴺᵀ)`;
* they are combined with the *composition* cases of `Dialectica/Monotone.lean` — `MRealizer.mp`,
  `.syllogism`, `.forallRule`, `.existRule`, `.univGen`, `.induction`, `.qfer` — which compute
  the majorant *semantically* and never build a term;
* the fixed `¬¬`-combinators `negTrans_sound` applies at every node — `dnn_intro`,
  `neg_neg_mp`, `neg_neg_imp_rev`, `neg_neg_imp_rev2`, `nn_all_nn`, the exportation /
  importation / expansion forms and `dnn_lem` — are **hand-written monotone realizers**
  (`Dialectica/MonotoneNDLeaves.lean`: `dnnIntroF`, `nnMpF`, `nnImpRevF`, `expF`, `impF`,
  `expansionF`, `dnnLemF`; `neg_neg_imp_rev2` and `K`/`S` are eliminated — `syllogism`
  composes `MRealizer.syllogism` with `dnnIntroF` and `nnImpRevF` — and `nn_all_nn` is
  assembled from them as `nnAllNnF`). Their majorants are hat-level λ-terms, so per node the
  kernel β-reduces a few small closures instead of running `termMajorizer` over a
  `syntactic_soundness` term of a 100–200-node Hilbert derivation several times per node —
  which is what the first version of this file did (`leafM` on every combinator) and what made
  the classical bound's kernel reduction a 12 GB `std::bad_alloc`: `prenexify`'s 347 nodes are
  134 `syllogism`s (5 leaves each), 34 exportations, 30 importations, 11 `forall_rule`s.
* **`leafM` (`ofSRealizer ∘ syntactic_soundness`, the term route on one closed derivation)
  survives only for**: the propositional axioms' own terms (`sAndWeak`, … — fixed tiny
  combinators, the same as `monotone_soundness` uses; wrapped in `dnnIntroF`), the
  `forall_ax`/`exist_ax` terms (`sForallAx t`/`sExistAx t` — one `lam` around `t`), and the
  cases NOT on the classical gate route: `succ_ne_zero`, `succ_inj`, the equational axioms
  (`rec_*`, `beta_eq`, `pair_*`), the pseudometric axioms, `qfac`, and the two
  `negTrans_iff_pu` legs of `qfer`. Those are left as leaves deliberately and are listed here
  so nobody mistakes them for hand-written ones.

### NT-stability is gone

`negTrans_sound` needs `nts : NTStableD Premises` — every premise must imply its own negative
translation — because its premise case is `.mp (.premise hp) (nts _ _ hp)`. Here the premise
case takes an `MRealizer cm Bᴺᵀ` **directly** (`spremise_nd`), so no condition on the premise
set is needed at all. For purely universal premises — every space axiom in the tree —
`spremise_nd_of_pu` supplies it from the existing syntactic premise realizer through
`negTrans_iff_pu` (interpreted as a leaf), so the space models need nothing new.

## `MRealizer.nnAllNnF`

— the object-level `nn_all_nn` is 274 constructors, almost all of them `neg_neg_imp_rev` and
`neg_neg_mp`.
