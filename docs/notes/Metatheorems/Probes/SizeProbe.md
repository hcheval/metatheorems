# Probes/SizeProbe.lean

## module header

## 1. Physical (pointer-identity) size of `#eval`-built realizers

Every earlier "too big" result measured a *tree* (`termSize`, `lTermSize`, `erase`) — a
recursive traversal that visits a shared node once per path to it, and so re-expands whatever
sharing the compiled evaluator preserved. CLAUDE.md's own measurement rule (Track A item 1)
bans exactly that. `visit` below memoises on the physical address (`ptrAddrUnsafe`), so it
cannot re-expand anything: the memo's size is the in-memory DAG node count, and the returned
`Nat` is the tree size, computed without expanding.

| realizer (via `extractTerm`) | dag | tree |
|---|---|---|
| `UPremiseDemo.uFinal` (calibration; `TermPrintDemo` says 533) | 533 | 533 |
| `ConjBoundDemo.tFinalOnce` — the reducing control | 413 | 413 |
| **`ConjBoundDemo.acFinal` — the one-`and_contract` `whnf` stall** | **2,529** | **2,529** |
| `LemBoundDemo.lUtExt` — the intuitionistic control | 302 | 302 |
| `LemBoundDemo.lUtNoLem` — the classical route, no LEM | OOM at 12 GB **while being built** | — |

Two findings.

**(a) `dag = tree`: the compiled evaluator preserves NO sharing** — predicted from the code
before measuring, and confirmed. `wtSyllogism` builds its result with `Term.weaken (.fst bc)`,
`Term.weaken (Term.weaken (.snd ab))`, …, and `Term.weaken` is a structural recursion that
*copies* its argument; so every combinator makes physically distinct copies of its
sub-realizers and the sharing is gone at every level. There is no free lunch from `#eval`'s
DAGs. Sharing would need weakening as an O(1) *node* (an explicit shift constructor), not a
copying function — a `Term` design change.

**(b) The stalling term is SMALL.** `acFinal`'s realizer — whose `U` bound is a kernel `whnf`
timeout (`ConjBoundDemo.acUt_at_5_9`) — is 2,529 nodes, smaller than `Term.add_Q` as written,
and builds instantly under `#eval`. So that stall was never the *size* of the extracted term.
The kernel is choking on the **reduction path** — running `Term.weaken`/`Term.rename` over
dependent indices with `Eq.rec` casts — to expose a term that is tiny. Routing the same bound
through `extractTerm` instead of `syntactic_soundness` (no `Subtype`, no `si`, no
`SRealizer.imp`) does not help: it times out identically, with `Eq.rec ↦ 16074`,
`Term.rec ↦ 2990`, `Term.rename ↦ 2566`, `Var.rec ↦ 1073`, `Term.Renaming.ext ↦ 882`,
`Term.subst ↦ 219`, `Term.weaken ↦ 95` — the kernel *executing the renamings*. That is the
cast/rename commutation debt of Track A item 1, now measured on a term whose final size is
known.

What this makes available: the number for `acFinal` is one metaprogram away. Build the
2,529-node term with `#eval`, reflect it as a literal `Term` expression (all `weaken`s already
executed, so the kernel never runs one), and the kernel checks `closedMajorizer cm lit x* = n`
cheaply on a literal. The remaining obligation `lit = extractUTerm (extractTerm sp acFinal)`
is exactly the expensive reduction and would carry compiler-level trust (as `native_decide`
does). A clean, stated trust boundary — kernel-checked majorant of a literal, compiler-checked
identity of the literal — rather than no number.

## 2. Where the classical route's size comes from: `negTrans_sound`, ≈230× per node

`derivSize` counts `Derivable` constructors. On `LemBoundDemo`'s 12-constructor derivation:

| stage of `classical_to_prenex_extended` | constructors |
|---|---|
| the input derivation `lFinalNoLem` | 12 |
| step 1, `prenexify` alone (uses LEM) | 347 |
| `forall_map prenexify` | 350 |
| the prenexified derivation `prf'` | 363 |
| **step 2, `negTrans_sound nts prf'`** | **84,905** |
| step 3, `nn_all_nn` alone | 274 |
| the whole thing (steps 1–4) | 85,180 |
| the whole thing on the LEM-using `lFinalLem` (33 constructors) | 89,556 |

So the classical route hands Dialectica a derivation **7,000× larger than the input**, and
**the negative translation is the whole of it**: 363 → 84,905, i.e. ≈234 constructors per
translated node. It is linear, not a fixed cost — the LEM derivation is 21 nodes bigger and
costs 4,376 more, ≈208 per node again — so it is the per-case `¬¬`-shuffling lemmas of
`negTrans_sound` (`neg_neg_imp_rev`, `dnn_lem`, …) being *expanded* as Hilbert combinator
trees at every node. Excluded middle itself is 4,376 of 89,556.

That is why the classical extractors OOM under `#eval` where `acFinal` does not: Dialectica on
an 85k-constructor derivation, at the measured ≈×2 per 4 constructors, is not a term that
exists. **The fix is at the translation layer, before Dialectica sees it**: either commutation
lemmas for the NT cases (realizer of `negTrans_sound (rule …)` from the realizers of the
parts, never expanding the ≈230-node combinator — the `wit_seq_*` strategy, one layer down),
or a `negTrans_sound` that emits shared, named combinators rather than inlined ones.

## What to carry forward

- **The two stalls are different problems.** `acFinal`: small term, kernel reduction path
  (rename/cast). Classical: genuinely huge term, produced by `negTrans_sound`'s per-node
  expansion. `LemBoundDemo` had concluded "same blocker" from a profile resemblance and then
  retracted it by sidedness; this is the mechanism behind the retraction.
- **Measure physical size with pointer identity, never with a traversal.** `visit` is the
  tool; it is `unsafe`, which is fine in `Probes/`.
- **`derivSize` before Dialectica, always.** It costs nothing and it would have located the
  classical blow-up in one minute.
