/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.ConjBoundDemo
import Metatheorems.Probes.ExtractTermDemo
import Metatheorems.Probes.LemBoundDemo
import Std.Data.HashMap

/-!
# Probe: how big are the extracted terms, REALLY — and where the classical route's size enters

Two measurements this project had never taken, each answering a question that had been argued
about from indirect evidence.

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

NOT imported by `Metatheorems.lean`, per the `Probes/` convention. The OOMing evaluations are
not live; every live `#eval` below completes in seconds under a 12 GB cap.
-/

namespace Metatheorems
namespace SizeProbe

open Formula

-- ============================================================================
-- 1. Pointer-identity size
-- ============================================================================

abbrev M := StateT (Std.HashMap USize Nat) IO

/-- Tree size, memoised on the physical address. The memo's size afterwards is the DAG size.
`unsafe` because of `ptrAddrUnsafe`; that is the whole point — a pure traversal could not
tell a shared node from a copy. -/
unsafe def visit {ι κ : Type} {F : κ → Ty ι} :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → M Nat
  | _, _, t => do
    let addr := ptrAddrUnsafe t
    if let some n := (← get).get? addr then return n
    let n ← match t with
      | .app f a    => do let x ← visit f; let y ← visit a; pure (1 + x + y)
      | .lam b      => do let x ← visit b; pure (1 + x)
      | .mkPair a b => do let x ← visit a; let y ← visit b; pure (1 + x + y)
      | .fst p      => do let x ← visit p; pure (1 + x)
      | .snd p      => do let x ← visit p; pure (1 + x)
      | _           => pure 1
    modify (·.insert addr n)
    return n

unsafe def report {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} {τ : Ty ι}
    (name : String) (t : Term F Γ τ) : IO Unit := do
  let (tree, memo) ← (visit t).run {}
  IO.println s!"{name}: dag={memo.size} tree={tree}"

#eval report "uFinal (calibration, 533)" ExtractTermDemo.uRealizer
#eval report "tFinalOnce (reducing control)" (extractTerm ExtractTermDemo.wSp ConjBoundDemo.tFinalOnce)
#eval report "acFinal (the and_contract stall)" (extractTerm ExtractTermDemo.wSp ConjBoundDemo.acFinal)
#eval report "lUtExt (intuitionistic control)" LemBoundDemo.lUtExt
-- #eval report "lUtNoLem" LemBoundDemo.lUtNoLem   -- INTERNAL PANIC: out of memory at 12 GB, while building

-- ============================================================================
-- 2. Derivation size
-- ============================================================================

/-- Constructor count of a `Derivable`. Rules with sub-derivations recurse; everything else
is a leaf. -/
def derivSize {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Nat
  | _, _, .mp a b          => 1 + derivSize a + derivSize b
  | _, _, .syllogism a b   => 1 + derivSize a + derivSize b
  | _, _, .exportation a   => 1 + derivSize a
  | _, _, .importation a   => 1 + derivSize a
  | _, _, .expansion a     => 1 + derivSize a
  | _, _, .forall_rule a   => 1 + derivSize a
  | _, _, .exist_rule a    => 1 + derivSize a
  | _, _, .univ_gen a      => 1 + derivSize a
  | _, _, .qfer _ _ a      => 1 + derivSize a
  | _, _, .induction a b   => 1 + derivSize a + derivSize b
  | _, _, _                => 1

open LemBoundDemo in
/-- Step 1 of `classical_to_prenex_extended`, alone. -/
def pren := prenexify (F := lFE) (Premises := lPremE) (Γ := []) (ρ := Ty.nat)
  (B₀ := lB0) (C₀ := lC0) lB0_qf lB0_vf lC0_qf lC0_vf

open LemBoundDemo in
/-- The prenexified derivation — what step 2 translates. -/
def prf' : @Derivable Empty Empty lFE Allowed.classical lPremE []
    (Formula.all Ty.nat (Formula.ex Ty.nat (Formula.ex Ty.nat
      (lB0.weakenBy Ty.nat →ᶠ lC0.renameF (Term.Renaming.ext Term.Renaming.shift))))) :=
  Derivable.mp lFinalNoLem (forall_map pren)

open LemBoundDemo in
/-- Step 2: the negative translation. THIS is the 85k. -/
def nt := negTrans_sound lNts prf'

open LemBoundDemo in
#eval derivSize lFinalNoLem
#eval derivSize pren
#eval derivSize prf'
#eval derivSize nt
open LemBoundDemo in
#eval derivSize (classical_to_prenex_extended lNts lB0_qf lB0_vf lC0_qf lC0_vf lFinalNoLem)
open LemBoundDemo in
#eval derivSize (classical_to_prenex_extended lNts lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem)
#eval derivSize ConjBoundDemo.acFinal
#eval derivSize ConjBoundDemo.tFinalOnce

end SizeProbe
end Metatheorems
