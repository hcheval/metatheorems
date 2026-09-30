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

**Result.** (1) Pointer-identity size: `dag = tree` everywhere (the compiled evaluator preserves
no sharing), and `ConjBoundDemo.acFinal`'s realizer, whose bound is a kernel `whnf` timeout, is
only 2,529 nodes. (2) On `LemBoundDemo`'s 12-constructor derivation the classical route hands
Dialectica 85,180 constructors, of which `negTrans_sound` accounts for 363 → 84,905 (≈230 per
translated node). Tables, profiles and the conclusions to carry forward are in the notes.

NOT imported by `Metatheorems.lean`, per the `Probes/` convention. The OOMing evaluations are
not live; every live `#eval` below completes in seconds under a 12 GB cap.
-/

namespace Metatheorems
namespace SizeProbe

open Formula

-- 1. Pointer-identity size

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

-- 2. Derivation size

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
