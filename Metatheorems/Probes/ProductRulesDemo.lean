/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Soundness

/-!
# Demo: the product β/η rules make `∃w^(nat ×ₜ nat) (fst w =₀ 0 ∧ snd w =₀ S 0)` derivable

Until 2026-09-05 `Derivable` had **no** rule about `mkPair`/`fst`/`snd` — the constructors
were in `Term` (since the `syntactic-witnesses` merge) but `fst (mkPair a b) =₀ a` was not a
theorem of the object system. Two things were blocked on exactly that: the `∃u∃v` collapse on
the classical route (`classical_to_prenex_extended`'s docstring in `MetatheoremPrereqs.lean`, "no
product β-rules") and the nested existentials of `Probes/ConjBoundDemo.lean`. This file shows
the wall is gone.

## The statement

At `ι = Empty` (pure `WE-HA^ω`), with `w : nat ×ₜ nat`:

    ∃w ( fst w =₀ 0  ∧  snd w =₀ S 0 )

## The derivation

Four raw constructors and one library lemma, generic in `Allowed` and in the premise set —
no extension principle and no premise is touched:

1. `pair_fst 0 (S 0) : fst ⟨0, S 0⟩ =₀ 0`         — the new β×₁ rule
2. `pair_snd 0 (S 0) : snd ⟨0, S 0⟩ =₀ S 0`       — the new β×₂ rule
3. `and_intro` + `mp`×2                            — the conjunction
4. `exist_ax ⟨0, S 0⟩ C` + `mp`                    — the existential

Step 4 typechecks only because `C.subst0 ⟨0, S 0⟩` is *definitionally* the conjunction in
step 3 (`C_subst0` below, by `rfl`) — substitution into a formula whose only free variable
is `w` just plugs the pair in.

## Negative control

The wrong projection is **not** derivable by the new rules. Kept as a comment because a
failing declaration is not a green build; the text is the verbatim error from
`lake env lean` on the snippet (2026-09-05):

```
example : Derivable pFE al P (Formula.eq0 (Term.fst pairTerm) (Term.app Term.succ Term.zero)) :=
  .pair_fst Term.zero (Term.app Term.succ Term.zero)
```

    error: Type mismatch
      Derivable.pair_fst 0 (Term.succ ⬝ 0)
    has type
      Derivable ?m.54 ?m.33 ?m.34 (eqAtType nat (0.mkPair (Term.succ ⬝ 0)).fst 0)
    but is expected to have type
      Derivable pFE al P (Formula.eq0 pairTerm.fst (Term.succ ⬝ 0))

With the arguments left to inference (`.pair_fst _ _`):

    error: Type mismatch
      Derivable.pair_fst ?m.38 ?m.39
    has type
      Derivable ?m.32 ?m.33 ?m.34 (eqAtType ?m.36 (Term.mkPair ?m.38 ?m.39).fst ?m.38)
    but is expected to have type
      Derivable pFE al P (Formula.eq0 pairTerm.fst (Term.succ ⬝ 0))

— the rule's conclusion has the *same* `?m.38` in both the pair and the right-hand side, and
`0` and `S 0` cannot both be it. The right projection in the same shape (`hfst` below)
elaborates in the same run. Nothing else in the system can bridge it either:
`soundness` refutes the target in the standard model (`(0, 1).1 = 1` is false), so it is
underivable outright, not merely underivable *by these rules*.
-/

namespace Metatheorems
namespace ProductRulesDemo

open Formula

-- Pure `WE-HA^ω`: no base types, no constants. Same recipe as `TinyBoundDemo`, own names.

/-- The carrier family: no base types. -/
def pXE : Empty → Type := fun i => i.elim
/-- The function-constant signature: none. -/
def pFE : Empty → Ty Empty := fun i => i.elim

def pSiE : SpaceInterp pXE pFE where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

-- The statement

/-- The pair type `nat ×ₜ nat`. -/
abbrev pairTy : Ty Empty := Ty.nat ×ₜ Ty.nat

/-- `⟨0, S 0⟩ : nat ×ₜ nat`, closed. -/
def pairTerm : Term pFE [] pairTy :=
  Term.mkPair Term.zero (Term.app Term.succ Term.zero)

/-- The matrix `fst w =₀ 0 ∧ snd w =₀ S 0`, with `w` the bound variable. -/
def C : Formula pFE [pairTy] :=
  Formula.eq0 (Term.fst (.var .vz)) Term.zero
    ∧ᶠ Formula.eq0 (Term.snd (.var .vz)) (Term.app Term.succ Term.zero)

/-- The target: `∃w^(nat ×ₜ nat) (fst w =₀ 0 ∧ snd w =₀ S 0)`. -/
def target : Formula pFE [] := Formula.ex pairTy C

/-- Substituting the pair for `w` is definitionally the closed conjunction. -/
theorem C_subst0 :
    C.subst0 pairTerm
      = (Formula.eq0 (Term.fst pairTerm) Term.zero
          ∧ᶠ Formula.eq0 (Term.snd pairTerm) (Term.app Term.succ Term.zero)) := rfl

-- The derivation — generic in `Allowed` and in the premise set

section
variable {al : Allowed} {P : PremiseSet pFE}

/-- β×₁ at the pair: `fst ⟨0, S 0⟩ =₀ 0`. `eqAtType Ty.nat` *is* `Formula.eq0`, by `rfl`. -/
def hfst : Derivable pFE al P (Formula.eq0 (Term.fst pairTerm) Term.zero) :=
  .pair_fst Term.zero (Term.app Term.succ Term.zero)

/-- β×₂ at the pair: `snd ⟨0, S 0⟩ =₀ S 0`. -/
def hsnd : Derivable pFE al P
    (Formula.eq0 (Term.snd pairTerm) (Term.app Term.succ Term.zero)) :=
  .pair_snd Term.zero (Term.app Term.succ Term.zero)

/-- The closed conjunction, by `and_intro`. -/
def hboth : Derivable pFE al P
    (Formula.eq0 (Term.fst pairTerm) Term.zero
      ∧ᶠ Formula.eq0 (Term.snd pairTerm) (Term.app Term.succ Term.zero)) :=
  .mp hsnd (.mp hfst and_intro)

/-- **The previously underivable statement.** `exist_ax` at the pair, fed the conjunction. -/
def derivation : Derivable pFE al P target :=
  .mp hboth (.exist_ax pairTerm C)

/-- The variable `w : nat ×ₜ nat`, in the one-element context. -/
def wVar : Term pFE [pairTy] pairTy := .var .vz

/-- η× at a variable: `⟨fst w, snd w⟩ =_{nat ×ₜ nat} w`. -/
def etaAtVar : Derivable pFE al P
    (eqAtType pairTy (Term.mkPair (Term.fst wVar) (Term.snd wVar)) wVar) :=
  .pair_eta wVar

/-- The η-equation at a product type is literally the conjunction of two `=₀`s —
`fst ⟨fst w, snd w⟩ =₀ fst w ∧ snd ⟨fst w, snd w⟩ =₀ snd w` — by `rfl`. -/
theorem eta_shape :
    eqAtType pairTy (Term.mkPair (Term.fst wVar) (Term.snd wVar)) wVar
      = (Formula.eq0 (Term.fst (Term.mkPair (Term.fst wVar) (Term.snd wVar))) (Term.fst wVar)
          ∧ᶠ Formula.eq0 (Term.snd (Term.mkPair (Term.fst wVar) (Term.snd wVar)))
              (Term.snd wVar)) := rfl

end

-- The derivation is sound: the target is true in the model — and the extraction pipeline
-- accepts it unchanged

/-- Semantic soundness at `ι = Empty` — all five model facts are vacuous. -/
theorem target_true : Formula.interpret pSiE target () :=
  soundness (si := pSiE) (Premises := fun _ => False)
    (fun _ h => h.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    (derivation (al := Allowed.extended)) ()

/-- The witness the model actually sees, read off `target_true`'s statement: `(0, 1)`. -/
example : Formula.interpret pSiE target () = ∃ w : ℕ × ℕ, w.1 = 0 ∧ w.2 = 1 := rfl

/-- The extracted realizer *term* — model-free (`extractTerm`), evaluable, and (by
`extractTerm_eq`) what `syntactic_soundness` produces. -/
def realizer : Term pFE [] (wTy target) :=
  extractTerm (Premises := fun _ => False) (fun _ _ h => h.elim)
    (derivation (al := Allowed.extended))

/-- The realizer's witness component is the pair `(0, 1)`. Stated **semantically**: as a
term the realizer is `wtMP`'s syntactic redex `app (fst ⟨…⟩) …` around `exist_ax`'s lambda,
not literally `pairTerm` — `Term` is syntax, so it is not definitionally the pair. -/
theorem realizer_witness : (Term.interpret pSiE realizer ()).1 = (0, 1) := rfl

#print axioms derivation
#print axioms hfst
#print axioms hsnd
#print axioms etaAtVar
#print axioms eta_shape
#print axioms target_true
#print axioms realizer_witness

end ProductRulesDemo
end Metatheorems
