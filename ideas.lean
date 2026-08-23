/-



Deepest encoding:

Type system:
inductive 𝕋 (ι : Type) where
| nat : 𝕋
| arrow : 𝕋 → 𝕋 → 𝕋
| prod : 𝕋 → 𝕋 → 𝕋
| rational : 𝕋
| user : ι → 𝕋

inductive Term : Context → 𝕋 → Type where
-- standard labmda terms
-- shallow embedded rational literals?

inductive Formula
-- standard FOL formulas over Term

inductive Proof

iris-style proof mode over Proof, outputting WE-HA proofs,
crucially, tactics for intro, specialize, induction, etc

Dialectica, MFI, MR (+ND), Shoenfield
Witness is Term, soundness is semantical

Metatheorems


theory
    type X

    =_X := fun x y => d x y = 0_R

    constant d : X -> X -> R

    axiom
        ...



-/
