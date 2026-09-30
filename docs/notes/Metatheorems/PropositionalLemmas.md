# PropositionalLemmas.lean

## `contract`

Derivation (C abbreviates `(A →ᶠ A →ᶠ B) ∧ᶠ A`):
| #  | Formula                   | Justification                       |
|----|---------------------------|-------------------------------------|
| 1  | (A→A→B) → (A→A→B)        | I_comb at A→A→B                     |
| 2  | (A→A→B)∧A → (A→B)        | importation 1                       |
| 3  | C∧A → B                   | importation 2                       |
| 4  | C → A                     | syllogism and_perm and_weak         |
| 5  | A∧C → A∧C                 | I_comb at A∧C                       |
| 6  | A → C → A∧C               | exportation 5                       |
| 7  | C → C → A∧C               | syllogism 4 6                       |
| 8  | C∧C → A∧C                 | importation 7                       |
| 9  | C∧C → C∧A                 | syllogism 8 and_perm                |
| 10 | C → C∧C                   | and_contract                        |
| 11 | C → C∧A                   | syllogism 10 9                      |
| 12 | C → B                     | syllogism 11 3                      |
| 13 | (A→A→B) → A → B           | exportation 12                      |

## `and_assocl`

Pairing trick: to build `H → X∧Y` from `H→X` and `H→Y`:
  1. syllogism(H→Y)(and_intro[Y,H]) : H → H → Y∧H
  2. importation → H∧H → Y∧H; compose with and_contract: H → Y∧H
  3. and_perm → H → H∧Y
  4. syllogism(H→X)(and_intro[X,Y]) : H → Y → X∧Y; importation → H∧Y → X∧Y
  5. compose 3 and 4: H → X∧Y

## `or_elim_rule`

Note: `or_elim` as a *formula* `(A→C)→(B→C)→A∨B→C` is not derivable from the given
primitives because `expansion` requires a closed proof, not a formula hypothesis.
This meta-level function is used instead for building further results.
