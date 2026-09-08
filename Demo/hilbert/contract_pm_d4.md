# `Metatheorems.Demo.contract_pm`

117 steps, proof-mode depth 4.

| # | Formula | Justification |
|---:|---|---|
| 1 | `B →ᶠ B` | I (identity) |
| 2 | `(B →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | ∧-weakening |
| 3 | `(B →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | exportation 2 |
| 4 | `(A →ᶠ B) →ᶠ B →ᶠ B` | modus ponens 1, 3 |
| 5 | `((A →ᶠ B) →ᶠ B →ᶠ B) ∧ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | ∧-weakening |
| 6 | `((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | exportation 5 |
| 7 | `A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | modus ponens 4, 6 |
| 8 | `(A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | ∧-weakening |
| 9 | `(A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | exportation 8 |
| 10 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | modus ponens 7, 9 |
| 11 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B` | ProofMode.seq_of_thm 10 |
| 12 | `((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 13 | `(((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 14 | `(((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 13 |
| 15 | `A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 12, 14 |
| 16 | `(A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 17 | `(A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 16 |
| 18 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 15, 17 |
| 19 | `(A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 20 | `((A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 21 | `((A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 20 |
| 22 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 19, 21 |
| 23 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 24 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 22, 23 |
| 25 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 18, 24 |
| 26 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 27 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 25, 26 |
| 28 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 11, 27 |
| 29 | `(A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 30 | `((A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 31 | `((A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | exportation 30 |
| 32 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 29, 31 |
| 33 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 34 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 32, 33 |
| 35 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 28, 34 |
| 36 | `(A →ᶠ B) →ᶠ A →ᶠ B` | I (identity) |
| 37 | `((A →ᶠ B) →ᶠ A →ᶠ B) ∧ᶠ A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B` | ∧-weakening |
| 38 | `((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B` | exportation 37 |
| 39 | `A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B` | modus ponens 36, 38 |
| 40 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B` | ProofMode.weaken_intro_h 39 |
| 41 | `((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 42 | `(((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 43 | `(((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 42 |
| 44 | `A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 41, 43 |
| 45 | `(A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 46 | `(A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 45 |
| 47 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 44, 46 |
| 48 | `(A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 49 | `((A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 50 | `((A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | exportation 49 |
| 51 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 48, 50 |
| 52 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 53 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 51, 52 |
| 54 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 47, 53 |
| 55 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 56 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 54, 55 |
| 57 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 40, 56 |
| 58 | `(A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 59 | `((A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | ∧-weakening |
| 60 | `((A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | exportation 59 |
| 61 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 58, 60 |
| 62 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 63 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ ((A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 61, 62 |
| 64 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 57, 63 |
| 65 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | S |
| 66 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | modus ponens 64, 65 |
| 67 | `A →ᶠ (A →ᶠ B) →ᶠ A` | K |
| 68 | `(A →ᶠ (A →ᶠ B) →ᶠ A) ∧ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | ∧-weakening |
| 69 | `(A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | exportation 68 |
| 70 | `A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 67, 69 |
| 71 | `(A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | ∧-weakening |
| 72 | `(A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | exportation 71 |
| 73 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 70, 72 |
| 74 | `(A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | S |
| 75 | `((A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | ∧-weakening |
| 76 | `((A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | exportation 75 |
| 77 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 74, 76 |
| 78 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | S |
| 79 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 77, 78 |
| 80 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 73, 79 |
| 81 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | S |
| 82 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | modus ponens 80, 81 |
| 83 | `A →ᶠ A` | I (identity) |
| 84 | `(A →ᶠ A) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A` | ∧-weakening |
| 85 | `(A →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A` | exportation 84 |
| 86 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A` | modus ponens 83, 85 |
| 87 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ A` | ProofMode.seq_mp 82, 86 |
| 88 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B` | ProofMode.seq_mp 66, 87 |
| 89 | `⟨1 hypotheses⟩ ⊢ A →ᶠ (A →ᶠ B) →ᶠ B` | ProofMode.seq_mp 35, 88 |
| 90 | `(A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | S |
| 91 | `((A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | ∧-weakening |
| 92 | `((A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | exportation 91 |
| 93 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | modus ponens 90, 92 |
| 94 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | S |
| 95 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ (A →ᶠ B) →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | modus ponens 93, 94 |
| 96 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | modus ponens 89, 95 |
| 97 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | S |
| 98 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | modus ponens 96, 97 |
| 99 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | I (identity) |
| 100 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | K |
| 101 | `((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | ∧-weakening |
| 102 | `((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | exportation 101 |
| 103 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | modus ponens 100, 102 |
| 104 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | S |
| 105 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | modus ponens 103, 104 |
| 106 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B` | modus ponens 99, 105 |
| 107 | `(A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | S |
| 108 | `((A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | ∧-weakening |
| 109 | `((A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | exportation 108 |
| 110 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 107, 109 |
| 111 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | S |
| 112 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 110, 111 |
| 113 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 106, 112 |
| 114 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | S |
| 115 | `· ⊢ ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 113, 114 |
| 116 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 86, 115 |
| 117 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | ProofMode.seq_mp 98, 116 |
