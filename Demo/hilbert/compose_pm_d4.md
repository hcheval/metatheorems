# `Metatheorems.Demo.compose_pm`

271 steps, proof-mode depth 4.

| # | Formula | Justification |
|---:|---|---|
| 1 | `C →ᶠ C` | I (identity) |
| 2 | `(C →ᶠ C) ∧ᶠ B →ᶠ C →ᶠ C` | ∧-weakening |
| 3 | `(C →ᶠ C) →ᶠ B →ᶠ C →ᶠ C` | exportation 2 |
| 4 | `B →ᶠ C →ᶠ C` | modus ponens 1, 3 |
| 5 | `(B →ᶠ C →ᶠ C) ∧ᶠ A →ᶠ B →ᶠ C →ᶠ C` | ∧-weakening |
| 6 | `(B →ᶠ C →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C` | exportation 5 |
| 7 | `A →ᶠ B →ᶠ C →ᶠ C` | modus ponens 4, 6 |
| 8 | `(A →ᶠ B →ᶠ C →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C` | ∧-weakening |
| 9 | `(A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C` | exportation 8 |
| 10 | `(B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C` | modus ponens 7, 9 |
| 11 | `⟨1 hypotheses⟩ ⊢ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C` | ProofMode.seq_of_thm 10 |
| 12 | `(B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 13 | `((B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 14 | `((B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 13 |
| 15 | `A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 12, 14 |
| 16 | `(A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 17 | `(A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 16 |
| 18 | `(B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 15, 17 |
| 19 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ProofMode.weaken_intro_h 18 |
| 20 | `(A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 21 | `((A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 22 | `((A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 21 |
| 23 | `(B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 20, 22 |
| 24 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 25 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 24 |
| 26 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 23, 25 |
| 27 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 28 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ   ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 29 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ   (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 28 |
| 30 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 27, 29 |
| 31 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ   ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 32 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 30, 31 |
| 33 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 26, 32 |
| 34 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 35 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 33, 34 |
| 36 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 19, 35 |
| 37 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 38 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 39 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 38 |
| 40 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 37, 39 |
| 41 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 42 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 40, 41 |
| 43 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 36, 42 |
| 44 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | S |
| 45 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 43, 44 |
| 46 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 11, 45 |
| 47 | `(A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 48 | `((A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 49 | `((A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 48 |
| 50 | `(B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 47, 49 |
| 51 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 52 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 51 |
| 53 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 50, 52 |
| 54 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 55 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 56 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 55 |
| 57 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 54, 56 |
| 58 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 59 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 57, 58 |
| 60 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 53, 59 |
| 61 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 62 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 60, 61 |
| 63 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 46, 62 |
| 64 | `(B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | K |
| 65 | `((B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 66 | `((B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | exportation 65 |
| 67 | `A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | modus ponens 64, 66 |
| 68 | `(A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 69 | `(A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | exportation 68 |
| 70 | `(B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | modus ponens 67, 69 |
| 71 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C` | ProofMode.weaken_intro_h 70 |
| 72 | `(A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 73 | `((A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 74 | `((A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | exportation 73 |
| 75 | `(B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 72, 74 |
| 76 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 77 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | exportation 76 |
| 78 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 75, 77 |
| 79 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 80 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 81 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | exportation 80 |
| 82 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 79, 81 |
| 83 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 84 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 82, 83 |
| 85 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 78, 84 |
| 86 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 87 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ C) →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 85, 86 |
| 88 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 71, 87 |
| 89 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 90 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | ∧-weakening |
| 91 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | exportation 90 |
| 92 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 89, 91 |
| 93 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | S |
| 94 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 92, 93 |
| 95 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | modus ponens 88, 94 |
| 96 | `(B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | K |
| 97 | `((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 98 | `((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 97 |
| 99 | `(B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 96, 98 |
| 100 | `((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 101 | `((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 100 |
| 102 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 99, 101 |
| 103 | `((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 104 | `(((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 105 | `(((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 104 |
| 106 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 103, 105 |
| 107 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 108 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 106, 107 |
| 109 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 102, 108 |
| 110 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 111 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 109, 110 |
| 112 | `(B →ᶠ C) →ᶠ B →ᶠ C` | I (identity) |
| 113 | `((B →ᶠ C) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | ∧-weakening |
| 114 | `((B →ᶠ C) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | exportation 113 |
| 115 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | modus ponens 112, 114 |
| 116 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ProofMode.seq_mp 111, 115 |
| 117 | `⟨1 hypotheses⟩ ⊢ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C` | ProofMode.seq_mp 95, 116 |
| 118 | `(B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 119 | `((B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 120 | `((B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 119 |
| 121 | `A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 118, 120 |
| 122 | `(A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 123 | `(A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 122 |
| 124 | `(B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 121, 123 |
| 125 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ProofMode.weaken_intro_h 124 |
| 126 | `(A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 127 | `((A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 128 | `((A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 127 |
| 129 | `(B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 126, 128 |
| 130 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 131 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 130 |
| 132 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 129, 131 |
| 133 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 134 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ   ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 135 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ   (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 134 |
| 136 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 133, 135 |
| 137 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ   ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 138 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 136, 137 |
| 139 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 132, 138 |
| 140 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 141 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 139, 140 |
| 142 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 125, 141 |
| 143 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 144 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 145 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | exportation 144 |
| 146 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 143, 145 |
| 147 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 148 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 146, 147 |
| 149 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 142, 148 |
| 150 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | S |
| 151 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 149, 150 |
| 152 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C` | modus ponens 117, 151 |
| 153 | `(A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | S |
| 154 | `((A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 155 | `((A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | exportation 154 |
| 156 | `(B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 153, 155 |
| 157 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 158 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | exportation 157 |
| 159 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 156, 158 |
| 160 | `((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | S |
| 161 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 162 | `(((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | exportation 161 |
| 163 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 160, 162 |
| 164 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | S |
| 165 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 163, 164 |
| 166 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 159, 165 |
| 167 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | S |
| 168 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ (B →ᶠ B) →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 166, 167 |
| 169 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 152, 168 |
| 170 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 171 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ∧-weakening |
| 172 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | exportation 171 |
| 173 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 170, 172 |
| 174 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | S |
| 175 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ B) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 173, 174 |
| 176 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | modus ponens 169, 175 |
| 177 | `B →ᶠ B` | I (identity) |
| 178 | `(B →ᶠ B) ∧ᶠ A →ᶠ B →ᶠ B` | ∧-weakening |
| 179 | `(B →ᶠ B) →ᶠ A →ᶠ B →ᶠ B` | exportation 178 |
| 180 | `A →ᶠ B →ᶠ B` | modus ponens 177, 179 |
| 181 | `(A →ᶠ B →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | ∧-weakening |
| 182 | `(A →ᶠ B →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | exportation 181 |
| 183 | `(B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | modus ponens 180, 182 |
| 184 | `((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | ∧-weakening |
| 185 | `((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | exportation 184 |
| 186 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | modus ponens 183, 185 |
| 187 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ B` | ProofMode.seq_of_thm 186 |
| 188 | `⟨1 hypotheses⟩ ⊢ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C` | ProofMode.seq_mp 176, 187 |
| 189 | `⟨2 hypotheses⟩ ⊢ A →ᶠ B →ᶠ C` | ProofMode.seq_mp 63, 188 |
| 190 | `(A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | S |
| 191 | `((A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | ∧-weakening |
| 192 | `((A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | exportation 191 |
| 193 | `(B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 190, 192 |
| 194 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | ∧-weakening |
| 195 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | exportation 194 |
| 196 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 193, 195 |
| 197 | `((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | S |
| 198 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | ∧-weakening |
| 199 | `(((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | exportation 198 |
| 200 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 197, 199 |
| 201 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | S |
| 202 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 200, 201 |
| 203 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 196, 202 |
| 204 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | S |
| 205 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 203, 204 |
| 206 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C` | modus ponens 189, 205 |
| 207 | `((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | S |
| 208 | `(((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | ∧-weakening |
| 209 | `(((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | exportation 208 |
| 210 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | modus ponens 207, 209 |
| 211 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | S |
| 212 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | modus ponens 210, 211 |
| 213 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | modus ponens 206, 212 |
| 214 | `(A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | K |
| 215 | `((A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | ∧-weakening |
| 216 | `((A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | exportation 215 |
| 217 | `(B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 214, 216 |
| 218 | `((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | ∧-weakening |
| 219 | `((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | exportation 218 |
| 220 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 217, 219 |
| 221 | `((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | S |
| 222 | `(((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | ∧-weakening |
| 223 | `(((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | exportation 222 |
| 224 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 221, 223 |
| 225 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | S |
| 226 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 224, 225 |
| 227 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 220, 226 |
| 228 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | S |
| 229 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | modus ponens 227, 228 |
| 230 | `(A →ᶠ B) →ᶠ A →ᶠ B` | I (identity) |
| 231 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | K |
| 232 | `((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | ∧-weakening |
| 233 | `((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | exportation 232 |
| 234 | `(A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 231, 233 |
| 235 | `((A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | S |
| 236 | `· ⊢ ((A →ᶠ B) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 234, 235 |
| 237 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 230, 236 |
| 238 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B` | ProofMode.seq_mp 229, 237 |
| 239 | `(A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | S |
| 240 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | ∧-weakening |
| 241 | `((A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | exportation 240 |
| 242 | `(B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 239, 241 |
| 243 | `((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | ∧-weakening |
| 244 | `((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | exportation 243 |
| 245 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 242, 244 |
| 246 | `((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | S |
| 247 | `(((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | ∧-weakening |
| 248 | `(((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | exportation 247 |
| 249 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 246, 248 |
| 250 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | S |
| 251 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 249, 250 |
| 252 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 245, 251 |
| 253 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | S |
| 254 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 252, 253 |
| 255 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B` | modus ponens 238, 254 |
| 256 | `((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | S |
| 257 | `(((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) ∧ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | ∧-weakening |
| 258 | `(((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | exportation 257 |
| 259 | `(A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 256, 258 |
| 260 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | S |
| 261 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ A) →ᶠ A →ᶠ B) →ᶠ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 259, 260 |
| 262 | `· ⊢ (A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 255, 261 |
| 263 | `((A →ᶠ B) →ᶠ ((B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B) →ᶠ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | S |
| 264 | `· ⊢ ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A) →ᶠ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | modus ponens 262, 263 |
| 265 | `A →ᶠ A` | I (identity) |
| 266 | `(A →ᶠ A) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ A` | ∧-weakening |
| 267 | `(A →ᶠ A) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A` | exportation 266 |
| 268 | `(B →ᶠ C) →ᶠ A →ᶠ A` | modus ponens 265, 267 |
| 269 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ A` | ProofMode.weaken_intro_h 268 |
| 270 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | ProofMode.seq_mp 264, 269 |
| 271 | `⟨1 hypotheses⟩ ⊢ (B →ᶠ C) →ᶠ A →ᶠ C` | ProofMode.seq_mp 213, 270 |
