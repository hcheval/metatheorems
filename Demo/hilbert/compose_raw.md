# `Metatheorems.Demo.compose_raw`

14 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ (A →ᶠ B) ∧ᶠ (B →ᶠ C)` | ∧-weakening |
| 2 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ B` | ∧-weakening |
| 3 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ A →ᶠ B` | syllogism 1, 2 |
| 4 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ (B →ᶠ C) ∧ᶠ (A →ᶠ B)` | ∧-permutation |
| 5 | `(B →ᶠ C) ∧ᶠ (A →ᶠ B) →ᶠ B →ᶠ C` | ∧-weakening |
| 6 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ B →ᶠ C` | syllogism 4, 5 |
| 7 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ B →ᶠ C` | syllogism 1, 6 |
| 8 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ A ∧ᶠ ((A →ᶠ B) ∧ᶠ (B →ᶠ C))` | ∧-permutation |
| 9 | `A ∧ᶠ ((A →ᶠ B) ∧ᶠ (B →ᶠ C)) →ᶠ A` | ∧-weakening |
| 10 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ A` | syllogism 8, 9 |
| 11 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ B` | eval_h 3, 10 |
| 12 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ C` | eval_h 7, 11 |
| 13 | `(A →ᶠ B) ∧ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | exportation 12 |
| 14 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | exportation 13 |
