# `Metatheorems.Demo.demo_add_comm`

198 steps, proof-mode depth 4.

| # | Formula | Justification |
|---:|---|---|
| 1 | `x +ᵗ 0 =₀ x` | add_zero_r |
| 2 | `eqAtType nat (0 +ᵗ x) (0 +ᵗ x)` | qfer_no_premise_at_nf 1 |
| 3 | `0 +ᵗ x =₀ 0 +ᵗ x →ᶠ 0 +ᵗ x =₀ 0 +ᵗ x` | symmetry |
| 4 | `· ⊢ 0 +ᵗ x =₀ 0 +ᵗ x` | modus ponens 2, 3 |
| 5 | `0 +ᵗ x =₀ x` | add_zero_l |
| 6 | `eqAtType nat (0 +ᵗ x) x` | qfer_no_premise_at_nf 5 |
| 7 | `0 +ᵗ x =₀ x →ᶠ x =₀ 0 +ᵗ x` | symmetry |
| 8 | `· ⊢ x =₀ 0 +ᵗ x` | modus ponens 6, 7 |
| 9 | `x =₀ x` | reflexivity |
| 10 | `x =₀ x →ᶠ x =₀ 0 +ᵗ x →ᶠ x =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | and_intro |
| 11 | `· ⊢ x =₀ 0 +ᵗ x →ᶠ x =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 9, 10 |
| 12 | `· ⊢ x =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 8, 11 |
| 13 | `x =₀ x ∧ᶠ x =₀ 0 +ᵗ x →ᶠ x =₀ 0 +ᵗ x` | transitivity |
| 14 | `· ⊢ x =₀ 0 +ᵗ x` | modus ponens 12, 13 |
| 15 | `eqAtType nat x x` | qfer_no_premise_at_nf 5 |
| 16 | `· ⊢ x =₀ 0 +ᵗ x →ᶠ x =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 15, 10 |
| 17 | `· ⊢ x =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 14, 16 |
| 18 | `· ⊢ x =₀ 0 +ᵗ x` | modus ponens 17, 13 |
| 19 | `x =₀ 0 +ᵗ x →ᶠ 0 +ᵗ x =₀ 0 +ᵗ x →ᶠ x =₀ 0 +ᵗ x ∧ᶠ 0 +ᵗ x =₀ 0 +ᵗ x` | and_intro |
| 20 | `· ⊢ 0 +ᵗ x =₀ 0 +ᵗ x →ᶠ x =₀ 0 +ᵗ x ∧ᶠ 0 +ᵗ x =₀ 0 +ᵗ x` | modus ponens 18, 19 |
| 21 | `· ⊢ x =₀ 0 +ᵗ x ∧ᶠ 0 +ᵗ x =₀ 0 +ᵗ x` | modus ponens 4, 20 |
| 22 | `x =₀ 0 +ᵗ x ∧ᶠ 0 +ᵗ x =₀ 0 +ᵗ x →ᶠ x =₀ 0 +ᵗ x` | transitivity |
| 23 | `· ⊢ x =₀ 0 +ᵗ x` | modus ponens 21, 22 |
| 24 | `eqAtType nat (x +ᵗ 0) x` | qfer_no_premise_at_nf 1 |
| 25 | `x +ᵗ 0 =₀ x →ᶠ x =₀ 0 +ᵗ x →ᶠ x +ᵗ 0 =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | and_intro |
| 26 | `· ⊢ x =₀ 0 +ᵗ x →ᶠ x +ᵗ 0 =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 24, 25 |
| 27 | `· ⊢ x +ᵗ 0 =₀ x ∧ᶠ x =₀ 0 +ᵗ x` | modus ponens 23, 26 |
| 28 | `x +ᵗ 0 =₀ x ∧ᶠ x =₀ 0 +ᵗ x →ᶠ x +ᵗ 0 =₀ 0 +ᵗ x` | transitivity |
| 29 | `· ⊢ x +ᵗ 0 =₀ 0 +ᵗ x` | modus ponens 27, 28 |
| 30 | `⊥ᶠ →ᶠ ⊥ᶠ` | I (identity) |
| 31 | `⊥ᶠ →ᶠ ⊥ᶠ` | I (identity) |
| 32 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | add_succ |
| 33 | `eqAtType nat (S x₀ +ᵗ x) (S x₀ +ᵗ x)` | qfer_no_premise_at_nf 32 |
| 34 | `S x₀ +ᵗ x =₀ S x₀ +ᵗ x ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | ∧-weakening |
| 35 | `S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | exportation 34 |
| 36 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 33, 35 |
| 37 | `S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | symmetry |
| 38 | `(S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | ∧-weakening |
| 39 | `(S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | exportation 38 |
| 40 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 37, 39 |
| 41 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | S |
| 42 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 40, 41 |
| 43 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 36, 42 |
| 44 | `S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | add_succ_l |
| 45 | `eqAtType nat (S x₀ +ᵗ x) S (x₀ +ᵗ x)` | qfer_no_premise_at_nf 44 |
| 46 | `S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 47 | `S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | exportation 46 |
| 48 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | modus ponens 45, 47 |
| 49 | `S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | symmetry |
| 50 | `(S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 51 | `(S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | exportation 50 |
| 52 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 49, 51 |
| 53 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | S |
| 54 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 52, 53 |
| 55 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 48, 54 |
| 56 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)` | I (identity) |
| 57 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)` | I (identity) |
| 58 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat S (x₀ +ᵗ x) S (x₀ +ᵗ x)` | qfer_at_nf 57 |
| 59 | `(eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 60 | `(eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 59 |
| 61 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 58, 60 |
| 62 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 63 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 61, 62 |
| 64 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 56, 63 |
| 65 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | symmetry |
| 66 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 67 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 66 |
| 68 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 65, 67 |
| 69 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 70 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 68, 69 |
| 71 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 64, 70 |
| 72 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | reflexivity |
| 73 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 74 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 73 |
| 75 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 72, 74 |
| 76 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | and_intro |
| 77 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 78 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 77 |
| 79 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 76, 78 |
| 80 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 81 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 79, 80 |
| 82 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 75, 81 |
| 83 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 84 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 82, 83 |
| 85 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 71, 84 |
| 86 | `S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | transitivity |
| 87 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 88 | `(S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 87 |
| 89 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 86, 88 |
| 90 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 91 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 89, 90 |
| 92 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 85, 91 |
| 93 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat S (x +ᵗ x₀) S (x₀ +ᵗ x)` | qfer_at_nf 57 |
| 94 | `(eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 95 | `(eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | exportation 94 |
| 96 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 93, 95 |
| 97 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | S |
| 98 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 96, 97 |
| 99 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 56, 98 |
| 100 | `S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | and_intro |
| 101 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 102 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | exportation 101 |
| 103 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 100, 102 |
| 104 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 105 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 103, 104 |
| 106 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 99, 105 |
| 107 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | S |
| 108 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 106, 107 |
| 109 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | modus ponens 92, 108 |
| 110 | `S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | transitivity |
| 111 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | ∧-weakening |
| 112 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | exportation 111 |
| 113 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 110, 112 |
| 114 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | S |
| 115 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 113, 114 |
| 116 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | modus ponens 109, 115 |
| 117 | `S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | and_intro |
| 118 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 119 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | exportation 118 |
| 120 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 117, 119 |
| 121 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | S |
| 122 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 120, 121 |
| 123 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 116, 122 |
| 124 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | S |
| 125 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 123, 124 |
| 126 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | modus ponens 55, 125 |
| 127 | `S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | transitivity |
| 128 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 129 | `(S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | exportation 128 |
| 130 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 127, 129 |
| 131 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 132 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x) ∧ᶠ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 130, 131 |
| 133 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 126, 132 |
| 134 | `eqAtType nat S (x +ᵗ x₀) S (x +ᵗ x₀)` | qfer_no_premise_at_nf 44 |
| 135 | `S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)` | ∧-weakening |
| 136 | `S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)` | exportation 135 |
| 137 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)` | modus ponens 134, 136 |
| 138 | `S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | and_intro |
| 139 | `(S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 140 | `(S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | exportation 139 |
| 141 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 138, 140 |
| 142 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 143 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 141, 142 |
| 144 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 137, 143 |
| 145 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 146 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 144, 145 |
| 147 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 133, 146 |
| 148 | `S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | transitivity |
| 149 | `(S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 150 | `(S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | exportation 149 |
| 151 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 148, 150 |
| 152 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 153 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 151, 152 |
| 154 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 147, 153 |
| 155 | `S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | and_intro |
| 156 | `(S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | ∧-weakening |
| 157 | `(S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | exportation 156 |
| 158 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 155, 157 |
| 159 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | S |
| 160 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 158, 159 |
| 161 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 154, 160 |
| 162 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | S |
| 163 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 161, 162 |
| 164 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | modus ponens 43, 163 |
| 165 | `S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | transitivity |
| 166 | `(S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 167 | `(S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | exportation 166 |
| 168 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 165, 167 |
| 169 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 170 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x ∧ᶠ S x₀ +ᵗ x =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 168, 169 |
| 171 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 164, 170 |
| 172 | `eqAtType nat (x +ᵗ S x₀) S (x +ᵗ x₀)` | qfer_no_premise_at_nf 32 |
| 173 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | ∧-weakening |
| 174 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | exportation 173 |
| 175 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | modus ponens 172, 174 |
| 176 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | and_intro |
| 177 | `(x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ∧-weakening |
| 178 | `(x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | exportation 177 |
| 179 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 176, 178 |
| 180 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 181 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 179, 180 |
| 182 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 175, 181 |
| 183 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | S |
| 184 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 182, 183 |
| 185 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | modus ponens 171, 184 |
| 186 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | transitivity |
| 187 | `(x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x) ∧ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | ∧-weakening |
| 188 | `(x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | exportation 187 |
| 189 | `x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | modus ponens 186, 188 |
| 190 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x) →ᶠ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | S |
| 191 | `· ⊢ (x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S (x +ᵗ x₀) ∧ᶠ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | modus ponens 189, 190 |
| 192 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | modus ponens 185, 191 |
| 193 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0) ∧ᶠ (⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | ∧-weakening |
| 194 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0) →ᶠ (⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | exportation 193 |
| 195 | `(⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | modus ponens 192, 194 |
| 196 | `(⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ ∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | ∀-rule 195 |
| 197 | `· ⊢ ∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | modus ponens 31, 196 |
| 198 | `∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x` | induction 29, 197 |
