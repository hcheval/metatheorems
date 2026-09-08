# `Metatheorems.Demo.demo_add_comm`

49 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `x +ᵗ 0 =₀ x` | add_zero_r |
| 2 | `eqAtType nat (x +ᵗ 0) x` | qfer_no_premise_at_nf 1 |
| 3 | `· ⊢ x +ᵗ 0 =₀ x` | ProofMode.pm_have 2 |
| 4 | `0 +ᵗ x =₀ x` | add_zero_l |
| 5 | `eqAtType nat x x` | qfer_no_premise_at_nf 4 |
| 6 | `· ⊢ x =₀ x` | ProofMode.pm_have 5 |
| 7 | `· ⊢ x =₀ x` | ProofMode.pm_refl |
| 8 | `eqAtType nat (0 +ᵗ x) x` | qfer_no_premise_at_nf 4 |
| 9 | `· ⊢ 0 +ᵗ x =₀ x` | ProofMode.pm_have 8 |
| 10 | `· ⊢ x =₀ 0 +ᵗ x` | ProofMode.pm_sym 9 |
| 11 | `· ⊢ x =₀ 0 +ᵗ x` | ProofMode.pm_trans 7, 10 |
| 12 | `· ⊢ x =₀ 0 +ᵗ x` | ProofMode.pm_trans 6, 11 |
| 13 | `eqAtType nat (0 +ᵗ x) (0 +ᵗ x)` | qfer_no_premise_at_nf 1 |
| 14 | `· ⊢ 0 +ᵗ x =₀ 0 +ᵗ x` | ProofMode.pm_have 13 |
| 15 | `· ⊢ 0 +ᵗ x =₀ 0 +ᵗ x` | ProofMode.pm_sym 14 |
| 16 | `· ⊢ x =₀ 0 +ᵗ x` | ProofMode.pm_trans 12, 15 |
| 17 | `· ⊢ x +ᵗ 0 =₀ 0 +ᵗ x` | ProofMode.pm_trans 3, 16 |
| 18 | `x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | add_succ |
| 19 | `eqAtType nat (x +ᵗ S x₀) S (x +ᵗ x₀)` | qfer_no_premise_at_nf 18 |
| 20 | `ih ⊢ x +ᵗ S x₀ =₀ S (x +ᵗ x₀)` | ProofMode.pm_have 19 |
| 21 | `S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | add_succ_l |
| 22 | `eqAtType nat S (x +ᵗ x₀) S (x +ᵗ x₀)` | qfer_no_premise_at_nf 21 |
| 23 | `ih ⊢ S (x +ᵗ x₀) =₀ S (x +ᵗ x₀)` | ProofMode.pm_have 22 |
| 24 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)` | I (identity) |
| 25 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat S (x +ᵗ x₀) S (x₀ +ᵗ x)` | qfer_at_nf 24 |
| 26 | `ih ⊢ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_have 25 |
| 27 | `(x +ᵗ x₀ =₀ x₀ +ᵗ x) :: List.map (weakenBy nat) [] ⊢ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x)` | ProofMode.seq_id |
| 28 | `ih ⊢ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_mp 26, 27 |
| 29 | `ih ⊢ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_refl |
| 30 | `eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ eqAtType nat S (x₀ +ᵗ x) S (x₀ +ᵗ x)` | qfer_at_nf 24 |
| 31 | `ih ⊢ eqAtType nat (x +ᵗ x₀) (x₀ +ᵗ x) →ᶠ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_have 30 |
| 32 | `ih ⊢ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_mp 31, 27 |
| 33 | `ih ⊢ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_sym 32 |
| 34 | `ih ⊢ S (x₀ +ᵗ x) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_trans 29, 33 |
| 35 | `ih ⊢ S (x +ᵗ x₀) =₀ S (x₀ +ᵗ x)` | ProofMode.pm_trans 28, 34 |
| 36 | `eqAtType nat (S x₀ +ᵗ x) S (x₀ +ᵗ x)` | qfer_no_premise_at_nf 21 |
| 37 | `ih ⊢ S x₀ +ᵗ x =₀ S (x₀ +ᵗ x)` | ProofMode.pm_have 36 |
| 38 | `ih ⊢ S (x₀ +ᵗ x) =₀ S x₀ +ᵗ x` | ProofMode.pm_sym 37 |
| 39 | `ih ⊢ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ProofMode.pm_trans 35, 38 |
| 40 | `ih ⊢ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ProofMode.pm_trans 23, 39 |
| 41 | `eqAtType nat (S x₀ +ᵗ x) (S x₀ +ᵗ x)` | qfer_no_premise_at_nf 18 |
| 42 | `ih ⊢ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | ProofMode.pm_have 41 |
| 43 | `ih ⊢ S x₀ +ᵗ x =₀ S x₀ +ᵗ x` | ProofMode.pm_sym 42 |
| 44 | `ih ⊢ S (x +ᵗ x₀) =₀ S x₀ +ᵗ x` | ProofMode.pm_trans 40, 43 |
| 45 | `ih ⊢ x +ᵗ S x₀ =₀ S x₀ +ᵗ x` | ProofMode.pm_trans 20, 44 |
| 46 | `· ⊢ x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | ProofMode.pm_intro 45 |
| 47 | `· ⊢ ∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x →ᶠ substVar0 (x +ᵗ x₀ =₀ x₀ +ᵗ x) succVar0` | ProofMode.pm_allI 46 |
| 48 | `· ⊢ ∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x` | ProofMode.pm_induction 17, 47 |
| 49 | `∀ᶠ x₀ : nat, x +ᵗ x₀ =₀ x₀ +ᵗ x` | ProofMode.pm_enter 48 |
