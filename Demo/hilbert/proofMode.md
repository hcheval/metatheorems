# `Metatheorems.Demo.proofMode`

7 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `(∀ᶠ x₁ : nat, triB) :: List.map (weakenBy pTy) [] ⊢ ∀ᶠ x₁ : nat, triB` | ProofMode.seq_id |
| 2 | `subst0 triB triWit :: (∀ᶠ x₁ : nat, triB) :: List.map (weakenBy pTy) [] ⊢ subst0 triB triWit` | ProofMode.seq_id |
| 3 | `h1, h ⊢ ∃ᶠ x₁ : nat, triB` | ProofMode.pm_exI 2 |
| 4 | `h ⊢ ∃ᶠ x₁ : nat, triB` | ProofMode.pm_inst 1, 3 |
| 5 | `· ⊢ (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | ProofMode.pm_intro 4 |
| 6 | `· ⊢ ∀ᶠ x₀ : pTy, (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | ProofMode.pm_allI 5 |
| 7 | `stmt` | ProofMode.pm_enter 6 |
