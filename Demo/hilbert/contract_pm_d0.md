# `Metatheorems.Demo.contract_pm`

12 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `⟨2 hypotheses⟩ ⊢ A →ᶠ A →ᶠ B` | ProofMode.seq_id |
| 2 | `⟨2 hypotheses⟩ ⊢ A` | ProofMode.seq_id |
| 3 | `ha, h ⊢ A →ᶠ B` | ProofMode.pm_mp 1, 2 |
| 4 | `⟨3 hypotheses⟩ ⊢ A →ᶠ B` | ProofMode.seq_id |
| 5 | `⟨3 hypotheses⟩ ⊢ A` | ProofMode.seq_id |
| 6 | `h1, ha, h ⊢ B` | ProofMode.pm_mp 4, 5 |
| 7 | `⟨4 hypotheses⟩ ⊢ B` | ProofMode.seq_id |
| 8 | `h1, ha, h ⊢ B` | ProofMode.pm_cut 6, 7 |
| 9 | `ha, h ⊢ B` | ProofMode.pm_cut 3, 8 |
| 10 | `h ⊢ A →ᶠ B` | ProofMode.pm_intro 9 |
| 11 | `· ⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | ProofMode.pm_intro 10 |
| 12 | `(A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B` | ProofMode.pm_enter 11 |
