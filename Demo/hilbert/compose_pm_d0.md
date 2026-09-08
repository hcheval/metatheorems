# `Metatheorems.Demo.compose_pm`

13 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `⟨3 hypotheses⟩ ⊢ A →ᶠ B` | ProofMode.seq_id |
| 2 | `⟨3 hypotheses⟩ ⊢ A` | ProofMode.seq_id |
| 3 | `ha, hBC, hAB ⊢ B` | ProofMode.pm_mp 1, 2 |
| 4 | `⟨4 hypotheses⟩ ⊢ B →ᶠ C` | ProofMode.seq_id |
| 5 | `⟨4 hypotheses⟩ ⊢ B` | ProofMode.seq_id |
| 6 | `hb, ha, hBC, hAB ⊢ C` | ProofMode.pm_mp 4, 5 |
| 7 | `⟨5 hypotheses⟩ ⊢ C` | ProofMode.seq_id |
| 8 | `hb, ha, hBC, hAB ⊢ C` | ProofMode.pm_cut 6, 7 |
| 9 | `ha, hBC, hAB ⊢ C` | ProofMode.pm_cut 3, 8 |
| 10 | `hBC, hAB ⊢ A →ᶠ C` | ProofMode.pm_intro 9 |
| 11 | `hAB ⊢ (B →ᶠ C) →ᶠ A →ᶠ C` | ProofMode.pm_intro 10 |
| 12 | `· ⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | ProofMode.pm_intro 11 |
| 13 | `(A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ A →ᶠ C` | ProofMode.pm_enter 12 |
