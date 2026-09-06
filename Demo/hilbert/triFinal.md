# `Metatheorems.TriangleBoundDemo.triFinal`

9 steps.

| # | Formula | Justification |
|---:|---|---|
| 1 | `0 =₀ 0` | reflexivity |
| 2 | `(∀ᶠ x₁ : nat, triB) →ᶠ subst0 triB triWit` | ∀-axiom [triWit] |
| 3 | `subst0 triB triWit →ᶠ ∃ᶠ x₁ : nat, triB` | ∃-axiom [triWit] |
| 4 | `(∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | syllogism 2, 3 |
| 5 | `((∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB) ∧ᶠ TriangleBoundDemo.triDummy →ᶠ (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | ∧-weakening |
| 6 | `((∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB) →ᶠ TriangleBoundDemo.triDummy →ᶠ (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | exportation 5 |
| 7 | `TriangleBoundDemo.triDummy →ᶠ (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | modus ponens 4, 6 |
| 8 | `0 =₀ 0 →ᶠ ∀ᶠ x₀ : pTy, (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | ∀-rule 7 |
| 9 | `∀ᶠ x₀ : pTy, (∀ᶠ x₁ : nat, triB) →ᶠ ∃ᶠ x₁ : nat, triB` | modus ponens 1, 8 |
