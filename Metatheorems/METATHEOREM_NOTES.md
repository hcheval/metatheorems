# Notes on the General Metatheorem (Theorem 6.1)

## Current status

- `general_metatheorem` (extended-system input): **fully proved**
- `general_metatheorem_classical` (classical input): **1 sorry** — witness extraction through ¬¬ layers

## Why the classical version needs prenexification

The paper prenexifies before applying NT + Dialectica:

```
∀x(∀u B₀ → ∃v C₀)  ──prenex──▶  ∀x ∃u,v (B₀ → C₀)
```

This is critical. Without prenexification, the ND interpretation of
`∀x(∀u B₀ → ∃v C₀)` produces entangled witness/counter types:

### Without prenexification (current)

```
NT(A) = ¬¬∀x ¬¬((∀u ¬¬B₀) → (∃v C₀))

W(NT(A)) ≅ ((ρ → ℕ²) → ρ) → (ρ → ℕ²)
C(NT(A)) ≅ (ρ → ℕ²) → ρ

Matrix: ∀ y, B₀(U, y(w(y))) → C₀(V, y(w(y)))
  where V = π₁(w(y)(y(w(y)))), U = π₂(w(y)(y(w(y))))
```

U and V depend on y (the adversary's strategy), not just on x.
This is a game-theoretic entanglement that prevents clean extraction.

### With prenexification (paper's approach)

```
NT(∀x ∃u,v (B₀ → C₀)) simplifies to ∀x ¬¬∃u,v (B₀ → C₀)

W ≅ ρ → ℕ²       C ≅ ρ

Matrix: ∀x. ¬¬(B₀(U(x), x) → C₀(V(x), x))
  where V = π₁(w(x)), U = π₂(w(x))
```

U and V depend only on x. The single ¬¬ on a QF formula is
eliminated classically. Clean Skolem functions, no entanglement.

## Path forward

To prove `general_metatheorem_classical`, we need **prenexification
in the proof system**: a derivation of

```
∀x(∀u B₀ → ∃v C₀) ⊢ ∀x ∃u,v (B₀ → C₀)
```

in `Allowed.classical`. This is classical propositional/quantifier
manipulation (uses LEM to pull ∀ out of the premise of →).

Then compose: classical derivation → prenexify → NT → Dialectica
→ clean extraction → majorize → bound.
