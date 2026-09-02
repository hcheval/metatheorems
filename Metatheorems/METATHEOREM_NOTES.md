# Notes on the General Metatheorem (Theorem 6.1)

## Current status

- `general_metatheorem` (extended-system input): **fully proved**
- `general_metatheorem_classical` (classical input): **fully proved** as of 2026-09-02,
  `[propext, Classical.choice, Quot.sound]`, via the prenexified route described below.
  The old skeleton (direct ND interpretation, default challenges) is deleted.

### How the classical version is actually proved

`prenexify` under `∀x` (`forall_map`) → `negTrans_sound` → `nn_all_nn` (pushes the outer `¬¬`
inside the `∀`; it was `private`, now public) → `castAllowed` to `Allowed.extended` →
`dialectica_soundness_ctx'`.

The one `¬¬` that survives is discharged **semantically**, by `Classical.not_not` on the
matrix, not by an object-level Markov step. Markov needs a quantifier-free body and
`∃v(B₀' → C₀')` is not one; collapsing `∃u∃v` to a single `∃w : nat ×ₜ nat` would need
`Term.fst (Term.mkPair a b) = a` as a *derivable* equation, and the proof system has **no
product β-rules** (only `beta_eq` for `lam`), while the Cantor-pairing route has the equations
but drags in `RationalNumbers`. The semantic step is legitimate exactly because
prenexification made the body's matrix quantifier-free and ∨-free, so
`dialecticaMatrix_iff_interpFormula` reduces it *for every counter* and the counter the `¬¬`
layer hands us is irrelevant. `dialectica_soundness_ctx'` already uses `Classical.choice`
(Markov case), so nothing is lost.

One mechanical trap, worth remembering: the realizer must be destructed with
`obtain ⟨w, hw⟩ := …`, not bound with `let`. As a `let`-value it is a huge term and every
later defeq check tries to `whnf` it — a deterministic heartbeat timeout, not a type error.

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
