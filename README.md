# Proof mining metatheorems in Lean 4

A Lean 4 formalization of weakly extensional Heyting arithmetic in all finite types extended
with abstract spaces, $\mathrm{WE\text{-}HA}^{\omega,X}$, and of the general logical
metatheorems of proof mining [1]. Bounds are extracted from derivations in the formal
system through the monotone functional interpretation [1] and evaluated by the Lean
kernel.

## Contents

- **Formal system.** $\mathrm{WE\text{-}HA}^{\omega,X}$ is defined as a single Hilbert-style
  inductive type. Excluded middle, Markov's principle, independence of premise, the axiom of
  choice and quantifier-free choice are enabled separately for each system.
- **Semantics.** Soundness with respect to the full set-theoretic type structure.
- **Interpretations.** Gödel's Dialectica interpretation, Kuroda's negative translation, and
  the monotone functional interpretation, each with its soundness theorem.
- **Metatheorems.** The general metatheorems for the intuitionistic and the classical system,
  with purely universal premises and purely existential conclusions as in [1].
  The bound is returned as a term rather than an existential.
- **Spaces.** Theories of metric, normed, W-hyperbolic and CAT(0) spaces [1], with
  majorants for their constants. Mathlib metric spaces, normed spaces and inner product spaces
  are models of the corresponding theories.
- **Numbers.** The rationals and the reals are represented inside the system following
  [1]. Their ordered ring axioms, the Archimedean property and Cauchy completeness are
  derived in the system. Division is not defined.
- **Proof mode.** A set of tactics for writing derivations with named hypotheses, rewriting
  and induction. Each tactic produces a derivation in the object system, so the proof mode
  needs no separate soundness proof. See [`docs/TACTICS.md`](docs/TACTICS.md).
- **Examples.** Two proofs of the monotone convergence theorem over ℕ, the monotone
  convergence theorem over ℝ in metastable form, and the reverse triangle inequality in metric
  spaces.

The development contains no `sorry`. `Metatheorems/Headline.lean` prints the axioms used by
each main result.

## Example

The statement below is trivially true, but its proof constructs the witness by induction on
`k`, doubling at each step. The extracted bound on `v` is $2^{k^*} \cdot f^*(0)$ for any
majorant $(k^*, f^*)$ of the input.

```lean
-- ∀ (k, f). (∀u. f (u+1) = f u + f u) → ∃v. f k = v
def doubling : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (…) :=
  Examples.Doubling.derivation

-- the monotone realizer of the derivation
def doublingR := monotone_soundness PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm doubling

-- evaluated by the kernel at k* = 3, f* = (n ↦ n + 1): 2³ · 1 = 8
theorem exp_V_3 : (8 : ℕ) = mfiV cm doublingR (xs 3) := by kernel_rfl
```

The derivation is in `Metatheorems/Examples/Doubling.lean`. The evaluated bounds, together
with checks that reject incorrect values, are in `Metatheorems/Probes/DemoChecks.lean`.

## Limitations

- Bounds from derivations of up to a few hundred inference steps evaluate to numerals. For
  larger derivations, including the proofs of the monotone convergence theorem, the bound is
  constructed and type-checks but cannot be evaluated within memory. The composition
  combinators recompute their sub-majorants instead of sharing them, so the cost of evaluation
  grows exponentially with the nesting depth of the derivation. The same limitation currently
  prevents evaluating bounds from classical derivations.
- Extracted bounds are not simplified and are much larger than bounds obtained by hand.
- [`docs/RESULTS.md`](docs/RESULTS.md) lists the extracted bounds and the cases that do not
  evaluate.

## Building

The project uses Lean 4.28 and Mathlib. Exact versions are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build           # the library
lake build Probes    # examples and measurements
```

## Documentation

- [`ARCHITECTURE.md`](ARCHITECTURE.md): design decisions and the alternatives considered.
- [`docs/notes/`](docs/notes/): notes on individual modules.

## References

[1] U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and Their Use in
Mathematics*, Springer Monographs in Mathematics, Springer, 2008.

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
