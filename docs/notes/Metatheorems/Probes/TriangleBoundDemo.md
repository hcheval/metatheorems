# Probes/TriangleBoundDemo.lean

## module header

### Why this statement fits, exactly

Three facts, each checked by `rfl` below:

1. `le_R_pu f g` (`Terms/Real.lean`) is *literally* `Formula.all Ty.nat B` for a
   quantifier-free `B` — the Cauchy index `n` is the outer `∀`.
2. `syntactic_general_metatheorem_at_gen` wants
   `Derivable … (Formula.all ρ (Formula.all .nat B →ᶠ Formula.ex .nat C))`, so **the
   metatheorem's own premise variable `u` is that Cauchy index**. Take `B := triB`, the
   quantifier-free body, and `Formula.all .nat triB` *is* the triangle inequality (`triAll_eq`).
3. `Derivable.dist_tri` (`Derivable.lean`) is a **free constructor** — no `.premise`, no proof
   mode — concluding exactly `le_R_pu (d x z) (d x y +ℝ d y z)`.

So `U` is the bound on the index at which the triangle inequality has to be known — "to what
precision" — which is a proof-mining-shaped quantity, and the first `U` in the project that is
not a copy of `V`… except that here it *is* numerically equal to `V`, because the same term is
used on both sides (see `uP`-serves-as-both, inherited from `UPremiseDemo`).

### What is and is not established

**Established.** The pipeline `Derivable → syntactic_soundness → extractedUTerm/VTerm →
closedMajorizer` reduces to a literal numeral through a matrix containing `cauchyfy`, `sub_Q`,
`le_Q_dec` and `pow2neg_Q` under `subst0` — the repo's documented delta-expansion pathology
does **not** bite here, because `U` and `V` are read off the *instantiation term*, not off the
matrix, and `whnf` never enters the matrix. And the second derivation (`triUncond`) is the
first in this project to consume a **space axiom** (`Derivable.dist_tri`) rather than only
logical constructors.

**Not established.** The mathematics is still shallow: the conclusion is the same formula as
the premise, so nothing is *proved about* the space — the file demonstrates that a real
space-axiom premise carries through the extraction, not that a nontrivial theorem does.
Genuine mathematical content still waits on `sInduction` (CLAUDE.md, Track A item 2).

## What this file adds over `UPremiseDemo` (the closing comment block)

### What this file adds over `UPremiseDemo`

| | `WBoundDemo` | `UPremiseDemo` | this file |
|---|---|---|---|
| `ρ` | `X ×ₜ ℝ` | `X ×ₜ ℝ` | `X ×ₜ X` |
| premise matrix | `u =₀ u` | `u =₀ u` | **body of `d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)`** |
| premise-consuming route | no | yes | yes |
| space axiom used | no | no | **yes** (`triUncond`, via `Derivable.dist_tri`) |
| `U` at `(5,5)` | `0` | `901` | `901` |
| `V` at `(5,5)` | `901` | `901` | `901` |

The premise matrix is the substantive change: `U` is now the index at which a *real* statement
about the space must be known, and the `∀n` it bounds is `≤ℝ`'s own Cauchy index rather than a
dummy variable. The QF-matrix metatheorem could not have taken it, since the premise is a
∀-formula; `syntactic_general_metatheorem_at_gen` can.

### The delta-expansion pathology did NOT bite

The matrix contains `le_Q_dec`, `sub_Q`, `cauchyfy` and `pow2neg_Q` under `subst0` — the repo's
documented 28-second trap (`lt_Q_dec_closed_subst`). It costs nothing here, and the reason is
structural rather than lucky: **`U` and `V` are read off the instantiation term, not the
matrix.** `triB.subst0 triWit` appears in `triInst`/`triGen` only as the shared middle formula
of a `syllogism`, where it is matched against itself and never reduced; and `closedMajorizer`
walks `extractedUTerm`, whose leaves are `Term.dist`, `Term.fst`/`snd`, `Term.zeroX`,
`Term.zero`. `whnf` never enters the ℚ constants. No `closed_subst` lemma had to be invoked.

The prediction that this would be the hard part was therefore wrong, and the corrected rule is
worth stating: **the matrix's size is irrelevant to bound extraction whenever the witness and
counter terms do not mention it.** It would bite for a derivation whose *witness* is computed
from the matrix — e.g. anything routed through `matrixTerm`/`sQfer`.

### Controls actually run

* **Permanent, positive**: `triUt_ne_zero`, `triUt_ne_902`, `triUt_ne_900`,
  `triBound_ne_902` — `decide` *refutes* each in every build.
* **Live, run as an edit and then reverted** (a control that is not run is not a control):
  claiming `900 = closedMajorizer (triCm M h) (triUt M) ((5,5))`. The `have hval … := rfl` step
  **still succeeded** — so the pipeline genuinely reduces through `syntactic_soundness`,
  `extractedUTerm` and `termMajorizer` to a closed ℕ expression, and the `rfl` is not a
  both-sides-stuck no-op (trap 12) — and then

      error: Tactic `decide` proved that the proposition
        900 = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)
      is false

  Refutation, not merely "the proof did not go through".
* **Live, on the space axiom itself**: replacing `Derivable.dist_tri () xL yL zL` by
  `Derivable.dist_tri () xL xL zL` (wrong middle point) in `triHyp`. Rejected, with the real
  inequality printed:

      Type mismatch
        Derivable.dist_tri () xL xL zL
      has type
        Derivable WHyperbolic.F ?m ?m
          (le_R_pu (Term.dist () ⬝ xL ⬝ zL)
            (Term.add_R ⬝ (Term.dist () ⬝ xL ⬝ xL) ⬝ (Term.dist () ⬝ xL ⬝ zL)))
      but is expected to have type
        Derivable WHyperbolic.F Allowed.extended WHyperbolic.Premises (∀ᶠ x₁ : nat, triB)

  So `triB` really is the body of the triangle inequality **at the stated three points**, and
  `triAll_eq` is not an accident of some looser matching.
* **In-file, controlled**: `triUncUtB_is_zero` against `triUt_is_901` — **one formula, two
  proofs**, same `triCm M h`, same premise matrix `triB`, `U = 0` vs `901`. This is the one to
  cite. `triUncUt_is_zero` is weaker and its docstring says why: its premise slot holds the
  tautology, so it compares bounds on two different formulas.
* **Cross-file**: `wbound_U_is_zero`, `WBoundDemo`'s `U` under its own majorants.

### Cost, measured

Goal `numObjs` at the point of reduction (DAG size; never `sizeWithoutSharing`, whose ratio
here is ≈10⁵):

| goal | numObjs | approxDepth |
|---|---|---|
| `triUt_is_901` | 66 | 12 |
| `triVt_is_901` | 66 | 12 |
| `triBound_at_5` | 150 | 23 |

Slightly *smaller* than `UPremiseDemo`'s 71/71/155, because `ρ = X ×ₜ X` is a simpler type than
`X ×ₜ ℝ` and the witness spine is shorter (no `W`). The matrix does not appear in these goals
at all — see the previous section.

Wall clock, `lake env lean` on this file with all dependencies built: **21.9 s**, against
`UPremiseDemo`'s 17 s and `WBoundDemo`'s 23 s. The extra ~5 s over `UPremiseDemo` buys nine
numeral theorems (against six) plus the second derivation; per numeral the cost is unchanged.
**So a real space-axiom premise costs nothing measurable over a tautologous one.**
