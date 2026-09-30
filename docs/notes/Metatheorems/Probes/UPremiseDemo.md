# Probes/UPremiseDemo.lean

## What the comparison with `WBoundDemo` isolates (the closing comment block)

Held fixed: the model (`WHyperbolicModel`, `WHyperbolic.Premises`, `Allowed.extended`), the
majorants (`M.constMajorants 5 h` with the same `distM` rewrite), the quantified type
`X ×ₜ ℝ`, the witness term `s`, and the outer `forall_rule` + dummy-`refl0` scaffolding.

Changed: only the middle of the implication.

| | `WBoundDemo` | this file |
|---|---|---|
| route | `refl0` ⟶ `exist_ax`, premise weakened away | `forall_ax s` ⟶ `exist_ax s` |
| `U` at `(5,g)` | `0` | `901` |
| `V` at `(5,g)` | `901` | `901` |
| `Φ` at `(5,g)` | `901` | `901` |
| `U` at `(7,g)` | `0` (independent of `x_star`) | `1273` |
| `U` at `(9,g)` | `0` | `1709` |

The last rows are the evidence that `U` here is read off the derivation rather than supplied by
a default: it moves with `x_star` through `WMajorant`'s `max`, which only the instantiation
term reaches.

**The comparison is made airtight by `wUt_is_zero_under_uCm`**, which evaluates `WBoundDemo`'s
`U` under *this* file's `uCm` — the same `ConstMajorants` value, not merely an equal one — so
the `0` and the `901` are produced by one majorant object applied to two derivations. Comparing
the two files' separately-reported numbers would have left open that the majorants differed.

### Controls actually run

* **Permanent, positive**: `uUt_ne_zero` and `uUt_ne_902` are theorems, so `decide` has
  *refuted* both `0` and `902` as values of `U` in every build. `uUt_ne_zero` is the exact
  negation of `WBoundDemo.wUt_is_zero`'s claim for this derivation.
* **Live, run as an edit and reverted** (a control that is not run is not a control): claiming
  `900 = closedMajorizer (uCm M h) (uUt M) ((5, g))`. The `have hval … := rfl` step **still
  succeeded** — so the pipeline really does reduce through `syntactic_soundness`,
  `extractUTerm` and `termMajorizer` to a closed ℕ expression, and the `rfl` is not a
  both-sides-stuck no-op — and then

      Tactic `decide` proved that the proposition
        900 = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)
      is false

  Refutation, not merely "the proof did not go through".

### Cost, measured

Goal `numObjs` at the point of reduction (DAG size; never `sizeWithoutSharing`):

| goal | numObjs | approxDepth |
|---|---|---|
| `uUt_is_901` | 71 | 12 |
| `uVt_is_901` | 71 | 12 |
| `uBound_at_5` | 155 | 23 |

Wall clock, cold `lake build Metatheorems.Probes.UPremiseDemo` with `WHyperbolic` already
built: **17 s** for this module — the same order as `WBoundDemo`'s 23 s, so routing the proof
*through* the premise instead of weakening it away costs nothing measurable. `lake build
Probes` is green at 8111 jobs.
