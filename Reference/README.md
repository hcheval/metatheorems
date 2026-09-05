# Reference material

Mathlib-level files. They are *about* the project but are not part of the object system, and
they are **not built by `lake build`** — each imports `Mathlib` wholesale, which would put the
whole of Mathlib on the library's critical path for no benefit.

That means nothing checks them automatically. If you change something they depend on, they
will not tell you. Build one by hand:

    lake env lean Reference/MCT.lean

| file | what it is |
|---|---|
| `MCT.lean` | Monotone convergence before and after proof mining, in Lean/Mathlib: the textbook statement and proof beside the metastable one. The contrast between `cauchy` and `metastable` is the point — same content, but the second carries a number you can `#eval`, and its bound does not mention the sequence. Documentation for the talk, not input to the formalization. |
| `Mine.lean` | An early sketch of bound extraction by composition — `Bnd Q` as a bound plus its verification, one combinator per proof rule. Superseded in practice by the real Dialectica extraction in `Metatheorems/Dialectica/`, kept as a historical sketch because the combinator framing reads more directly than the interpretation does; not maintained, and not what the project does. |
| `MCTBridge.lean` | (2026-09-05) The `K := 2^k` bridge between ℕ-MCT (`Metatheorems/MCTStatement.lean`, `ProofMode/MCT.lean`) and ℝ-MCT (`MCT.lean`), CLAUDE.md Track A item 4. ℕ-MCT's budget descent on Mathlib with its bound `Φℕ K g = (shift g)^[K] 0` (attained), the coarsening `⌊a n · 2^k⌋₊`, and ℝ-metastability transported through it with bound `(shift g)^[2^k] 0` — **one iterate below `MCT.lean`'s `Φ k g = (shift g)^[2^k+1] 0`**, so the literal identification is off by one. Also the sharp bounds for both the strict and the non-strict real conclusion (`2^k` and `2^k − 1` for `g ≡ 1`). Self-contained (`shift`/`it`/`Φ` copied verbatim); `lake env lean Reference/MCTBridge.lean` checks it. See `docs/REAL_MCT.md` §6. |

The *probes* went the other way: `Probe.lean` and `ProbeR1.lean` became
`Metatheorems/Probes/P1.lean` and `R1.lean`, imported by the library, because they assert
facts about the real encoding by `rfl` and so are live regression tests rather than prose.
