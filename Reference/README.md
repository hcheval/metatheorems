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
| `Mine.lean` | An early sketch of bound extraction by composition — `Bnd Q` as a bound plus its verification, one combinator per proof rule. Superseded in practice by the real Dialectica extraction in `Metatheorems/Dialectica/`, kept because the combinator framing reads more directly than the interpretation does. Status not decided. |

The *probes* went the other way: `Probe.lean` and `ProbeR1.lean` became
`Metatheorems/Probes/P1.lean` and `R1.lean`, imported by the library, because they assert
facts about the real encoding by `rfl` and so are live regression tests rather than prose.
