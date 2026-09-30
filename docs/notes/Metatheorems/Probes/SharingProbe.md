# Probes/SharingProbe.lean

## module header

## RESULT (2026-09-06): the `let`-sharing experiment changes NOTHING. Hypothesis refuted.

`Dialectica/Monotone.lean` on this branch binds each repeated sub-majorant once with `let`
(`MRealizer.syllogism`: `hAB.val n e` was used 3× and `hBC.val n e` 2×;
`MRealizer.exportation`: `h.val n e` 3×; `MRealizer.forallRule`: the closure and the two
type equations). The change is definitionally transparent — **no proof needed editing**, the
full build is green (8110 jobs) and every axiom list is unchanged.

Kernel type-checking time of `theorem wk : (5 : ℕ) = wit k 5 := by kernel_rfl`
(`set_option profiler true`, 12 GB cap, machine shared with three other Lean builds; the
before/after runs are interleaved on the same machine, `Monotone.lean` reverted in between so
that the only difference is the `let`s):

| k (syllogisms in the chain) | 0 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| kernel, **before** | <0.1 s | 0.16 s | 0.71 s | 2.9 s | 9.4 s | `std::bad_alloc` @ 12 GB |
| kernel, **after**  | <0.1 s | 0.17 s | 0.65 s | 2.8 s | 11.7 s | `std::bad_alloc` @ 12 GB |
| evaluator (`#eval`), **before** | 14.1 s¹ | 0.22 s | — | — | — | — |
| evaluator (`#eval`), **after**  | 13.5 s¹ | 0.22 s | — | — | — | — |

¹ the first `#eval` in the module pays the interpreter/JIT warm-up; `wit 1` and `wit 2` are
0.22 s each on both sides. `#eval wit 4 5` produced **no result in 50 minutes** (CPU-bound at
100 %, RSS flat at 7 GB) before and after — so the evaluator's own wall is at k ≈ 3, exactly
where `ClassicalMfiProbe`'s header put it.

The growth is ≈ ×3.7 per level on both sides, and the OOM is at the same k. **So the ×5 per
level is not closure reconstruction, and `let` at the definition site cannot remove it.**
Two reasons, and they are independent:

1. **Lean's kernel zeta-reduces `let` by substitution.** `whnf` of `let x := v; b` is
   `b[v/x]`, so after one step the three occurrences are back. `let` buys sharing in the
   *compiled* code, never in the kernel — and the kernel is where every `kernel_rfl` bound
   is decided.
2. **The evaluator already shared these values by pointer.** `hAB.val n e` is one closure
   call per level whose *result* call-by-value shares; what does not share is the
   **application** `a.1 xA` — evaluated at a different `xA` in the witness component and in
   the counter component, and again inside the counter's own body. That is the inherent ×2
   the brief asked about, and it is per Dialectica *pair projection*, not per closure.

A fix therefore has to change what is *applied*, not where it is bound: memoise on the
argument (staged evaluation keyed by `(n, e, xA)`), or emit a majorant representation in
which the counter component does not call the witness component at all.
