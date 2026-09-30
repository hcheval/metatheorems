# ProofMode/RealMCTLazy.lean

## module header

Reused from `p2`: `leIdx_dne`, `budget_zero_R`, `budget_succ_R`, `one_R_le_budget`,
`rmnorm`, and from `MCTLemmas` `window_drop`, `antitone_chain_R`, `le_R_zero_add`,
`le_R_add_cancel_r_core`. No new ℝ lemma was needed: the one algebraic step,
`x +ℝ (q +ℝ ε) ≤ℝ (x +ℝ ε) +ℝ q`, is `add_comm_R_core` under `le_R_add_mono_l_core` then
`add_assoc_R_core`, each through `le_R_of_eq_R_core` (a nested Lean-level `leRt`/`leR_mono_l`
does not work here: the `xₖ` tokens inside it have no goal context to resolve against). `real_mct_bound_p1` is the metatheorem applied (named, not evaluated —
ARCHITECTURE §14.7's two blockers apply as for `p2`).
