# Probes/RevTriangleDemo.lean

## `derivSize` does not terminate on any of these (the comment block after `triChain`)

**`derivSize` does not terminate on any of these.** `#eval SizeProbe.derivSize revTri`
(and `triChain`, `revTri'`, `revTriAbs`) dies with `INTERNAL PANIC: out of memory` under
the 12 GB cap *while building the value*: `derivSize` is a tree count and the compiled
evaluator preserves no sharing (`SizeProbe.lean`, finding 1), so a derivation that cites the
proof-mode ℝ-layer lemmas — each `le_R_trans_core` unfolds the `leR_tail` induction, each
`lt_Q_congr` a `lt_Q_of_eq_Q_diff` script, each `add_Q_comm_inst` the closed `add_Q_comm` —
is materialised as a tree far beyond memory. The evals are therefore *not* in this file (a
file of panics is not a green build); the reproduction is the four lines

    #eval SizeProbe.derivSize triChain
    #eval SizeProbe.derivSize revTri
    #eval SizeProbe.derivSize revTri'
    #eval SizeProbe.derivSize revTriAbs

Bracketed from below (scratch runs, 2026-09-05, same cap): `Derivable.dist_tri () x y z`
counts `1`; the single ℚ leaf `zero_lt_pow2neg_Q (.var .vz)` — `0 <ℚ 2^{-n}`, one
instantiation of a closed ℚ theorem — counts **2,963,450**; and the next piece up,
`le_R_of_all dxz dxz` (a 15-line proof-mode script citing a handful of such leaves), already
overflows, as does `le_R_refl_core dxz`. So the reverse triangle inequality, which goes
through `le_R_trans_core` four times, is many orders of magnitude beyond anything a tree
count can reach. `derivSize` is a ruler for raw-constructor derivations (`LemBoundDemo`,
`ConjBoundDemo`); on anything that goes through the ℚ/ℝ tower it is the
`sizeWithoutSharing` CLAUDE.md bans, one layer down.
