/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Lean

/-!
# The `mfi_memo` simp set

An attribute cannot be used in the module that declares it (see `SimpSets.lean`), and
`SimpSets.lean` sits below everything — touching it rebuilds the whole tree — so this one
lives in its own module.

`mfi_memo` holds the commutation lemmas that push `monotone_soundness` (the monotone
functional interpretation, `Dialectica/Monotone.lean`) through the proof-mode packaging layer
(`ProofMode/Packing.lean`'s `seq_*`, `Tactics.lean`'s `pm_*`) and through the casts that
`anorm`/`canorm`/`qfer_*_nf`/`seq_cast` leave in a derivation. Populated in
`Dialectica/MonotoneSeq.lean` (2026-09-05, MFI Lane D1), which also tags in the three cast
entries of `Dialectica/MonotoneMemo.lean`.
-/

register_simp_attr mfi_memo
