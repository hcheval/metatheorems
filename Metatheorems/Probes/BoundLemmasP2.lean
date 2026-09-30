/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.MCT
import Metatheorems.Majorizability
import Metatheorems.Probes.BoundProbe

/-!
# Probe: can `termMajorizer` be pushed through `mct_p2` COMPOSITIONALLY?

`Probes/BoundProbe.lean` established that a naive `#eval` of `syntactic_soundness`'s output on
`mct_p2` (even the RAW realizer, before any extraction wrapping) exhausts 8-10 GB — the cost is
inside `syntactic_soundness`'s structural recursion, not in `extractUTerm`'s wrapping.

This file asks the follow-up question `BoundProbe.lean` posed at its end: is there a
COMPOSITIONAL route — named equation lemmas, each unfolding a small bounded amount, citing
sub-lemmas rather than re-deriving — that gets a kernel-checked numeral anyway, the way
`QValBridge.lean` does for `Term.interpret` of the ℚ layer?

NOT imported by `Metatheorems.lean`, per the `Probes/` convention.
-/

namespace Metatheorems
namespace BoundLemmasP2

-- Part 1: the enabling lemmas — PROMOTED OUT OF THIS FILE 2026-09-04

/-! `termMajorizer_rename_gen`, `termMajorizer_weaken` and `termMajorizer_castTy` were written
here and are now in the library: the first two in `Majorizability.lean`, `termMajorizer_castTy`
in `Dialectica/Syntactic.lean`. -/

-- Part 2: CORRECTED — the compositional route does NOT get past the proof-mode layer

/-! **Result: the compositional route does not get past the proof-mode layer.**
`syntactic_soundness`'s pattern match never fires on `mct_p2`, whose argument is the
unexpanded `ProofMode.pm_*` tactic tree rather than a literal `Derivable` constructor. No
claim in this file reaches a numeral. -/

noncomputable def cmE := bezemConstMajorantsEmpty BoundProbe.siE

end BoundLemmasP2
end Metatheorems
