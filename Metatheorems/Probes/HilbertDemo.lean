/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Hilbert

/-!
# Demo driver for `#hilbert`

Not imported by `Metatheorems.lean`. Building this module regenerates every listing at the top
level of `hilbert-out/`.

Every invocation here is at the **default** opacity, and that is the point: this file is the
regression control for `depth`, which was added on 2026-09-07. Its eight listings are
byte-identical before and after that change. The `depth`/`keeping` ladder, and what it costs,
is `Probes/HilbertDepth.lean` — including the finding that `seq_id` alone is what makes the
proof-mode layer unexpandable.
-/

namespace Metatheorems

-- Tiny: a three-line combinator, fully expanded.
#hilbert I_comb all

-- Small: the S combinator, with its helper `eval_h` cited rather than expanded …
#hilbert S_comb

-- … expanding just that one helper …
#hilbert S_comb unfolding eval_h pair_h to "hilbert-out/S_comb_eval_h"

-- … and with everything expanded, to show the difference.
#hilbert S_comb all to "hilbert-out/S_comb_full"

-- Medium: contraction, whose docstring in PropositionalLemmas.lean carries a hand-written
-- version of the same table.
#hilbert contract all

-- A real arithmetic proof.
#hilbert add_comm

-- A proof-mode proof, with proof-mode steps opaque (the default). `mct_p2` is a four-line
-- wrapper; `mct_body` is where the dichotomy derivation actually is, and reads as the
-- tactic script that produced it.
#hilbert ProofMode.mct_p2
#hilbert ProofMode.mct_body

end Metatheorems
