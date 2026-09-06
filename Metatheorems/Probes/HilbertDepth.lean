/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Hilbert

/-!
# `#hilbert … depth n` — how far into the proof-mode layer a listing can actually go

`Hilbert.lean`'s `shouldUnfold` was a **binary** predicate: `all` unfolded everything except
the whole `Metatheorems.ProofMode` namespace, because unfolding that namespace on a real
derivation never finished. `depth n` replaces it with a fueled one — `n` `ProofMode`
unfoldings along any path, cited by name below that — plus a `keeping` stop set. The design is
`Probes/ExprBound.lean`'s, one level up.

This file is the driver *and* the measurement. Building it regenerates everything under
`hilbert-out/`.

## Results

TO BE FILLED IN BY THE MEASUREMENT RUN.
-/

namespace Metatheorems

-- ============================================================================
-- Controls: the pre-`depth` invocations, unchanged, to show nothing regressed.
-- ============================================================================

#hilbert I_comb all
#hilbert S_comb
#hilbert S_comb unfolding eval_h pair_h to "hilbert-out/S_comb_eval_h"
#hilbert S_comb all to "hilbert-out/S_comb_full"
#hilbert contract all
#hilbert add_comm
#hilbert ProofMode.mct_p2
#hilbert ProofMode.mct_body

-- ============================================================================
-- The ladder on `mct_p2` — four proof-mode nodes, the cheapest real target.
-- ============================================================================

#hilbert ProofMode.mct_p2 depth 1
#hilbert ProofMode.mct_p2 depth 2

end Metatheorems
