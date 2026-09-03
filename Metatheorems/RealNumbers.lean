/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Defs
import Metatheorems.RealNumbers.Cauchyfy
import Metatheorems.RealNumbers.QBounds
import Metatheorems.RealNumbers.Estimates
import Metatheorems.RealNumbers.Bounds
import Metatheorems.RealNumbers.Field
import Metatheorems.RealNumbers.Negation
import Metatheorems.RealNumbers.Mul
import Metatheorems.RealNumbers.Order
import Metatheorems.RealNumbers.Metric

/-!
# Real Numbers in WE-HA^{ω} — umbrella module

This file used to hold the whole ℝ layer (3,615 lines); a one-character edit cost a 37.5 s
rebuild. It was split on 2026-09-03 into `Metatheorems/RealNumbers/*.lean`, in dependency
order:

| module | content |
|---|---|
| `Defs` | the `closed_subst` lemmas, `cauchyBase`/`cauchyStep`/`cauchyState`, `rTy` |
| `Cauchyfy` | the `cauchyfy` theory: unfolding, the invariant, Cauchy-ness, identity on Cauchy sequences, the constants, `cauchyfy_add_R` |
| `Estimates` | `cauchy_pair_step`, the `canorm` macro, the `eqR_tail`/`eqR_le`/`eqR_strict` telescoping engine, `=_ℝ` as an equivalence, the ℚ helpers, `cauchyfy_cauchy`/`cauchyfy_two_step` |
| `Field` | the additive axioms (`add_zero_R`, `add_comm_R`, `add_assoc_R`), the `le_R`/`le_R_pu` bridges, the ℚ rearrangements |
| `Negation` | `cauchyState_neg`/`cauchyfy_neg`, `add_neg_R`, `cauchyState_congr`/`cauchyfy_congr` |
| `Mul` | `mul_assoc_R`/`mul_one_R`/`distrib_R` (sorried), `mul_R_apply`, `mul_comm_R` |
| `Order` | `lt_irrefl_R`, `lt_add_R`/`lt_mul_pos_R`/`archimedean_R` (sorried), `zero_lt_one_R`, `lt_shift*`, `lt_trans_R` |
| `QBounds` | ℚ-code bounds: `abs_le_encode` (a code dominates its magnitude), `rat_num_le_self`, the encode-parts cluster, `exp2_add`, `sub_lt_of_le` — pure ℚ/ℕ, sits beside `Defs` |
| `Bounds` | `cauchyfy_mag_le`, `abs_R_apply`/`embed_nat_R_apply`, `cauchyfy_embed` — the cauchyfy-level magnitude layer |
| `Metric` | `add_eq_zero_R`, `le_zero_eq_zero_R`, `nonneg_of_add_self_nonneg`, `abs_R_bound`, Kohlenbach §4.1 |

The import graph is deliberately flat below `Field`: `Negation → Mul` is a real dependency
(`mul_comm_R_core` needs `cauchyfy_congr`), but `Order` and `Metric` import only `Field`, so an
edit to `Negation` (the 14 s module) does not cascade into them.

Importing `Metatheorems.RealNumbers` still brings the whole layer into scope, so no other file
in the project changed. Everything is in the `Metatheorems` namespace, as before.
-/

namespace Metatheorems

-- ============================================================================
-- Axiom hygiene: every axiom claimed proved above is checked here
-- ============================================================================
-- A falling `sorry` count is not evidence (CLAUDE.md note 9); these are.

#print axioms eq_R_refl
#print axioms eq_R_sym
#print axioms eq_R_trans
#print axioms add_eq_zero_R
#print axioms add_comm_R
#print axioms add_comm_R_core
#print axioms add_zero_R
#print axioms add_zero_R_core
#print axioms add_assoc_R
#print axioms add_assoc_R_core
#print axioms add_neg_R
#print axioms add_neg_R_core
#print axioms cauchyState_neg
#print axioms cauchyfy_neg
#print axioms cauchyState_congr
#print axioms cauchyfy_congr
#print axioms eq_R_of_cauchyfy_eqQ
#print axioms mul_R_apply
#print axioms mul_R_pointwise_comm
#print axioms mul_comm_R
#print axioms mul_comm_R_core
#print axioms mul_one_R
#print axioms mul_one_R_core
#print axioms mul_one_R_apply
#print axioms mul_one_R_check
#print axioms cauchyfy_mul_one_R
#print axioms mul_Q_one_inst
-- The `<_ℝ` shift estimate. `lt_trans_R` itself is NOT here: it is still `sorryAx`, through
-- `lt_trans_R_core`, and the note there says why. These three are the mathematics of it.
#print axioms lt_shift1
#print axioms lt_shift
#print axioms lt_shift_at
#print axioms cauchyfy_add_R
#print axioms cauchy_pair_step
#print axioms eqR_tail
#print axioms eqR_le
#print axioms eqR_strict
-- The symbolic-shift telescope (2026-09-03) — what `mul_one_R` is built on.
#print axioms cauchyfy_tele
#print axioms cauchyfy_tele_at
#print axioms cauchyfy_shift_le
#print axioms lt_irrefl_R
#print axioms zero_lt_one_R
#print axioms le_zero_eq_zero_R
#print axioms le_zero_eq_zero_R_core
#print axioms nonneg_of_add_self_nonneg
#print axioms nonneg_of_add_self_nonneg_core
-- The ℚ and `cauchyfy` lemmas those two rest on:
#print axioms le_Q_self_abs
#print axioms abs_Q_lt_of_two_sided
#print axioms cauchyfy_two_step
#print axioms le_R_all
#print axioms le_R_of_le_R_pu
#print axioms le_R_pu_of_le_R
#print axioms le_R_of_all
#print axioms pow2neg_triple_bound
#print axioms nonneg_R_of_double_bound
-- The `cauchyfy` theory the remaining axioms rest on:
#print axioms cauchy_inv
#print axioms cauchyState_cauchy
#print axioms cauchyfy_zero
#print axioms cauchyState_id_of_cauchy
#print axioms cauchyfy_zero_R
#print axioms cauchyfy_one_R
-- The code-dominates chain and `abs_R_bound` (2026-09-03):
#print axioms rat_num_le_self
#print axioms abs_le_encode
#print axioms encode_succ
#print axioms exp2_add
#print axioms succ_succ_le_exp2_succ
#print axioms cauchyfy_mag_le
#print axioms cauchyfy_embed
#print axioms abs_R_bound
-- `mul_R` is provably Cauchy (2026-09-03) — REALS_PLAN §1's majorization argument:
#print axioms mul_R_check
#print axioms cauchyfy_mul_R
#print axioms encode_pow2_mul
#print axioms encode_add
#print axioms mul_move_le
#print axioms abs_Q_mul
-- The last two ring axioms (2026-09-03): four `mul_move_le` moves onto a common index,
-- where `mul_Q_assoc_inst` / `distrib_Q_inst` close the gap exactly.
#print axioms mul_assoc_R
#print axioms mul_assoc_R_core
#print axioms distrib_R
#print axioms distrib_R_core

end Metatheorems
