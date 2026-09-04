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
import Metatheorems.RealNumbers.OrderBounds
import Metatheorems.RealNumbers.Approx
import Metatheorems.RealNumbers.Order
import Metatheorems.RealNumbers.LeOrder
import Metatheorems.RealNumbers.Metric
import Metatheorems.RealNumbers.Interval

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
| `Mul` | `mul_R_apply`, `mul_comm_R`, `mul_one_R`, `mul_R_check`/`cauchyfy_mul_R`, `mul_assoc_R`, `distrib_R` — the multiplicative side, complete |
| `LeOrder` | the **non-strict** order package (2026-09-04): `le_R_refl`, `le_R_trans`, `le_R_of_eq_R_core`, `lt_imp_le_R_core`, `le_R_antisymm_core`, `le_R_congr`, additive monotonicity on either side and two-sided — plus the one-sided telescope `leR_pair_step`/`leR_tail`/`leR_le`/`leR_strict` that transitivity needs. None of this existed before; `≤_ℝ` had only the `Field.lean` conversions, so two `Derivable.dist_tri`s could not be chained |
| `Order` | `lt_irrefl_R`, `lt_add_R`/`lt_mul_pos_R`/`archimedean_R`, `zero_lt_one_R`, `lt_shift*`, `lt_trans_R` — all proved; this row said "(sorried)" until 2026-09-04, two days after they closed |
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
-- The `<_ℝ` shift estimate — the mathematics of `lt_trans_R`.
#print axioms lt_shift1
#print axioms lt_shift
#print axioms lt_shift_at
-- The order axioms (closed 2026-09-03, branch `reals-order`): both `∃`-eliminations at the
-- Lean level via `Derivable.exist_rule` (exit 3 of the old note at `lt_trans_R_core`).
#print axioms lt_trans_R
#print axioms lt_trans_R_core
#print axioms lt_add_R
#print axioms lt_add_R_core
#print axioms lt_mul_pos_R
#print axioms lt_mul_pos_R_core
#print axioms archimedean_R
-- ...and the `OrderBounds.lean` kit they rest on:
#print axioms pow2neg_Q_mul
#print axioms cauchyfy_lb_imp
#print axioms le_Q_mul_o
#print axioms le_Q_add_cancel
-- Two genuinely different lemmas, one per lane, that collided on a name at merge time
-- (2026-09-03): `_r` subtracts the right summand, `_l` the left. See the note in CLAUDE.md's
-- parallel-agent recipe — a name collision across lanes builds cleanly and then fails.
#print axioms le_Q_sub_of_le_add_r
#print axioms le_Q_sub_of_le_add_l
#print axioms neg_Q_antitone
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
-- Kohlenbach §4.1, Lemmas 4.2 and 4.3 (2026-09-03): the approximation layer
-- (`RealNumbers/Approx.lean`) and the two `Metric.lean` results built on it.
#print axioms abs_Q_rev_triangle
#print axioms cauchyfy_const
#print axioms cauchyfy_abs_R
#print axioms cauchyfy_sub_R
#print axioms abs_sub_le_const_R
#print axioms bound_of_abs_sub_le_const
#print axioms approx_le_R
#print axioms approx_le_R_core
#print axioms diag_seq_apply
#print axioms diag_check_bound
#print axioms diag_goal_bound
#print axioms approx_R
#print axioms approx_R_core
#print axioms cauchy_complete_R
-- The `[0,1]` representation (`RealNumbers/Interval.lean`, 2026-09-03): the retraction
-- `clamp01` for CLAUDE.md Track C item C0, and the four results it needs.
#print axioms clamp01_Q_lip
#print axioms clamp01_Q_lip_core
#print axioms sub_Q_mono
#print axioms clamp01_Q_nonneg
#print axioms clamp01_Q_le_one
#print axioms clamp01_check
#print axioms cauchyfy_clamp01
#print axioms clamp01_nonneg
#print axioms clamp01_nonneg_core
#print axioms clamp01_le_one
#print axioms clamp01_le_one_core
#print axioms clamp01_eq
#print axioms clamp01_eq_core
-- The NON-STRICT order package (`RealNumbers/LeOrder.lean`, 2026-09-04). Before it the ℝ
-- layer had reflexivity/transitivity/monotonicity for `<_ℝ` and *nothing* for `≤_ℝ` beyond
-- the `le_R`/`le_R_pu`/bound conversions in `Field.lean`, so two `Derivable.dist_tri`s could
-- not be chained. `BaseEquality.dist_tri_chain` is the first consumer.
#print axioms leR_pair_step
#print axioms leR_tail
#print axioms leR_le
#print axioms leR_strict
#print axioms le_R_refl_core
#print axioms le_R_refl
#print axioms le_R_of_eq_R_core
#print axioms lt_irrefl_R_core
#print axioms lt_imp_le_R_core
#print axioms le_R_trans_core
#print axioms le_R_trans
#print axioms le_R_antisymm_core
#print axioms le_R_congr
#print axioms le_R_add_mono_r_core
#print axioms le_R_add_mono_l_core
#print axioms le_R_add_mono_core

end Metatheorems
