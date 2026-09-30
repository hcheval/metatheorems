# QValBridgeMul.lean

## module header

`QValBridge.lean` stops at `add_R`, because the metric model needed nothing more. The
W-hyperbolic axioms multiply (`(1−λ)·d(z,x) + λ·d(z,y)`), so this file adds the `mul_Q` rung
and the ℝ-layer evaluations.

Kept in its own module so that the elaboration cost of unfolding `Term.mul_Q`
(590,955 nodes fully reduced) is isolated from `QValBridge.lean`. Method unchanged: one
constant per unfold, S1 lemmas for the rest.
