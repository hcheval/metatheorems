/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems

/-!
# The headline theorems, and their axioms, in one place

Not imported by the umbrella (it would print on every build). Check it with

    lake build Metatheorems.Headline

Every `#print axioms` below is the project's claim about that declaration; a change in any
list is a change in what the project asserts. Expected lists:

* object-level derivations and the proof-theoretic core: `[propext, Quot.sound]` or none;
* anything that mentions a model, Mathlib `ℝ`, or Markov's principle:
  `[propext, Classical.choice, Quot.sound]`.

`sorryAx` must never appear.
-/

namespace Metatheorems

/-! ## The kernel: soundness, all 39 constructors -/
#print axioms soundness

/-! ## Majorizability -/
#print axioms all_closed_terms_majorizable
#print axioms termMajorizer_maj

/-! ## The metatheorems, term route -/
#print axioms syntactic_general_metatheorem
#print axioms syntactic_general_metatheorem_classical
#print axioms syntactic_general_metatheorem_at
#print axioms syntactic_general_metatheorem_gen
#print axioms syntactic_general_metatheorem_at_gen
#print axioms syntactic_general_metatheorem_classical_gen
#print axioms syntactic_general_metatheorem_classical_at

/-! ## The metatheorems, monotone functional interpretation -/
#print axioms monotone_soundness
#print axioms monotone_general_metatheorem_at
#print axioms monotone_general_metatheorem_at_gen
#print axioms monotone_nd_soundness
#print axioms monotone_general_metatheorem_classical_at

/-! ## Instantiated at spaces -/
#print axioms MetricModel.metric_metatheorem
#print axioms MetricModel.metric_metatheorem_classical
#print axioms WHyperbolicModel.w_metatheorem
#print axioms CAT0Model.cat0_metatheorem
#print axioms NormedModel.normed_metatheorem

/-! ## Example derivations in the object logic -/
#print axioms ProofMode.mct_p1
#print axioms ProofMode.mct_p2
#print axioms ProofMode.real_mct_p2
#print axioms ProofMode.real_mct_bound_p2
#print axioms ProofMode.real_mct_p1
#print axioms RealMCT.real_mct_of_bound
#print axioms dist_tri_chain
#print axioms dist_rev_tri
#print axioms dist_rev_tri_abs

/-! ## The encoded number systems -/
#print axioms add_Q_assoc
#print axioms distrib_Q
#print axioms cauchy_complete_R
#print axioms le_R_trans_core

end Metatheorems
