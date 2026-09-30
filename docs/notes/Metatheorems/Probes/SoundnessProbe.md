# Probes/SoundnessProbe.lean

## module header

VERDICT (everything below compiles, zero `sorry`):

* The congruence question is CHEAP. `eq_R_interp_congr` / `le_R_pu_interp_congr` are
  three-line `simp only`s; they did not exist, and they are the reusable part of this probe.
  One genuinely missing general lemma turned up: `Formula.interpret_substF`, the formula-level
  counterpart of `Term.interpret_substF`. It is 10 lines and any soundness theorem needs it
  (`forall_ax`, `exist_ax`, `qfer`, `induction`, `ac`, `qfac`).
  `Formula.interpret_renameF_gen` (weakening) already exists in `MetatheoremPrereqs.lean`.

* Given soundness, `realize`, `realizeTerm_sound` and `dist_comm_holds` do follow — see
  `probe_realize_truth`, `probe_realize`, `probe_dist_comm`.

* BUT soundness is NOT provable from the two `dist_comm`/`dist_tri` facts alone. See
  `probe_beta_needs_dist_self` at the bottom: the `beta_eq` case at a base type reduces,
  by the very same congruence, to `eq_R (d w w) 0ℝ` — which IS `realize`'s model content.
  So the parameterised soundness would have to take `realize` as a hypothesis, and
  `realize` is therefore not freed. `rec_zero`, `rec_succ` and `qfer` force the same thing;
  `qfer` additionally forces `extract` (it must turn semantic `eqAtType` back into Lean
  equality of interpretations before substituting).
