# Soundness.lean

## module header

* `hdist_self`  — (This is the obstruction `Probes/SoundnessProbe.lean`
                  identified as `probe_beta_needs_dist_self`.)
* `hsep`        — See `eq_of_interp_eqAtType` below: it is
                  a genuine restriction (a proper pseudometric model does *not* satisfy it),
                  and it is exactly what makes the quantifier-free extensionality rule sound
                  in the full set-theoretic type structure.  The weaker, more faithful
                  alternative would be to assume the model is *extensional* — that
                  `funcInterp` and `distInterp` respect `=_X` — and derive the congruence for
                  all terms by induction.  That is strictly more work (a logical relation over
                  `Ty.interpret`) and is not done here; separation implies it.

## Semantics of formula substitution / weakening (section comment)

`Formula.interpret_substF` and `Formula.interpret_subst0` were developed here and have
since been hoisted into `Semantics.lean`, where they belong: they are pure core semantics
and need no imports beyond it.  They are used below exactly as before.
