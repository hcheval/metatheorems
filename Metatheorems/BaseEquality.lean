/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers

namespace Metatheorems

/-!
# Equality at a base type is an equivalence relation

`eqAtType (.base i) s t` is *defined* as `d_i(s,t) =ℝ 0ℝ`. That it is reflexive, symmetric
and transitive is therefore a **theorem**, not an assumption — but proving it needs
symmetry and transitivity of `=ℝ`, which live in `RealNumbers.lean`. So it cannot be done
where `eqAtType_refl`/`sym`/`trans` are defined (`Arithmetic.lean`), which sits *below* the
real-number layer because ℚ and ℝ depend on it.

That is the one genuine stratification the `Term.dist` design forces, and this file is where
it is discharged:

* `Arithmetic.lean` proves `eqAtType_sym`/`eqAtType_trans` for **eq-base-free** types (an
  `autoParam` on `Ty.eqBaseFree`, so the ~164 ℚ/ℝ call sites are unchanged);
* this file proves the **base** cases, which is everything the earlier ones exclude;
* nothing in between needs them.

`eqAtType_refl` needs nothing from here: at a base type it is literally the constructor
`Derivable.dist_self`.

See ARCHITECTURE.md §1 and §8.
-/

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {al : Allowed} {Premises : PremiseSet F}

/-- Reflexivity of equality at a base type — `d_i(t,t) =ℝ 0ℝ`, i.e. the `dist_self`
constructor, restated in `eqAtType` form. -/
def eqAtType_refl_base {Γ : Ctx ι} (i : ι) (t : Term F Γ (Ty.base i)) :
    Derivable F al Premises (eqAtType (Ty.base i) t t) :=
  .dist_self i t

/-- Symmetry of equality at a base type.

`dist_comm` gives `d(s,t) =ℝ d(t,s)`; `eq_R_sym_core` turns that around, and
`eq_R_trans_core` chains it with the hypothesis `d(s,t) =ℝ 0ℝ`. Nothing beyond the two
already-proved `=ℝ` facts is needed — in particular none of the open ordered-field axioms. -/
def eqAtType_sym_base {Γ : Ctx ι} (i : ι) (s t : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (eqAtType (Ty.base i) s t →ᶠ eqAtType (Ty.base i) t s) :=
  let dst : Term F Γ (realTy ι) := Term.app2 (Term.dist i) s t
  let dts : Term F Γ (realTy ι) := Term.app2 (Term.dist i) t s
  -- d(t,s) =ℝ d(s,t), from the axiom via symmetry of =ℝ
  let hrev : Derivable F al Premises (eq_R dts dst) :=
    .mp (.dist_comm i s t) (eq_R_sym_core dst dts)
  -- d(t,s) =ℝ d(s,t)  ∧  d(s,t) =ℝ 0ℝ  →  d(t,s) =ℝ 0ℝ
  let htr : Derivable F al Premises
      (eq_R dts dst ∧ᶠ eq_R dst Term.zero_R →ᶠ eq_R dts Term.zero_R) :=
    eq_R_trans_core dts dst Term.zero_R
  -- discharge the left conjunct, which is already proved
  .syllogism (pair_h (weaken_intro_h hrev) (.syllogism .and_contract .and_weak)) htr

end Metatheorems
