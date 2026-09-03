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

variable {ι κ : Type} {F : κ → Ty ι}
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

/-- **Non-negativity of the distance**: `⊢ 0_ℝ ≤_ℝ d_i(s,u)`.

Derivable, not assumed. The mathematics is Kohlenbach's one-liner

    `0 =ℝ d(s,s) ≤ℝ d(s,u) +ℝ d(u,s) =ℝ d(s,u) +ℝ d(s,u)`

— `dist_self`, `dist_tri` at `(s,u,s)`, `dist_comm` — followed by
`nonneg_of_add_self_nonneg_core` to halve. What costs work is that `≤ℝ` and `=ℝ` are *tight*
Π₁⁰ statements about `cauchyfy` codes, so the three ingredients must be read at indices far
enough out that the estimate still fits inside `2^{-n}` after the doubling.

The budget, with `Pₖ := 2^{-(n+k)}`, `D̂ₖ := ĉ(d(s,u))(n+k)`, `Êₖ`, `Ŝₖ` likewise for
`d(u,s)` and `d(s,s)`:

* `dist_tri` at `n+3` gives `Ŝ₄ −ℚ (D̂₅ +ℚ Ê₅) <ℚ P₃`, and `dist_self` at `n+3` gives
  `−ℚ Ŝ₄ <ℚ P₃`; together `−ℚ(D̂₅ +ℚ Ê₅) <ℚ P₂`;
* `dist_comm` at `n+4` gives `Ê₅ −ℚ D̂₅ <ℚ P₄`; adding, `−D̂₅ −ℚ D̂₅ <ℚ P₂ +ℚ P₄`;
* moving back from index `n+5` to `n+2` costs `P₂` (`cauchyfy_two_step`) plus `P₅ ≤ P₄`
  (`cauchyfy_cauchy`), i.e. the *same* bound `B := P₂ +ℚ P₄`, twice after doubling.

Total `3B`, and `pow2neg_triple_bound` is exactly the fact that `3B ≤ℚ 2^{-n}` — with
`2^{-(n+4)}` to spare. It is the sole reason index `n+3` is where the triangle inequality is
read: at `n+2` the same accounting overshoots by `2^{-(n+3)}`.

`MetricModel` will want this too, so it is factored out rather than inlined into
`eqAtType_trans_base`. -/
def dist_nonneg {Γ : Ctx ι} (i : ι) (s u : Term F Γ (Ty.base i)) :
    Derivable F al Premises (le_R Term.zero_R (Term.app2 (Term.dist i) s u)) :=
  let sw : Term F (Ty.nat :: Γ) (Ty.base i) := s.weaken
  let uw : Term F (Ty.nat :: Γ) (Ty.base i) := u.weaken
  let dW : Term F (Ty.nat :: Γ) (realTy ι) := Term.app2 (Term.dist i) sw uw
  let eW : Term F (Ty.nat :: Γ) (realTy ι) := Term.app2 (Term.dist i) uw sw
  let sW : Term F (Ty.nat :: Γ) (realTy ι) := Term.app2 (Term.dist i) sw sw
  let m0 : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let m1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ m0
  let m2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ m1
  let m3 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ m2
  let m4 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ m3
  let m5 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ m4
  let d2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy dW m2
  let d4 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy dW m4
  let d5 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy dW m5
  let e5 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy eW m5
  let s4 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy sW m4
  let p0 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q m0
  let p2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q m2
  let p3 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q m3
  let p4 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q m4
  let p5 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q m5
  let c2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q d2
  let c5 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q d5
  let bd : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q p2 p4
  let dd : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.sub_Q c2 c5
  let sm : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q d5 e5
  -- the three axioms, in the extended context
  let htriA : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.all Ty.nat
        (lt_Q (Term.app2 Term.sub_Q
                 (Term.app2 Term.cauchyfy sW.weaken (.app .succ (.var .vz)))
                 (Term.app2 Term.cauchyfy (Term.app2 Term.add_R dW eW).weaken
                   (.app .succ (.var .vz))))
              (.app Term.pow2neg_Q (.var .vz)))) :=
    Derivable.mp
      (Derivable.mp (Derivable.dist_tri i sw uw sw)
        (le_R_of_le_R_pu sW (Term.app2 Term.add_R dW eW)))
      (le_R_all sW (Term.app2 Term.add_R dW eW))
  nonneg_R_of_double_bound (Term.app2 (Term.dist i) s u) (by
    show Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (Term.app2 Term.add_Q c2 c2) p0)
    pmode
    -- triangle inequality at index `n+3`
    pfrom hT := htriA
    pinst hT m3 with hT1
    canorm
    prw (cauchyfy_add_R dW eW m4) in hT1 with hT2
    -- `d(s,s) =ℝ 0` at index `n+3`, as the directed bound `−ℚ Ŝ₄ <ℚ P₃`
    pfrom hS := (Derivable.dist_self i sw)
    pinst hS m3 with hS1
    canorm
    prw (cauchyfy_zero_R m4) in hS1 with hS2
    phave hnegS : lt_Q (.app Term.neg_Q s4) p3
    · papplym (le_lt_Q_trans (.app Term.neg_Q s4)
        (.app Term.abs_Q (Term.app2 Term.sub_Q s4 Term.zero_Q)) p3)
      psplit
      · papplym (le_Q_congr (.app Term.neg_Q s4) (.app Term.abs_Q (.app Term.neg_Q s4))
          (.app Term.neg_Q s4) (.app Term.abs_Q (Term.app2 Term.sub_Q s4 Term.zero_Q))
          (eq_Q_refl_inst (.app Term.neg_Q s4))
          (eqQtrans (abs_Q_neg_Q s4) (abs_Q_congr (eqQsym (sub_Q_zero_Q s4)))))
        pthm (le_Q_self_abs (.app Term.neg_Q s4))
      · pexact hS2
    phave hnegX : lt_Q (.app Term.neg_Q sm) p2
    · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q s4 sm)
          (.app Term.neg_Q s4)) (Term.app2 Term.add_Q p3 p3)
        (.app Term.neg_Q sm) p2
        (sub_add_neg_cancel s4 sm) (pow2neg_Q_halve m2))
      papplym (lt_Q_add_both (Term.app2 Term.sub_Q s4 sm) (.app Term.neg_Q s4) p3 p3)
      psplit
      · pexact hT2
      · pexact hnegS
    -- symmetry at index `n+4`
    pfrom hC := (Derivable.dist_comm i uw sw)
    pinst hC m4 with hC1
    canorm
    phave hED : lt_Q (Term.app2 Term.sub_Q e5 d5) p4
    · papplym (le_lt_Q_trans (Term.app2 Term.sub_Q e5 d5)
        (.app Term.abs_Q (Term.app2 Term.sub_Q e5 d5)) p4)
      psplit
      · pthm (le_Q_self_abs (Term.app2 Term.sub_Q e5 d5))
      · pexact hC1
    phave hX5 : lt_Q (Term.app2 Term.add_Q c5 c5) bd
    · papplym (lt_Q_congr (Term.app2 Term.add_Q (.app Term.neg_Q sm)
          (Term.app2 Term.sub_Q e5 d5)) bd (Term.app2 Term.add_Q c5 c5) bd
        (neg_add_sub_cancel d5 e5) (eq_Q_refl_inst bd))
      papplym (lt_Q_add_both (.app Term.neg_Q sm) (Term.app2 Term.sub_Q e5 d5) p2 p4)
      psplit
      · pexact hnegX
      · pexact hED
    -- moving `d̂` back from index `n+5` to `n+2`
    phave hmv : lt_Q dd bd
    · papplym (lt_Q_congr (Term.app2 Term.sub_Q d5 d2) bd dd bd
        (eqQsym (sub_Q_neg_neg d2 d5)) (eq_Q_refl_inst bd))
      papplym (le_lt_Q_trans (Term.app2 Term.sub_Q d5 d2)
        (.app Term.abs_Q (Term.app2 Term.sub_Q d5 d2)) bd)
      psplit
      · pthm (le_Q_self_abs (Term.app2 Term.sub_Q d5 d2))
      · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q d2 d5)) bd
          (.app Term.abs_Q (Term.app2 Term.sub_Q d5 d2)) bd
          (abs_diff_Q_comm d2 d5) (eq_Q_refl_inst bd))
        papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q d2 d5))
          (Term.app2 Term.add_Q (.app Term.abs_Q (Term.app2 Term.sub_Q d2 d4))
            (.app Term.abs_Q (Term.app2 Term.sub_Q d4 d5))) bd)
        psplit
        · pthm (abs_Q_sub_triangle d2 d4 d5)
        · papplym (lt_le_Q_add (.app Term.abs_Q (Term.app2 Term.sub_Q d2 d4))
            (.app Term.abs_Q (Term.app2 Term.sub_Q d4 d5)) p2 p4)
          psplit
          · pthm (cauchyfy_two_step dW m2)
          · papplym (le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q d4 d5)) p5 p4)
            psplit
            · pthm (Derivable.mp (cauchyfy_cauchy dW m4)
                (lt_Q_imp_le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q d4 d5)) p5))
            · pthm (pow2neg_Q_le_succ m4)
    -- assembly: `2·(−D̂₂) = 2·(−D̂₅) + 2·(−D̂₂ − −D̂₅) < B + (B + B) ≤ 2^{-n}`
    papplym (lt_le_Q_trans (Term.app2 Term.add_Q c2 c2)
      (Term.app2 Term.add_Q bd (Term.app2 Term.add_Q bd bd)) p0)
    psplit
    · papplym (lt_Q_congr
        (Term.app2 Term.add_Q (Term.app2 Term.add_Q c5 c5) (Term.app2 Term.add_Q dd dd))
        (Term.app2 Term.add_Q bd (Term.app2 Term.add_Q bd bd))
        (Term.app2 Term.add_Q c2 c2)
        (Term.app2 Term.add_Q bd (Term.app2 Term.add_Q bd bd))
        (eqQtrans (add_Q_shuffle c5 c5 dd dd)
          (eqQtrans (addQl (add_Q_sub_cancel c2 c5) (Term.app2 Term.add_Q c5 dd))
            (addQr c2 (add_Q_sub_cancel c2 c5))))
        (eq_Q_refl_inst (Term.app2 Term.add_Q bd (Term.app2 Term.add_Q bd bd))))
      papplym (lt_Q_add_both (Term.app2 Term.add_Q c5 c5) (Term.app2 Term.add_Q dd dd)
        bd (Term.app2 Term.add_Q bd bd))
      psplit
      · pexact hX5
      · papplym (lt_Q_add_both dd dd bd bd)
        psplit
        · pexact hmv
        · pexact hmv
    · pthm (pow2neg_triple_bound m0))

/-- **Transitivity of equality at a base type.**

`eqAtType (.base i) s t` is `d(s,t) =ℝ 0ℝ`, so this is: from `d(s,t) =ℝ 0` and
`d(t,u) =ℝ 0`, derive `d(s,u) =ℝ 0`. Three ingredients, all now available:

* `Derivable.dist_tri` gives `d(s,u) ≤ℝ d(s,t) +ℝ d(t,u)` — in `le_R_pu` form, converted by
  `le_R_of_le_R_pu`;
* `add_eq_zero_R_core` turns the two hypotheses into `d(s,t) +ℝ d(t,u) =ℝ 0`;
* `le_zero_eq_zero_R_core` closes it — and its first conjunct, non-negativity, is the
  hypothesis whose absence once made that lemma false. `dist_nonneg` supplies it.

With `eqAtType_refl_base` and `eqAtType_sym_base` this completes the proof that base-type
equality is an equivalence relation — the three fields the deleted `AdmissibleEqX` used to
assume. -/
def eqAtType_trans_base {Γ : Ctx ι} (i : ι) (s t u : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (eqAtType (Ty.base i) s t ∧ᶠ eqAtType (Ty.base i) t u →ᶠ
        eqAtType (Ty.base i) s u) :=
  let dst : Term F Γ (realTy ι) := Term.app2 (Term.dist i) s t
  let dtu : Term F Γ (realTy ι) := Term.app2 (Term.dist i) t u
  let dsu : Term F Γ (realTy ι) := Term.app2 (Term.dist i) s u
  let sum : Term F Γ (realTy ι) := Term.app2 Term.add_R dst dtu
  by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  pfrom hle := Derivable.mp (Derivable.dist_tri i s t u) (le_R_of_le_R_pu dsu sum)
  phave hsum : eq_R sum Term.zero_R
  · papplym (add_eq_zero_R_core dst dtu)
    psplit
    · pexact h1
    · pexact h2
  papplym (le_zero_eq_zero_R_core dsu sum)
  psplit
  · psplit
    · pthm (dist_nonneg i s u)
    · pexact hle
  · pexact hsum

-- Axiom hygiene: base-type equality is an equivalence, with nothing assumed.
#print axioms eqAtType_refl_base
#print axioms eqAtType_sym_base
#print axioms eqAtType_trans_base
#print axioms dist_nonneg

end Metatheorems
