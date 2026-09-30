/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Defs

namespace Metatheorems

open Formula

variable {ι κ : Type} {F : κ → Ty ι}
variable {al : Allowed} {Premises : PremiseSet F}

-- `cauchyfy` theory

section Cauchyfy

variable {Γ : Ctx ι}

/-- `Term.weaken_subst0` in the shape simp leaves behind once `Term.weaken` has been
unfolded to `Term.rename`. Without it the last `subst0` of a beta step does not close. -/
private theorem subst0_rename_vs {Γ : Ctx ι} {τ ρ : Ty ι}
    (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (fun {_τ} => Term.subst0_map s) (Term.rename (fun {_τ} => Var.vs) t) = t :=
  Term.weaken_subst0 t s

/-- The body `cauchyfy` compiles to, in the two-variable context `[n, f, …Γ]`. -/
private def cauchyfy_body : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat :=
  .app Term.fst_pair
    (Term.app3 (.prec Ty.nat)
      (Term.app2 Term.pair (.app (.var (.vs .vz)) .zero) .zero)
      (Term.lam (Term.lam
        (Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
          (Term.app3 Term.ite_nat
            (.app Term.sg_bar
              (Term.app2 Term.lt_Q_dec
                (.app Term.abs_Q (Term.app2 Term.sub_Q
                  (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))
                  (.app (.var (.vs (.vs (.vs .vz)))) (.app .succ (.var .vz)))))
                (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
            (Term.app2 Term.pair
              (.app (.var (.vs (.vs (.vs .vz)))) (.app .succ (.var .vz))) .zero)
            (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
              (.app .succ .zero))))))
      (.var .vz))

/-- The one beta step: `cauchyfy f n =₀ fst_pair (state f n)`. Everything else about
`cauchyfy` is reasoning about `cauchyState`, which is an ordinary `prec`. -/
def cauchyfy_unfold (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy f n)
        (.app Term.fst_pair (Term.cauchyState f n))) :=
  have body_eq : (Term.cauchyfy : Term F Γ _) = Term.lam (Term.lam cauchyfy_body) := by rfl
  have nf : ((cauchyfy_body : Term F (Ty.nat :: realTy ι :: Γ) Ty.nat).subst0
      (n.weaken)).subst0 f = .app Term.fst_pair (Term.cauchyState f n) := by
    simp only [cauchyfy_body, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
      Term.cauchy_check_at, Term.subst0, Term.subst, Term.subst0_map, Term.Subst.ext,
      Term.app2, Term.app3, Term.weaken, Term.rename, Term.Renaming.shift,
      subst0_rename_vs, closed_subst]
  body_eq ▸ lam2_correct_nf cauchyfy_body f n nf

/-- Congruence under `fst_pair`. -/
def fst_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.fst_pair s) (.app Term.fst_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.fst_pair (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- Congruence under `snd_pair`. -/
private def snd_pair_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.snd_pair s) (.app Term.snd_pair t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.snd_pair (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- The recursion's base case, as a statement about the state. -/
def cauchyState_zero (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.eq0 (Term.cauchyState f Term.zero) (Term.cauchyBase f)) :=
  Derivable.rec_zero (ρ := Ty.nat) (y := Term.cauchyBase f) (z := Term.cauchyStep f)

/-- The recursion's step, as a statement about the state. -/
def cauchyState_succ (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.cauchyState f (.app .succ n))
        (Term.app2 (Term.cauchyStep f) (Term.cauchyState f n) n)) :=
  Derivable.rec_succ (ρ := Ty.nat) (y := Term.cauchyBase f) (z := Term.cauchyStep f) (x := n)

/-- The body of `cauchyStep`, in the two-variable context `[k, st, …Γ]`. -/
private def cauchyStep_body (f : Term F Γ (realTy ι)) :
    Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
  Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
    (Term.app3 Term.ite_nat
      (.app Term.sg_bar (Term.cauchy_check_at (f.weaken.weaken) (.var .vz)))
      (Term.app2 Term.pair
        (.app (f.weaken.weaken) (.app .succ (.var .vz))) .zero)
      (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
        (.app .succ .zero)))

/-- One step of the recursion, beta-reduced. -/
def cauchyStep_unfold (f : Term F Γ (realTy ι)) (st k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 (Term.cauchyStep f) st k)
        (Term.app3 Term.ite_nat (.app Term.snd_pair st) st
          (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f k))
            (Term.app2 Term.pair (.app f (.app .succ k)) .zero)
            (Term.app2 Term.pair (.app Term.fst_pair st) (.app .succ .zero))))) :=
  have body_eq : Term.cauchyStep f = Term.lam (Term.lam (cauchyStep_body f)) := by rfl
  have nf : (((cauchyStep_body f).subst0 (k.weaken)).subst0 st) =
      Term.app3 Term.ite_nat (.app Term.snd_pair st) st
        (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f k))
          (Term.app2 Term.pair (.app f (.app .succ k)) .zero)
          (Term.app2 Term.pair (.app Term.fst_pair st) (.app .succ .zero))) := by
    simp only [cauchyStep_body, Term.cauchy_check_at, Term.subst0, Term.subst,
      Term.subst0_map, Term.app2, Term.app3, Term.weaken, Term.Renaming.shift,
      subst0_rename_vs, closed_subst]
  body_eq ▸ lam2_correct_nf (cauchyStep_body f) st k nf

/-- The step, with the state's two components exposed. -/
def cauchyState_succ_unfold (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.cauchyState f (.app .succ n))
        (Term.app3 Term.ite_nat (.app Term.snd_pair (Term.cauchyState f n))
          (Term.cauchyState f n)
          (Term.app3 Term.ite_nat (.app Term.sg_bar (Term.cauchy_check_at f n))
            (Term.app2 Term.pair (.app f (.app .succ n)) .zero)
            (Term.app2 Term.pair (.app Term.fst_pair (Term.cauchyState f n))
              (.app .succ .zero))))) :=
  qtrans (cauchyState_succ f n) (cauchyStep_unfold f (Term.cauchyState f n) n)

/-- Once the flag is set the state freezes. -/
def cauchyState_frozen (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n)) (Term.cauchyState f n)) := by
  pmode
  pintro h
  prw (cauchyState_succ_unfold f n)
  prwby h
  pthm (ite_nat_one (Term.cauchyState f n) _)

/-- Flag clear and the Cauchy check passing at `n`: the next value is `f (n+1)`. -/
def cauchyState_advance (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) .zero
        ∧ᶠ Formula.eq0 (.app Term.sg_bar (Term.cauchy_check_at f n)) (.app .succ .zero) →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n))
         (Term.app2 Term.pair (.app f (.app .succ n)) .zero)) := by
  pmode
  pintro hyp
  pdestruct hyp with h0 h1
  prw (cauchyState_succ_unfold f n)
  prwby h0
  prwby h1
  pthm (qtrans (ite_nat_zero _ _) (ite_nat_one _ _))

/-- Flag clear and the Cauchy check failing at `n`: the value freezes and the flag is set. -/
def cauchyState_trip (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f n)) .zero
        ∧ᶠ Formula.eq0 (.app Term.sg_bar (Term.cauchy_check_at f n)) .zero →ᶠ
       Formula.eq0 (Term.cauchyState f (.app .succ n))
         (Term.app2 Term.pair (.app Term.fst_pair (Term.cauchyState f n))
           (.app .succ .zero))) := by
  pmode
  pintro hyp
  pdestruct hyp with h0 h1
  prw (cauchyState_succ_unfold f n)
  prwby h0
  prwby h1
  pthm (qtrans (ite_nat_zero _ _) (ite_nat_zero _ _))

/-- The flag starts clear. -/
def cFlag_zero (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f Term.zero)) .zero) :=
  qtrans (snd_pair_congr (cauchyState_zero f))
    (snd_pair_pair (.app f .zero) Term.zero)

/-- The value starts at `f 0`. -/
def cVal_zero (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.fst_pair (Term.cauchyState f Term.zero)) (.app f .zero)) :=
  qtrans (fst_pair_congr (cauchyState_zero f))
    (fst_pair_pair (.app f .zero) Term.zero)

/-- `f̂(0) =₀ f(0)`: cauchyfication does not move the first term. -/
def cauchyfy_zero (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy f Term.zero) (.app f .zero)) :=
  qtrans (cauchyfy_unfold f Term.zero) (cVal_zero f)

-- ── The invariant ──────────────────────────────────────────────────────────
--
-- Everything above is one step of the recursion. This is the induction: at every index the
-- state is in one of exactly two shapes. Without it nothing pins the flag down to `{0,1}`,
-- and `ite_nat` on anything else computes garbage.

/-- The invariant formula, in context `[n, …Γ]`. -/
private def invF (f : Term F Γ (realTy ι)) : Formula F (Ty.nat :: Γ) :=
  (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz))) .zero
      ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz)))
          (.app f.weaken (.var .vz)))
    ∨ᶠ Formula.eq0 (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz)))
        (.app .succ .zero)

/-- The invariant at an explicit index. -/
abbrev invAt (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) : Formula F Γ :=
  (Formula.eq0 (.app Term.snd_pair (Term.cauchyState f s)) .zero
      ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f s)) (.app f s))
    ∨ᶠ Formula.eq0 (.app Term.snd_pair (Term.cauchyState f s)) (.app .succ .zero)

private theorem invF_subst0 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    (invF f).subst0 s = invAt f s := by
  simp only [invF, invAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.subst0, Formula.substF, Term.subst,
    Term.subst0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, subst_subst0_map_weaken, closed_subst]

private theorem invF_substVar0 (f : Term F Γ (realTy ι)) :
    Formula.substVar0 (invF f) (.app .succ (.var .vz)) =
      invAt f.weaken (.app .succ (.var .vz)) := by
  simp only [invF, invAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.substVar0, Formula.substF, Term.subst,
    Term.substVar0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, weaken_substVar0, closed_subst]

/-- **The `cauchyfy` invariant.** At every index the state is in one of exactly two shapes:
either the flag is clear and the value is `f n` verbatim, or the flag is set. Nothing else
about `cauchyfy` can be proved without this — in particular nothing pins the flag down to
`{0, 1}`, and `ite_nat` applied to anything else computes garbage. -/
def cauchy_inv (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (Formula.all Ty.nat (invF f)) :=
  let base : Derivable F al Premises ((invF f).subst0 Term.zero) :=
    invF_subst0 f Term.zero ▸
      Derivable.mp (Derivable.mp (cVal_zero f)
        (Derivable.mp (cFlag_zero f) and_intro)) .or_weak
  let fw : Term F (Ty.nat :: Γ) (realTy ι) := f.weaken
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let step : Derivable F al Premises
      (invF f →ᶠ Formula.substVar0 (invF f) (.app .succ (.var .vz))) :=
    invF_substVar0 f ▸ (by
      pmode
      pintro ih
      pcases ih with hL | hR
      · pdestruct hL with h0 _hv
        pfrom hsg := sg_bar_cases (Term.cauchy_check_at fw nv)
        pcases hsg with hs1 | hs0
        · -- the Cauchy check passes at `n`: the value advances to `f (n+1)`
          pconj h0 hs1 with hboth
          papplym (cauchyState_advance fw nv) in hboth with hst
          pleft
          psplit
          · prwby hst
            pthm (snd_pair_pair (.app fw (.app .succ nv)) Term.zero)
          · prwby hst
            pthm (fst_pair_pair (.app fw (.app .succ nv)) Term.zero)
        · -- the check fails: the flag trips
          pconj h0 hs0 with hboth
          papplym (cauchyState_trip fw nv) in hboth with hst
          pright
          prwby hst
          pthm (snd_pair_pair (.app Term.fst_pair (Term.cauchyState fw nv))
            (.app .succ .zero))
      · -- already tripped: the state freezes, so the flag stays set
        papplym (cauchyState_frozen fw nv) in hR with hst
        pright
        prwby hst
        pexact hR)
  .induction base (univ_gen step)

/-- The invariant at an explicit index. -/
def cauchy_inv_at (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises (invAt f s) :=
  invF_subst0 f s ▸ Derivable.mp (cauchy_inv f) (.forall_ax s)

/-- **`cauchyfy` produces a Cauchy sequence**, for *any* `f` whatsoever:
`|f̂(n) −ℚ f̂(n+1)|ℚ <ℚ 2^{-(n+1)}`. Stated on the state's value component; `cauchyfy_unfold`
turns it into a statement about `cauchyfy` itself.

Three cases, all supplied by the invariant: the check passed at `n` (so the two values are
`f n` and `f (n+1)`, and the check *is* the inequality), the check failed at `n`, or the flag
was already set — in the latter two the value does not move and the difference is `0`. -/
def cauchyState_cauchy (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (.app Term.fst_pair (Term.cauchyState f n))
              (.app Term.fst_pair (Term.cauchyState f (.app .succ n)))))
            (.app Term.pow2neg_Q (.app .succ n))) := by
  pmode
  pfrom hinv := cauchy_inv_at f n
  pcases hinv with hL | hR
  · pdestruct hL with h0 hv
    pfrom hsg := sg_bar_cases (Term.cauchy_check_at f n)
    pcases hsg with hs1 | hs0
    · pconj h0 hs1 with hboth
      papplym (cauchyState_advance f n) in hboth with hst
      prwby hst
      prw (fst_pair_pair (.app f (.app .succ n)) Term.zero)
      prwby hv
      papplym (sg_bar_eq_S0_implies_zero (Term.cauchy_check_at f n)) in hs1 with hchk
      pexact hchk
    · pconj h0 hs0 with hboth
      papplym (cauchyState_trip f n) in hboth with hst
      prwby hst
      prw (fst_pair_pair (.app Term.fst_pair (Term.cauchyState f n)) (.app .succ .zero))
      pthm (lt_Q_abs_sub_self (.app Term.fst_pair (Term.cauchyState f n)) (.app .succ n))
  · papplym (cauchyState_frozen f n) in hR with hst
    prwby hst
    pthm (lt_Q_abs_sub_self (.app Term.fst_pair (Term.cauchyState f n)) (.app .succ n))

-- ── `cauchyfy` is the identity on sequences that are already Cauchy ────────

/-- "The flag never trips and the value is `f n`", in context `[n, …Γ]`. -/
private def idF (f : Term F Γ (realTy ι)) : Formula F (Ty.nat :: Γ) :=
  Formula.eq0 (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz))) .zero
    ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz)))
        (.app f.weaken (.var .vz))

/-- The same at an explicit index. -/
abbrev idAt (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (.app Term.snd_pair (Term.cauchyState f s)) .zero
    ∧ᶠ Formula.eq0 (.app Term.fst_pair (Term.cauchyState f s)) (.app f s)

private theorem idF_subst0 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    (idF f).subst0 s = idAt f s := by
  simp only [idF, idAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.subst0, Formula.substF, Term.subst,
    Term.subst0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, subst_subst0_map_weaken, closed_subst]

private theorem idF_substVar0 (f : Term F Γ (realTy ι)) :
    Formula.substVar0 (idF f) (.app .succ (.var .vz)) =
      idAt f.weaken (.app .succ (.var .vz)) := by
  simp only [idF, idAt, Term.cauchyState, Term.cauchyBase, Term.cauchyStep,
    Term.cauchy_check_at, Formula.substVar0, Formula.substF, Term.subst,
    Term.substVar0_map, Term.Subst.ext, Term.app2, Term.app3,
    Term.weaken_subst_ext, Term.weaken_var, weaken_substVar0, closed_subst]

/-- **`cauchyfy` is the identity on sequences that already pass the check everywhere.**

The hypothesis is stated at the bound index `x₀` of the context `[n, …Γ]`, which is exactly
where the induction step needs it — so no weakening of a derivation is required, and this is
why the lemma takes a Lean-level argument rather than an object-level antecedent. -/
def cauchyState_id_of_cauchy (f : Term F Γ (realTy ι))
    (hC : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.cauchy_check_at f.weaken (.var .vz)) .zero)) :
    Derivable F al Premises (Formula.all Ty.nat (idF f)) :=
  let base : Derivable F al Premises ((idF f).subst0 Term.zero) :=
    idF_subst0 f Term.zero ▸
      Derivable.mp (cVal_zero f) (Derivable.mp (cFlag_zero f) and_intro)
  let fw : Term F (Ty.nat :: Γ) (realTy ι) := f.weaken
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let hsg : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (.app Term.sg_bar (Term.cauchy_check_at fw nv)) (.app .succ .zero)) :=
    qtrans (sg_bar_congr hC) sg_bar_zero
  let step : Derivable F al Premises
      (idF f →ᶠ Formula.substVar0 (idF f) (.app .succ (.var .vz))) :=
    idF_substVar0 f ▸ (by
      pmode
      pintro ih
      pdestruct ih with h0 _hv
      pfrom hs1 := hsg
      pconj h0 hs1 with hboth
      papplym (cauchyState_advance fw nv) in hboth with hst
      psplit
      · prwby hst
        pthm (snd_pair_pair (.app fw (.app .succ nv)) Term.zero)
      · prwby hst
        pthm (fst_pair_pair (.app fw (.app .succ nv)) Term.zero))
  .induction base (univ_gen step)

/-- The same, at an explicit index. -/
def cauchyState_id_at (f : Term F Γ (realTy ι))
    (hC : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.cauchy_check_at f.weaken (.var .vz)) .zero))
    (s : Term F Γ Ty.nat) :
    Derivable F al Premises (idAt f s) :=
  idF_subst0 f s ▸ Derivable.mp (cauchyState_id_of_cauchy f hC) (.forall_ax s)

/-- Weakening *is* a substitution (`Term.rename_eq_subst`), so the `closed_subst` set
discharges weakening of a closed constant too. -/
theorem zero_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.zero_R : Term F Δ (realTy ι)).weaken (σ := ρ) = Term.zero_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact zero_R_closed_subst _

private theorem one_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.one_R : Term F Δ (realTy ι)).weaken (σ := ρ) = Term.one_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_R_closed_subst _

/-- `f̂(n) =₀ f(n)` for a sequence that already passes the check everywhere. -/
def cauchyfy_id (f : Term F Γ (realTy ι))
    (hC : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0 (Term.cauchy_check_at f.weaken (.var .vz)) .zero))
    (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy f s) (.app f s)) :=
  qtrans (cauchyfy_unfold f s)
    (Derivable.mp (cauchyState_id_at f hC s) and_proj2)

-- ── The two constant sequences ────────────────────────────────────────────

/-- `0_ℝ` is the constant sequence `0_ℚ`. -/
def zero_R_apply (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.zero_R x) Term.zero_Q) :=
  lam_correct_nf (Term.zero_Q : Term F (Ty.nat :: Γ) Ty.nat) x
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- `1_ℝ` is the constant sequence `1_ℚ`. -/
def one_R_apply (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.one_R x) Term.one_Q) :=
  lam_correct_nf (Term.one_Q : Term F (Ty.nat :: Γ) Ty.nat) x
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

-- The check formula is spelled out rather than written with `Term.cauchy_check_at`: `prw`
-- descends through `Term.app`/`app2`/`app3` nodes only, so a named wrapper would hide the
-- applications of `0_ℝ` from the rewrite. It is definitionally the same formula.
private def zero_R_check :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (Term.zero_R : Term F (Ty.nat :: Γ) _) (.var .vz))
            (.app (Term.zero_R : Term F (Ty.nat :: Γ) _) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (zero_R_apply (.var .vz))
  prw (zero_R_apply (.app .succ (.var .vz)))
  pthm (lt_Q_abs_sub_self Term.zero_Q (.app .succ (.var .vz)))

private def one_R_check :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (Term.one_R : Term F (Ty.nat :: Γ) _) (.var .vz))
            (.app (Term.one_R : Term F (Ty.nat :: Γ) _) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (one_R_apply (.var .vz))
  prw (one_R_apply (.app .succ (.var .vz)))
  pthm (lt_Q_abs_sub_self Term.one_Q (.app .succ (.var .vz)))

-- ── The sum of two reals is Cauchy, so `cauchyfy` fixes it ────────────────

/-- `(f +_ℝ g)(x) =₀ f̂(x+1) +_ℚ ĝ(x+1)` — the three beta steps of `add_R`. -/
def add_R_apply (f g : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app3 Term.add_R f g x)
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f (.app .succ x))
          (Term.app2 Term.cauchyfy g (.app .succ x)))) :=
  lam3_correct_nf
    (Term.app2 Term.add_Q
      (Term.app2 Term.cauchyfy (.var (.vs (.vs .vz))) (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy (.var (.vs .vz)) (.app .succ (.var .vz))))
    f g x
    (by
      simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2, Term.Subst.ext,
        Term.weaken_var, subst_subst0_map_weaken, closed_subst])

private theorem add_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.add_R : Term F Δ _).weaken (σ := ρ) = Term.add_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact add_R_closed_subst _

theorem add_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f g : Term F Δ (realTy ι)) :
    (Term.app2 Term.add_R f g).weaken (σ := ρ) =
      Term.app2 Term.add_R f.weaken g.weaken := by
  show Term.app2 (Term.weaken Term.add_R) f.weaken g.weaken = _
  rw [add_R_weaken]

/-- The Cauchy check passes for `f +_ℝ g` at every index: each summand moves by less than
`2^{-(k+2)}`, and the two together by less than `2^{-(k+1)}`. Spelled out rather than written
with `Term.cauchy_check_at`, for the same reason `zero_R_check` is. -/
def add_R_check (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.lt_Q_dec
          (.app Term.abs_Q (Term.app2 Term.sub_Q
            (.app (Term.app2 Term.add_R f.weaken g.weaken) (.var .vz))
            (.app (Term.app2 Term.add_R f.weaken g.weaken) (.app .succ (.var .vz)))))
          (.app Term.pow2neg_Q (.app .succ (.var .vz))))
        .zero) := by
  pmode
  prw (add_R_apply f.weaken g.weaken (.var .vz))
  prw (add_R_apply f.weaken g.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold g.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold f.weaken (.app .succ (.app .succ (.var .vz))))
  prw (cauchyfy_unfold g.weaken (.app .succ (.app .succ (.var .vz))))
  -- Rung 8: the two ends of the transitivity are read off the goal; only the midpoint is
  -- written.
  papply (le_lt_Q_trans _
    (Term.app2 Term.add_Q
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz))))))))
    _)
  psplit
  · pthm (abs_Q_sub_add_split
      (.app Term.fst_pair
        (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))
      (.app Term.fst_pair
        (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz)))))
      (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
      (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz)))))
  · -- Rung 8: `x` and `x'` come from the reflexivity proof and the goal, `y` and `y'` from
    -- the halving equation; nothing is spelled out.
    papply (lt_Q_congr _ _ _ _ (eq_Q_refl_inst _) (pow2neg_Q_halve (.app .succ (.var .vz))))
    -- Rung 8: all four summands are read off the goal.
    papply (lt_Q_add_both _ _ _ _)
    psplit
    · pthm (cauchyState_cauchy f.weaken (.app .succ (.var .vz)))
    · pthm (cauchyState_cauchy g.weaken (.app .succ (.var .vz)))

/-- `(f +_ℝ g)^(s) =₀ f̂(s+1) +_ℚ ĝ(s+1)`: `cauchyfy` is the identity on a sum. -/
def cauchyfy_add_R (f g : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (Term.app2 Term.add_R f g) s)
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f (.app .succ s))
          (Term.app2 Term.cauchyfy g (.app .succ s)))) :=
  qtrans (cauchyfy_id (Term.app2 Term.add_R f g)
      (add_R_app_weaken f g ▸ add_R_check f g) s)
    (add_R_apply f g s)

/-- `0̂_ℝ(n) =₀ 0_ℚ`: the constant sequences are fixed by `cauchyfy`. -/
def cauchyfy_zero_R (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy Term.zero_R s) Term.zero_Q) :=
  qtrans (cauchyfy_id Term.zero_R (zero_R_weaken ▸ zero_R_check) s)
    (zero_R_apply s)

/-- `1̂_ℝ(n) =₀ 1_ℚ`. -/
def cauchyfy_one_R (s : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy Term.one_R s) Term.one_Q) :=
  qtrans (cauchyfy_id Term.one_R (one_R_weaken ▸ one_R_check) s)
    (one_R_apply s)

end Cauchyfy

end Metatheorems
