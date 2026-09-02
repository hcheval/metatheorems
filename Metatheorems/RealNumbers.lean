/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RationalNumbers
import Metatheorems.Terms.Real

namespace Metatheorems

/-!
# Real Numbers in WE-HA^{ω}

Real numbers are encoded as rapidly converging Cauchy sequences of rationals.
Following §real-numbers of the reference document, the type of reals is
`1 = 0 → 0` (functions ℕ → ℕ), where `x(n)` encodes a rational approximation
to within 2^{-n}.

## Structure

1. **Cauchyfication**: `cauchyfy` (f ↦ f̂)
2. **Real operations**: `zero_R`, `one_R`, `add_R`, `neg_R`, `sub_R`, `mul_R`, `abs_R`
3. **Real formulas**: `eq_R`, `lt_R`, `le_R`, `le_R_pu`
4. **Ordered field axioms** (sorry'd)
-/

open Formula

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Sections 1-2: term definitions and the ℝ formulas — MOVED
-- ============================================================================
-- `Term.cauchy_check_at`, `cauchyfy`, `zero_R`, `one_R`, `embed_nat_R`, `neg_R`, `add_R`,
-- `sub_R`, `mul_R`, `abs_R`, `round_nat`, and the formulas `eq_R`, `lt_R`, `le_R`,
-- `le_R_pu` now live in `Metatheorems/Terms/Real.lean`.
--
-- This is the file the layering exists for: `eqAtType` at a base type is
-- `eq_R (dist i s t) 0ℝ`, so `eqAtType` must see `eq_R`. Only definitions moved; every
-- proof — the `closed_subst` lemmas, the `cauchyfy` theory, the ordered-field axioms —
-- stays here. See ARCHITECTURE.md.

namespace Term

end Term

-- ============================================================================
-- Closed term substitution lemmas (real-level)
-- ============================================================================

section ClosedSubst
variable {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)

-- `cauchyfy_closed_subst`, `zero_R_closed_subst` and `one_R_closed_subst` MOVED to
-- `Metatheorems/Terms/ClosedSubst.lean` (below `eqAtType`), together with the ℚ block they
-- rest on and with `eq_R_substF` / `le_R_pu_substF`. See that file and ARCHITECTURE.md §7.

@[simp] private theorem embed_nat_R_closed_subst :
    (Term.embed_nat_R : Term F Γ _).subst σ = Term.embed_nat_R := by rfl
@[simp] private theorem neg_R_closed_subst :
    (Term.neg_R : Term F Γ _).subst σ = Term.neg_R := by rfl
@[simp] private theorem add_R_closed_subst :
    (Term.add_R : Term F Γ _).subst σ = Term.add_R := by
  simp only [Term.add_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_Q_closed_subst, cauchyfy_closed_subst]
@[simp] private theorem sub_R_closed_subst :
    (Term.sub_R : Term F Γ _).subst σ = Term.sub_R := by
  simp only [Term.sub_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    add_R_closed_subst, neg_R_closed_subst]
@[simp] private theorem mul_R_closed_subst :
    (Term.mul_R : Term F Γ _).subst σ = Term.mul_R := by
  simp only [Term.mul_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift, Term.ofNat,
    mul_Q_closed_subst, cauchyfy_closed_subst, add_closed_subst]
@[simp] private theorem abs_R_closed_subst :
    (Term.abs_R : Term F Γ _).subst σ = Term.abs_R := by
  simp only [Term.abs_R, Term.subst, Term.Subst.ext, Term.app2,
    Term.weaken, Term.rename, Term.Renaming.shift,
    abs_Q_closed_subst, cauchyfy_closed_subst]

end ClosedSubst

-- ============================================================================
-- The `cauchyfy` recursion, named
-- ============================================================================
--
-- `cauchyfy` is a `prec` over a `pair(value, violation flag)` state, buried under two
-- lambdas. Nothing can be said about it until that state is a term one can name, so these
-- three definitions expose it, and `cauchyfy_unfold` is the single beta step that connects
-- them to `Term.cauchyfy` itself.

namespace Term

variable {Γ : Ctx ι}

/-- The base of `cauchyfy`'s recursion: `pair(f 0, 0)` — value `f 0`, flag clear. -/
def cauchyBase (f : Term F Γ (realTy ι)) : Term F Γ Ty.nat :=
  Term.app2 Term.pair (.app f .zero) .zero

/-- The step of `cauchyfy`'s recursion, as a function of `(state, index)`. -/
def cauchyStep (f : Term F Γ (realTy ι)) :
    Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 Term.ite_nat (Term.app Term.snd_pair (.var (.vs .vz))) (.var (.vs .vz))
      (Term.app3 Term.ite_nat
        (.app Term.sg_bar (cauchy_check_at (f.weaken.weaken) (.var .vz)))
        (Term.app2 Term.pair
          (.app (f.weaken.weaken) (.app .succ (.var .vz))) .zero)
        (Term.app2 Term.pair (Term.app Term.fst_pair (.var (.vs .vz)))
          (.app .succ .zero)))))

/-- The state of the recursion after `n` steps. `cauchyfy f n` is its first component. -/
def cauchyState (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app3 (.prec Ty.nat) (cauchyBase f) (cauchyStep f) n

-- The state's two components are `fst_pair (cauchyState f n)` — the value, which is
-- `cauchyfy f n` — and `snd_pair (cauchyState f n)` — the violation flag, `0` while the
-- Cauchy check has held at every index so far and `1` from the first failure onwards.
-- They are deliberately *not* given names: `prw` finds its pattern by descending through
-- `Term.app`/`app2`/`app3` nodes, and a named wrapper would hide `cauchyState` from it.

end Term

-- ============================================================================
-- Real Number Formulas
-- ============================================================================

-- ============================================================================
-- Key Properties
-- ============================================================================

-- `eq_R_isPurelyUniversal`, `eq_R_substF`, `le_R_pu_isPurelyUniversal` and
-- `le_R_pu_substF` MOVED to `Metatheorems/Terms/ClosedSubst.lean`: `eqAtType`'s base case is
-- `eq_R`, so `eqAtType_substF` (in `Arithmetic.lean`) needs `eq_R_substF` below it.

-- `le_R` is Π₁⁰ (purely universal after unfolding ¬∃ to ∀¬).
-- Note: le_R unfolds to (∃n. body) → ⊥, which is NOT syntactically purely
-- universal in our formula representation. For metric space axioms that need
-- purely universal premises, we would need to reformulate le_R as
-- ∀n. ¬(body) = ∀n. (body → ⊥). This is logically equivalent but
-- syntactically different. See le_R_unfolded below.

-- ============================================================================
-- Rounding: (·)_∘ for embedding [0,∞) into ℕ^ℕ
-- ============================================================================

-- ============================================================================
-- Ordered Field Axioms (Derivable in WE-HA^ω)
-- ============================================================================

-- Following Kohlenbach's condition (m): (ℕ^ℕ, +_ℝ, ·_ℝ, 0_ℝ, 1_ℝ, <_ℝ)
-- is an Archimedean ordered field, provably in WE-HA^ω.

variable {al : Allowed} {Premises : PremiseSet F}

-- Notation: real-typed variables in context
private abbrev rTy := realTy ι
-- In context [rTy, Γ]: f = var vz
-- In context [rTy, rTy, Γ]: f = var (vs vz), g = var vz
-- In context [rTy, rTy, rTy, Γ]: f = var (vs (vs vz)), g = var (vs vz), h = var vz

-- ============================================================================
-- `cauchyfy` theory
-- ============================================================================

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
private def fst_pair_congr {s t : Term F Γ Ty.nat}
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
private theorem zero_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
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

private theorem add_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f g : Term F Δ (realTy ι)) :
    (Term.app2 Term.add_R f g).weaken (σ := ρ) =
      Term.app2 Term.add_R f.weaken g.weaken := by
  show Term.app2 (Term.weaken Term.add_R) f.weaken g.weaken = _
  rw [add_R_weaken]

/-- The Cauchy check passes for `f +_ℝ g` at every index: each summand moves by less than
`2^{-(k+2)}`, and the two together by less than `2^{-(k+1)}`. Spelled out rather than written
with `Term.cauchy_check_at`, for the same reason `zero_R_check` is. -/
private def add_R_check (f g : Term F Γ (realTy ι)) :
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
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q
        (.app Term.fst_pair
          (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))
        (.app Term.fst_pair
          (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz))))))))
    (Term.app2 Term.add_Q
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz))))))))
    (.app Term.pow2neg_Q (.app .succ (.var .vz))))
  psplit
  · pthm (abs_Q_sub_add_split
      (.app Term.fst_pair
        (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))
      (.app Term.fst_pair
        (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz)))))
      (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
      (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz)))))
  · papplym (lt_Q_congr
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
          (.app Term.fst_pair
            (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz))))
          (.app Term.fst_pair
            (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz))))))))
      (Term.app2 Term.add_Q
        (.app Term.pow2neg_Q (.app .succ (.app .succ (.var .vz))))
        (.app Term.pow2neg_Q (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
          (.app Term.fst_pair
            (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz))))
          (.app Term.fst_pair
            (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz))))))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (eq_Q_refl_inst _)
      (pow2neg_Q_halve (.app .succ (.var .vz))))
    papplym (lt_Q_add_both
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState f.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState f.weaken (.app .succ (.app .succ (.var .vz)))))))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (.app Term.fst_pair (Term.cauchyState g.weaken (.app .succ (.var .vz))))
        (.app Term.fst_pair
          (Term.cauchyState g.weaken (.app .succ (.app .succ (.var .vz)))))))
      (.app Term.pow2neg_Q (.app .succ (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.app .succ (.app .succ (.var .vz)))))
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

section OrderedFieldAxioms

variable {Γ : Ctx ι}

-- ── Additive group ──────────────────────────────────────────────────────────

/-- ⊢ ∀f,g : ℝ. f +_ℝ g =_ℝ g +_ℝ f -/
def add_comm_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.add_R (.var .vz) (.var (.vs .vz)))))) :=
  sorry

-- `add_assoc_R` and `add_zero_R` are PROVED, but further down the file: both rest on
-- `cauchyfy_cauchy` / `cauchyfy_two_step`, which are stated after the order axioms. See
-- "The additive axioms `cauchyfy_cauchy` alone settles" below.

-- `add_neg_R` is PROVED, further down: it needs `cauchyfy_neg`, which is an induction on
-- the `cauchyfy` recursion and so sits with the rest of that theory.

-- ── Multiplicative monoid ───────────────────────────────────────────────────

/-- ⊢ ∀f,g : ℝ. f ·_ℝ g =_ℝ g ·_ℝ f -/
def mul_comm_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))
              (Term.app2 Term.mul_R (.var .vz) (.var (.vs .vz)))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. (f ·_ℝ g) ·_ℝ h =_ℝ f ·_ℝ (g ·_ℝ h) -/
def mul_assoc_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))))) :=
  sorry

/-- ⊢ ∀f : ℝ. f ·_ℝ 1_ℝ =_ℝ f -/
def mul_one_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.mul_R (.var .vz) Term.one_R)
              (.var .vz))) :=
  sorry

-- ── Distributivity ──────────────────────────────────────────────────────────

/-- ⊢ ∀f,g,h : ℝ. f ·_ℝ (g +_ℝ h) =_ℝ (f ·_ℝ g) +_ℝ (f ·_ℝ h) -/
def distrib_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))
          (Term.app2 Term.add_R
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (Term.app2 Term.mul_R (.var (.vs (.vs .vz)))
              (.var .vz))))))) :=
  sorry

-- ── Order ───────────────────────────────────────────────────────────────────

/-- ⊢ ∀f : ℝ. ¬(f <_ℝ f) (irreflexivity of <_ℝ) -/
def lt_irrefl_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.neg (lt_R (.var .vz) (.var .vz)))) :=
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  -- `f̂(n+1) −ℚ f̂(n+1) =ℚ 0`, and `2^{-n} ≤ℚ 0` contradicts `0 <ℚ 2^{-n}`.
  let step : Derivable F al Premises
      (le_Q e (Term.app2 Term.sub_Q A A) →ᶠ ⊥ᶠ) :=
    .syllogism
      (le_Q_congr e (Term.app2 Term.sub_Q A A) e Term.zero_Q
        (eq_Q_refl_inst e) (sub_Q_self A))
      (.syllogism (pair_h (weaken_intro_h (zero_lt_pow2neg_Q (.var .vz))) I_comb)
        (lt_Q_le_Q_absurd Term.zero_Q e))
  univ_gen (.exist_rule step)

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g ∧ g <_ℝ h → f <_ℝ h -/
def lt_trans_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        ((lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ lt_R (.var (.vs .vz)) (.var .vz))
          →ᶠ lt_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  sorry

/-- ⊢ ∀f,g,h : ℝ. f <_ℝ g → f +_ℝ h <_ℝ g +_ℝ h -/
def lt_add_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (lt_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          →ᶠ lt_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var .vz))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz)))))) :=
  sorry

/-- ⊢ ∀f,g : ℝ. 0 <_ℝ f ∧ 0 <_ℝ g → 0 <_ℝ f ·_ℝ g -/
def lt_mul_pos_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        ((lt_R Term.zero_R (.var (.vs .vz))
          ∧ᶠ lt_R Term.zero_R (.var .vz))
          →ᶠ lt_R Term.zero_R
            (Term.app2 Term.mul_R (.var (.vs .vz)) (.var .vz))))) :=
  sorry

/-- ⊢ 0_ℝ <_ℝ 1_ℝ -/
def zero_lt_one_R :
    Derivable F al Premises (Γ := Γ)
      (lt_R Term.zero_R Term.one_R) :=
  -- `2^{-0} = 1_ℚ`, and both sides are constant, so the witness is `n = 0`:
  -- `1̂(1) −ℚ 0̂(1) = 1_ℚ −ℚ 0_ℚ = 1_ℚ ≥ℚ 2^{-0}`.
  let pow0 : Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (.app Term.pow2neg_Q Term.zero) Term.one_Q) := by
    pmode
    prw (pow2neg_Q_unfold Term.zero)
    prw exp2_zero
    prw (pd_succ Term.zero)
    prefl
  let body : Derivable F al Premises (Γ := Γ)
      (Formula.eq0
        (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q Term.zero)
          (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy Term.one_R (.app .succ Term.zero))
            (Term.app2 Term.cauchyfy Term.zero_R (.app .succ Term.zero))))
        Term.zero) := by
    pmode
    prw (cauchyfy_one_R (.app .succ Term.zero))
    prw (cauchyfy_zero_R (.app .succ Term.zero))
    prw (sub_Q_one_zero)
    prw pow0
    pthm (le_Q_refl Term.one_Q)
  have nf : (Formula.eq0
      (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy (Term.one_R : Term F Γ _).weaken
            (.app .succ (.var .vz)))
          (Term.app2 Term.cauchyfy (Term.zero_R : Term F Γ _).weaken
            (.app .succ (.var .vz)))))
      Term.zero).subst0 Term.zero =
      Formula.eq0
        (Term.app2 Term.le_Q_dec (.app Term.pow2neg_Q Term.zero)
          (Term.app2 Term.sub_Q
            (Term.app2 Term.cauchyfy Term.one_R (.app .succ Term.zero))
            (Term.app2 Term.cauchyfy Term.zero_R (.app .succ Term.zero))))
        Term.zero := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      subst_subst0_map_weaken, cauchyfy_closed_subst, closed_subst]
  Derivable.mp (nf ▸ body) (Derivable.exist_ax Term.zero _)

-- ── Archimedean property ────────────────────────────────────────────────────

/-- ⊢ ∀f : ℝ. ∃n⁰. f <_ℝ embed_nat(n) -/
def archimedean_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (Formula.ex Ty.nat
          (lt_R (Term.var (.vs .vz))
                (.app Term.embed_nat_R (.var .vz))))) :=
  sorry

-- ── The tightness estimate behind `eq_R_trans` ─────────────────────────────
--
-- `eq_R`'s bound is exactly tight — `2^{-n} = 2·2^{-(n+1)}` — so no route through
-- "|f̂−ĝ| + |ĝ−ĥ| at a common index" closes: every such estimate overshoots by exactly one
-- dyadic step, at *every* choice of index. (REALS_PLAN.md §0.5 records this, and its
-- proposed five-term split does not in fact close either: it collects `2·2^{-(m-1)}` from
-- the two hypotheses where the telescope only returns `2·2^{-m}`.)
--
-- What does work is a *limit* argument made finite:
--
--   1. `cauchy_pair_step`  — one step, strict: `X_q <ℚ 2^{-q} +ℚ X_{q+1}`, where
--      `X_q := |f̂(q) −ℚ ĥ(q)|`. Two strict `cauchyfy` steps at `2^{-(q+1)}` each.
--   2. `eqR_tail`  — iterate it: `∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}`. Induction on `k`.
--   3. `eqR_le`  — squeeze: holding for *every* `k`, that gives `X_{p+1} ≤ℚ 2^{-p}`.
--      `pow2neg_rat_den_le` supplies the index at which the dyadic scale falls below the
--      hypothetical excess. This is where the strict `<` is traded for a non-strict `≤`.
--   4. `eqR_strict`  — spend one *more* step: `X_{n+1} <ℚ 2^{-(n+1)} +ℚ X_{n+2}` with
--      `X_{n+2} ≤ℚ 2^{-(n+1)}` gives `X_{n+1} <ℚ 2^{-n}` — strictly, because step 1 is.
--
-- Steps 3 and 4 together are the finite surrogate for "`|f̂(p) − F| < 2^{-p}` strictly".

/-- Substitution is natural in `cauchyState`. Without this the substitutions an induction
leaves behind cannot be pushed past the recursion without delta-expanding it. -/
@[simp] theorem cauchyState_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ)
    (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    (Term.cauchyState f n).subst σ = Term.cauchyState (f.subst σ) (n.subst σ) := by
  simp only [Term.cauchyState, Term.cauchyBase, Term.cauchyStep, Term.cauchy_check_at,
    Term.subst, Term.Subst.ext, Term.app2, Term.app3, Term.weaken_subst_ext, closed_subst]
  rfl

/-- `f̂(n)`, in the form the `cauchyfy` theory states its facts about. -/
abbrev cV (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  .app Term.fst_pair (Term.cauchyState f n)

/-- `|f̂(n) −ℚ ĥ(n)|ℚ`. -/
abbrev cDiff (f h : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  .app Term.abs_Q (Term.app2 Term.sub_Q (cV f n) (cV h n))

/-- **The one-step estimate.** `|f̂(q) −ℚ ĥ(q)| <ℚ 2^{-q} +ℚ |f̂(q+1) −ℚ ĥ(q+1)|`.

Both `cauchyfy` steps are *strict*, and their sum is exactly `2^{-q}`; carrying that
strictness is the whole reason `eq_R_trans` closes at all. -/
def cauchy_pair_step (f h : Term F Γ (realTy ι)) (q : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (cDiff f h q)
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) (cDiff f h (.app .succ q)))) :=
  let a  : Term F Γ Ty.nat := cV f q
  let a' : Term F Γ Ty.nat := cV f (.app .succ q)
  let b  : Term F Γ Ty.nat := cV h q
  let b' : Term F Γ Ty.nat := cV h (.app .succ q)
  let X : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a')
  let Y : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a' b')
  let Z : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q b' b)
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ q)
  by
  pmode
  pfrom hX := cauchyState_cauchy f q
  pfrom hZ0 := cauchyState_cauchy h q
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q b b')) e Z e
      (abs_diff_Q_comm b b') (eq_Q_refl_inst e)) in hZ0 with hZ
  phave hXZ : lt_Q (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q X Z) (Term.app2 Term.add_Q e e)
      (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q)
      (eq_Q_refl_inst (Term.app2 Term.add_Q X Z)) (pow2neg_Q_halve q))
    papplym (lt_Q_add_both X Z e e)
    psplit
    · pexact hX
    · pexact hZ
  phave htri : le_Q (cDiff f h q) (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
  · papplym (le_Q_trans (cDiff f h q)
      (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y))
    psplit
    · papplym (le_Q_trans (cDiff f h q)
        (Term.app2 Term.add_Q X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b)))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
      psplit
      · pthm (abs_Q_sub_triangle a a' b)
      · papplym (le_Q_add_both X (.app Term.abs_Q (Term.app2 Term.sub_Q a' b))
          X (Term.app2 Term.add_Q Y Z))
        psplit
        · pthm (le_Q_refl X)
        · pthm (abs_Q_sub_triangle a' b' b)
    · papplym (le_Q_congr (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z))
        (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
        (eq_Q_refl_inst (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
        (eqQtrans (addQr X (add_Q_comm_inst Y Z))
          (eqQsym (add_Q_assoc_inst X Z Y))))
      pthm (le_Q_refl (Term.app2 Term.add_Q X (Term.app2 Term.add_Q Y Z)))
  papplym (le_lt_Q_trans (cDiff f h q)
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q X Z) Y)
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q q) Y))
  psplit
  · pexact htri
  · papplym (lt_Q_add_inst (Term.app2 Term.add_Q X Z) (.app Term.pow2neg_Q q) Y)
    pexact hXZ

/-- `q_ord_norm`, with the `cauchyfy` state and the two display abbreviations folded in. -/
macro "canorm" : tactic =>
  `(tactic| (try q_cons_norm
             simp only [cDiff, cV, cauchyState_subst,
               lt_Q, le_Q, eq_Q,
               Formula.subst0, Formula.substVar0, Formula.substF, Formula.neg,
               Term.subst,
               Term.subst0_map_vz, Term.subst0_map_vs,
               Term.substVar0_map_vz, Term.substVar0_map_vs,
               Term.Subst.ext_vz, Term.Subst.ext_vs, Term.weaken_var, Term.app2,
               Term.weaken_subst0, subst_subst0_map_weaken, Term.weaken_subst_ext,
               weaken_substVar0, ProofMode.succVar0, closed_subst]
             try q_cons_norm))

/-- The base of the telescoping induction: `∀p. |f̂(p+1) −ℚ ĥ(p+1)| <ℚ 2^{-p} +ℚ 2^{-p}`. -/
def eqR_hyp (f h : Term F Γ (realTy ι)) : Formula F Γ :=
  Formula.all Ty.nat
    (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (.var .vz))))

/-- **The telescoping induction.** From `eqR_hyp` and the one-step estimate,
`∀k ∀p. X_{p+1} <ℚ 2^{-p} +ℚ 2^{-(p+k)}`.

Each round spends one `cauchyfy` step on each side — together exactly
`2^{-(p+1)} +ℚ 2^{-(p+1)} =ℚ 2^{-p}` — and pushes the residual one index further out. -/
def eqR_tail (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat (Formula.all Ty.nat
        (lt_Q (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
          (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
            (.app Term.pow2neg_Q
              (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))) := by
  pmode
  pintro hh
  pinduction
  · -- base: `2^{-(p+0)}` is `2^{-p}`
    canorm
    pforall
    pspecialize hh with h1
    canorm
    prw (add_zero_r (.var .vz))
    pexact h1
  · pforall
    pintro ih
    canorm
    pforall
    pinst ih (.app .succ (.var .vz)) with ihp
    canorm
    prw (add_succ_l (.var .vz) (.var (.vs .vz))) in ihp with ihp2
    prw (add_succ (.var .vz) (.var (.vs .vz)))
    papplym (lt_Q_congr
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q
          (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))
      (eq_Q_refl_inst _)
      (eqQtrans
        (eqQsym (add_Q_assoc_inst
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
        (addQl (pow2neg_Q_halve (.var .vz))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    papplym (lt_Q_trans_inst
      (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz)))))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))))))
    psplit
    · pthm (cauchy_pair_step f.weaken.weaken h.weaken.weaken
        (.app .succ (.var .vz)))
    · papplym (lt_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (cDiff f.weaken.weaken h.weaken.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q
            (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz)))))))
      pexact ihp2

/-- **The Archimedean squeeze.** The telescoping estimate holds for *every* `k`, so the
strict `<ℚ 2^{-p} +ℚ 2^{-(p+k)}` collapses to a non-strict `≤ℚ 2^{-p}`.

`pow2neg_rat_den_le` supplies the index: if the excess `r := X_{p+1} −ℚ 2^{-p}` were positive,
`2^{-(p + den r)} ≤ℚ 2^{-den r} ≤ℚ r` and the estimate at `k := den r` gives `X <ℚ X`. -/
def eqR_le (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (le_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_tail f h) in hh with hT
  pforall
  pfrom hdic := le_Q_or_lt_Q
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
  pcases hdic with hle | hgt
  · pexact hle
  · pexfalso
    papplym (lt_Q_to_zero_sub (.app Term.pow2neg_Q (.var .vz))
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))) in hgt with hpos
    papplym (pow2neg_rat_den_le (Term.app2 Term.sub_Q
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) in hpos with hd
    pinst hT (.app Term.rat_den (Term.app2 Term.sub_Q
      (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)))) with hT1
    canorm
    pinst hT1 (.var .vz) with hT2
    canorm
    phave hchain : le_Q
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
    · papplym (le_Q_add_l (.app Term.pow2neg_Q (.var .vz))
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (le_Q_trans
        (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))))
        (.app Term.pow2neg_Q (.app Term.rat_den (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz)))))
        (Term.app2 Term.sub_Q
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      psplit
      · pthm (pow2neg_Q_le_add_r (.var .vz)
          (.app Term.rat_den (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      · pexact hd
    phave hXX : lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
                     (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    · papplym (lt_Q_congr
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz))))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (eq_Q_refl_inst _)
        (add_Q_sub_cancel
          (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
          (.app Term.pow2neg_Q (.var .vz))))
      papplym (lt_le_Q_trans
        (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (.app Term.pow2neg_Q (Term.app2 Term.add (.var .vz)
            (.app Term.rat_den (Term.app2 Term.sub_Q
              (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))))))
        (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
          (Term.app2 Term.sub_Q
            (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
            (.app Term.pow2neg_Q (.var .vz)))))
      psplit
      · pexact hT2
      · pexact hchain
    papplym (lt_Q_irrefl_inst
      (cDiff f.weaken h.weaken (.app .succ (.var .vz))))
    pexact hXX

/-- **The strict estimate.** One more `cauchyfy` step on top of the non-strict one: the step
is strict and costs `2^{-(n+1)}`, the squeeze at `n+1` costs `2^{-(n+1)}`, and they sum to
exactly `2^{-n}`. This is where the tightness of `eq_R` is finally paid for. -/
def eqR_strict (f h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eqR_hyp f h →ᶠ
       Formula.all Ty.nat
        (lt_Q (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
              (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro hh
  papplym (eqR_le f h) in hh with hle
  pforall
  pinst hle (.app .succ (.var .vz)) with hle1
  canorm
  papplym (lt_Q_congr
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (.app Term.pow2neg_Q (.var .vz))
    (eq_Q_refl_inst _)
    (pow2neg_Q_halve (.var .vz)))
  papplym (lt_le_Q_trans
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz)))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))))
  psplit
  · pthm (cauchy_pair_step f.weaken h.weaken (.app .succ (.var .vz)))
  · papplym (le_Q_add_l (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (cDiff f.weaken h.weaken (.app .succ (.app .succ (.var .vz))))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    pexact hle1

/-- The base of the induction, from the two `=_ℝ` hypotheses: one triangle inequality at
each index. -/
def eqR_hyp_of (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f g ∧ᶠ eq_R g h →ᶠ eqR_hyp f h) := by
  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  pforall
  pspecialize hfg with h1
  pspecialize hgh with h2
  canorm
  prw (cauchyfy_unfold f.weaken (.app .succ (.var .vz))) in h1 with h1a
  prw (cauchyfy_unfold g.weaken (.app .succ (.var .vz))) in h1a with h1b
  prw (cauchyfy_unfold g.weaken (.app .succ (.var .vz))) in h2 with h2a
  prw (cauchyfy_unfold h.weaken (.app .succ (.var .vz))) in h2a with h2b
  papplym (le_lt_Q_trans
    (cDiff f.weaken h.weaken (.app .succ (.var .vz)))
    (Term.app2 Term.add_Q
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz))))
    (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.var .vz))
      (.app Term.pow2neg_Q (.var .vz))))
  psplit
  · pthm (abs_Q_sub_triangle (cV f.weaken (.app .succ (.var .vz)))
      (cV g.weaken (.app .succ (.var .vz))) (cV h.weaken (.app .succ (.var .vz))))
  · papplym (lt_Q_add_both
      (cDiff f.weaken g.weaken (.app .succ (.var .vz)))
      (cDiff g.weaken h.weaken (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.var .vz)) (.app Term.pow2neg_Q (.var .vz)))
    psplit
    · pexact h1b
    · pexact h2b

/-- Transitivity of `=_ℝ` at explicit reals. -/
def eq_R_trans_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R f g ∧ᶠ eq_R g h →ᶠ eq_R f h) := by
  pmode
  pintro hyp
  papplym (eqR_hyp_of f g h) in hyp with hH0
  papplym (eqR_strict f h) in hH0 with hst
  pforall
  pspecialize hst with hs1
  canorm
  prw (cauchyfy_unfold f.weaken (.app .succ (.var .vz)))
  prw (cauchyfy_unfold h.weaken (.app .succ (.var .vz)))
  pexact hs1

/-- `f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0`, at explicit reals.

`add_R` shifts by one, and `cauchyfy_add_R` says that shift is all it does, so the two
hypotheses are read one index in — where each is bounded by `2^{-(n+1)}`, and the two sum to
exactly `2^{-n}`. No telescoping is needed: unlike `eq_R_trans` this one is not tight. -/
private def add_eq_zero_R_gen (f g u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises
      (eq_R f Term.zero_R ∧ᶠ eq_R g Term.zero_R →ᶠ eq_R u Term.zero_R) := by
  pmode
  pintro hyp
  pdestruct hyp with hf hg
  pforall
  pinst hf (.app .succ (.var .vz)) with hf1
  pinst hg (.app .succ (.var .vz)) with hg1
  canorm
  prw (cauchyfy_zero_R (.app .succ (.app .succ (.var .vz)))) in hf1 with hf2
  prw (cauchyfy_zero_R (.app .succ (.app .succ (.var .vz)))) in hg1 with hg2
  prw (cauchyfy_zero_R (.app .succ (.var .vz)))
  prw hu
  papplym (le_lt_Q_trans
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
      Term.zero_Q))
    (Term.app2 Term.add_Q
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q)))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · papplym (le_Q_congr
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
        (Term.app2 Term.add_Q Term.zero_Q Term.zero_Q)))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
        Term.zero_Q))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (abs_Q_congr (sub_Q_congr
        (eq_Q_refl_inst (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))))
        (add_Q_zero_inst Term.zero_Q)))
      (eq_Q_refl_inst _))
    pthm (abs_Q_sub_add_split Term.zero_Q Term.zero_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz)))))
  · papplym (lt_Q_congr
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.var .vz)))
        (.app Term.pow2neg_Q (.app .succ (.var .vz))))
      (Term.app2 Term.add_Q
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q))
        (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
          Term.zero_Q)))
      (.app Term.pow2neg_Q (.var .vz))
      (eq_Q_refl_inst _)
      (pow2neg_Q_halve (.var .vz)))
    papplym (lt_Q_add_both
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.abs_Q (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken (.app .succ (.app .succ (.var .vz))))
        Term.zero_Q))
      (.app Term.pow2neg_Q (.app .succ (.var .vz)))
      (.app Term.pow2neg_Q (.app .succ (.var .vz))))
    psplit
    · pexact hf2
    · pexact hg2

/-- `f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0`, at explicit reals.

The sum is fed in through `add_eq_zero_R_gen`'s abstract `u` rather than rewritten inside the
goal: `prw` would have to push a substitution through `Term.add_R`, which is the
delta-expansion blow-up CLAUDE.md's build-cost section warns about (measured here: a
heartbeat timeout). As a Lean-level parameter it costs nothing. -/
def add_eq_zero_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R f Term.zero_R ∧ᶠ eq_R g Term.zero_R →ᶠ
       eq_R (Term.app2 Term.add_R f g) Term.zero_R) :=
  add_eq_zero_R_gen f g (Term.app2 Term.add_R f g)
    ((add_R_app_weaken f g).symm ▸
      cauchyfy_add_R f.weaken g.weaken (.app .succ (.var .vz)))

-- ── =_ℝ is an equivalence relation ─────────────────────────────────────────

/-- ⊢ ∀f : ℝ. f =_ℝ f

`eq_R` is not an equation, so this is not `refl`: it says `|f̂(n+1) −ℚ f̂(n+1)|ℚ <ℚ 2^{-n}`,
which is `0 <ℚ 2^{-n}` transported along `abs_Q_sub_self`. -/
def eq_R_refl :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (eq_R (.var .vz) (.var .vz))) :=
  let A : Term F (Ty.nat :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen
    (Derivable.mp (zero_lt_pow2neg_Q (.var .vz))
      (lt_Q_congr Term.zero_Q e (.app Term.abs_Q (Term.app2 Term.sub_Q A A)) e
        (eqQsym (abs_Q_sub_self A)) (eq_Q_refl_inst e))))

/-- ⊢ ∀f,g : ℝ. f =_ℝ g → g =_ℝ f -/
def eq_R_sym :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) (.var .vz) →ᶠ
         eq_R (.var .vz) (.var (.vs .vz))))) :=
  let A : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var (.vs .vz)))) (.app .succ (.var .vz))
  let B : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy (Term.weaken (.var .vz))) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: rTy :: rTy :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  univ_gen (univ_gen (forall_map
    (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A B)) e
        (.app Term.abs_Q (Term.app2 Term.sub_Q B A)) e
      (abs_diff_Q_comm A B) (eq_Q_refl_inst e))))

/-- Symmetry of `=_ℝ` at explicit reals — the `_core` companion of `eq_R_sym`, in the same
style as `eq_R_trans_core` / `add_eq_zero_R_core`.

Instantiating the `∀`-quantified `eq_R_sym` at two terms means pushing two `subst0`s through
`eq_R`; taking the terms as parameters skips that entirely, and the proof is `eq_R_sym`'s own
body with `f`/`g` in place of the two bound variables. Used by
`MetricSpace.admissibleEqX.eqx_sym`. -/
def eq_R_sym_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R f g →ᶠ eq_R g f) :=
  let A : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy f.weaken) (.app .succ (.var .vz))
  let B : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app (Term.app Term.cauchyfy g.weaken) (.app .succ (.var .vz))
  let e : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  forall_map
    (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A B)) e
        (.app Term.abs_Q (Term.app2 Term.sub_Q B A)) e
      (abs_diff_Q_comm A B) (eq_Q_refl_inst e))

/-- ⊢ ∀f,g,h : ℝ. f =_ℝ g ∧ g =_ℝ h → f =_ℝ h -/
def eq_R_trans :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs (.vs .vz))) (.var (.vs .vz))
          ∧ᶠ eq_R (.var (.vs .vz)) (.var .vz)
          →ᶠ eq_R (.var (.vs (.vs .vz))) (.var .vz))))) :=
  univ_gen (univ_gen (univ_gen
    (eq_R_trans_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

-- ── ℚ helpers: `|·|_ℚ` against a two-sided bound ────────────────────────────
--
-- Everything in this block is a ℚ fact; it lives here rather than in
-- `RationalNumbers.lean` only because that file is another workstream's. The two
-- load-bearing ones are `le_Q_self_abs` (`z ≤_ℚ |z|_ℚ`, which is how a *directed*
-- estimate is recovered from a `cauchyfy` bound) and `abs_Q_lt_of_two_sided`
-- (`z <_ℚ c` and `−z <_ℚ c` give `|z| <_ℚ c`, which is how an `eq_R` goal is discharged
-- from a pair of one-sided bounds). Neither existed; REALS_PLAN §0.8 item 1 lists the
-- family as missing.
--
-- The route is `le_Q_of_cross` throughout: it turns a `≤_ℚ` goal into ℕ arithmetic on
-- signed cross products, with no `sub_Q` anywhere.

/-- `0_ℚ −_ℚ x =_ℚ −_ℚ x`. -/
def sub_Q_zero_l (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q Term.zero_Q x) (.app Term.neg_Q x)) :=
  eqQtrans (sub_Q_eq_add_neg Term.zero_Q x)
    (eqQtrans (add_Q_comm_inst Term.zero_Q (.app Term.neg_Q x))
      (add_Q_zero_inst (.app Term.neg_Q x)))

/-- **`z ≤_ℚ |z|_ℚ`**, and no sign case is needed: the cross criterion asks
`posN z · D ≤ (posN z + negN z) · D + negN z · D`, which holds outright. -/
def le_Q_self_abs (z : Term F Γ Ty.nat) :
    Derivable F al Premises (le_Q z (.app Term.abs_Q z)) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  let P : Term F Γ Ty.nat := Term.app2 Term.mul (posN z) D
  let N : Term F Γ Ty.nat := Term.app2 Term.mul (negN z) D
  pmode
  papplym (le_Q_of_cross z (.app Term.abs_Q z))
  prw (negN_abs_Q z)
  prw (posN_abs_Q z)
  prw (rat_den_abs_Q z)
  prw (mul_zero_l D)
  prw (add_zero_l P)
  papplym (monus_le_of_eq_add P
    (Term.app2 Term.add (Term.app2 Term.mul (.app Term.rat_num z) D) N)
    (Term.app2 Term.add N N))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prw (add_mul (posN z) (negN z) D)
  pthm (qtrans (add_assoc P N N) (add_comm P (Term.app2 Term.add N N)))

/-- `|z|_ℚ ≤_ℚ z` when `z`'s negative part vanishes, i.e. when `0 ≤_ℚ z`. -/
def abs_Q_le_self_of_negN_zero (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (negN z) .zero →ᶠ le_Q (.app Term.abs_Q z) z) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  pmode
  pintro h
  papplym (le_Q_of_cross (.app Term.abs_Q z) z)
  prw (rat_den_abs_Q z)
  prw (posN_abs_Q z)
  prw (negN_abs_Q z)
  prw (mul_zero_l D)
  prw (add_zero_r (Term.app2 Term.mul (posN z) D))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prwby h
  prw (add_zero_r (posN z))
  prw (mul_zero_l D)
  prw (add_zero_l (Term.app2 Term.mul (posN z) D))
  pthm (monus_self (Term.app2 Term.mul (posN z) D))

/-- `|z|_ℚ ≤_ℚ −_ℚ z` when `z`'s positive part vanishes, i.e. when `z ≤_ℚ 0`. -/
def abs_Q_le_neg_of_posN_zero (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (posN z) .zero →ᶠ le_Q (.app Term.abs_Q z) (.app Term.neg_Q z)) := by
  let D : Term F Γ Ty.nat := .app Term.rat_den z
  pmode
  pintro h
  papplym (le_Q_of_cross (.app Term.abs_Q z) (.app Term.neg_Q z))
  prw (rat_den_abs_Q z)
  prw (rat_den_neg_Q z)
  prw (posN_abs_Q z)
  prw (negN_abs_Q z)
  prw (negN_neg_Q z)
  prw (posN_neg_Q z)
  prw (mul_zero_l D)
  prw (add_zero_r (Term.app2 Term.mul (negN z) D))
  prw (Derivable.mp (posN_add_negN z) Derivable.sym0)
  prwby h
  prw (add_zero_l (negN z))
  prw (mul_zero_l D)
  prw (add_zero_l (Term.app2 Term.mul (negN z) D))
  pthm (monus_self (Term.app2 Term.mul (negN z) D))

/-- `|z|_ℚ` is bounded by `z` or by `−_ℚ z` — the dichotomy `|z| = max(z, −z)` in the only
form the encoding supports. The case split is on `0 ≤_ℚ z` versus `z <_ℚ 0`, not on the sign
bit, because `le_Q_zero_parts` / `lt_Q_zero_parts` already convert those into the vanishing of
one signed part, and `prw` cannot see inside `posN`/`negN`. -/
def abs_Q_le_cases (z : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (.app Term.abs_Q z) z ∨ᶠ le_Q (.app Term.abs_Q z) (.app Term.neg_Q z)) := by
  pmode
  pfrom hc := le_Q_or_lt_Q Term.zero_Q z
  pcases hc with hnn | hneg
  · pleft
    papplym (le_Q_zero_parts z) in hnn with hz
    papplym (abs_Q_le_self_of_negN_zero z) in hz with hle
    pexact hle
  · pright
    papplym (lt_Q_to_zero_sub z Term.zero_Q) in hneg with h1
    papplym (lt_Q_zero_congr (Term.app2 Term.sub_Q Term.zero_Q z) (.app Term.neg_Q z)
      (sub_Q_zero_l z)) in h1 with h2
    papplym (lt_Q_zero_parts (.app Term.neg_Q z)) in h2 with h3
    pdestruct h3 with h4 _h5
    prw (negN_neg_Q z) in h4 with h6
    papplym (abs_Q_le_neg_of_posN_zero z) in h6 with hle
    pexact hle

/-- **The two-sided bound**: `z <_ℚ c` and `−_ℚ z <_ℚ c` give `|z|_ℚ <_ℚ c`. -/
def abs_Q_lt_of_two_sided (z c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q z c ∧ᶠ lt_Q (.app Term.neg_Q z) c →ᶠ lt_Q (.app Term.abs_Q z) c) := by
  pmode
  pintro hyp
  pdestruct hyp with h1 h2
  pfrom hc := abs_Q_le_cases z
  pcases hc with hA | hB
  · papplym (le_lt_Q_trans (.app Term.abs_Q z) z c)
    psplit
    · pexact hA
    · pexact h1
  · papplym (le_lt_Q_trans (.app Term.abs_Q z) (.app Term.neg_Q z) c)
    psplit
    · pexact hB
    · pexact h2

/-- `¬(a ≤_ℚ b)` gives `b <_ℚ a`. The `≤_ℚ`/`<_ℚ` dichotomy is decidable in the encoding, so
this is `le_Q_or_lt_Q` and needs no Markov step. -/
def lt_Q_of_not_le_Q (a b : Term F Γ Ty.nat) :
    Derivable F al Premises (¬ᶠ(le_Q a b) →ᶠ lt_Q b a) := by
  pmode
  pintro h
  pfrom hc := le_Q_or_lt_Q a b
  pcases hc with hle | hlt
  · pexfalso
    papply h
    pexact hle
  · pexact hlt

/-- Cancelling a common right summand in a `<_ℚ`. `<_ℚ` sees its arguments only through the
`eq_Q` class of their difference, so this is `sub_Q_add_cancel` read backwards. -/
def lt_Q_add_cancel (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) →ᶠ lt_Q a b) :=
  lt_Q_of_eq_Q_diff (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c) a b
    (sub_Q_add_cancel a b c)

/-- …and on the left. -/
def lt_Q_add_cancel_l (c a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (Term.app2 Term.add_Q c a) (Term.app2 Term.add_Q c b) →ᶠ lt_Q a b) :=
  Derivable.syllogism
    (lt_Q_congr (Term.app2 Term.add_Q c a) (Term.app2 Term.add_Q c b)
      (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b c)
      (add_Q_comm_inst c a) (add_Q_comm_inst c b))
    (lt_Q_add_cancel a b c)

-- ── The `cauchyfy` estimates, phrased on `cauchyfy` itself ──────────────────

/-- `cauchyState_cauchy` with `cauchyfy_unfold` applied on both sides:
`|f̂(n) −ℚ f̂(n+1)|ℚ <ℚ 2^{-(n+1)}`. -/
def cauchyfy_cauchy (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f n)
              (Term.app2 Term.cauchyfy f (.app .succ n))))
            (.app Term.pow2neg_Q (.app .succ n))) := by
  pmode
  prw (cauchyfy_unfold f n)
  prw (cauchyfy_unfold f (.app .succ n))
  pthm (cauchyState_cauchy f n)

/-- **Two `cauchyfy` steps**: `|f̂(m) −ℚ f̂(m+2)|ℚ <ℚ 2^{-m}`.

The two steps cost `2^{-(m+1)}` and `2^{-(m+2)}`; relaxing the second to `2^{-(m+1)}` still
leaves the sum `2^{-m}`, so no telescoping induction is needed — this is a *fixed* two-step
estimate, unlike the unbounded one `eq_R_trans` needs. -/
def cauchyfy_two_step (f : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
              (Term.app2 Term.cauchyfy f m)
              (Term.app2 Term.cauchyfy f (.app .succ (.app .succ m)))))
            (.app Term.pow2neg_Q m)) := by
  let a  : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f m
  let a1 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ m)
  let a2 : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f (.app .succ (.app .succ m))
  let X : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a a1)
  let Y : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q a1 a2)
  let e : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ m)
  pmode
  pfrom hX := cauchyfy_cauchy f m
  pfrom hY0 := cauchyfy_cauchy f (.app .succ m)
  phave hY : lt_Q Y e
  · papplym (lt_le_Q_trans Y (.app Term.pow2neg_Q (.app .succ (.app .succ m))) e)
    psplit
    · pexact hY0
    · pthm (pow2neg_Q_le_succ (.app .succ m))
  papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q a a2))
    (Term.app2 Term.add_Q X Y) (.app Term.pow2neg_Q m))
  psplit
  · pthm (abs_Q_sub_triangle a a1 a2)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q X Y) (Term.app2 Term.add_Q e e)
      (Term.app2 Term.add_Q X Y) (.app Term.pow2neg_Q m)
      (eq_Q_refl_inst (Term.app2 Term.add_Q X Y)) (pow2neg_Q_halve m))
    papplym (lt_Q_add_both X Y e e)
    psplit
    · pexact hX
    · pexact hY

-- ── The additive axioms `cauchyfy_cauchy` alone settles ─────────────────────
--
-- `add_zero_R` and `add_assoc_R` are **not tight**, and that is the whole story: the two
-- sides of each are the *same* sum read at indices that differ by a fixed number of
-- `cauchyfy` steps, each step costing `2^{-(index+1)}`, against a budget of `2^{-n}` at the
-- goal's own index `n`. Both close with room to spare, so neither needs the `eqR_le`
-- telescoping engine that `eq_R_trans` needed. (`add_neg_R` is a different matter — see the
-- note at its `sorry`.)
--
-- Each goes through a `_gen` companion taking the composed real as an **abstract Lean
-- parameter**, for the reason `add_eq_zero_R_gen` does: `prw` at a goal containing
-- `Term.add_R` has to push a substitution through that constant, which is the
-- delta-expansion blow-up the build-cost notes warn about. As a parameter it costs nothing,
-- and the `cauchyfy_add_R` chain that computes it is assembled outside the proof mode.

/-- Congruence for `add_Q` in its **first** argument, at the level of `=₀` (not `eq_Q`) —
the mirror image of `RationalNumbers.lean`'s (private) `add_Q_congr_r_nat`. -/
private def addQ_l_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add_Q s u) (Term.app2 Term.add_Q t u)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add_Q (.var .vz) u.weaken)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- Congruence for `add_Q` in its **second** argument, at the level of `=₀`. -/
private def addQ_r_nat (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.add_Q u s) (Term.app2 Term.add_Q u t)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.add_Q u.weaken (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- `u =_ℝ f` for any `u` whose cauchyfication is `f̂(·+2) +ℚ 0̂(·+2)`.

The estimate is a single `cauchyfy` step: `û(n+1) ≃ℚ f̂(n+2)`, and `|f̂(n+2) −ℚ f̂(n+1)|` is
below `2^{-(n+2)}`, hence below `2^{-n}` twice over. -/
private def add_zero_R_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises (eq_R u f) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let A1 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s1
  let A2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s1
  let P2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s2
  pmode
  pforall
  canorm
  prw hu
  prw (cauchyfy_zero_R s2)
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q (Term.app2 Term.add_Q A2 Term.zero_Q) A1)) P
    (abs_Q_congr (sub_Q_congr (eqQsym (add_Q_zero_inst A2)) (eq_Q_refl_inst A1)))
    (eq_Q_refl_inst P))
  papplym (lt_le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P2 P)
  psplit
  · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q A1 A2)) P2
      (.app Term.abs_Q (Term.app2 Term.sub_Q A2 A1)) P2
      (abs_diff_Q_comm A1 A2) (eq_Q_refl_inst P2))
    pthm (cauchyfy_cauchy f.weaken s1)
  · papplym (le_Q_trans P2 P1 P)
    psplit
    · pthm (pow2neg_Q_le_succ s1)
    · pthm (pow2neg_Q_le_succ (.var .vz))

/-- `f +_ℝ 0_ℝ =_ℝ f`, at an explicit real. -/
def add_zero_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises (eq_R (Term.app2 Term.add_R f Term.zero_R) f) :=
  add_zero_R_gen f (Term.app2 Term.add_R f Term.zero_R) (by
    rw [add_R_app_weaken, zero_R_weaken]
    exact cauchyfy_add_R f.weaken Term.zero_R (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. f +_ℝ 0_ℝ =_ℝ f -/
def add_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz) Term.zero_R)
              (.var .vz))) :=
  univ_gen (add_zero_R_core (.var .vz))

/-- `u =_ℝ v` for any `u`, `v` whose cauchyfications are the two bracketings of `f + g + h`.

Writing `Fₖ := f̂(n+k)` and so on, the two sides at the goal's index `n` are
`(F₃ +ℚ G₃) +ℚ H₂` and `F₂ +ℚ (G₃ +ℚ H₃)` — the *same* three summands, with `f` read one
index later on the left and `h` one index later on the right. Re-bracketing the left,
`abs_Q_sub_add_split` twice splits the difference into `|F₃ −ℚ F₂|` and `|H₂ −ℚ H₃|` (the `g`
term cancels exactly), each below `2^{-(n+3)}` by `cauchyfy_cauchy`, so the total is below
`2^{-(n+2)}` — a factor of four inside the budget `2^{-n}`. -/
private def add_assoc_R_gen (f g h u v : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.add_Q
            (Term.app2 Term.cauchyfy f.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz)))))
            (Term.app2 Term.cauchyfy g.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz))))))
          (Term.app2 Term.cauchyfy h.weaken (.app .succ (.app .succ (.var .vz)))))))
    (hv : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy v.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.add_Q
            (Term.app2 Term.cauchyfy g.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz)))))
            (Term.app2 Term.cauchyfy h.weaken
              (.app .succ (.app .succ (.app .succ (.var .vz))))))))) :
    Derivable F al Premises (eq_R u v) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let s3 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s2
  let F2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let F3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s3
  let G3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken s3
  let H2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy h.weaken s2
  let H3 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy h.weaken s3
  let X  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q G3 H2
  let Y  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q G3 H3
  let DF : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q F3 F2)
  let DX : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q X Y)
  let DH : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q H2 H3)
  let DG : Term F (Ty.nat :: Γ) Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q G3 G3)
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s1
  let P2 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s2
  let P3 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q s3
  pmode
  pforall
  canorm
  prw hu
  prw hv
  -- re-bracket the left-hand sum so that both sides are binary sums with matching parts
  papplym (lt_Q_congr
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y))) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q (Term.app2 Term.add_Q F3 G3) H2)
      (Term.app2 Term.add_Q F2 Y))) P
    (abs_Q_congr (sub_Q_congr (eqQsym (add_Q_assoc_inst F3 G3 H2))
      (eq_Q_refl_inst (Term.app2 Term.add_Q F2 Y))))
    (eq_Q_refl_inst P))
  papplym (lt_le_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q
    (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y))) P2 P)
  psplit
  · papplym (le_lt_Q_trans (.app Term.abs_Q (Term.app2 Term.sub_Q
      (Term.app2 Term.add_Q F3 X) (Term.app2 Term.add_Q F2 Y)))
      (Term.app2 Term.add_Q DF DX) P2)
    psplit
    · pthm (abs_Q_sub_add_split F2 Y F3 X)
    · papplym (lt_Q_congr (Term.app2 Term.add_Q DF DX) (Term.app2 Term.add_Q P3 P3)
        (Term.app2 Term.add_Q DF DX) P2
        (eq_Q_refl_inst (Term.app2 Term.add_Q DF DX)) (pow2neg_Q_halve s2))
      papplym (lt_Q_add_both DF DX P3 P3)
      psplit
      · papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q F2 F3)) P3 DF P3
          (abs_diff_Q_comm F2 F3) (eq_Q_refl_inst P3))
        pthm (cauchyfy_cauchy f.weaken s2)
      · papplym (le_lt_Q_trans DX (Term.app2 Term.add_Q DG DH) P3)
        psplit
        · pthm (abs_Q_sub_add_split G3 H3 G3 H2)
        · papplym (lt_Q_congr DH P3 (Term.app2 Term.add_Q DG DH) P3
            (eqQsym (eqQtrans (addQl (abs_Q_sub_self G3) DH)
              (eqQtrans (add_Q_comm_inst Term.zero_Q DH) (add_Q_zero_inst DH))))
            (eq_Q_refl_inst P3))
          pthm (cauchyfy_cauchy h.weaken s2)
  · papplym (le_Q_trans P2 P1 P)
    psplit
    · pthm (pow2neg_Q_le_succ s1)
    · pthm (pow2neg_Q_le_succ (.var .vz))

/-- `(f +_ℝ g) +_ℝ h =_ℝ f +_ℝ (g +_ℝ h)`, at explicit reals. -/
def add_assoc_R_core (f g h : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.add_R (Term.app2 Term.add_R f g) h)
            (Term.app2 Term.add_R f (Term.app2 Term.add_R g h))) :=
  add_assoc_R_gen f g h
    (Term.app2 Term.add_R (Term.app2 Term.add_R f g) h)
    (Term.app2 Term.add_R f (Term.app2 Term.add_R g h))
    (by
      rw [add_R_app_weaken, add_R_app_weaken]
      exact qtrans
        (cauchyfy_add_R (Term.app2 Term.add_R f.weaken g.weaken) h.weaken
          (.app .succ (.var .vz)))
        (addQ_l_nat _ (cauchyfy_add_R f.weaken g.weaken
          (.app .succ (.app .succ (.var .vz))))))
    (by
      rw [add_R_app_weaken, add_R_app_weaken]
      exact qtrans
        (cauchyfy_add_R f.weaken (Term.app2 Term.add_R g.weaken h.weaken)
          (.app .succ (.var .vz)))
        (addQ_r_nat _ (cauchyfy_add_R g.weaken h.weaken
          (.app .succ (.app .succ (.var .vz))))))

/-- ⊢ ∀f,g,h : ℝ. (f +_ℝ g) +_ℝ h =_ℝ f +_ℝ (g +_ℝ h) -/
def add_assoc_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy (Formula.all rTy
        (eq_R
          (Term.app2 Term.add_R
            (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var (.vs .vz)))
            (.var .vz))
          (Term.app2 Term.add_R (.var (.vs (.vs .vz)))
            (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))))))) :=
  univ_gen (univ_gen (univ_gen
    (add_assoc_R_core (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- **`le_R_pu` implies `le_R`** — `∀n ¬B(n) → ¬∃n B(n)`, which is intuitionistic.

Since the `le_R_pu` argument-order repair (2026-09-02, see `Terms/Real.lean`) the two
formulas are built from *literally the same* body `B`:

* `le_R f g` is `¬(g <ℝ f)`, i.e. `(∃n. B n) →ᶠ ⊥ᶠ`;
* `le_R_pu f g` is `∀n. (B n →ᶠ ⊥ᶠ)`.

So this is pure logic: destruct the existential, instantiate the universal at the witness,
apply. The converse is `le_R_pu_of_le_R` just below, and is equally cheap. -/
def le_R_of_le_R_pu (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R_pu f g →ᶠ le_R f g) := by
  pmode
  pintro h
  pintro hex
  pobtain hex with hn
  canorm
  pinst h (.var .vz) with hh
  canorm
  papply hh
  pexact hn

/-- The converse of `le_R_of_le_R_pu`: `¬∃n B(n) → ∀n ¬B(n)`, also intuitionistic. -/
def le_R_pu_of_le_R (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises (le_R f g →ᶠ le_R_pu f g) := by
  pmode
  pintro h
  pforall
  pintro hn
  papply h
  pexists (.var .vz)
  canorm
  pexact hn

/-- **`f ≤_ℝ g` in Π₁⁰ form**: `∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}`.

`le_R` is a *negated existential*, so it is spent by ∃-introduction — a failure at any single
index would produce the very witness the hypothesis denies — and the `≤`/`<` dichotomy at ℚ
then turns the negation into a positive bound. No Markov step is involved: `le_Q_or_lt_Q` is a
derivable disjunction, the encoding's order being decidable.

The conclusion is stated as a `∀`-formula rather than at a caller-supplied index so that it
can be `pinst`-antiated *after* a `pforall`; instantiating is what lets `closed_subst` clear
the proof mode's weakening of `Term.zero_R`, which a direct `papplym` at the weakened
hypothesis cannot do.

Note the argument order: this is `le_R f g`, i.e. `f ≤ g`, and `le_R_pu f g` now means the
same thing. (Until 2026-09-02 `le_R_pu` took its arguments the other way round and meant
`g ≤_ℝ f`; that bug is fixed in `Terms/Real.lean`, and `le_R_of_le_R_pu` /
`le_R_pu_of_le_R` above convert between the two forms in either direction.) -/
def le_R_all (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R f g →ᶠ
        Formula.all Ty.nat
          (lt_Q (Term.app2 Term.sub_Q
                   (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
                   (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
                (.app Term.pow2neg_Q (.var .vz)))) := by
  pmode
  pintro h
  pforall
  papplym (lt_Q_of_not_le_Q (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz)))))
  pintro hle
  papply h
  pexists (.var .vz)
  canorm
  pexact hle

/-- **The converse of `le_R_all`**: the Π₁⁰ bound `∀n. f̂(n+1) −ℚ ĝ(n+1) <ℚ 2^{-n}` gives
`f ≤_ℝ g`.

Together with `le_R_all` this pins `le_R` down completely: it *is* that bound, and every
`≤_ℝ` fact in the development can be established index by index in ℚ. The proof is the
`≤_ℚ`/`<_ℚ` clash — a witness against `le_R f g` asserts `2^{-n} ≤ℚ f̂(n+1) −ℚ ĝ(n+1)` at
some `n`, which the bound at that same `n` contradicts. No Markov step, no dichotomy. -/
def le_R_of_all (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat
          (lt_Q (Term.app2 Term.sub_Q
                   (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
                   (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
                (.app Term.pow2neg_Q (.var .vz)))
       →ᶠ le_R f g) := by
  pmode
  pintro h
  pintro hex
  pobtain hex with hn
  canorm
  pinst h (.var .vz) with h1
  canorm
  papplym (lt_Q_irrefl_inst (.app Term.pow2neg_Q (.var .vz)))
  papplym (le_lt_Q_trans (.app Term.pow2neg_Q (.var .vz))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
      (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
    (.app Term.pow2neg_Q (.var .vz)))
  psplit
  · pexact hn
  · pexact h1

/-- `le_R_of_all` in the form callers actually want: hand it the estimate as a derivation in
the extended context `Ty.nat :: Γ` and it universally generalises for you. -/
def le_R_of_bound (f g : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (Term.app2 Term.sub_Q
               (Term.app2 Term.cauchyfy f.weaken (.app .succ (.var .vz)))
               (Term.app2 Term.cauchyfy g.weaken (.app .succ (.var .vz))))
            (.app Term.pow2neg_Q (.var .vz)))) :
    Derivable F al Premises (le_R f g) :=
  Derivable.mp (univ_gen h) (le_R_of_all f g)

-- ── ℚ rearrangements the ℝ estimates need ───────────────────────────────────
--
-- Four abelian-group identities and one `pow2neg` bound. They are ℚ facts, but they live
-- here rather than in `RationalNumbers.lean` for the reason stated above: that file is
-- another workstream's, and these exist only to serve `dist_nonneg`.

/-- **Middle-four exchange**: `(a +ℚ b) +ℚ (c +ℚ d) =ℚ (a +ℚ c) +ℚ (b +ℚ d)`.

The one rearrangement every multi-term ℚ estimate in the ℝ layer needs, and the reason the
sums below can be written in whatever bracketing the inequality lemmas produce. -/
def add_Q_shuffle (a b c d : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (Term.app2 Term.add_Q a b) (Term.app2 Term.add_Q c d))
            (Term.app2 Term.add_Q (Term.app2 Term.add_Q a c) (Term.app2 Term.add_Q b d))) :=
  eqQtrans (add_Q_assoc_inst a b (Term.app2 Term.add_Q c d))
    (eqQtrans (addQr a (eqQsym (add_Q_assoc_inst b c d)))
      (eqQtrans (addQr a (addQl (add_Q_comm_inst b c) d))
        (eqQtrans (addQr a (add_Q_assoc_inst c b d))
          (eqQsym (add_Q_assoc_inst a c (Term.app2 Term.add_Q b d))))))

/-- `(a −ℚ x) +ℚ (−ℚ a) =ℚ −ℚ x`. -/
def sub_add_neg_cancel (a x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a x) (.app Term.neg_Q a))
            (.app Term.neg_Q x)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  let nx : Term F Γ Ty.nat := .app Term.neg_Q x
  eqQtrans (addQl (sub_Q_eq_add_neg a x) na)
    (eqQtrans (addQl (add_Q_comm_inst a nx) na)
      (eqQtrans (add_Q_assoc_inst nx a na)
        (eqQtrans (addQr nx (add_Q_neg_inst a)) (add_Q_zero_inst nx))))

/-- `(−ℚ (d +ℚ e)) +ℚ (e −ℚ d) =ℚ (−ℚ d) +ℚ (−ℚ d)`.

This is the step that turns the triangle inequality's `d(x,y) + d(y,x)` into `2·d(x,y)`, once
symmetry has supplied `e −ℚ d`. -/
def neg_add_sub_cancel (d e : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q (.app Term.neg_Q (Term.app2 Term.add_Q d e))
              (Term.app2 Term.sub_Q e d))
            (Term.app2 Term.add_Q (.app Term.neg_Q d) (.app Term.neg_Q d))) :=
  let nd : Term F Γ Ty.nat := .app Term.neg_Q d
  let ne : Term F Γ Ty.nat := .app Term.neg_Q e
  eqQtrans (addQl (neg_Q_add_Q d e) (Term.app2 Term.sub_Q e d))
    (eqQtrans (addQr (Term.app2 Term.add_Q nd ne) (sub_Q_eq_add_neg e d))
      (eqQtrans (addQr (Term.app2 Term.add_Q nd ne) (add_Q_comm_inst e nd))
        (eqQtrans (add_Q_shuffle nd ne nd e)
          (eqQtrans (addQr (Term.app2 Term.add_Q nd nd)
              (eqQtrans (add_Q_comm_inst ne e) (add_Q_neg_inst e)))
            (add_Q_zero_inst (Term.app2 Term.add_Q nd nd))))))

/-- `(−ℚ a) −ℚ (−ℚ b) =ℚ b −ℚ a`: negating both sides reverses a difference. -/
def sub_Q_neg_neg (a b : Term F Γ Ty.nat) :
    Derivable F al Premises
      (eq_Q (Term.app2 Term.sub_Q (.app Term.neg_Q a) (.app Term.neg_Q b))
            (Term.app2 Term.sub_Q b a)) :=
  let na : Term F Γ Ty.nat := .app Term.neg_Q a
  eqQtrans (sub_Q_eq_add_neg na (.app Term.neg_Q b))
    (eqQtrans (addQr na (neg_Q_neg_Q b))
      (eqQtrans (add_Q_comm_inst na b) (eqQsym (sub_Q_eq_add_neg b a))))

/-- **The budget that makes `dist_nonneg` fit.** With `B := 2^{-(n+2)} +ℚ 2^{-(n+4)}`,

    `B +ℚ (B +ℚ B) ≤ℚ 2^{-n}`

because `3B = 3·2^{-(n+2)} + 3·2^{-(n+4)} = 2^{-(n+1)} + 2^{-(n+2)} + 2^{-(n+3)} + 2^{-(n+4)}`,
which falls short of `2^{-n}` by exactly `2^{-(n+4)}`. `dist_nonneg` spends one `B` on the
triangle-plus-symmetry estimate at index `n+5` and two on moving `d̂` back from `n+5` to `n+2`,
so this is the whole of its arithmetic. -/
def pow2neg_triple_bound (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (le_Q (Term.app2 Term.add_Q
               (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                 (.app Term.pow2neg_Q
                   (.app .succ (.app .succ (.app .succ (.app .succ n))))))
               (Term.app2 Term.add_Q
                 (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                   (.app Term.pow2neg_Q
                     (.app .succ (.app .succ (.app .succ (.app .succ n))))))
                 (Term.app2 Term.add_Q (.app Term.pow2neg_Q (.app .succ (.app .succ n)))
                   (.app Term.pow2neg_Q
                     (.app .succ (.app .succ (.app .succ (.app .succ n))))))))
            (.app Term.pow2neg_Q n)) :=
  let n1 : Term F Γ Ty.nat := .app .succ n
  let n2 : Term F Γ Ty.nat := .app .succ n1
  let n3 : Term F Γ Ty.nat := .app .succ n2
  let p0 : Term F Γ Ty.nat := .app Term.pow2neg_Q n
  let p1 : Term F Γ Ty.nat := .app Term.pow2neg_Q n1
  let p2 : Term F Γ Ty.nat := .app Term.pow2neg_Q n2
  let p3 : Term F Γ Ty.nat := .app Term.pow2neg_Q n3
  let p4 : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n3)
  let B  : Term F Γ Ty.nat := Term.app2 Term.add_Q p2 p4
  -- `B +ℚ B =ℚ 2^{-(n+1)} +ℚ 2^{-(n+3)}`
  let hBB : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q B B) (Term.app2 Term.add_Q p1 p3)) :=
    eqQtrans (add_Q_shuffle p2 p4 p2 p4)
      (eqQtrans (addQl (pow2neg_Q_halve n1) (Term.app2 Term.add_Q p4 p4))
        (addQr p1 (pow2neg_Q_halve n3)))
  -- `B +ℚ (B +ℚ B) =ℚ (2^{-(n+1)} +ℚ 2^{-(n+2)}) +ℚ (2^{-(n+3)} +ℚ 2^{-(n+4)})`
  let hFwd : Derivable F al Premises
      (eq_Q (Term.app2 Term.add_Q B (Term.app2 Term.add_Q B B))
            (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
              (Term.app2 Term.add_Q p3 p4))) :=
    eqQtrans (addQr B hBB)
      (eqQtrans (add_Q_shuffle p2 p4 p1 p3)
        (eqQtrans (addQl (add_Q_comm_inst p2 p1) (Term.app2 Term.add_Q p4 p3))
          (addQr (Term.app2 Term.add_Q p1 p2) (add_Q_comm_inst p4 p3))))
  by
  pmode
  papplym (le_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
      (Term.app2 Term.add_Q p3 p4)) p0
    (Term.app2 Term.add_Q B (Term.app2 Term.add_Q B B)) p0
    (eqQsym hFwd) (eq_Q_refl_inst p0))
  papplym (le_Q_trans (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2)
      (Term.app2 Term.add_Q p3 p4))
    (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2) p2) p0)
  psplit
  · -- `2^{-(n+3)} +ℚ 2^{-(n+4)} ≤ℚ 2^{-(n+2)}`
    papplym (le_Q_add_l (Term.app2 Term.add_Q p1 p2) (Term.app2 Term.add_Q p3 p4) p2)
    papplym (le_Q_congr (Term.app2 Term.add_Q p3 p4) (Term.app2 Term.add_Q p3 p3)
      (Term.app2 Term.add_Q p3 p4) p2 (eq_Q_refl_inst (Term.app2 Term.add_Q p3 p4))
      (pow2neg_Q_halve n2))
    papplym (le_Q_add_l p3 p4 p3)
    pthm (pow2neg_Q_le_succ n3)
  · -- `(2^{-(n+1)} +ℚ 2^{-(n+2)}) +ℚ 2^{-(n+2)} =ℚ 2^{-n}`
    papplym (le_Q_congr p0 p0 (Term.app2 Term.add_Q (Term.app2 Term.add_Q p1 p2) p2) p0
      (eqQsym (eqQtrans (add_Q_assoc_inst p1 p2 p2)
        (eqQtrans (addQr p1 (pow2neg_Q_halve n1)) (pow2neg_Q_halve n))))
      (eq_Q_refl_inst p0))
    pthm (le_Q_refl p0)

-- ── `cauchyfy` commutes with negation, and `add_neg_R` ──────────────────────
--
-- `add_zero_R` and `add_assoc_R` above needed no new `cauchyfy` theory, because `add_R`'s
-- own `cauchyfy_add_R` already says everything about the composite. **`add_neg_R` does**,
-- and this is the one place in the additive package where that bites:
-- `neg_R f = λn. neg_Q (f n)` applies to the *raw* `f`, not to `f̂`, so nothing yet relates
-- `(neg_R f)^` to `f̂` — and `f` is an arbitrary `ℕ → ℕ`, so `neg_R f` is not Cauchy and
-- `cauchyfy_id` does not apply either.
--
-- What makes it work is that the two recursions run in *lockstep*, on the nose:
--
--     state(neg_R f, n)  =₀  pair( neg_Q (fst_pair (state(f, n))), snd_pair (state(f, n)) )
--
-- — same flag, negated value, at *every* index. The value half is immediate; the flag half
-- is the content, because the Cauchy check is taken on the raw sequences and
-- `|neg_Q a −ℚ neg_Q b|` is only `eq_Q`-equal to `|a −ℚ b|`, not `=₀`-equal. So the flags
-- agree only because `lt_Q_dec`'s *decision* is `eq_Q`-invariant, which is what
-- `sg_bar_congr_iff` below is for: it turns the two-way implication `lt_Q_congr` supplies
-- into the `=₀` equality of `sg_bar` values that `cauchyState_advance` / `cauchyState_trip`
-- demand.
--
-- (This is the same machinery `add_comm_R` / `mul_comm_R` are blocked on — see REALS_PLAN
-- §0.2 — but only in the special case where the two sequences are related by a *fixed*
-- ℚ-operation, so the induction needs no object-level hypothesis beyond its own IH.)

/-- `sg_bar u =₀ sg_bar v` whenever `u` and `v` vanish together.

The bridge from "`lt_Q` is `eq_Q`-invariant" (an equivalence of *formulas*, which is all
`lt_Q_congr` gives) to "the flag bits are equal" (an `=₀` fact about `lt_Q_dec`, which is what
the `cauchyfy` recursion branches on). Note `sg_bar` is the *complement* indicator here —
`sg_bar 0 =₀ S0`, `sg_bar (S n) =₀ 0` — which is why the case split reads the way it does. -/
private def sg_bar_congr_iff (u v : Term F Γ Ty.nat) :
    Derivable F al Premises
      ((Formula.eq0 u Term.zero →ᶠ Formula.eq0 v Term.zero)
        ∧ᶠ (Formula.eq0 v Term.zero →ᶠ Formula.eq0 u Term.zero) →ᶠ
       Formula.eq0 (.app Term.sg_bar u) (.app Term.sg_bar v)) := by
  pmode
  pintro h
  pdestruct h with h1 h2
  pfrom hcu := sg_bar_cases u
  pcases hcu with hu1 | hu0
  · -- `sg_bar u = S0`, i.e. `u = 0`; carry it across to `v` and back up
    papplym (sg_bar_eq_S0_implies_zero u) in hu1 with huz
    phave hv1 : Formula.eq0 (.app Term.sg_bar v) (.app .succ .zero)
    · phave hvz : Formula.eq0 v Term.zero
      · papply h1
        pexact huz
      prwby hvz
      pthm sg_bar_zero
    prwby hu1
    prwby hv1
    prefl
  · -- `sg_bar u = 0`, i.e. `u ≠ 0`; likewise
    pfrom hiu := sg_bar_eq_zero_iff u
    pdestruct hiu with hiuF _hiuB
    phave hunz : ¬ᶠ(Formula.eq0 u Term.zero)
    · papply hiuF
      pexact hu0
    phave hv0 : Formula.eq0 (.app Term.sg_bar v) Term.zero
    · pfrom hiv := sg_bar_eq_zero_iff v
      pdestruct hiv with _hivF hivB
      papply hivB
      pintro hvz
      papply hunz
      papply h2
      pexact hvz
    prwby hu0
    prwby hv0
    prefl

/-- `neg_R(f)(x) =₀ neg_Q(f x)` — the two beta steps of `neg_R`. -/
def neg_R_apply (f : Term F Γ (realTy ι)) (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.neg_R f x) (.app Term.neg_Q (.app f x))) :=
  lam2_correct_nf
    (.app Term.neg_Q (.app (.var (.vs .vz)) (.var .vz)))
    f x
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.Subst.ext,
          subst_subst0_map_weaken, closed_subst])

private theorem neg_R_weaken {Δ : Ctx ι} {ρ : Ty ι} :
    (Term.neg_R : Term F Δ _).weaken (σ := ρ) = Term.neg_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact neg_R_closed_subst _

private theorem neg_R_app_weaken {Δ : Ctx ι} {ρ : Ty ι} (f : Term F Δ (realTy ι)) :
    (Term.app Term.neg_R f).weaken (σ := ρ) = Term.app Term.neg_R f.weaken := by
  show Term.app (Term.weaken Term.neg_R) f.weaken = _
  rw [neg_R_weaken]

/-- Congruence under `neg_Q`, at the level of `=₀`. -/
private def neg_Q_nat {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (.app Term.neg_Q s) (.app Term.neg_Q t)) :=
  qfer_no_premise_nat_nf h (r := .app Term.neg_Q (.var .vz))
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, closed_subst])

/-- Congruence for `pair` in its first argument, at the level of `=₀`. -/
private def pair_l_nat (c : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.pair s c) (Term.app2 Term.pair t c)) :=
  qfer_no_premise_nat_nf h (r := Term.app2 Term.pair (.var .vz) c.weaken)
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])
    (by simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app2,
          subst_subst0_map_weaken, closed_subst])

/-- The Cauchy checks of `f` and of `neg_R f` agree *as bits*. The two checked quantities are
only `eq_Q`-equal — `|neg_Q a −ℚ neg_Q b|ℚ` is `|b −ℚ a|ℚ` re-encoded — so this is exactly
where `sg_bar_congr_iff` is spent. -/
private def neg_check_sg (f : Term F Γ (realTy ι)) (n : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0
        (.app Term.sg_bar (Term.cauchy_check_at (.app Term.neg_R f) n))
        (.app Term.sg_bar (Term.cauchy_check_at f n))) := by
  let A : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (Term.app2 Term.neg_R f n) (Term.app2 Term.neg_R f (.app .succ n)))
  let B : Term F Γ Ty.nat := .app Term.abs_Q (Term.app2 Term.sub_Q
    (.app f n) (.app f (.app .succ n)))
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q (.app .succ n)
  have hAB : Derivable F al Premises (eq_Q A B) := by
    pmode
    prw (neg_R_apply f n)
    prw (neg_R_apply f (.app .succ n))
    pthm (eqQtrans (abs_Q_congr (sub_Q_neg_neg (.app f n) (.app f (.app .succ n))))
      (abs_diff_Q_comm (.app f (.app .succ n)) (.app f n)))
  pmode
  papplym (sg_bar_congr_iff (Term.app2 Term.lt_Q_dec A P) (Term.app2 Term.lt_Q_dec B P))
  psplit
  · pthm (lt_Q_congr A P B P hAB (eq_Q_refl_inst P))
  · pthm (lt_Q_congr B P A P (eqQsym hAB) (eq_Q_refl_inst P))

-- The lockstep claim is written out at both of its occurrences rather than given a name.
-- `canorm` normalises substitutions with `simp only`, which does not unfold a named
-- `Formula` definition, so a `negF` abbreviation would hide the whole statement from the
-- induction's own bookkeeping — the same reason the file has no `cVal`/`cFlag` wrappers.

/-- The lockstep claim at an explicit index. -/
abbrev negAt (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.eq0 (Term.cauchyState (.app Term.neg_R f) s)
    (Term.app2 Term.pair
      (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f s)))
      (.app Term.snd_pair (Term.cauchyState f s)))

private theorem negF_subst0 (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    (Formula.eq0 (Term.cauchyState (.app Term.neg_R f.weaken) (.var .vz))
        (Term.app2 Term.pair
          (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz))))
          (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz))))).subst0 s
      = negAt f s := by
  simp only [negAt, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
    Term.app2, cauchyState_subst, neg_R_closed_subst, subst_subst0_map_weaken, closed_subst]

/-- **`cauchyfy` and negation run in lockstep.** At every index the negated sequence's state
is the original's with the value negated and the flag copied verbatim.

Three cases, exactly as in `cauchy_inv`: the flag was already set (both freeze), the flag is
clear and the check passes (both advance, to `neg_Q (f (n+1))` and `f (n+1)`), or the flag is
clear and the check fails (both trip, freezing the values they already hold). The checks agree
by `neg_check_sg`, which is the only step that is not bookkeeping. -/
def cauchyState_neg (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (Formula.all Ty.nat
        (Formula.eq0 (Term.cauchyState (.app Term.neg_R f.weaken) (.var .vz))
          (Term.app2 Term.pair
            (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f.weaken (.var .vz))))
            (.app Term.snd_pair (Term.cauchyState f.weaken (.var .vz)))))) := by
  let fw : Term F (Ty.nat :: Γ) (realTy ι) := f.weaken
  let gw : Term F (Ty.nat :: Γ) (realTy ι) := .app Term.neg_R fw
  let nv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let V : Term F (Ty.nat :: Γ) Ty.nat := .app Term.fst_pair (Term.cauchyState fw nv)
  let Φ : Term F (Ty.nat :: Γ) Ty.nat := .app Term.snd_pair (Term.cauchyState fw nv)
  pmode
  pinduction
  · -- base: both states are their bases, and `neg_R f 0 =₀ neg_Q (f 0)`
    canorm
    prw (cVal_zero f)
    prw (cFlag_zero f)
    pthm (qtrans (cauchyState_zero (.app Term.neg_R f))
      (pair_l_nat Term.zero (neg_R_apply f Term.zero)))
  · pforall
    pintro ih
    canorm
    pfrom hinv := cauchy_inv_at fw nv
    pcases hinv with hL | hR
    · pdestruct hL with h0 _hv
      phave hsnd0 : Formula.eq0 (.app Term.snd_pair (Term.cauchyState gw nv)) Term.zero
      · prwby ih
        prw (snd_pair_pair (.app Term.neg_Q V) Φ)
        pexact h0
      pfrom hsg := sg_bar_cases (Term.cauchy_check_at fw nv)
      pcases hsg with hs1 | hs0
      · -- the check passes: both advance
        phave hsgn : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at gw nv)) (.app .succ .zero)
        · prw (neg_check_sg fw nv)
          pexact hs1
        pconj hsnd0 hsgn with hbn
        papplym (cauchyState_advance gw nv) in hbn with hgn
        pconj h0 hs1 with hbf
        papplym (cauchyState_advance fw nv) in hbf with hfn
        prwby hgn
        prwby hfn
        prw (fst_pair_pair (.app fw (.app .succ nv)) Term.zero)
        prw (snd_pair_pair (.app fw (.app .succ nv)) Term.zero)
        prw (neg_R_apply fw (.app .succ nv))
        prefl
      · -- the check fails: both trip, and both values freeze where they are
        phave hsgn : Formula.eq0
            (.app Term.sg_bar (Term.cauchy_check_at gw nv)) Term.zero
        · prw (neg_check_sg fw nv)
          pexact hs0
        pconj hsnd0 hsgn with hbn
        papplym (cauchyState_trip gw nv) in hbn with hgn
        pconj h0 hs0 with hbf
        papplym (cauchyState_trip fw nv) in hbf with hfn
        prwby hgn
        prwby hfn
        prw (fst_pair_pair V (.app .succ Term.zero))
        prw (snd_pair_pair V (.app .succ Term.zero))
        prwby ih
        prw (fst_pair_pair (.app Term.neg_Q V) Φ)
        prefl
    · -- already tripped: both states freeze
      phave hsnd1 : Formula.eq0
          (.app Term.snd_pair (Term.cauchyState gw nv)) (.app .succ .zero)
      · prwby ih
        prw (snd_pair_pair (.app Term.neg_Q V) Φ)
        pexact hR
      papplym (cauchyState_frozen gw nv) in hsnd1 with hgn
      papplym (cauchyState_frozen fw nv) in hR with hfn
      prwby hgn
      prwby hfn
      pexact ih

/-- The lockstep claim at an explicit index. -/
def cauchyState_neg_at (f : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises (negAt f s) :=
  negF_subst0 f s ▸ Derivable.mp (cauchyState_neg f) (.forall_ax s)

/-- **`(neg_R f)^(k) =₀ neg_Q (f̂(k))`** — cauchyfication commutes with negation, on the nose.
-/
def cauchyfy_neg (f : Term F Γ (realTy ι)) (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.cauchyfy (.app Term.neg_R f) k)
        (.app Term.neg_Q (Term.app2 Term.cauchyfy f k))) :=
  qtrans (cauchyfy_unfold (.app Term.neg_R f) k)
    (qtrans (fst_pair_congr (cauchyState_neg_at f k))
      (qtrans (fst_pair_pair
          (.app Term.neg_Q (.app Term.fst_pair (Term.cauchyState f k)))
          (.app Term.snd_pair (Term.cauchyState f k)))
        (neg_Q_nat (Derivable.mp (cauchyfy_unfold f k) Derivable.sym0))))

/-- `u =_ℝ 0_ℝ` for any `u` whose cauchyfication is `f̂(·+2) +ℚ (−ℚ f̂(·+2))`.

Once `cauchyfy_neg` has put the sum in that shape there is no estimate left at all: the sum is
`eq_Q`-zero outright, and `0_ℚ <ℚ 2^{-n}`. -/
private def add_neg_R_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
            (.app .succ (.app .succ (.var .vz)))))))) :
    Derivable F al Premises (eq_R u Term.zero_R) := by
  let s1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ (.var .vz)
  let s2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ s1
  let A2 : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken s2
  let S  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.add_Q A2 (.app Term.neg_Q A2)
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  pmode
  pforall
  canorm
  prw hu
  prw (cauchyfy_zero_R s1)
  papplym (lt_Q_congr Term.zero_Q P
    (.app Term.abs_Q (Term.app2 Term.sub_Q S Term.zero_Q)) P
    (eqQsym (eqQtrans (abs_Q_congr (eqQtrans (sub_Q_zero_Q S) (add_Q_neg_inst A2)))
      abs_Q_zero_Q))
    (eq_Q_refl_inst P))
  pthm (zero_lt_pow2neg_Q (.var .vz))

/-- `f +_ℝ neg_R(f) =_ℝ 0_ℝ`, at an explicit real. -/
def add_neg_R_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R (Term.app2 Term.add_R f (.app Term.neg_R f)) Term.zero_R) :=
  add_neg_R_gen f (Term.app2 Term.add_R f (.app Term.neg_R f)) (by
    rw [add_R_app_weaken, neg_R_app_weaken]
    exact qtrans
      (cauchyfy_add_R f.weaken (.app Term.neg_R f.weaken) (.app .succ (.var .vz)))
      (addQ_r_nat _ (cauchyfy_neg f.weaken (.app .succ (.app .succ (.var .vz))))))

/-- ⊢ ∀f : ℝ. f +_ℝ neg_R(f) =_ℝ 0_ℝ -/
def add_neg_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz)
                (.app Term.neg_R (.var .vz)))
              Term.zero_R)) :=
  univ_gen (add_neg_R_core (.var .vz))

-- ── Properties needed for metric space transitivity ─────────────────────────

/-- ⊢ ∀f,g : ℝ. f =_ℝ 0 ∧ g =_ℝ 0 → f +_ℝ g =_ℝ 0 -/
def add_eq_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (eq_R (.var (.vs .vz)) Term.zero_R
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (Term.app2 Term.add_R (.var (.vs .vz)) (.var .vz))
                   Term.zero_R))) :=
  univ_gen (univ_gen (add_eq_zero_R_core (.var (.vs .vz)) (.var .vz)))

/-- `0_ℝ ≤_ℝ f ∧ f ≤_ℝ g ∧ g =_ℝ 0_ℝ → f =_ℝ 0_ℝ`, at explicit reals.

**The old statement of `le_zero_eq_zero_R` — without the first conjunct — was FALSE**, and the
counterexample is worth keeping. Take `f := λn.⟨−1⟩_ℚ` and `g := 0_ℝ`. Then

* `le_R f g` unfolds to `¬ lt_R g f`, i.e. `¬∃n (f̂(n+1) −_ℚ ĝ(n+1) ≥_ℚ 2^{-n})`. Here that
  difference is `−1`, which is below every `2^{-n}`, so the `∃` is empty and `f ≤_ℝ g` holds;
* `g =_ℝ 0_ℝ` holds (`cauchyfy_zero_R`);
* `f =_ℝ 0_ℝ` fails already at `n = 0`: it asks `|−1|_ℚ <_ℚ ⟨2^{-0}⟩_ℚ`, i.e. `1 <_ℚ 1`.

So that formula was false in the standard model and hence not derivable: `f ≤_ℝ 0` says
nothing about how far *below* `0` the real `f` is. Adding `0_ℝ ≤_ℝ f` repairs it, and the
repaired form is what is proved here (2026-09-02).

The estimate, at the goal's index `n`. Write `a_k := f̂(k)`, `b_k := ĝ(k)`.

* **lower bound** `−a_{n+1} <ℚ 2^{-n}` — `0_ℝ ≤_ℝ f` read at `n`, directly;
* **upper bound** `a_{n+1} <ℚ 2^{-n}` — three steps, at index `n+2` rather than `n`, because
  reading the two hypotheses at `n` gives only `2^{-n} + 2^{-n}` and overshoots:
  `f ≤_ℝ g` at `n+2` gives `a_{n+3} −ℚ b_{n+3} <ℚ 2^{-(n+2)}`, `g =_ℝ 0` at `n+2` gives
  `b_{n+3} <ℚ 2^{-(n+2)}` (through `le_Q_self_abs`), so `a_{n+3} <ℚ 2^{-(n+1)}`; and
  `cauchyfy_two_step` moves back from `n+3` to `n+1` for another `2^{-(n+1)}`.

Both bounds are then folded into `|a_{n+1}| <ℚ 2^{-n}` by `abs_Q_lt_of_two_sided`. Unlike
`eq_R_trans` this needs no telescoping induction — the shift is a fixed two steps.

`eqAtType_trans_base` (`BaseEquality.lean`) still has to supply `0_ℝ ≤_ℝ d(x,z)` from the
pseudometric axioms; `nonneg_of_add_self_nonneg` below is the ℝ-side half of that, and
`dist_nonneg` is the assembly. -/
def le_zero_eq_zero_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R Term.zero_R f ∧ᶠ le_R f g ∧ᶠ eq_R g Term.zero_R →ᶠ eq_R f Term.zero_R) :=
  let n   : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n
  let n2  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n1
  let n3  : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n2
  let a   : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n1
  let a3  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n3
  let b3  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy g.weaken n3
  let P   : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n
  let P1  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n1
  let P2  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n2
  by
  pmode
  pintro hyp
  pdestruct hyp with h01 h3
  pdestruct h01 with h0 h12
  papplym (le_R_all Term.zero_R f) in h0 with p0
  papplym (le_R_all f g) in h12 with p12
  pforall
  pinst p0 n with q0
  pinst p12 n2 with q1
  pinst h3 n2 with q2
  canorm
  -- the lower bound, straight from `0_ℝ ≤_ℝ f` at `n`
  prw (cauchyfy_zero_R n1) in q0 with q0a
  papplym (lt_Q_congr (Term.app2 Term.sub_Q Term.zero_Q a) P (.app Term.neg_Q a) P
    (sub_Q_zero_l a) (eq_Q_refl_inst P)) in q0a with hlow
  -- `g =_ℝ 0` at `n+2`, turned into the directed bound `b_{n+3} <ℚ 2^{-(n+2)}`
  prw (cauchyfy_zero_R n3) in q2 with q2a
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q b3 Term.zero_Q)) P2
    (.app Term.abs_Q b3) P2 (abs_Q_congr (sub_Q_zero_Q b3)) (eq_Q_refl_inst P2)) in q2a with q2b
  phave hb3 : lt_Q b3 P2
  · papplym (le_lt_Q_trans b3 (.app Term.abs_Q b3) P2)
    psplit
    · pthm (le_Q_self_abs b3)
    · pexact q2b
  -- adding the two at `n+2`: `a_{n+3} <ℚ 2^{-(n+1)}`
  phave ha3 : lt_Q a3 P1
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a3 b3) b3)
      (Term.app2 Term.add_Q P2 P2) a3 P1
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q a3 b3) b3) (add_Q_sub_cancel a3 b3))
      (pow2neg_Q_halve n1))
    papplym (lt_Q_add_both (Term.app2 Term.sub_Q a3 b3) b3 P2 P2)
    psplit
    · pexact q1
    · pexact hb3
  -- two `cauchyfy` steps back from `n+3` to `n+1`
  phave hstep : lt_Q (Term.app2 Term.sub_Q a a3) P1
  · papplym (le_lt_Q_trans (Term.app2 Term.sub_Q a a3)
      (.app Term.abs_Q (Term.app2 Term.sub_Q a a3)) P1)
    psplit
    · pthm (le_Q_self_abs (Term.app2 Term.sub_Q a a3))
    · pthm (cauchyfy_two_step f.weaken n1)
  phave hup : lt_Q a P
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q a a3) a3)
      (Term.app2 Term.add_Q P1 P1) a P
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q a a3) a3) (add_Q_sub_cancel a a3))
      (pow2neg_Q_halve n))
    papplym (lt_Q_add_both (Term.app2 Term.sub_Q a a3) a3 P1 P1)
    psplit
    · pexact hstep
    · pexact ha3
  -- fold the two one-sided bounds into the `eq_R` goal
  prw (cauchyfy_zero_R n1)
  papplym (lt_Q_congr (.app Term.abs_Q a) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q a Term.zero_Q)) P
    (abs_Q_congr (eqQsym (sub_Q_zero_Q a))) (eq_Q_refl_inst P))
  papplym (abs_Q_lt_of_two_sided a P)
  psplit
  · pexact hup
  · pexact hlow

/-- ⊢ ∀f,g : ℝ. 0_ℝ ≤_ℝ f ∧ f ≤_ℝ g ∧ g =_ℝ 0_ℝ → f =_ℝ 0_ℝ

The repaired form of the old (false) `le_zero_eq_zero_R`; see `le_zero_eq_zero_R_core` for
the counterexample to the version without `0_ℝ ≤_ℝ f`, and for the estimate. -/
def le_zero_eq_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (le_R Term.zero_R (.var (.vs .vz))
          ∧ᶠ le_R (.var (.vs .vz)) (.var .vz)
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (.var (.vs .vz)) Term.zero_R))) :=
  univ_gen (univ_gen (le_zero_eq_zero_R_core (.var (.vs .vz)) (.var .vz)))

/-- `0_ℝ ≤_ℝ u → 0_ℝ ≤_ℝ f` where `u` is *any* real whose cauchyfication is `f̂(·+1) +ℚ f̂(·+1)`.

The sum is fed in through an abstract `u` rather than rewritten inside the goal, for the same
reason `add_eq_zero_R_gen` does it: `prw` at a goal containing `Term.add_R` has to push a
substitution through that constant, and that is the delta-expansion blow-up CLAUDE.md's
build-cost section warns about.

The argument, contrapositively — `le_R` on both sides is a negated `∃`, so a witness `n`
against `0_ℝ ≤_ℝ f` has to be turned into a witness against `0_ℝ ≤_ℝ u`, and the *same* index
works. Writing `c := −ℚ f̂(n+1)`, `b := −ℚ f̂(n+2)`:

    2^{-n} ≤ℚ c                              -- the given witness at n
    c <ℚ 2^{-(n+2)} +ℚ b                      -- one `cauchyfy` step, |c −ℚ b| = |f̂(n+1) −ℚ f̂(n+2)|
    2^{-n} <ℚ 2^{-(n+1)} +ℚ b                 -- and 2^{-(n+2)} ≤ℚ 2^{-(n+1)}
    2^{-(n+1)} <ℚ b                           -- cancel, since 2^{-n} =ℚ 2^{-(n+1)} +ℚ 2^{-(n+1)}
    2^{-n} <ℚ b +ℚ b                          -- double

and `b +ℚ b` is `−ℚ û(n+1)`. Note the margin: the Cauchy step costs `2^{-(n+2)}` where a whole
`2^{-(n+1)}` is available, so this is not a tight estimate and needs no telescoping. -/
private def nonneg_of_add_self_gen (f u : Term F Γ (realTy ι))
    (hu : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (Formula.eq0
        (Term.app2 Term.cauchyfy u.weaken (.app .succ (.var .vz)))
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))
          (Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz))))))) :
    Derivable F al Premises (le_R Term.zero_R u →ᶠ le_R Term.zero_R f) :=
  let n  : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
  let n1 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n
  let n2 : Term F (Ty.nat :: Γ) Ty.nat := .app .succ n1
  let a  : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n1
  let a' : Term F (Ty.nat :: Γ) Ty.nat := Term.app2 Term.cauchyfy f.weaken n2
  let c  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q a
  let b  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.neg_Q a'
  let P  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n
  let P1 : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n1
  let Q  : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q n2
  -- `c −ℚ b =ℚ f̂(n+2) −ℚ f̂(n+1)`: negation reverses the difference.
  let hCB : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (Term.app2 Term.sub_Q c b) (Term.app2 Term.sub_Q a' a)) :=
    eqQtrans (sub_Q_eq_add_neg c b)
      (eqQtrans (addQr c (neg_Q_neg_Q a'))
        (eqQtrans (add_Q_comm_inst c a') (eqQsym (sub_Q_eq_add_neg a' a))))
  let hAbs : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (eq_Q (.app Term.abs_Q (Term.app2 Term.sub_Q c b))
            (.app Term.abs_Q (Term.app2 Term.sub_Q a a'))) :=
    eqQtrans (abs_Q_congr hCB) (abs_diff_Q_comm a' a)
  by
  pmode
  pintro hsum
  pintro hex
  pobtain hex with hn
  canorm
  prw (cauchyfy_zero_R n1) in hn with hn1
  papplym (le_Q_congr P (Term.app2 Term.sub_Q Term.zero_Q a) P c
    (eq_Q_refl_inst P) (sub_Q_zero_l a)) in hn1 with hPc
  phave hcb : lt_Q (Term.app2 Term.sub_Q c b) Q
  · papplym (le_lt_Q_trans (Term.app2 Term.sub_Q c b)
      (.app Term.abs_Q (Term.app2 Term.sub_Q c b)) Q)
    psplit
    · pthm (le_Q_self_abs (Term.app2 Term.sub_Q c b))
    · pthm (Derivable.mp (cauchyfy_cauchy f.weaken n1)
        (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q a a')) Q
          (.app Term.abs_Q (Term.app2 Term.sub_Q c b)) Q
          (eqQsym hAbs) (eq_Q_refl_inst Q)))
  phave hcQb : lt_Q c (Term.app2 Term.add_Q Q b)
  · papplym (lt_Q_congr (Term.app2 Term.add_Q (Term.app2 Term.sub_Q c b) b)
      (Term.app2 Term.add_Q Q b) c (Term.app2 Term.add_Q Q b)
      (eqQtrans (add_Q_comm_inst (Term.app2 Term.sub_Q c b) b) (add_Q_sub_cancel c b))
      (eq_Q_refl_inst (Term.app2 Term.add_Q Q b)))
    papplym (lt_le_Q_add (Term.app2 Term.sub_Q c b) b Q b)
    psplit
    · pexact hcb
    · pthm (le_Q_refl b)
  phave hPQb : lt_Q P (Term.app2 Term.add_Q Q b)
  · papplym (le_lt_Q_trans P c (Term.app2 Term.add_Q Q b))
    psplit
    · pexact hPc
    · pexact hcQb
  phave hPP1b : lt_Q P (Term.app2 Term.add_Q P1 b)
  · papplym (lt_le_Q_trans P (Term.app2 Term.add_Q Q b) (Term.app2 Term.add_Q P1 b))
    psplit
    · pexact hPQb
    · pthm (Derivable.mp (pow2neg_Q_le_succ n1) (le_Q_add Q P1 b))
  phave hP1b : lt_Q P1 b
  · papplym (lt_Q_add_cancel_l P1 P1 b)
    papplym (lt_Q_congr P (Term.app2 Term.add_Q P1 b)
      (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q P1 b)
      (eqQsym (pow2neg_Q_halve n)) (eq_Q_refl_inst (Term.app2 Term.add_Q P1 b)))
    pexact hPP1b
  -- the same index `n` refutes `0_ℝ ≤_ℝ u`
  papply hsum
  pexists n
  canorm
  prw (cauchyfy_zero_R n1)
  prw hu
  papplym (le_Q_congr P (Term.app2 Term.add_Q b b) P
    (Term.app2 Term.sub_Q Term.zero_Q (Term.app2 Term.add_Q a' a'))
    (eq_Q_refl_inst P)
    (eqQsym (eqQtrans (sub_Q_zero_l (Term.app2 Term.add_Q a' a')) (neg_Q_add_Q a' a'))))
  papplym (lt_Q_imp_le_Q P (Term.app2 Term.add_Q b b))
  papplym (lt_Q_congr (Term.app2 Term.add_Q P1 P1) (Term.app2 Term.add_Q b b) P
    (Term.app2 Term.add_Q b b) (pow2neg_Q_halve n)
    (eq_Q_refl_inst (Term.app2 Term.add_Q b b)))
  papplym (lt_Q_add_both P1 P1 b b)
  psplit
  · pexact hP1b
  · pexact hP1b

/-- `0_ℝ ≤_ℝ f +_ℝ f → 0_ℝ ≤_ℝ f`, at an explicit real.

This is the ℝ-side half of the non-negativity of a pseudo-metric: with `ax_refl`, `ax_sym` and
`ax_triangle` one gets `0 =_ℝ d(x,x) ≤_ℝ d(x,y) +_ℝ d(y,x) =_ℝ d(x,y) +_ℝ d(x,y)`, and this
lemma converts that into `0_ℝ ≤_ℝ d(x,y)` — the hypothesis `le_zero_eq_zero_R` needs and whose
absence made the old statement of that lemma false. -/
def nonneg_of_add_self_nonneg_core (f : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (le_R Term.zero_R (Term.app2 Term.add_R f f) →ᶠ le_R Term.zero_R f) :=
  nonneg_of_add_self_gen f (Term.app2 Term.add_R f f)
    ((add_R_app_weaken f f).symm ▸
      cauchyfy_add_R f.weaken f.weaken (.app .succ (.var .vz)))

/-- ⊢ ∀f : ℝ. 0_ℝ ≤_ℝ f +_ℝ f → 0_ℝ ≤_ℝ f -/
def nonneg_of_add_self_nonneg :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (le_R Term.zero_R (Term.app2 Term.add_R (.var .vz) (.var .vz))
          →ᶠ le_R Term.zero_R (.var .vz))) :=
  univ_gen (nonneg_of_add_self_nonneg_core (.var .vz))

/-- **`0_ℝ ≤_ℝ f` from the doubled ℚ estimate.** The caller supplies

    `∀n. (−ℚ f̂(n+2)) +ℚ (−ℚ f̂(n+2)) <ℚ 2^{-n}`

and gets `0_ℝ ≤_ℝ f`. This packages `le_R_of_bound`, the two `Term.weaken` computations, the
`cauchyfy_zero_R` / `cauchyfy_add_R` rewrites and `nonneg_of_add_self_nonneg_core`, so that a
caller never has to see `f +_ℝ f` at all — which matters, because pushing a substitution
through `Term.add_R` is the delta-expansion blow-up the build-cost notes warn about.

`dist_nonneg` (`BaseEquality.lean`) is the one consumer, and the doubling is not an artefact:
the triangle inequality at `(x, y, x)` bounds `0` by `d(x,y) + d(y,x)`, which symmetry turns
into `2·d(x,y)` and nothing smaller. -/
def nonneg_R_of_double_bound (f : Term F Γ (realTy ι))
    (h : Derivable F al Premises (Γ := Ty.nat :: Γ)
      (lt_Q (Term.app2 Term.add_Q
               (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
                  (.app .succ (.app .succ (.var .vz)))))
               (.app Term.neg_Q (Term.app2 Term.cauchyfy f.weaken
                  (.app .succ (.app .succ (.var .vz))))))
            (.app Term.pow2neg_Q (.var .vz)))) :
    Derivable F al Premises (le_R Term.zero_R f) :=
  let d2 : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.cauchyfy f.weaken (.app .succ (.app .succ (.var .vz)))
  let pn : Term F (Ty.nat :: Γ) Ty.nat := .app Term.pow2neg_Q (.var .vz)
  Derivable.mp
    (le_R_of_bound Term.zero_R (Term.app2 Term.add_R f f) (by
      rw [zero_R_weaken, add_R_app_weaken]
      pmode
      prw (cauchyfy_zero_R (.app .succ (.var .vz)))
      prw (cauchyfy_add_R f.weaken f.weaken (.app .succ (.var .vz)))
      papplym (lt_Q_congr (Term.app2 Term.add_Q (.app Term.neg_Q d2) (.app Term.neg_Q d2)) pn
        (Term.app2 Term.sub_Q Term.zero_Q (Term.app2 Term.add_Q d2 d2)) pn
        (eqQsym (eqQtrans (sub_Q_zero_l (Term.app2 Term.add_Q d2 d2)) (neg_Q_add_Q d2 d2)))
        (eq_Q_refl_inst pn))
      pthm h))
    (nonneg_of_add_self_nonneg_core f)

-- ── From Kohlenbach, *Applied Proof Theory*, §4.1 ───────────────────────────
--
-- Three facts the book states and uses but does not prove. They are NOT in
-- `Metateorema-New3`, which is why they were missing here; added 2026-09-01
-- after reading the book directly.
--
-- Note the book's own calibration of effort: it calls the ℚ ordered-field
-- package "easily verified" (p. 79) — that is the ~4,600 lines of
-- `RationalNumbers.lean` — and asserts the ℝ package in one parenthesis
-- (p. 80) with no proof at all.

/-- The constant real sequence at a rational code — the book's `r ↦ λn.⟨r⟩` embedding
    of ℚ into ℝ (p. 80). `⟨2^{-k}⟩_ℝ` is `const_R (pow2neg_Q k)`. -/
def const_R {Γ : Ctx ι} (q : Term F Γ Ty.nat) : Term F Γ (realTy ι) :=
  Term.lam q.weaken

/-- **Lemma 4.2** (Kohlenbach p. 80). `f̂(k)` is a rational `2^{-k}`-approximation of `f`:

    `WE-HA^ω↾ ⊢ ∀f,k. |f −_ℝ λn.f̂(k)|_ℝ <_ℝ ⟨2^{-k}⟩_ℝ`

    This is the workhorse for the tightness estimates that block Class C — it is what
    lets a proof move between a real and a rational approximation of it at a chosen
    index, which is exactly what the five-term split needs.

    **Worked out 2026-09-01; see `REALS_PLAN.md` §0.8.** The goal reduces to
    `∃n. 2^{-k} −ℚ |f̂(n+2) −ℚ f̂(k)| ≥ℚ 2^{-n}`, and the crude telescoping bound falls short
    by a factor of 4 *at every `n`*. The witness has to be `n := max(k, rat_den d)` with
    `d := 2^{-(k+1)} −ℚ |f̂(k) −ℚ f̂(k+1)|` — the Cauchy slack at index `k`, positive for
    every `f` because `cauchyState_cauchy` is strict. `pow2neg_rat_den_le` (proved) is the
    Archimedean step that makes that witness work; what is still missing is the triangle
    inequality (forward *and* reverse), the refined telescoping induction, and
    `cauchyfy_const` at an arbitrary constant. Note that with `le_R` in place of `lt_R` the
    statement is Π₁⁰ and needs no witness at all. -/
def approx_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all Ty.nat
        (lt_R
          (Term.app Term.abs_R
            (Term.app2 Term.sub_R
              (.var (.vs .vz))
              (const_R (Term.app (Term.app Term.cauchyfy (.var (.vs .vz))) (.var .vz)))))
          (const_R (.app Term.pow2neg_Q (.var .vz)))))) :=
  sorry

/-- **Lemma 4.3** (Kohlenbach p. 80). Cauchy completeness of ℝ:

    `∀Φ^{1(0)}(∀n,m,k (n ≤ m → n ≤ k → |Φm −_ℝ Φk|_ℝ ≤_ℝ ⟨2^{-n}⟩)
                → ∃f¹ ∀n (|Φn −_ℝ f|_ℝ ≤_ℝ ⟨2^{-n}⟩))`

    The book notes the witness is definable outright — `f k := Φ(k+3)(k+3)` — so the
    `∃` should not need to be found by search. -/
def cauchy_complete_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all (Ty.nat →ₜ rTy)
        (Formula.all Ty.nat (Formula.all Ty.nat (Formula.all Ty.nat
            (Formula.eq0 (Term.app2 Term.monus (.var (.vs (.vs .vz))) (.var (.vs .vz)))
               Term.zero →ᶠ
             Formula.eq0 (Term.app2 Term.monus (.var (.vs (.vs .vz))) (.var .vz))
               Term.zero →ᶠ
             le_R
               (Term.app Term.abs_R
                 (Term.app2 Term.sub_R
                   (Term.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
                   (Term.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))))
               (const_R (.app Term.pow2neg_Q (.var (.vs (.vs .vz))))))))
          →ᶠ Formula.ex rTy (Formula.all Ty.nat
              (le_R
                (Term.app Term.abs_R
                  (Term.app2 Term.sub_R
                    (Term.app (.var (.vs (.vs .vz))) (.var .vz))
                    (.var (.vs .vz))))
                (const_R (.app Term.pow2neg_Q (.var .vz))))))) :=
  sorry

/-- Kohlenbach p. 430 (cited as Remark `rmrk:bound-on-real` in `real-numbers.tex`):

    `|α|_ℝ ≤_ℝ (α(0) + 1)_ℝ`

    This is the majorization fact `mul_R`'s operand bound silently relies on — a code
    dominates the magnitude it encodes. It is Kohlenbach's lemma, not an invention of
    this development, and `mul_R` should not be "fixed" to avoid it. -/
def abs_R_bound :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (le_R (Term.app Term.abs_R (.var .vz))
              (Term.app Term.embed_nat_R
                (.app .succ (Term.app (.var .vz) Term.zero))))) :=
  sorry

end OrderedFieldAxioms

-- ============================================================================
-- Axiom hygiene: every axiom claimed proved above is checked here
-- ============================================================================
-- A falling `sorry` count is not evidence (CLAUDE.md note 9); these are.

#print axioms eq_R_refl
#print axioms eq_R_sym
#print axioms eq_R_trans
#print axioms add_eq_zero_R
#print axioms add_zero_R
#print axioms add_zero_R_core
#print axioms add_assoc_R
#print axioms add_assoc_R_core
#print axioms add_neg_R
#print axioms add_neg_R_core
#print axioms cauchyState_neg
#print axioms cauchyfy_neg
#print axioms cauchyfy_add_R
#print axioms cauchy_pair_step
#print axioms eqR_tail
#print axioms eqR_le
#print axioms eqR_strict
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

end Metatheorems
