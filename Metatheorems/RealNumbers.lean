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
  sorry

/-- ⊢ ∀f : ℝ. f +_ℝ 0_ℝ =_ℝ f -/
def add_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz) Term.zero_R)
              (.var .vz))) :=
  sorry

/-- ⊢ ∀f : ℝ. f +_ℝ neg_R(f) =_ℝ 0_ℝ -/
def add_neg_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy
        (eq_R (Term.app2 Term.add_R (.var .vz)
                (.app Term.neg_R (.var .vz)))
              Term.zero_R)) :=
  sorry

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

/-- ⊢ ∀f,g : ℝ. f ≤_ℝ g ∧ g =_ℝ 0 → f =_ℝ 0

**This statement is FALSE and cannot be proved. It needs a non-negativity hypothesis.**

Assessed 2026-09-02. Take `f := λn.⟨−1⟩_ℚ` and `g := 0_ℝ`. Then

* `le_R f g` unfolds to `¬ lt_R g f`, i.e. `¬∃n (f̂(n+1) −_ℚ ĝ(n+1) ≥_ℚ 2^{-n})`. Here that
  difference is `−1`, which is below every `2^{-n}`, so the `∃` is empty and `f ≤_ℝ g` holds;
* `g =_ℝ 0_ℝ` holds (`cauchyfy_zero_R`);
* `f =_ℝ 0_ℝ` fails already at `n = 0`: it asks `|−1|_ℚ <_ℚ ⟨2^{-0}⟩_ℚ`, i.e. `1 <_ℚ 1`.

So the universally quantified formula is false in the standard model and hence not derivable.
`f ≤_ℝ 0` says nothing about how far *below* `0` the real `f` is.

What `MetricSpaces.admissibleEqX.eqx_trans` actually needs is the version with the missing
hypothesis, e.g.

    ∀f,g. 0_ℝ ≤_ℝ f  ∧  f ≤_ℝ g  ∧  g =_ℝ 0_ℝ  →  f =_ℝ 0_ℝ

and then `0_ℝ ≤_ℝ d(x,z)` has to be *derived* from the pseudo-metric premises — it is
available, since `0 =_ℝ d(x,x) ≤_ℝ d(x,y) +_ℝ d(y,x) =_ℝ d(x,y) +_ℝ d(x,y)` by
`ax_refl`/`ax_sym`/`ax_triangle` — but nothing in this file or `MetricSpaces.lean` derives it
yet. Fixing the statement is therefore a *design* decision about the metric-space layer, not
a proof step, and it is left to whoever owns that layer.

Note also that unlike `eq_R_trans` and `add_eq_zero_R`, the corrected statement is not an
estimate: `le_R` is a negated `∃`, so it is Markov-flavoured and needs a different toolkit. -/
def le_zero_eq_zero_R :
    Derivable F al Premises (Γ := Γ)
      (Formula.all rTy (Formula.all rTy
        (le_R (.var (.vs .vz)) (.var .vz)
          ∧ᶠ eq_R (.var .vz) Term.zero_R
          →ᶠ eq_R (.var (.vs .vz)) Term.zero_R))) :=
  sorry

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
#print axioms cauchyfy_add_R
#print axioms cauchy_pair_step
#print axioms eqR_tail
#print axioms eqR_le
#print axioms eqR_strict
#print axioms lt_irrefl_R
#print axioms zero_lt_one_R
-- The `cauchyfy` theory the remaining axioms rest on:
#print axioms cauchy_inv
#print axioms cauchyState_cauchy
#print axioms cauchyfy_zero
#print axioms cauchyState_id_of_cauchy
#print axioms cauchyfy_zero_R
#print axioms cauchyfy_one_R

end Metatheorems
