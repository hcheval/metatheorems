/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetricTransfer
import Metatheorems.CodeReal
import Mathlib.Analysis.Normed.Module.Basic

namespace Metatheorems

/-!
# Real normed linear spaces

Kohlenbach's `A^ω[X,‖·‖]`: the case the `ι`/`κ` split was done for. One base type `X`
(`ι = Unit`) and **three** function constants over it (`κ = Normed.κ`):

    +   : X →ₜ X →ₜ X          smul : ℝ →ₜ X →ₜ X          ‖·‖ : X →ₜ ℝ

The metric is still the structural `Term.dist ()`, so the pseudometric theory and the whole
metric `EqXInterp` (`MetricTransfer.lean`) are inherited; what ties `d` to the norm is an
**axiom**, `d(x,y) =ℝ ‖x + (−1)·y‖`, and `x =_X y` is, as everywhere, `d(x,y) =ℝ 0ℝ`.

## Two differences from the hyperbolic case

* **Scalars range over all of type `1`, unrestricted** — there is no `[0,1]`-retraction. The
  majorant of `smul` is therefore *not* uniform in the scalar: it is
  `λα* n. (α*(0) + 1)·n`, using `|r_α| ≤ α(0) + 1` (`abs_codeReal_le`, `CodeReal.lean`), which
  is what Kohlenbach's `≽`-majorant for scalar multiplication is built on.
* **`0_X` is majorized by `0`, with no parameter.** The reference point is `a := 0_X`
  (Kohlenbach, p. 402–403; ARCHITECTURE.md §13), so `d(a, 0_X) = 0` and the majorant is the
  literal `0`. Where `MetricModel.constMajorants` takes `n₀ ≥ d(a, 0_X)` as an input,
  `NormedModel.constMajorants` takes nothing. On that axis normed is cheaper than metric.

## The model

Mathlib's `NormedAddCommGroup E` + `NormedSpace ℝ E`, with `d x y := ‖x − y‖`. The `MetricModel`
it induces (separation is `norm_sub_eq_zero`) feeds `MetricTransfer.lean` unchanged.

## Axioms

The vector-space axioms (1)–(8) with `−x := (−1)·x`, the two norm axioms, and the `d`/norm
link. All eleven are purely universal and ∨-free. The exact list should be checked against
Kohlenbach's Definition for `A^ω[X,‖·‖]` before it is relied on; what is fixed here is the
*shape* — every axiom is a `∀`-closure of `=_X`, `=ℝ` or `≤ℝ` between terms.
-/

open Formula

-- ============================================================================
-- Signature
-- ============================================================================

/-- The three function constants. -/
inductive Normed.κ
  | add
  | smul
  | norm

/-- `+ : X →ₜ X →ₜ X`, `smul : ℝ →ₜ X →ₜ X`, `‖·‖ : X →ₜ ℝ`. -/
def Normed.F : Normed.κ → Ty MetricSpace.ι
  | .add  => xTy →ₜ xTy →ₜ xTy
  | .smul => realTy MetricSpace.ι →ₜ xTy →ₜ xTy
  | .norm => xTy →ₜ realTy MetricSpace.ι

abbrev Normed.vadd {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ (xTy →ₜ xTy →ₜ xTy) :=
  Term.func Normed.κ.add

abbrev Normed.vsmul {Γ : Ctx MetricSpace.ι} :
    Term Normed.F Γ (realTy MetricSpace.ι →ₜ xTy →ₜ xTy) :=
  Term.func Normed.κ.smul

abbrev Normed.vnorm {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ (xTy →ₜ realTy MetricSpace.ι) :=
  Term.func Normed.κ.norm

abbrev Normed.d {Γ : Ctx MetricSpace.ι} :
    Term Normed.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.dist ()

abbrev Normed.zero {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ xTy := Term.zeroX ()

/-- `−1ℝ`, the scalar that gives additive inverses. -/
abbrev Normed.negOne {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ (realTy MetricSpace.ι) :=
  .app Term.neg_R Term.one_R

-- ============================================================================
-- The axioms
-- ============================================================================

/-- (1) `∀x y. x + y =_X y + x`. -/
def Normed.ax_add_comm {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy (Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vadd (.var (.vs .vz)) (.var .vz))
      (Term.app2 Normed.vadd (.var .vz) (.var (.vs .vz)))))

/-- (2) `∀x y z. (x + y) + z =_X x + (y + z)`. -/
def Normed.ax_add_assoc {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vadd (Term.app2 Normed.vadd (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.var .vz))
      (Term.app2 Normed.vadd (.var (.vs (.vs .vz)))
        (Term.app2 Normed.vadd (.var (.vs .vz)) (.var .vz))))))

/-- (3) `∀x. x + 0_X =_X x`. -/
def Normed.ax_add_zero {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy
    (eqAtType xTy (Term.app2 Normed.vadd (.var .vz) Normed.zero) (.var .vz))

/-- (4) `∀x. x + (−1)·x =_X 0_X`. -/
def Normed.ax_add_neg {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vadd (.var .vz) (Term.app2 Normed.vsmul Normed.negOne (.var .vz)))
      Normed.zero)

/-- (5) `∀α x y. α·(x + y) =_X α·x + α·y`. -/
def Normed.ax_smul_add {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all rTy (Formula.all xTy (Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vsmul (.var (.vs (.vs .vz)))
        (Term.app2 Normed.vadd (.var (.vs .vz)) (.var .vz)))
      (Term.app2 Normed.vadd
        (Term.app2 Normed.vsmul (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (Term.app2 Normed.vsmul (.var (.vs (.vs .vz))) (.var .vz))))))

/-- (6) `∀α β x. (α +ℝ β)·x =_X α·x + β·x`. -/
def Normed.ax_add_smul {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all rTy (Formula.all rTy (Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vsmul
        (Term.app2 Term.add_R (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
      (Term.app2 Normed.vadd
        (Term.app2 Normed.vsmul (.var (.vs (.vs .vz))) (.var .vz))
        (Term.app2 Normed.vsmul (.var (.vs .vz)) (.var .vz))))))

/-- (7) `∀α β x. (α ·ℝ β)·x =_X α·(β·x)`. -/
def Normed.ax_smul_smul {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all rTy (Formula.all rTy (Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vsmul
        (Term.app2 Term.mul_R (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
      (Term.app2 Normed.vsmul (.var (.vs (.vs .vz)))
        (Term.app2 Normed.vsmul (.var (.vs .vz)) (.var .vz))))))

/-- (8) `∀x. 1ℝ·x =_X x`. -/
def Normed.ax_one_smul {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy
    (eqAtType xTy (Term.app2 Normed.vsmul Term.one_R (.var .vz)) (.var .vz))

/-- (9) `∀α x. ‖α·x‖ =ℝ |α| ·ℝ ‖x‖`. -/
def Normed.ax_norm_smul {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all rTy (Formula.all xTy
    (eq_R
      (.app Normed.vnorm (Term.app2 Normed.vsmul (.var (.vs .vz)) (.var .vz)))
      (Term.app2 Term.mul_R (.app Term.abs_R (.var (.vs .vz))) (.app Normed.vnorm (.var .vz)))))

/-- (10) `∀x y. ‖x + y‖ ≤ℝ ‖x‖ +ℝ ‖y‖`. -/
def Normed.ax_norm_add {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy (Formula.all xTy
    (le_R_pu
      (.app Normed.vnorm (Term.app2 Normed.vadd (.var (.vs .vz)) (.var .vz)))
      (Term.app2 Term.add_R (.app Normed.vnorm (.var (.vs .vz))) (.app Normed.vnorm (.var .vz)))))

/-- (11) `∀x y. d(x,y) =ℝ ‖x + (−1)·y‖` — the metric is the norm distance. -/
def Normed.ax_dist {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy (Formula.all xTy
    (eq_R
      (Term.app2 Normed.d (.var (.vs .vz)) (.var .vz))
      (.app Normed.vnorm
        (Term.app2 Normed.vadd (.var (.vs .vz))
          (Term.app2 Normed.vsmul Normed.negOne (.var .vz))))))

-- ============================================================================
-- The premise set
-- ============================================================================

/-- The eleven axioms, in every context. -/
def Normed.Premises : PremiseSet Normed.F
  | ⟨_, A⟩ =>
      A = Normed.ax_add_comm ∨ A = Normed.ax_add_assoc ∨ A = Normed.ax_add_zero
      ∨ A = Normed.ax_add_neg ∨ A = Normed.ax_smul_add ∨ A = Normed.ax_add_smul
      ∨ A = Normed.ax_smul_smul ∨ A = Normed.ax_one_smul ∨ A = Normed.ax_norm_smul
      ∨ A = Normed.ax_norm_add ∨ A = Normed.ax_dist

theorem Normed.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Normed.F Γ'),
      Normed.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := by
  intro Γ' B h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

theorem Normed.premises_vf :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Normed.F Γ'),
      Normed.Premises ⟨Γ', B⟩ → B.isVFree = true := by
  intro Γ' B h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

/-- `⊢ (11)`, the `d`/norm link — the axiom a derivation about the metric reaches for. -/
def Normed.dist_ax {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable Normed.F a Normed.Premises (Normed.ax_dist (Γ := Γ)) :=
  .premise (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr rfl))))))))))

-- ============================================================================
-- The model
-- ============================================================================

/-- **A normed model**: a Mathlib real normed space. -/
structure NormedModel where
  /-- The carrier. -/
  E : Type
  [normedGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace ℝ E]

attribute [instance] NormedModel.normedGroup NormedModel.normedSpace

/-- The metric model `d(x,y) := ‖x − y‖`, reference point and `0_X` both `0`. An `abbrev`, so
that `M.toMetricModel.carrier` is `M.E` at elaboration time. -/
noncomputable abbrev NormedModel.toMetricModel (M : NormedModel) : MetricModel where
  carrier := M.E
  -- parenthesised: the norm notation would otherwise swallow the next field as an argument
  d := fun x y => (‖x - y‖)
  d_nonneg := fun _ _ => norm_nonneg _
  d_self := fun x => by simp
  d_comm := fun x y => norm_sub_rev x y
  d_triangle := fun x y z => by
    have := dist_triangle x y z
    simpa [dist_eq_norm] using this
  d_eq_zero := fun x y h => sub_eq_zero.mp (norm_eq_zero.mp h)
  zeroX := 0
  ref := 0

/-- The interpretation of the three constants: `+`, `α • x` through `codeReal`, and
`(‖x‖)◦`. -/
noncomputable def NormedModel.funcInterp (M : NormedModel) :
    (c : Normed.κ) → Ty.interpret (fun () => M.E) (Normed.F c)
  | .add  => fun x y => x + y
  | .smul => fun f x => codeReal f • x
  | .norm => fun x => Rounding.roundR (‖x‖)

/-- The `SpaceInterp`. -/
noncomputable def NormedModel.si (M : NormedModel) : SpaceInterp (fun () => M.E) Normed.F where
  funcInterp := M.funcInterp
  zeroInterp := fun () => 0
  distInterp := fun () => fun x y => Rounding.roundR (‖x - y‖)

/-- The base relation, unfolded: `n ≽ x` iff `‖x‖ ≤ n`. -/
theorem NormedModel.base_iff (M : NormedModel) (n : ℕ) (x : M.E) :
    M.toMetricModel.base () n x ↔ ‖x‖ ≤ (n : ℝ) := by
  change ‖(0 : M.E) - x‖ ≤ (n : ℝ) ↔ ‖x‖ ≤ (n : ℝ)
  rw [zero_sub, norm_neg]

/-- `base_iff` in the shape the majorization clauses present it: `bezemMaj … xTy n x`. The
binder types are the `hat`-interpreted ones, because `Ty.hat` is not reducible and `rw` would
otherwise not match. -/
theorem NormedModel.bezem_base_iff (M : NormedModel)
    (n : Ty.interpret (fun () => M.E) xTy.hat) (x : Ty.interpret (fun () => M.E) xTy) :
    bezemMaj (X := fun () => M.E) M.toMetricModel.base xTy n x ↔ ‖x‖ ≤ Nat.cast (R := ℝ) n :=
  M.base_iff n x

/-- The bound behind the `+` majorant, over honest `ℕ` variables. -/
theorem NormedModel.add_bound (M : NormedModel) (n₁ n₂ : ℕ) (x y : M.E)
    (hx : ‖x‖ ≤ (n₁ : ℝ)) (hy : ‖y‖ ≤ (n₂ : ℝ)) :
    ‖x + y‖ ≤ ((n₁ + n₂ : ℕ) : ℝ) := by
  push_cast
  exact (norm_add_le x y).trans (add_le_add hx hy)

/-- The bound behind the `smul` majorant, over honest `ℕ` variables: `‖r_f • x‖ = |r_f|·‖x‖`
with `|r_f| ≤ f(0) + 1 ≤ f*(0) + 1` (`abs_codeReal_le`). -/
theorem NormedModel.smul_bound (M : NormedModel) (f_star f : ℕ → ℕ) (h0 : f 0 ≤ f_star 0)
    (n : ℕ) (x : M.E) (hx : ‖x‖ ≤ (n : ℝ)) :
    ‖codeReal f • x‖ ≤ (((f_star 0 + 1) * n : ℕ) : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs]
  have hc := abs_codeReal_le f
  have h0' : (f 0 : ℝ) + 1 ≤ (f_star 0 : ℝ) + 1 := by
    have : (f 0 : ℝ) ≤ f_star 0 := by exact_mod_cast h0
    linarith
  push_cast
  exact mul_le_mul (hc.trans h0') hx (norm_nonneg _) (by positivity)

-- ============================================================================
-- Majorants
-- ============================================================================

/-- `+ ↦ λn₁ n₂. n₁ + n₂`. -/
def NormedModel.addMajorant (M : NormedModel) :
    Ty.interpret (fun () => M.E) (xTy →ₜ xTy →ₜ xTy).hat :=
  fun (n₁ : ℕ) (n₂ : ℕ) => (n₁ + n₂ : ℕ)

/-- `‖·‖ ↦ λn. (n)◦`. -/
noncomputable def NormedModel.normMajorant (M : NormedModel) :
    Ty.interpret (fun () => M.E) (xTy →ₜ realTy MetricSpace.ι).hat :=
  fun (n : ℕ) => Rounding.roundR (n : ℝ)

/-- `smul ↦ λα* n. (α*(0) + 1)·n` — **not** uniform in the scalar, unlike `W`'s majorant:
scalars are unrestricted, and `|r_α| ≤ α(0) + 1 ≤ α*(0) + 1` is all a majorant of `α` gives. -/
def NormedModel.smulMajorant (M : NormedModel) :
    Ty.interpret (fun () => M.E) (realTy MetricSpace.ι →ₜ xTy →ₜ xTy).hat :=
  fun (f : ℕ → ℕ) (n : ℕ) => ((f 0 + 1) * n : ℕ)

theorem NormedModel.add_maj_at (M : NormedModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.E) M.toMetricModel.base (xTy →ₜ xTy →ₜ xTy)
      M.addMajorant (M.si.funcInterp .add) := by
  intro _ _
  unfold NormedModel.addMajorant
  refine ⟨?_, ?_⟩
  · intro n₁ x hx
    refine ⟨?_, ?_⟩
    · intro n₂ y hy
      rw [M.bezem_base_iff] at hx hy ⊢
      exact M.add_bound n₁ n₂ x y hx hy
    · intro _ _ h
      exact Nat.add_le_add_left h n₁
  · intro n₁' n₁ h
    refine ⟨?_, ?_⟩
    · intro _ _ h₂
      exact Nat.add_le_add h h₂
    · intro _ _ h₂
      exact Nat.add_le_add_left h₂ n₁'

theorem NormedModel.norm_maj_at (M : NormedModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.E) M.toMetricModel.base (xTy →ₜ realTy MetricSpace.ι)
      M.normMajorant (M.si.funcInterp .norm) := by
  intro _ _
  unfold NormedModel.normMajorant
  refine ⟨?_, ?_⟩
  · intro n x hx
    rw [M.bezem_base_iff] at hx
    exact Rounding.roundR_maj_pair (by positivity) hx
  · intro n' n h
    exact Rounding.roundR_maj_pair (by positivity) (by exact_mod_cast h)

theorem NormedModel.smul_maj_at (M : NormedModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.E) M.toMetricModel.base
      (realTy MetricSpace.ι →ₜ xTy →ₜ xTy)
      M.smulMajorant (M.si.funcInterp .smul) := by
  intro _ _
  unfold NormedModel.smulMajorant
  refine ⟨?_, ?_⟩
  · intro f_star f hf
    -- `f 0 ≤ f* 0`, from the first clause of `f* ≽ f` at type `1`. Stated through the explicit
    -- `ℕ` instance: the operands' types are only *definitionally* `ℕ`.
    have h0 : @LE.le ℕ _ (f (0 : ℕ)) (f_star (0 : ℕ)) := hf.1 (0 : ℕ) (0 : ℕ) (Nat.le_refl 0)
    refine ⟨?_, ?_⟩
    · intro n x hx
      rw [M.bezem_base_iff] at hx ⊢
      exact M.smul_bound f_star f h0 n x hx
    · intro _ _ h
      exact Nat.mul_le_mul_left _ h
  · intro f' f hff
    have h0 : @LE.le ℕ _ (f (0 : ℕ)) (f' (0 : ℕ)) := hff.1 (0 : ℕ) (0 : ℕ) (Nat.le_refl 0)
    refine ⟨?_, ?_⟩
    · intro _ _ h
      exact Nat.mul_le_mul (Nat.add_le_add_right h0 1) h
    · intro _ _ h
      exact Nat.mul_le_mul_left _ h

/-- Every constant is majorizable, by cases. -/
theorem NormedModel.func_maj (M : NormedModel) (c : Normed.κ) :
    ∃ f_star : ℕ → Ty.interpret (fun () => M.E) (Normed.F c).hat,
      ∀ n ≥ 0, bezemMaj (X := fun () => M.E) M.toMetricModel.base (Normed.F c)
        (f_star n) (M.si.funcInterp c) := by
  cases c with
  | add => exact ⟨fun _ => M.addMajorant, M.add_maj_at 0⟩
  | smul => exact ⟨fun _ => M.smulMajorant, M.smul_maj_at 0⟩
  | norm => exact ⟨fun _ => M.normMajorant, M.norm_maj_at 0⟩

/-- `0_X = a`, so `0` majorizes it. -/
theorem NormedModel.zeroX_maj_zero (M : NormedModel) :
    bezemMaj (X := fun () => M.E) M.toMetricModel.base (Ty.base ()) (0 : ℕ)
      (M.si.zeroInterp ()) := by
  change ‖(0 : M.E) - 0‖ ≤ ((0 : ℕ) : ℝ)
  simp

/-- **A normed model is an abstract majorizability.** -/
noncomputable def NormedModel.abstractMajorizability (M : NormedModel) :
    AbstractMajorizability M.si :=
  bezemAbstract M.si M.toMetricModel.base 0
    (bezem_zero_maj M.toMetricModel.base 0)
    (bezem_succ_maj M.toMetricModel.base 0)
    (fun ρ => bezem_prec_maj M.toMetricModel.base_mono 0 ρ)
    M.func_maj
    (fun () => ⟨fun _ => (0 : ℕ), fun _ _ => M.zeroX_maj_zero⟩)
    (fun () => M.toMetricModel.dist_maj_gen M.si (fun _ _ => rfl) 0)

/-- **The majorants as data — with no parameter at all.** `0_X ↦ 0`; the metric model's `n₀`
has disappeared because the reference point is `0_X` itself. -/
noncomputable def NormedModel.constMajorants (M : NormedModel) :
    ConstMajorants M.abstractMajorizability where
  zeroM := fun _ => 0
  zeroM_maj := fun _ _ => Nat.le_refl 0
  succM := fun _ => Nat.succ
  succM_maj := fun _ _ =>
    ⟨fun _ _ h => Nat.succ_le_succ h, fun _ _ h => Nat.succ_le_succ h⟩
  precM := fun ρ _ => fun y_star z_star n => recMaj ρ y_star z_star n
  precM_maj := fun ρ => bezem_prec_maj_at M.toMetricModel.base_mono 0 ρ
  funcM := fun c _ => match c with
    | .add => M.addMajorant
    | .smul => M.smulMajorant
    | .norm => M.normMajorant
  funcM_maj := fun c => match c with
    | .add => M.add_maj_at 0
    | .smul => M.smul_maj_at 0
    | .norm => M.norm_maj_at 0
  zeroXM := fun _ _ => 0
  zeroXM_maj := fun () _ _ => M.zeroX_maj_zero
  distM := fun _ _ => M.toMetricModel.distMajorant
  distM_maj := fun () => M.toMetricModel.dist_maj_at_gen M.si (fun _ _ => rfl) 0

section ComputesDemo

/-- `‖0_X + 0_X‖`'s majorant at precision `0`: `(0 + 0)◦(0) = j(0, 1) = triag(1) + 0 = 1`.
No hypothesis on the model at all. -/
example (M : NormedModel) :
    (1 : ℕ) = closedMajorizer M.constMajorants
      (Term.app Normed.vnorm (Term.app2 Normed.vadd (Term.zeroX ()) (Term.zeroX ())))
      ((0 : ℕ)) := by
  simp only [closedMajorizer, termMajorizer, NormedModel.constMajorants,
    NormedModel.abstractMajorizability, bezemAbstract, Term.app2, NormedModel.addMajorant,
    NormedModel.normMajorant]
  rw [show ((0 + 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) by norm_num, Rounding.roundR_natCast]
  decide

end ComputesDemo

-- ============================================================================
-- Equality interpretation, soundness, metatheorems
-- ============================================================================

/-- The metric `EqXInterp`, transferred. -/
noncomputable def NormedModel.eqXInterp (M : NormedModel) :
    EqXInterp (fun () => M.E) Normed.F M.si :=
  M.toMetricModel.eqXInterp_gen M.si (fun _ _ => rfl)

/-- The axioms hold in the model. **NOT discharged — this is the one remaining obligation of
the space tower**, and it is NOT a pattern to copy. W-hyperbolic and CAT(0) have no such
definition and no `hax` binder any more: their `axiomsHold` are theorems, stated inline
(`WHyperbolicModel.axiomsHold`, `CAT0Model.axiomsHold`). A surviving `AxiomsHold` binder means
"not done yet", not "this is how spaces are built". Discharging it needs `codeReal`-level
evaluation of the norm and scalar-multiplication constants, which does not exist yet. -/
def NormedModel.AxiomsHold (M : NormedModel) : Prop :=
  ∀ {Γ : Ctx MetricSpace.ι} (A : Formula Normed.F Γ), Normed.Premises ⟨Γ, A⟩ →
    ∀ env : Ctx.interpret (fun () => M.E) Γ, Formula.interpret M.si A env

def NormedModel.spremise (M : NormedModel) (hax : M.AxiomsHold) :
    ∀ (Γ : Ctx MetricSpace.ι) (B : Formula Normed.F Γ),
      Normed.Premises ⟨Γ, B⟩ → SRealizer M.si B :=
  fun Γ B hp =>
    srealizer_of_pu B (Normed.premises_pu Γ B hp) (Normed.premises_vf Γ B hp) (hax B hp)

theorem NormedModel.soundness (M : NormedModel) (hax : M.AxiomsHold)
    {Γ : Ctx MetricSpace.ι} {allowed : Allowed} {A : Formula Normed.F Γ}
    (h : Derivable Normed.F allowed Normed.Premises A) :
    ∀ env : Ctx.interpret (fun () => M.E) Γ, Formula.interpret M.si A env :=
  M.toMetricModel.soundness_gen M.si (fun _ _ => rfl) hax h

/-- **The normed-space metatheorem** (extended input). -/
theorem NormedModel.normed_metatheorem (M : NormedModel) (hax : M.AxiomsHold)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula Normed.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι Normed.κ Normed.F Allowed.extended Normed.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.E) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.E) ρ) (x_star : Ty.interpret (fun () => M.E) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem M.eqXInterp (M.spremise hax) M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- **The normed-space metatheorem, from a classical proof.** -/
theorem NormedModel.normed_metatheorem_classical (M : NormedModel) (hax : M.AxiomsHold)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula Normed.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι Normed.κ Normed.F Allowed.classical Normed.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.E) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.E) ρ) (x_star : Ty.interpret (fun () => M.E) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem_classical M.eqXInterp
    (ntStable_of_pu Normed.premises_pu) (M.spremise hax)
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms Normed.premises_pu
#print axioms NormedModel.smul_maj_at
#print axioms NormedModel.abstractMajorizability
#print axioms NormedModel.constMajorants
#print axioms NormedModel.eqXInterp
#print axioms NormedModel.soundness
#print axioms NormedModel.normed_metatheorem
#print axioms NormedModel.normed_metatheorem_classical

end Metatheorems
