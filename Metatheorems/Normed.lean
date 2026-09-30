/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetricTransfer
import Metatheorems.CodeReal
import Metatheorems.CodeRealOps
import Mathlib.Analysis.Normed.Module.Basic

namespace Metatheorems

/-!
# Real normed linear spaces

Kohlenbach's `A^ω[X,‖·‖]`: the case the `ι`/`κ` split was done for. One base type `X`
(`ι = Unit`) and **five** function constants over it (`κ = Normed.κ`):

    +   : X →ₜ X →ₜ X     smul : ℝ →ₜ X →ₜ X     ‖·‖ : X →ₜ ℝ     − : X →ₜ X     1_X : X

`1_X` is *nullary* — a constant of type `X`, which the framework supports directly (`Term.func`
at a base type). `−` is **primitive**, not `(−1)·x`: a defined operation inherits its definiens' majorant.

The metric is still the structural `Term.dist ()`, so the pseudometric theory and the whole
metric `EqXInterp` (`MetricTransfer.lean`) are inherited; what ties `d` to the norm is an
**axiom**, `d(x,y) =ℝ ‖x + (−y)‖`, and `x =_X y` is, as everywhere, `d(x,y) =ℝ 0ℝ`.

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

Mathlib's `NormedAddCommGroup E` + `NormedSpace ℝ E` + `Nontrivial E`, with `d x y := ‖x − y‖`.
The `MetricModel` it induces (separation is `norm_sub_eq_zero`) feeds `MetricTransfer.lean`
unchanged. Nontriviality is what interprets `1_X`: `NormedModel.unitVec` is `‖v‖⁻¹ • v` for a
`v ≠ 0` supplied by `exists_ne 0`, and `norm_unitVec` is `norm_smul_inv_norm`.

## Axioms

The vector-space axioms (1)–(8) — including `x + (−x) =_X 0_X` at the *primitive* `−` — the
three norm axioms (`‖α·x‖`, the triangle inequality, `‖−x‖ =ℝ ‖x‖`), nontriviality
`‖1_X‖ =ℝ 1ℝ`, and the `d`/norm link. All thirteen are purely universal and ∨-free, and
**all thirteen hold in every nontrivial real normed space** (`NormedModel.axiomsHold` below).
The signature and axioms follow Kohlenbach's `A^ω[X,‖·‖]` (Applied Proof Theory §17.3), with
`−_X` and `1_X` as primitive constants.
-/

open Formula

-- Signature

/-- The five function constants. `one` is nullary — a *point* of `X`. -/
inductive Normed.κ
  | add
  | smul
  | norm
  | neg
  | one

/-- `+ : X →ₜ X →ₜ X`, `smul : ℝ →ₜ X →ₜ X`, `‖·‖ : X →ₜ ℝ`, `− : X →ₜ X`, `1_X : X`. -/
def Normed.F : Normed.κ → Ty MetricSpace.ι
  | .add  => xTy →ₜ xTy →ₜ xTy
  | .smul => realTy MetricSpace.ι →ₜ xTy →ₜ xTy
  | .norm => xTy →ₜ realTy MetricSpace.ι
  | .neg  => xTy →ₜ xTy
  | .one  => xTy

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

/-- `− : X →ₜ X`, the primitive additive inverse. -/
abbrev Normed.vneg {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ (xTy →ₜ xTy) :=
  Term.func Normed.κ.neg

/-- `1_X`, the unit vector — a nullary constant of type `X`. -/
abbrev Normed.one {Γ : Ctx MetricSpace.ι} : Term Normed.F Γ xTy :=
  Term.func Normed.κ.one

-- The axioms

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

/-- (4) `∀x. x + (−x) =_X 0_X` — at the **primitive** `−`, as in Kohlenbach's (0). -/
def Normed.ax_add_neg {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy
    (eqAtType xTy
      (Term.app2 Normed.vadd (.var .vz) (.app Normed.vneg (.var .vz)))
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

/-- (11) `‖1_X‖ =ℝ 1ℝ` — Kohlenbach's (9), nontriviality in Skolemized form. No quantifier:
`1_X` is a constant. -/
def Normed.ax_norm_one {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  eq_R (.app Normed.vnorm Normed.one) Term.one_R

/-- (12) `∀x. ‖−x‖ =ℝ ‖x‖` — Kohlenbach's (7) in the "usual" (non-difference) form. -/
def Normed.ax_norm_neg {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy
    (eq_R
      (.app Normed.vnorm (.app Normed.vneg (.var .vz)))
      (.app Normed.vnorm (.var .vz)))

/-- (13) `∀x y. d(x,y) =ℝ ‖x + (−y)‖` — the metric is the norm distance, at Kohlenbach's
`x −_X y :≡ +_X(x, −_X y)`. -/
def Normed.ax_dist {Γ : Ctx MetricSpace.ι} : Formula Normed.F Γ :=
  Formula.all xTy (Formula.all xTy
    (eq_R
      (Term.app2 Normed.d (.var (.vs .vz)) (.var .vz))
      (.app Normed.vnorm
        (Term.app2 Normed.vadd (.var (.vs .vz))
          (.app Normed.vneg (.var .vz))))))

-- The premise set

/-- The thirteen axioms, in every context. -/
def Normed.Premises : PremiseSet Normed.F
  | ⟨_, A⟩ =>
      A = Normed.ax_add_comm ∨ A = Normed.ax_add_assoc ∨ A = Normed.ax_add_zero
      ∨ A = Normed.ax_add_neg ∨ A = Normed.ax_smul_add ∨ A = Normed.ax_add_smul
      ∨ A = Normed.ax_smul_smul ∨ A = Normed.ax_one_smul ∨ A = Normed.ax_norm_smul
      ∨ A = Normed.ax_norm_add ∨ A = Normed.ax_norm_one ∨ A = Normed.ax_norm_neg
      ∨ A = Normed.ax_dist

theorem Normed.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Normed.F Γ'),
      Normed.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := by
  intro Γ' B h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

theorem Normed.premises_vf :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula Normed.F Γ'),
      Normed.Premises ⟨Γ', B⟩ → B.isVFree = true := by
  intro Γ' B h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

-- The `Or`-chains below use `<|` rather than nested parentheses. With thirteen disjuncts the
-- paren form is write-only and miscounts silently into a parse error far from the cause.

/-- `⊢ (13)`, the `d`/norm link — the axiom a derivation about the metric reaches for.
Last of the thirteen, so twelve `Or.inr`. -/
def Normed.dist_ax {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable Normed.F a Normed.Premises (Normed.ax_dist (Γ := Γ)) :=
  .premise <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| rfl

/-- `⊢ (11)`, nontriviality. Eleventh, so ten `Or.inr` then `Or.inl`. -/
def Normed.norm_one_ax {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable Normed.F a Normed.Premises (Normed.ax_norm_one (Γ := Γ)) :=
  .premise <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inl rfl

/-- `⊢ (12)`, `‖−x‖ =ℝ ‖x‖`. Twelfth, so eleven `Or.inr` then `Or.inl`. -/
def Normed.norm_neg_ax {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable Normed.F a Normed.Premises (Normed.ax_norm_neg (Γ := Γ)) :=
  .premise <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

-- The model

/-- **A normed model**: a Mathlib real normed space, **nontrivial**. Nontriviality is an
instance field; the unit vector is built once, by `NormedModel.unitVec`. -/
structure NormedModel where
  /-- The carrier. -/
  E : Type
  [normedGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace ℝ E]
  [nontrivial : Nontrivial E]

attribute [instance] NormedModel.normedGroup NormedModel.normedSpace NormedModel.nontrivial

/-- Some nonzero vector — the content of `Nontrivial E`. -/
noncomputable def NormedModel.someNonzero (M : NormedModel) : M.E :=
  Classical.choose (exists_ne (0 : M.E))

theorem NormedModel.someNonzero_ne (M : NormedModel) : M.someNonzero ≠ 0 :=
  Classical.choose_spec (exists_ne (0 : M.E))

/-- **The interpretation of `1_X`**: a vector of norm exactly `1`, normalising
`someNonzero`. -/
noncomputable def NormedModel.unitVec (M : NormedModel) : M.E :=
  (‖M.someNonzero‖)⁻¹ • M.someNonzero

@[simp] theorem NormedModel.norm_unitVec (M : NormedModel) : (‖M.unitVec‖) = 1 :=
  norm_smul_inv_norm M.someNonzero_ne

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

/-- The interpretation of the five constants: `+`, `α • x` through `codeReal`, `(‖x‖)◦`,
negation, and the unit vector. -/
noncomputable def NormedModel.funcInterp (M : NormedModel) :
    (c : Normed.κ) → Ty.interpret (fun () => M.E) (Normed.F c)
  | .add  => fun x y => x + y
  | .smul => fun f x => codeReal f • x
  | .norm => fun x => Rounding.roundR (‖x‖)
  | .neg  => fun x => -x
  | .one  => M.unitVec

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

-- Majorants

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

/-- **`− ↦ λn. n`, exactly.** `‖−x‖ = ‖x‖`, and base-majorization at `X` *is* `‖x‖ ≤ n`, so
negation is majorized by the identity with nothing to spare. -/
def NormedModel.negMajorant (M : NormedModel) :
    Ty.interpret (fun () => M.E) (xTy →ₜ xTy).hat :=
  fun (n : ℕ) => n

/-- **`1_X ↦ 1`.** `‖1_X‖ = 1` *is* base-majorization by `1`. -/
def NormedModel.oneMajorant (M : NormedModel) :
    Ty.interpret (fun () => M.E) xTy.hat :=
  (1 : ℕ)

theorem NormedModel.neg_maj_at (M : NormedModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.E) M.toMetricModel.base (xTy →ₜ xTy)
      M.negMajorant (M.si.funcInterp .neg) := by
  intro _ _
  unfold NormedModel.negMajorant
  refine ⟨?_, ?_⟩
  · intro n x hx
    rw [M.bezem_base_iff] at hx ⊢
    change (‖-x‖) ≤ Nat.cast (R := ℝ) n
    rwa [norm_neg]
  · intro _ _ h
    exact h

theorem NormedModel.one_maj_at (M : NormedModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.E) M.toMetricModel.base xTy
      M.oneMajorant (M.si.funcInterp .one) := by
  intro _ _
  rw [M.bezem_base_iff]
  change (‖M.unitVec‖) ≤ ((1 : ℕ) : ℝ)
  rw [M.norm_unitVec]
  norm_num

/-- A vector of norm exactly `n`, for the tightness results below. Needs nontriviality —
in the trivial space no such vector exists for `n > 0`, which is the second thing (11) buys. -/
theorem NormedModel.norm_nsmul_unitVec (M : NormedModel) (n : ℕ) :
    (‖(n : ℝ) • M.unitVec‖) = (n : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, M.norm_unitVec, mul_one, abs_of_nonneg (by positivity)]

/-- **`negMajorant` is TIGHT — pointwise minimal.** *Every* majorant `g` of negation satisfies
`g n ≥ n` at every `n`, so `fun n => n` cannot be improved anywhere: nothing smaller at any
single argument is a majorant. This is the control for the deliverable, stated positively. -/
theorem NormedModel.neg_maj_lower_bound (M : NormedModel)
    (g : Ty.interpret (fun () => M.E) (xTy →ₜ xTy).hat)
    (hg : bezemMaj (X := fun () => M.E) M.toMetricModel.base (xTy →ₜ xTy)
      g (M.si.funcInterp .neg)) (n : ℕ) :
    n ≤ g n := by
  have hx : bezemMaj (X := fun () => M.E) M.toMetricModel.base xTy n ((n : ℝ) • M.unitVec) := by
    rw [M.bezem_base_iff, M.norm_nsmul_unitVec]
  have h := hg.1 n ((n : ℝ) • M.unitVec) hx
  rw [M.bezem_base_iff] at h
  -- `funcInterp .neg x` is `-x` by `rfl`, but not syntactically, so `rw` needs the `change`
  have h2 : (‖-((n : ℝ) • M.unitVec)‖) ≤ Nat.cast (R := ℝ) (g n) := h
  rw [norm_neg, M.norm_nsmul_unitVec] at h2
  exact_mod_cast h2

/-- **`oneMajorant` is TIGHT.** Every majorant of `1_X` is `≥ 1`, since `‖1_X‖ = 1`. -/
theorem NormedModel.one_maj_lower_bound (M : NormedModel)
    (m : Ty.interpret (fun () => M.E) xTy.hat)
    (hm : bezemMaj (X := fun () => M.E) M.toMetricModel.base xTy m (M.si.funcInterp .one)) :
    @LE.le ℕ _ 1 m := by
  rw [M.bezem_base_iff] at hm
  have h1 : (1 : ℝ) ≤ Nat.cast (R := ℝ) m := by
    rwa [show (M.si.funcInterp .one : M.E) = M.unitVec from rfl, M.norm_unitVec] at hm
  exact_mod_cast h1

/-- **Control, proved rather than merely observed to fail**: `λn. n − 1` — the smallest
perturbation of `negMajorant` downwards — is *not* a majorant of negation, in any model. Any
`g` with `g n < n` at even one `n` is refuted the same way by `neg_maj_lower_bound`. -/
theorem NormedModel.negMajorant_pred_not_maj (M : NormedModel) :
    ¬ bezemMaj (X := fun () => M.E) M.toMetricModel.base (xTy →ₜ xTy)
        (fun (n : ℕ) => n - 1) (M.si.funcInterp .neg) := by
  intro h
  have := M.neg_maj_lower_bound _ h 1
  simp at this

/-- Same for `1_X`: `0` does not majorize it. -/
theorem NormedModel.oneMajorant_zero_not_maj (M : NormedModel) :
    ¬ bezemMaj (X := fun () => M.E) M.toMetricModel.base xTy (0 : ℕ)
        (M.si.funcInterp .one) := by
  intro h
  have := M.one_maj_lower_bound _ h
  simp at this

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
  | neg => exact ⟨fun _ => M.negMajorant, M.neg_maj_at 0⟩
  | one => exact ⟨fun _ => M.oneMajorant, M.one_maj_at 0⟩

/-- `0_X = a`, so `0` majorizes it. -/
theorem NormedModel.zeroX_maj_zero (M : NormedModel) :
    bezemMaj (X := fun () => M.E) M.toMetricModel.base (Ty.base ()) (0 : ℕ)
      (M.si.zeroInterp ()) := by
  change ‖(0 : M.E) - 0‖ ≤ ((0 : ℕ) : ℝ)
  simp

/-- **A normed model is an abstract majorizability.** -/
noncomputable def NormedModel.abstractMajorizability (M : NormedModel) :
    AbstractMajorizability M.si :=
  bezemAbstract M.si M.toMetricModel.base M.toMetricModel.base_mono 0
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
    | .neg => M.negMajorant
    | .one => M.oneMajorant
  funcM_maj := fun c => match c with
    | .add => M.add_maj_at 0
    | .smul => M.smul_maj_at 0
    | .norm => M.norm_maj_at 0
    | .neg => M.neg_maj_at 0
    | .one => M.one_maj_at 0
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

-- Equality interpretation, soundness, metatheorems

/-- The metric `EqXInterp`, transferred. -/
noncomputable def NormedModel.eqXInterp (M : NormedModel) :
    EqXInterp (fun () => M.E) Normed.F M.si :=
  M.toMetricModel.eqXInterp_gen M.si (fun _ _ => rfl)

-- The premises in the model

-- As in `WHyperbolic.lean`/`CAT0.lean`: no named `AxiomsHold : Prop`. `axiomsHold` below has
-- the shape of `MetricModel.soundness_gen`'s `hprem`, spelled out inline, and is a theorem.

section AxiomsInModel

variable (M : NormedModel) {Γ : Ctx MetricSpace.ι}

/-- `+` evaluates to vector addition, by definition of `si`. -/
theorem NormedModel.interp_add (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Term.app2 Normed.vadd s t) env
      = Term.interpret M.si s env + Term.interpret M.si t env := rfl

/-- `smul` evaluates to `r_α • x`: the scalar arrives as a real through `codeReal`. -/
theorem NormedModel.interp_smul (r : Term Normed.F Γ rTy) (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Term.app2 Normed.vsmul r s) env
      = codeReal (Term.interpret M.si r env) • Term.interpret M.si s env := rfl

/-- `‖·‖` evaluates to `(‖x‖)◦`. -/
theorem NormedModel.interp_norm (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Term.app Normed.vnorm s) env
      = Rounding.roundR (‖Term.interpret M.si s env‖) := rfl

/-- `0_X` evaluates to the zero vector. -/
theorem NormedModel.interp_zero (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Normed.zero (Γ := Γ)) env = 0 := rfl

/-- `−` evaluates to Mathlib negation. -/
theorem NormedModel.interp_neg (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Term.app Normed.vneg s) env = -Term.interpret M.si s env := rfl

/-- `1_X` evaluates to the unit vector. -/
theorem NormedModel.interp_one (env : Ctx.interpret (fun () => M.E) Γ) :
    Term.interpret M.si (Normed.one (Γ := Γ)) env = M.unitVec := rfl

/-- `(‖x‖)◦` denotes `‖x‖` — `codeReal_roundR`, composed with `interp_norm`. -/
theorem NormedModel.codeReal_interp_norm (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    codeReal (Term.interpret M.si (Term.app Normed.vnorm s) env)
      = (‖Term.interpret M.si s env‖) := by
  rw [M.interp_norm, codeReal_roundR _ (norm_nonneg _)]

/-- The structural distance denotes `‖x − y‖`. Stated with `Term.dist ()` so it matches the
unfolded `eqAtType` as well as `Normed.d`. -/
theorem NormedModel.codeReal_interp_dist (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    codeReal (Term.interpret M.si (Term.app2 (Term.dist ()) s t) env)
      = (‖Term.interpret M.si s env - Term.interpret M.si t env‖) := by
  rw [M.toMetricModel.interp_dist_gen M.si (fun _ _ => rfl) s t env,
    codeReal_roundR _ (norm_nonneg _)]

/-- `=_X` between terms whose values coincide. `MetricTransfer`'s `eqAtType_base_holds_gen`
at `d(x,y) := ‖x − y‖`; this is what the eight vector-space axioms reduce to. -/
theorem NormedModel.eqX_of_eq (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ)
    (h : Term.interpret M.si s env = Term.interpret M.si t env) :
    Formula.interpret M.si (eqAtType xTy s t) env :=
  M.toMetricModel.eqAtType_base_holds_gen M.si (fun _ _ => rfl) s t env h

/-- (1) in the model, at arbitrary terms. -/
theorem NormedModel.add_comm_holds (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy (Term.app2 Normed.vadd s t) (Term.app2 Normed.vadd t s)) env := by
  apply M.eqX_of_eq
  simp only [M.interp_add]
  -- `_root_`: the bare name resolves to the object-level `Metatheorems.add_comm`, a `Derivable`
  exact _root_.add_comm _ _

/-- (2) in the model. -/
theorem NormedModel.add_assoc_holds (s t u : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app2 Normed.vadd (Term.app2 Normed.vadd s t) u)
        (Term.app2 Normed.vadd s (Term.app2 Normed.vadd t u))) env := by
  apply M.eqX_of_eq
  simp only [M.interp_add]
  exact _root_.add_assoc _ _ _

/-- (3) in the model. -/
theorem NormedModel.add_zero_holds (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (eqAtType xTy (Term.app2 Normed.vadd s Normed.zero) s) env := by
  apply M.eqX_of_eq
  simp only [M.interp_add, M.interp_zero]
  exact add_zero _

/-- (4) in the model: `x + (−x) = 0` at the primitive negation. -/
theorem NormedModel.add_neg_holds (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app2 Normed.vadd s (.app Normed.vneg s)) Normed.zero) env := by
  apply M.eqX_of_eq
  simp only [M.interp_add, M.interp_neg, M.interp_zero]
  exact add_neg_cancel _

/-- (5) in the model. -/
theorem NormedModel.smul_add_holds (r : Term Normed.F Γ rTy) (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app2 Normed.vsmul r (Term.app2 Normed.vadd s t))
        (Term.app2 Normed.vadd (Term.app2 Normed.vsmul r s) (Term.app2 Normed.vsmul r t)))
      env := by
  apply M.eqX_of_eq
  simp only [M.interp_add, M.interp_smul]
  exact smul_add _ _ _

/-- (6) in the model: the object-level `+ℝ` on the scalars is evaluated by
`codeReal_interp_add_R`. -/
theorem NormedModel.add_smul_holds (r r' : Term Normed.F Γ rTy) (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app2 Normed.vsmul (Term.app2 Term.add_R r r') s)
        (Term.app2 Normed.vadd (Term.app2 Normed.vsmul r s) (Term.app2 Normed.vsmul r' s)))
      env := by
  apply M.eqX_of_eq
  simp only [M.interp_add, M.interp_smul, codeReal_interp_add_R]
  exact add_smul _ _ _

/-- (7) in the model, via `codeReal_interp_mul_R`. -/
theorem NormedModel.smul_smul_holds (r r' : Term Normed.F Γ rTy) (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app2 Normed.vsmul (Term.app2 Term.mul_R r r') s)
        (Term.app2 Normed.vsmul r (Term.app2 Normed.vsmul r' s))) env := by
  apply M.eqX_of_eq
  simp only [M.interp_smul, codeReal_interp_mul_R]
  exact mul_smul _ _ _

/-- (8) in the model. -/
theorem NormedModel.one_smul_holds (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (eqAtType xTy (Term.app2 Normed.vsmul Term.one_R s) s) env := by
  apply M.eqX_of_eq
  simp only [M.interp_smul, codeReal_interp_one_R]
  exact one_smul _ _

/-- (9) in the model: `‖α·x‖ =ℝ |α|·‖x‖` is Mathlib's `norm_smul`. -/
theorem NormedModel.norm_smul_holds (r : Term Normed.F Γ rTy) (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eq_R
        (.app Normed.vnorm (Term.app2 Normed.vsmul r s))
        (Term.app2 Term.mul_R (.app Term.abs_R r) (.app Normed.vnorm s))) env := by
  apply interpret_eq_R_of_codeReal_eq
  simp only [M.codeReal_interp_norm, M.interp_smul, codeReal_interp_mul_R, codeReal_interp_abs_R]
  rw [norm_smul, Real.norm_eq_abs]

/-- (10) in the model: the triangle inequality of the norm. -/
theorem NormedModel.norm_add_holds (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (le_R_pu
        (.app Normed.vnorm (Term.app2 Normed.vadd s t))
        (Term.app2 Term.add_R (.app Normed.vnorm s) (.app Normed.vnorm t))) env := by
  apply interpret_le_R_pu_of_codeReal_le
  simp only [M.codeReal_interp_norm, M.interp_add, codeReal_interp_add_R]
  exact norm_add_le _ _

/-- (11) in the model: `‖1_X‖ = 1`, by construction of the unit vector. -/
theorem NormedModel.norm_one_holds (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eq_R (.app Normed.vnorm (Normed.one (Γ := Γ))) Term.one_R) env := by
  apply interpret_eq_R_of_codeReal_eq
  rw [M.codeReal_interp_norm, codeReal_interp_one_R, M.interp_one, M.norm_unitVec]

/-- (12) in the model: `‖−x‖ = ‖x‖`, Mathlib's `norm_neg`. -/
theorem NormedModel.norm_neg_holds (s : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eq_R (.app Normed.vnorm (.app Normed.vneg s)) (.app Normed.vnorm s)) env := by
  apply interpret_eq_R_of_codeReal_eq
  rw [M.codeReal_interp_norm, M.codeReal_interp_norm, M.interp_neg, norm_neg]

/-- (13) in the model: `d(x,y) = ‖x − y‖ = ‖x + (−y)‖`. -/
theorem NormedModel.dist_holds (s t : Term Normed.F Γ xTy)
    (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si
      (eq_R
        (Term.app2 Normed.d s t)
        (.app Normed.vnorm
          (Term.app2 Normed.vadd s (.app Normed.vneg t)))) env := by
  apply interpret_eq_R_of_codeReal_eq
  simp only [M.codeReal_interp_dist, M.codeReal_interp_norm, M.interp_add, M.interp_neg]
  rw [sub_eq_add_neg]

/-- **The thirteen axioms hold in the model.** With this, `spremise`, `soundness` and both
metatheorems take no hypothesis about the model beyond `NormedModel` itself — the last
`AxiomsHold` binder in the space tower is gone. -/
theorem NormedModel.axiomsHold :
    ∀ {Γ : Ctx MetricSpace.ι} (A : Formula Normed.F Γ), Normed.Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => M.E) Γ, Formula.interpret M.si A env := by
  intro Γ A hA env
  rcases hA with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · intro x y
    exact M.add_comm_holds _ _ _
  · intro x y z
    exact M.add_assoc_holds _ _ _ _
  · intro x
    exact M.add_zero_holds _ _
  · intro x
    exact M.add_neg_holds _ _
  · intro a x y
    exact M.smul_add_holds _ _ _ _
  · intro a b x
    exact M.add_smul_holds _ _ _ _
  · intro a b x
    exact M.smul_smul_holds _ _ _ _
  · intro x
    exact M.one_smul_holds _ _
  · intro a x
    exact M.norm_smul_holds _ _ _
  · intro x y
    exact M.norm_add_holds _ _ _
  · exact M.norm_one_holds _
  · intro x
    exact M.norm_neg_holds _ _
  · intro x y
    exact M.dist_holds _ _ _

/-- Non-vacuity: `ax_norm_add` is a premise, and `axiomsHold` applied to it yields the
interpreted axiom at any environment. -/
example {Γ : Ctx MetricSpace.ι} (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (Normed.ax_norm_add (Γ := Γ)) env :=
  M.axiomsHold _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))))))))) env

/-- Non-vacuity, `=_X` shape: `ax_add_comm` is a premise and the interpreted axiom follows. -/
example {Γ : Ctx MetricSpace.ι} (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (Normed.ax_add_comm (Γ := Γ)) env :=
  M.axiomsHold _ (Or.inl rfl) env

/-- Non-vacuity for the **new** nontriviality axiom (11): `ax_norm_one` is a premise, and
`axiomsHold` yields `‖1_X‖ =ℝ 1ℝ` at any environment. -/
example {Γ : Ctx MetricSpace.ι} (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (Normed.ax_norm_one (Γ := Γ)) env :=
  M.axiomsHold _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) env

/-- Non-vacuity for the **new** negation axiom (12). -/
example {Γ : Ctx MetricSpace.ι} (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (Normed.ax_norm_neg (Γ := Γ)) env :=
  M.axiomsHold _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) env

/-- Non-vacuity for the restated (4), `x + (−x) =_X 0_X` at the primitive `−`. -/
example {Γ : Ctx MetricSpace.ι} (env : Ctx.interpret (fun () => M.E) Γ) :
    Formula.interpret M.si (Normed.ax_add_neg (Γ := Γ)) env :=
  M.axiomsHold _ (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) env

end AxiomsInModel

/-- Premise realizers, by `srealizer_of_pu` — every axiom is purely universal and ∨-free. -/
def NormedModel.spremise (M : NormedModel) :
    ∀ (Γ : Ctx MetricSpace.ι) (B : Formula Normed.F Γ),
      Normed.Premises ⟨Γ, B⟩ → SRealizer M.si B :=
  fun Γ B hp =>
    srealizer_of_pu B (Normed.premises_pu Γ B hp) (Normed.premises_vf Γ B hp)
      (M.axiomsHold B hp)

/-- **Semantic soundness for a normed model.** -/
theorem NormedModel.soundness (M : NormedModel)
    {Γ : Ctx MetricSpace.ι} {allowed : Allowed} {A : Formula Normed.F Γ}
    (h : Derivable Normed.F allowed Normed.Premises A) :
    ∀ env : Ctx.interpret (fun () => M.E) Γ, Formula.interpret M.si A env :=
  M.toMetricModel.soundness_gen M.si (fun _ _ => rfl) M.axiomsHold h

/-- **The normed-space metatheorem** (extended input). -/
theorem NormedModel.normed_metatheorem (M : NormedModel)
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
  syntactic_general_metatheorem M.eqXInterp M.spremise M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- **The normed-space metatheorem, from a classical proof.** -/
theorem NormedModel.normed_metatheorem_classical (M : NormedModel)
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
    (ntStable_of_pu Normed.premises_pu) M.spremise
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

-- Axiom hygiene

#print axioms Normed.premises_pu
#print axioms Normed.premises_vf
#print axioms Normed.dist_ax
#print axioms Normed.norm_one_ax
#print axioms Normed.norm_neg_ax
#print axioms NormedModel.norm_nsmul_unitVec
#print axioms NormedModel.neg_maj_lower_bound
#print axioms NormedModel.one_maj_lower_bound
#print axioms NormedModel.negMajorant_pred_not_maj
#print axioms NormedModel.oneMajorant_zero_not_maj
#print axioms NormedModel.smul_maj_at
#print axioms NormedModel.abstractMajorizability
#print axioms NormedModel.constMajorants
#print axioms NormedModel.eqXInterp
#print axioms NormedModel.codeReal_interp_norm
#print axioms NormedModel.codeReal_interp_dist
#print axioms NormedModel.norm_unitVec
#print axioms NormedModel.negMajorant
#print axioms NormedModel.neg_maj_at
#print axioms NormedModel.one_maj_at
#print axioms NormedModel.add_neg_holds
#print axioms NormedModel.norm_one_holds
#print axioms NormedModel.norm_neg_holds
#print axioms NormedModel.smul_smul_holds
#print axioms NormedModel.norm_smul_holds
#print axioms NormedModel.norm_add_holds
#print axioms NormedModel.dist_holds
#print axioms NormedModel.axiomsHold
#print axioms NormedModel.spremise
#print axioms NormedModel.soundness
#print axioms NormedModel.normed_metatheorem
#print axioms NormedModel.normed_metatheorem_classical

end Metatheorems
