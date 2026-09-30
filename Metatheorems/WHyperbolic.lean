/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetricTransfer
import Metatheorems.CodeReal
import Metatheorems.CodeRealOps
import Metatheorems.BaseEquality

namespace Metatheorems

/-!
# W-hyperbolic spaces

The first rung of the space tower above metric spaces (Kohlenbach, *Applied Proof Theory*,
Def. 17.?? — the Kohlenbach/Leuştean `W`-hyperbolic spaces): a metric space `(X, d)` with a
convex-combination map `W : X × X × [0,1] → X` satisfying

* (W1) `d(z, W(x,y,λ)) ≤ (1−λ)·d(z,x) + λ·d(z,y)`
* (W2) `d(W(x,y,λ), W(x,y,μ)) = |λ−μ|·d(x,y)`
* (W3) `W(x,y,λ) = W(y,x,1−λ)`
* (W4) `d(W(x,z,λ), W(y,w,λ)) ≤ (1−λ)·d(x,y) + λ·d(z,w)`

## Signature

`ι = Unit` (the one base type `X`, shared with `MetricSpaces.lean`), `κ = Unit` with the one
function constant `W : X →ₜ X →ₜ ℝ →ₜ X`. The metric is **not** a constant — it is the
structural `Term.dist ()`, and `dist_self`/`dist_comm`/`dist_tri` are constructors of
`Derivable`, so the whole metric theory is inherited for free.

## The `[0,1]` parameter

`λ` ranges over **all** of type `1 = ℕ → ℕ`; the axioms are stated at `clamp01 λ`
(`RealNumbers/Interval.lean`), the object-level retraction onto `[0,1]`.

## The premise set and the model

The four axioms are purely universal and ∨-free; a premise realizer is `srealizer_of_pu`
applied to the axiom's truth in the model, `WHyperbolicModel.axiomsHold`.
`WHyperbolicModel extends MetricModel` with `W : carrier → carrier → ℝ → carrier` and the four
axioms as Lean-level facts on Mathlib `ℝ`, for `λ, μ ∈ [0,1]`; the constant `W` is interpreted
as `λx y f. W(x, y, clampReal (codeReal f))`.
-/

open Formula

-- Signature

/-- The function-constant index type: one constant, `W`. -/
abbrev WHyperbolic.κ := Unit

/-- `W : X →ₜ X →ₜ ℝ →ₜ X`. -/
def WHyperbolic.F : WHyperbolic.κ → Ty MetricSpace.ι
  | () => xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy

/-- The metric, structural. -/
abbrev WHyperbolic.d {Γ : Ctx MetricSpace.ι} :
    Term WHyperbolic.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.dist ()

/-- The convex-combination constant. -/
abbrev WHyperbolic.W {Γ : Ctx MetricSpace.ι} :
    Term WHyperbolic.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy) :=
  Term.func ()

-- The four axioms, as closed context-polymorphic formulas

/-- (W1) `∀z x y λ. d(z, W(x,y,λ̃)) ≤ℝ (1ℝ −ℝ λ̃)·ℝ d(z,x) +ℝ λ̃ ·ℝ d(z,y)`, with
`λ̃ = clamp01 λ`. De Bruijn: `z = x₃, x = x₂, y = x₁, λ = x₀`. -/
def WHyperbolic.ax_W1 {Γ : Ctx MetricSpace.ι} : Formula WHyperbolic.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all rTy
    (le_R_pu
      (Term.app2 WHyperbolic.d (.var (.vs (.vs (.vs .vz))))
        (Term.app3 WHyperbolic.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))
          (Term.app2 WHyperbolic.d (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))))
        (Term.app2 Term.mul_R (.app Term.clamp01 (.var .vz))
          (Term.app2 WHyperbolic.d (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))))))))

/-- (W2) `∀x y λ μ. d(W(x,y,λ̃), W(x,y,μ̃)) =ℝ |λ̃ −ℝ μ̃| ·ℝ d(x,y)`.
De Bruijn: `x = x₃, y = x₂, λ = x₁, μ = x₀`. -/
def WHyperbolic.ax_W2 {Γ : Ctx MetricSpace.ι} : Formula WHyperbolic.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all rTy (Formula.all rTy
    (eq_R
      (Term.app2 WHyperbolic.d
        (Term.app3 WHyperbolic.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var (.vs .vz))))
        (Term.app3 WHyperbolic.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.mul_R
        (.app Term.abs_R
          (Term.app2 Term.sub_R (.app Term.clamp01 (.var (.vs .vz)))
            (.app Term.clamp01 (.var .vz))))
        (Term.app2 WHyperbolic.d (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))))))))

/-- (W3) `∀x y λ. W(x,y,λ̃) =_X W(y,x,1ℝ −ℝ λ̃)`. Base-type equality is `eqAtType xTy`, i.e.
`d(·,·) =ℝ 0ℝ`. De Bruijn: `x = x₂, y = x₁, λ = x₀`. -/
def WHyperbolic.ax_W3 {Γ : Ctx MetricSpace.ι} : Formula WHyperbolic.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all rTy
    (eqAtType xTy
      (Term.app3 WHyperbolic.W (.var (.vs (.vs .vz))) (.var (.vs .vz))
        (.app Term.clamp01 (.var .vz)))
      (Term.app3 WHyperbolic.W (.var (.vs .vz)) (.var (.vs (.vs .vz)))
        (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))))))

/-- (W4) `∀x y z w λ. d(W(x,z,λ̃), W(y,w,λ̃)) ≤ℝ (1ℝ −ℝ λ̃)·ℝ d(x,y) +ℝ λ̃ ·ℝ d(z,w)`.
De Bruijn: `x = x₄, y = x₃, z = x₂, w = x₁, λ = x₀`. -/
def WHyperbolic.ax_W4 {Γ : Ctx MetricSpace.ι} : Formula WHyperbolic.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all xTy (Formula.all rTy
    (le_R_pu
      (Term.app2 WHyperbolic.d
        (Term.app3 WHyperbolic.W (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))
          (.app Term.clamp01 (.var .vz)))
        (Term.app3 WHyperbolic.W (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))
          (.app Term.clamp01 (.var .vz))))
      (Term.app2 Term.add_R
        (Term.app2 Term.mul_R
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 (.var .vz)))
          (Term.app2 WHyperbolic.d (.var (.vs (.vs (.vs (.vs .vz)))))
            (.var (.vs (.vs (.vs .vz))))))
        (Term.app2 Term.mul_R (.app Term.clamp01 (.var .vz))
          (Term.app2 WHyperbolic.d (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))))

-- All four are purely universal and ∨-free, by computation.

theorem WHyperbolic.ax_W1_pu {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W1 (Γ := Γ)).isPurelyUniversal = true := by rfl
theorem WHyperbolic.ax_W2_pu {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W2 (Γ := Γ)).isPurelyUniversal = true := by rfl
theorem WHyperbolic.ax_W3_pu {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W3 (Γ := Γ)).isPurelyUniversal = true := by rfl
theorem WHyperbolic.ax_W4_pu {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W4 (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem WHyperbolic.ax_W1_vf {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W1 (Γ := Γ)).isVFree = true := by rfl
theorem WHyperbolic.ax_W2_vf {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W2 (Γ := Γ)).isVFree = true := by rfl
theorem WHyperbolic.ax_W3_vf {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W3 (Γ := Γ)).isVFree = true := by rfl
theorem WHyperbolic.ax_W4_vf {Γ : Ctx MetricSpace.ι} :
    (WHyperbolic.ax_W4 (Γ := Γ)).isVFree = true := by rfl

-- The premise set

/-- **The W-hyperbolic premise set: the four axioms, in every context.** -/
def WHyperbolic.Premises : PremiseSet WHyperbolic.F
  -- by pattern matching, not `fun p => p.2 = …`: the latter leaves `⟨Γ, A⟩.1` inside the
  -- axiom's implicit context argument, and `subst` then sees `A` on both sides
  | ⟨_, A⟩ => A = WHyperbolic.ax_W1 ∨ A = WHyperbolic.ax_W2
    ∨ A = WHyperbolic.ax_W3 ∨ A = WHyperbolic.ax_W4

/-- Every premise is purely universal. -/
theorem WHyperbolic.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ'),
      WHyperbolic.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := by
  intro Γ' B h
  rcases h with h | h | h | h <;> subst h <;> rfl

/-- Every premise is ∨-free. -/
theorem WHyperbolic.premises_vf :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ'),
      WHyperbolic.Premises ⟨Γ', B⟩ → B.isVFree = true := by
  intro Γ' B h
  rcases h with h | h | h | h <;> subst h <;> rfl

-- The axioms as derivations, for use in proofs.

/-- `⊢ (W1)`. -/
def WHyperbolic.W1 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a WHyperbolic.Premises (WHyperbolic.ax_W1 (Γ := Γ)) :=
  .premise (Or.inl rfl)

/-- `⊢ (W2)`. -/
def WHyperbolic.W2 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a WHyperbolic.Premises (WHyperbolic.ax_W2 (Γ := Γ)) :=
  .premise (Or.inr (Or.inl rfl))

/-- `⊢ (W3)`. -/
def WHyperbolic.W3 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a WHyperbolic.Premises (WHyperbolic.ax_W3 (Γ := Γ)) :=
  .premise (Or.inr (Or.inr (Or.inl rfl)))

/-- `⊢ (W4)`. -/
def WHyperbolic.W4 {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a WHyperbolic.Premises (WHyperbolic.ax_W4 (Γ := Γ)) :=
  .premise (Or.inr (Or.inr (Or.inr rfl)))

-- The model

-- `codeReal` (the real a code denotes) and `clampReal` (the semantic `[0,1]`-retraction)
-- live in `CodeReal.lean`, shared with the normed-space instance.

/-- **A W-hyperbolic model**: a (separated) metric model with a convex-combination map and
the four axioms as facts on Mathlib `ℝ`, for parameters in `[0,1]`.

`W` is total on `ℝ` — its values outside `[0,1]` are unconstrained and never used, because
the interpretation clamps (`WHyperbolicModel.si`). -/
structure WHyperbolicModel extends MetricModel where
  /-- The convex-combination map. -/
  W : carrier → carrier → ℝ → carrier
  /-- (W1). -/
  W1 : ∀ (z x y : carrier) (l : ℝ), 0 ≤ l → l ≤ 1 →
    d z (W x y l) ≤ (1 - l) * d z x + l * d z y
  /-- (W2). -/
  W2 : ∀ (x y : carrier) (l m : ℝ), 0 ≤ l → l ≤ 1 → 0 ≤ m → m ≤ 1 →
    d (W x y l) (W x y m) = |l - m| * d x y
  /-- (W3). -/
  W3 : ∀ (x y : carrier) (l : ℝ), 0 ≤ l → l ≤ 1 → W x y l = W y x (1 - l)
  /-- (W4). -/
  W4 : ∀ (x y z w : carrier) (l : ℝ), 0 ≤ l → l ≤ 1 →
    d (W x z l) (W y w l) ≤ (1 - l) * d x y + l * d z w

/-- **The interpretation.** `d_X ↦ (d(x,y))◦` exactly as for the metric model, and
`W ↦ λx y f. W(x, y, clampReal (codeReal f))` — Kohlenbach's `W(x,y,r_λ̃)`: the code is read
as a real and clamped into `[0,1]` *in the model*, so the interpreted `W` only ever sees
parameters the axioms speak about. -/
noncomputable def WHyperbolicModel.si (M : WHyperbolicModel) :
    SpaceInterp (fun () => M.carrier) WHyperbolic.F where
  funcInterp := fun () => fun x y f => M.W x y (clampReal (codeReal f))
  zeroInterp := fun () => M.zeroX
  distInterp := fun () => fun x y => Rounding.roundR (M.d x y)

-- Majorizability

/-- **The majorant of `W`: `λn₁ n₂ f. max n₁ n₂`, independent of the real argument.**

If `d(a,x) ≤ n₁` and `d(a,y) ≤ n₂` then, for any `μ ∈ [0,1]`, (W1) at `z := a` gives
`d(a, W(x,y,μ)) ≤ (1−μ)·n₁ + μ·n₂ ≤ max n₁ n₂`. The model clamps its parameter, so this holds
for **every** code `f`, and the majorant does not look at `f` (or at its majorant) at all. -/
def WHyperbolicModel.WMajorant (M : WHyperbolicModel) :
    Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy).hat :=
  -- the binder ascriptions are load-bearing (`Ty.hat` is not reducible)
  fun (n₁ : ℕ) (n₂ : ℕ) (_ : ℕ → ℕ) => (max n₁ n₂ : ℕ)

/-- The metric content of `W_maj_at`, isolated: (W1) at the reference point. -/
theorem WHyperbolicModel.dist_ref_W_le (M : WHyperbolicModel) (n₁ n₂ : ℕ) (x y : M.carrier)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1)
    (hx : M.base () n₁ x) (hy : M.base () n₂ y) :
    M.base () (max n₁ n₂) (M.W x y l) := by
  change M.d M.ref (M.W x y l) ≤ ((max n₁ n₂ : ℕ) : ℝ)
  have hx' : M.d M.ref x ≤ (n₁ : ℝ) := hx
  have hy' : M.d M.ref y ≤ (n₂ : ℝ) := hy
  have hm1 : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left n₁ n₂
  have hm2 : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
  have h1l : 0 ≤ 1 - l := by linarith
  calc M.d M.ref (M.W x y l)
      ≤ (1 - l) * M.d M.ref x + l * M.d M.ref y := M.W1 M.ref x y l h0 h1
    _ ≤ (1 - l) * ((max n₁ n₂ : ℕ) : ℝ) + l * ((max n₁ n₂ : ℕ) : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx'.trans hm1) h1l)
          (mul_le_mul_of_nonneg_left (hy'.trans hm2) h0)
    _ = ((max n₁ n₂ : ℕ) : ℝ) := by ring

/-- **`W` is majorized by `WMajorant`**, at every index. The first clause is
`dist_ref_W_le`; every other clause is monotonicity of `max` on `ℕ`. -/
theorem WHyperbolicModel.W_maj_at (M : WHyperbolicModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
      (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy)
      M.WMajorant (M.si.funcInterp ()) := by
  intro _ _
  unfold WHyperbolicModel.WMajorant
  refine ⟨?_, ?_⟩
  · intro n₁ x hx
    refine ⟨?_, ?_⟩
    · intro n₂ y hy
      refine ⟨?_, ?_⟩
      · intro _ f _
        exact M.dist_ref_W_le n₁ n₂ x y _ (clampReal_nonneg _) (clampReal_le_one _) hx hy
      · intro _ _ _
        exact Nat.le_refl _
    · intro n₂' n₂ h
      refine ⟨?_, ?_⟩
      · intro _ _ _
        exact max_le_max (Nat.le_refl n₁) h
      · intro _ _ _
        exact Nat.le_refl _
  · intro n₁' n₁ h
    refine ⟨?_, ?_⟩
    · intro n₂' n₂ h₂
      refine ⟨?_, ?_⟩
      · intro _ _ _
        exact max_le_max h h₂
      · intro _ _ _
        exact Nat.le_refl _
    · intro n₂' n₂ h₂
      refine ⟨?_, ?_⟩
      · intro _ _ _
        exact max_le_max (Nat.le_refl n₁') h₂
      · intro _ _ _
        exact Nat.le_refl _

/-- `W_maj_at`, `∃`-packaged for `bezemAbstract`. -/
theorem WHyperbolicModel.W_maj (M : WHyperbolicModel) (N : ℕ) :
    ∃ f_star : ℕ →
      Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy).hat,
      ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι →ₜ xTy) (f_star n) (M.si.funcInterp ()) :=
  ⟨fun _ => M.WMajorant, M.W_maj_at N⟩

/-- **A W-hyperbolic model is an abstract majorizability.** Everything metric comes from
`MetricTransfer.lean`; the one new obligation is `W_maj`. -/
noncomputable def WHyperbolicModel.abstractMajorizability (M : WHyperbolicModel) :
    AbstractMajorizability M.si :=
  bezemAbstract M.si M.base M.base_mono 0
    (bezem_zero_maj M.base 0)
    (bezem_succ_maj M.base 0)
    (fun ρ => bezem_prec_maj M.base_mono 0 ρ)
    (fun () => M.W_maj 0)
    (fun () => M.zeroX_maj_gen M.si 0)
    (fun () => M.dist_maj_gen M.si (fun _ _ => rfl) 0)

/-- **The majorants as data**, parameterised by `n₀ ≥ d(a, 0_X)` exactly as
`MetricModel.constMajorants`; the only new entry is `W ↦ WMajorant`, which is closed. -/
noncomputable def WHyperbolicModel.constMajorants (M : WHyperbolicModel) (n₀ : ℕ)
    (h : M.d M.ref M.zeroX ≤ (n₀ : ℝ)) : ConstMajorants M.abstractMajorizability where
  zeroM := fun _ => 0
  zeroM_maj := fun _ _ => Nat.le_refl 0
  succM := fun _ => Nat.succ
  succM_maj := fun _ _ =>
    ⟨fun _ _ h => Nat.succ_le_succ h, fun _ _ h => Nat.succ_le_succ h⟩
  precM := fun ρ _ => fun y_star z_star n => recMaj ρ y_star z_star n
  precM_maj := fun ρ => bezem_prec_maj_at M.base_mono 0 ρ
  funcM := fun () _ => M.WMajorant
  funcM_maj := fun () => M.W_maj_at 0
  zeroXM := fun _ _ => n₀
  zeroXM_maj := fun () _ _ => h
  distM := fun _ _ => M.distMajorant
  distM_maj := fun () => M.dist_maj_at_gen M.si (fun _ _ => rfl) 0

section ComputesDemo

/-!
**What these examples are, and what they are NOT.** The extraction pipeline is

    Derivable → syntactic_soundness → extractUTerm/extractVTerm → closedMajorizer → numeral

and everything below starts at the **last** stage, applying `closedMajorizer` to a
*hand-written closed term*. **No derivation appears anywhere in this section.** So these
demonstrate that the majorization layer computes at this model's constants, and that
`WMajorant` genuinely discards its real argument — they do **not** exhibit a bound extracted
from a proof.
-/

/-- **The uniformity, kernel-checked**: for *any* closed real `f`, the majorant of
`W(0_X, 0_X, f)` is `n₀` — `max n₀ n₀`, with `f` never consulted. -/
example (M : WHyperbolicModel) (n₀ : ℕ) (h : M.d M.ref M.zeroX ≤ (n₀ : ℝ))
    (f : Term WHyperbolic.F [] rTy) :
    n₀ = closedMajorizer (M.constMajorants n₀ h)
      (Term.app3 WHyperbolic.W (Term.zeroX ()) (Term.zeroX ()) f) := by
  simp [closedMajorizer, termMajorizer, WHyperbolicModel.constMajorants,
    WHyperbolicModel.abstractMajorizability, bezemAbstract, Term.app3,
    WHyperbolicModel.WMajorant]

/-- **The same uniformity carried into a literal.** `MetricSpaces.lean`'s demo is
`901 = closedMajorizer (M.constMajorants 5 h) (d 0_X 0_X) 0`. Wrapping an argument in an
arbitrary convex combination leaves that number **unchanged**: `W(0_X,0_X,f)` majorizes to
`max 5 5 = 5`, exactly as `0_X` does, so the composite is still `901` — for every closed
real `f`. The parameter is absent from the arithmetic, not merely bounded in it. -/
example (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (f : Term WHyperbolic.F [] rTy) :
    (901 : ℕ) = closedMajorizer (M.constMajorants 5 h)
      (Term.app2 WHyperbolic.d
        (Term.app3 WHyperbolic.W (Term.zeroX ()) (Term.zeroX ()) f)
        (Term.zeroX ())) ((0 : ℕ)) := by
  simp only [closedMajorizer, termMajorizer, WHyperbolicModel.constMajorants,
    WHyperbolicModel.abstractMajorizability, bezemAbstract, Term.app2, Term.app3,
    WHyperbolicModel.WMajorant, MetricModel.distMajorant_apply]
  decide

/-- **Nesting does not accumulate** — the sharper form. Three arbitrary, distinct parameters
`f`, `g`, `k` in nested convex combinations, and the bound is still `901`. A majorant that
paid a factor per nesting could not do this; `WMajorant`'s `max` is idempotent on equal
arguments, so depth is free. -/
example (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))
    (f g k : Term WHyperbolic.F [] rTy) :
    (901 : ℕ) = closedMajorizer (M.constMajorants 5 h)
      (Term.app2 WHyperbolic.d
        (Term.app3 WHyperbolic.W
          (Term.app3 WHyperbolic.W (Term.zeroX ()) (Term.zeroX ()) f)
          (Term.app3 WHyperbolic.W (Term.zeroX ()) (Term.zeroX ()) g)
          k)
        (Term.zeroX ())) ((0 : ℕ)) := by
  simp only [closedMajorizer, termMajorizer, WHyperbolicModel.constMajorants,
    WHyperbolicModel.abstractMajorizability, bezemAbstract, Term.app2, Term.app3,
    WHyperbolicModel.WMajorant, MetricModel.distMajorant_apply]
  decide

end ComputesDemo

-- The equality interpretation — transferred, not rebuilt

/-- **`EqXInterp` for a W-hyperbolic model: the metric one, transferred.** Nothing about `W`
enters, because `eqAtType` at `X` speaks only about `d`. -/
noncomputable def WHyperbolicModel.eqXInterp (M : WHyperbolicModel) :
    EqXInterp (fun () => M.carrier) WHyperbolic.F M.si :=
  M.eqXInterp_gen M.si (fun _ _ => rfl)

-- The premises in the model

-- There is deliberately no named `AxiomsHold : Prop` here: the statement below is a theorem,
-- not a hypothesis.

section AxiomsInModel

variable (M : WHyperbolicModel) {Γ : Ctx MetricSpace.ι}

/-- `W` evaluates: `W(s,t,r) ↦ W(⟦s⟧, ⟦t⟧, clampReal (codeReal ⟦r⟧))`, by definition of `si`. -/
theorem WHyperbolicModel.interp_W (s t : Term WHyperbolic.F Γ xTy)
    (r : Term WHyperbolic.F Γ rTy) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Term.interpret M.si (Term.app3 WHyperbolic.W s t r) env
      = M.W (Term.interpret M.si s env) (Term.interpret M.si t env)
          (clampReal (codeReal (Term.interpret M.si r env))) := rfl

/-- The distance evaluates to the real distance at the `codeReal` level: `(d(x,y))◦` denotes
`d(x,y)`. Stated with `Term.dist ()` rather than the abbreviation `WHyperbolic.d`, so it
matches both spellings (the unfolded `eqAtType` produces the former). -/
theorem WHyperbolicModel.codeReal_interp_dist (s t : Term WHyperbolic.F Γ xTy)
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    codeReal (Term.interpret M.si (Term.app2 (Term.dist ()) s t) env)
      = M.d (Term.interpret M.si s env) (Term.interpret M.si t env) := by
  rw [M.interp_dist_gen M.si (fun _ _ => rfl) s t env, codeReal_roundR _ (M.d_nonneg _ _)]

/-- (W1) in the model, at arbitrary terms. `≤ℝ` is read off `≤` on the denoted reals
(`interpret_le_R_pu_of_codeReal_le`); every operation on the right is evaluated by its
`codeReal` homomorphism lemma; the double clamp inside `W` collapses since the clamped value
is already in `[0,1]`. -/
theorem WHyperbolicModel.W1_holds (s t u : Term WHyperbolic.F Γ xTy)
    (r : Term WHyperbolic.F Γ rTy) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (le_R_pu
        (Term.app2 WHyperbolic.d s (Term.app3 WHyperbolic.W t u (.app Term.clamp01 r)))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 r))
            (Term.app2 WHyperbolic.d s t))
          (Term.app2 Term.mul_R (.app Term.clamp01 r) (Term.app2 WHyperbolic.d s u)))) env := by
  apply interpret_le_R_pu_of_codeReal_le
  simp only [M.codeReal_interp_dist, codeReal_interp_add_R, codeReal_interp_mul_R,
    codeReal_interp_sub_R, codeReal_interp_one_R, codeReal_interp_clamp01,
    isCauchyCode_interp_clamp01, M.interp_W, clampReal_of_mem, clampReal_nonneg,
    clampReal_le_one]
  exact M.W1 _ _ _ _ (clampReal_nonneg _) (clampReal_le_one _)

/-- (W2) in the model, at arbitrary terms. -/
theorem WHyperbolicModel.W2_holds (s t : Term WHyperbolic.F Γ xTy)
    (r r' : Term WHyperbolic.F Γ rTy) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (eq_R
        (Term.app2 WHyperbolic.d
          (Term.app3 WHyperbolic.W s t (.app Term.clamp01 r))
          (Term.app3 WHyperbolic.W s t (.app Term.clamp01 r')))
        (Term.app2 Term.mul_R
          (.app Term.abs_R
            (Term.app2 Term.sub_R (.app Term.clamp01 r) (.app Term.clamp01 r')))
          (Term.app2 WHyperbolic.d s t))) env := by
  apply interpret_eq_R_of_codeReal_eq
  simp only [M.codeReal_interp_dist, codeReal_interp_mul_R, codeReal_interp_abs_R,
    codeReal_interp_sub_R, codeReal_interp_clamp01, isCauchyCode_interp_clamp01, M.interp_W,
    clampReal_of_mem, clampReal_nonneg, clampReal_le_one]
  exact M.W2 _ _ _ _ (clampReal_nonneg _) (clampReal_le_one _)
    (clampReal_nonneg _) (clampReal_le_one _)

/-- (W3) in the model, at arbitrary terms. `=_X` is `d(·,·) =ℝ 0ℝ`; the model's `W3` makes the
two points equal and `d_self` finishes. The parameter `1 − λ̃` is in `[0,1]`, so the clamp
inside the second `W` is the identity on it. -/
theorem WHyperbolicModel.W3_holds (s t : Term WHyperbolic.F Γ xTy)
    (r : Term WHyperbolic.F Γ rTy) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (eqAtType xTy
        (Term.app3 WHyperbolic.W s t (.app Term.clamp01 r))
        (Term.app3 WHyperbolic.W t s
          (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 r)))) env := by
  simp only [eqAtType]
  apply interpret_eq_R_of_codeReal_eq
  have h0 := clampReal_nonneg (codeReal (Term.interpret M.si r env))
  have h1 := clampReal_le_one (codeReal (Term.interpret M.si r env))
  have h0' : 0 ≤ 1 - clampReal (codeReal (Term.interpret M.si r env)) := by linarith
  have h1' : 1 - clampReal (codeReal (Term.interpret M.si r env)) ≤ 1 := by linarith
  simp only [codeReal_interp_zero_R, M.codeReal_interp_dist, M.interp_W,
    codeReal_interp_sub_R, codeReal_interp_one_R, codeReal_interp_clamp01,
    isCauchyCode_interp_clamp01, clampReal_of_mem, clampReal_nonneg, clampReal_le_one, h0', h1']
  rw [← M.W3 (Term.interpret M.si s env) (Term.interpret M.si t env) _ h0 h1, M.d_self]

/-- (W4) in the model, at arbitrary terms. -/
theorem WHyperbolicModel.W4_holds (s t u v : Term WHyperbolic.F Γ xTy)
    (r : Term WHyperbolic.F Γ rTy) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (le_R_pu
        (Term.app2 WHyperbolic.d
          (Term.app3 WHyperbolic.W s u (.app Term.clamp01 r))
          (Term.app3 WHyperbolic.W t v (.app Term.clamp01 r)))
        (Term.app2 Term.add_R
          (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 r))
            (Term.app2 WHyperbolic.d s t))
          (Term.app2 Term.mul_R (.app Term.clamp01 r) (Term.app2 WHyperbolic.d u v)))) env := by
  apply interpret_le_R_pu_of_codeReal_le
  simp only [M.codeReal_interp_dist, codeReal_interp_add_R, codeReal_interp_mul_R,
    codeReal_interp_sub_R, codeReal_interp_one_R, codeReal_interp_clamp01,
    isCauchyCode_interp_clamp01, M.interp_W, clampReal_of_mem, clampReal_nonneg,
    clampReal_le_one]
  exact M.W4 _ _ _ _ _ (clampReal_nonneg _) (clampReal_le_one _)

/-- **The four axioms hold in the model.** -/
theorem WHyperbolicModel.axiomsHold :
    ∀ {Γ : Ctx MetricSpace.ι} (A : Formula WHyperbolic.F Γ), WHyperbolic.Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env := by
  intro Γ A hA env
  rcases hA with h | h | h | h <;> subst h
  · intro z x y l
    exact M.W1_holds _ _ _ _ _
  · intro x y l m
    exact M.W2_holds _ _ _ _ _
  · intro x y l
    exact M.W3_holds _ _ _ _
  · intro x y z w l
    exact M.W4_holds _ _ _ _ _ _

end AxiomsInModel

/-- **Premise realizers**: every axiom is purely universal and ∨-free, so `srealizer_of_pu`
turns its truth in the model (`axiomsHold`) into a realizing term. -/
def WHyperbolicModel.spremise (M : WHyperbolicModel) :
    ∀ (Γ : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ),
      WHyperbolic.Premises ⟨Γ, B⟩ → SRealizer M.si B :=
  fun Γ B hp =>
    srealizer_of_pu B (WHyperbolic.premises_pu Γ B hp) (WHyperbolic.premises_vf Γ B hp)
      (M.axiomsHold B hp)

/-- **Semantic soundness for a W-hyperbolic model.** -/
theorem WHyperbolicModel.soundness (M : WHyperbolicModel)
    {Γ : Ctx MetricSpace.ι} {allowed : Allowed} {A : Formula WHyperbolic.F Γ}
    (h : Derivable WHyperbolic.F allowed WHyperbolic.Premises A) :
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env :=
  M.soundness_gen M.si (fun _ _ => rfl) M.axiomsHold h

-- The W-hyperbolic metatheorems

/-- **The W-hyperbolic metatheorem** (extended input). `MetricModel.metric_metatheorem` with
`W` in the signature and the four axioms as premises: from a derivation of
`∀x^ρ (∀u B₀ → ∃v C₀)` from (W1)–(W4), a bound `Φ` depending only on a majorant of `x` —
and, through `WMajorant`, on no `[0,1]`-parameter anywhere in `x`. -/
theorem WHyperbolicModel.w_metatheorem (M : WHyperbolicModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHyperbolic.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem M.eqXInterp M.spremise M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- **The W-hyperbolic metatheorem, from a classical proof.** -/
theorem WHyperbolicModel.w_metatheorem_classical (M : WHyperbolicModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula WHyperbolic.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.classical
      WHyperbolic.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem_classical M.eqXInterp
    (ntStable_of_pu WHyperbolic.premises_pu) M.spremise
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

-- A worked derivation: `W(x,x,λ̃) =_X x`

/-! The first consequence of the axioms one proves about a W-hyperbolic space, done in the
object theory to show it is *usable*, not merely definable. From (W1) at `z := x`, `y := x`:

    d(x, W(x,x,λ̃)) ≤ℝ (1 −ℝ λ̃)·d(x,x) +ℝ λ̃·d(x,x)

and `d(x,x) =ℝ 0ℝ` (`dist_self`), so the right-hand side is `=ℝ 0ℝ`; with `0ℝ ≤ℝ d(·,·)`
(`dist_nonneg`) and `le_zero_eq_zero_R` this gives `d(x, W(x,x,λ̃)) =ℝ 0ℝ`, i.e.
`x =_X W(x,x,λ̃)`, and symmetry (`eqAtType_sym_base`) finishes.

Two general ℝ-layer facts are supplied here: `mul_eq_zero_R_core : g =ℝ 0ℝ →ᶠ f ·ℝ g =ℝ 0ℝ`
and `le_R_of_le_R_pu_nf`, a `le_R_of_le_R_pu` whose antecedent is stated over the
*pushed-in* weakenings. -/

section MulZero

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

private def succ_congr'' {s t : Term F Γ Ty.nat}
    (h : Derivable F al Premises (Formula.eq0 s t)) :
    Derivable F al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) (by qb_nf) (by qb_nf)

/-- `mul_R`'s index shift `b = f(0) + g(0) + 2`, named. -/
abbrev mulBound (f g : Term F Γ (realTy ι)) : Term F Γ Ty.nat :=
  Term.app2 Term.add (Term.app2 Term.add (.app f .zero) (.app g .zero)) (Term.ofNat 2)

/-- The pointwise estimate behind `mul_eq_zero_R_core`: if `|ĝ(J+1)| < 2^{-J}` at the shifted
index `J = k + b`, then `|(f·g)^(k+1)| < 2^{-k}`. -/
def mul_zero_est (f g : Term F Γ (realTy ι)) (k : Term F Γ Ty.nat) :
    Derivable F al Premises
      (lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy g (.app .succ (Term.app2 Term.add k (mulBound f g))))
          (Term.app2 Term.cauchyfy Term.zero_R
            (.app .succ (Term.app2 Term.add k (mulBound f g))))))
        (.app Term.pow2neg_Q (Term.app2 Term.add k (mulBound f g)))
       →ᶠ
       lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy (Term.app2 Term.mul_R f g) (.app .succ k))
          (Term.app2 Term.cauchyfy Term.zero_R (.app .succ k))))
        (.app Term.pow2neg_Q k)) := by
  let f0 : Term F Γ Ty.nat := .app f .zero
  let g0 : Term F Γ Ty.nat := .app g .zero
  let e : Term F Γ Ty.nat := Term.app2 Term.add f0 g0
  let B : Term F Γ Ty.nat := mulBound f g
  let J : Term F Γ Ty.nat := Term.app2 Term.add k B
  let I : Term F Γ Ty.nat := Term.app2 Term.add (.app .succ k) B
  let A : Term F Γ Ty.nat := Term.app2 Term.cauchyfy f I
  let C : Term F Γ Ty.nat := Term.app2 Term.cauchyfy g I
  let Cj : Term F Γ Ty.nat := Term.app2 Term.cauchyfy g (.app .succ J)
  let P' : Term F Γ Ty.nat := .app Term.pow2neg_Q J
  let P : Term F Γ Ty.nat := .app Term.pow2neg_Q k
  let Bf : Term F Γ Ty.nat := Term.app2 Term.add_Q (.app Term.encode_nat_Q f0) Term.one_Q
  -- `I =₀ S J`, so `C =ℚ Cj`
  have hIJ : Derivable F al Premises (Formula.eq0 I (.app .succ J)) := add_succ_l k B
  have hCC : Derivable F al Premises (eq_Q Cj C) :=
    eqQ_of_nat_eq' (Derivable.mp (cauchyfy_idx_nat' g hIJ) Derivable.sym0)
  -- `B =₀ S (S e)`
  have hB2 : Derivable F al Premises (Formula.eq0 B (.app .succ (.app .succ e))) :=
    qtrans (add_succ e (.app .succ .zero))
      (succ_congr'' (qtrans (add_succ e .zero) (succ_congr'' (add_zero_r e))))
  -- `f0 ≤ S e`, since `S e =₀ S g0 + f0`
  have hSe : Derivable F al Premises
      (Formula.eq0 (.app .succ e) (Term.app2 Term.add (.app .succ g0) f0)) :=
    Derivable.mp (qtrans (add_succ_l g0 f0) (succ_congr'' (add_comm g0 f0))) Derivable.sym0
  have hf0e : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus f0 (.app .succ e)) .zero) :=
    Derivable.mp hSe (monus_le_of_eq_add f0 (.app .succ e) (.app .succ g0))
  -- `S S f0 ≤ S S S e ≤ 2^B`
  have s2 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ f0))
        (.app .succ (.app .succ (.app .succ e)))) .zero) :=
    qtrans (monus_succ_l (.app .succ f0) (.app .succ (.app .succ e)))
      (qtrans (monus_succ_l f0 (.app .succ e)) hf0e)
  have s1 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ (.app .succ e)))
        (.app Term.exp2 B)) .zero) :=
    qtrans (monus_congr_snd _ (exp2_congr' hB2))
      (succ_succ_le_exp2_succ (.app .succ e))
  have s3 : Derivable F al Premises
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.app .succ f0)) (.app Term.exp2 B)) .zero) :=
    Derivable.mp (Derivable.mp s1 (Derivable.mp s2 and_intro)) (monus_le_trans _ _ _)
  -- `Bf =ℚ ⟨S f0⟩ <ℚ ⟨2^B⟩`
  have hlt : Derivable F al Premises
      (lt_Q (.app Term.encode_nat_Q (.app .succ f0)) (.app Term.encode_nat_Q (.app Term.exp2 B))) :=
    encode_lt (.app .succ f0) (.app Term.exp2 B) s3
  have hBf : Derivable F al Premises (eq_Q Bf (.app Term.encode_nat_Q (.app .succ f0))) :=
    eqQsym (encode_succ f0)
  have hlt' : Derivable F al Premises (lt_Q Bf (.app Term.encode_nat_Q (.app Term.exp2 B))) :=
    Derivable.mp hlt (lt_Q_congr _ _ _ _ (eqQsym hBf) (eq_Q_refl_inst _))
  have hmul_lt : Derivable F al Premises
      (lt_Q (Term.app2 Term.mul_Q Bf P')
        (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app Term.exp2 B)) P')) :=
    lt_Q_mul_mono_l Bf _ P' hlt' (zero_lt_pow2neg_Q J)
  -- `⟨2^B⟩ · 2^{-J} =ℚ 2^{-k}`, since `J = k + B =₀ B + k`
  have hidx : Derivable F al Premises (Formula.eq0 (Term.app2 Term.add B k) J) := add_comm B k
  have hcoll : Derivable F al Premises
      (eq_Q (Term.app2 Term.mul_Q (.app Term.encode_nat_Q (.app Term.exp2 B)) P') P) :=
    eqQtrans
      (mulQr _ (eqQ_of_nat_eq' (Derivable.mp (pow2neg_idx_nat' hidx) Derivable.sym0)))
      (encode_pow2_mul B k)
  have hfin : Derivable F al Premises (lt_Q (Term.app2 Term.mul_Q Bf P') P) :=
    Derivable.mp hmul_lt (lt_Q_congr _ _ _ _ (eq_Q_refl_inst _) hcoll)
  pmode
  pintro hJ
  prw (cauchyfy_zero_R (.app .succ J)) in hJ with hJ1
  papplym (lt_Q_congr (.app Term.abs_Q (Term.app2 Term.sub_Q Cj Term.zero_Q)) P'
    (.app Term.abs_Q C) P'
    (eqQtrans (abs_Q_congr (sub_Q_zero_Q Cj)) (abs_Q_congr hCC))
    (eq_Q_refl_inst P')) in hJ1 with hC
  papplym (lt_Q_imp_le_Q (.app Term.abs_Q C) P') in hC with hCle
  prw (cauchyfy_mul_R f g (.app .succ k))
  prw (cauchyfy_zero_R (.app .succ k))
  papplym (lt_Q_congr (Term.app2 Term.mul_Q (.app Term.abs_Q A) (.app Term.abs_Q C)) P
    (.app Term.abs_Q (Term.app2 Term.sub_Q (Term.app2 Term.mul_Q A C) Term.zero_Q)) P
    (eqQtrans (eqQsym (abs_Q_mul A C))
      (abs_Q_congr (eqQsym (sub_Q_zero_Q (Term.app2 Term.mul_Q A C)))))
    (eq_Q_refl_inst P))
  papplym (le_lt_Q_trans (Term.app2 Term.mul_Q (.app Term.abs_Q A) (.app Term.abs_Q C))
    (Term.app2 Term.mul_Q Bf P') P)
  psplit
  · papplym (le_Q_mul_o (.app Term.abs_Q A) Bf (.app Term.abs_Q C) P')
    psplit
    · psplit
      · pthm (le_Q_zero_abs A)
      · pthm (le_Q_zero_abs C)
    · psplit
      · pthm (cauchyfy_mag_le f I)
      · pexact hCle
  · pthm hfin

/-- **`g =ℝ 0ℝ →ᶠ f ·ℝ g =ℝ 0ℝ`.** A general fact about the encoded reals. -/
def mul_eq_zero_R_core (f g : Term F Γ (realTy ι)) :
    Derivable F al Premises
      (eq_R g Term.zero_R →ᶠ eq_R (Term.app2 Term.mul_R f g) Term.zero_R) := by
  pmode
  pintro h
  pforall
  -- fold the weakening around the product BEFORE `canorm` unfolds `app2`: otherwise
  -- `papplym` has to push `rename` through `mul_R`'s body, which times out
  simp only [mul_R_app_weaken2, zero_R_weaken]
  pinst h (Term.app2 Term.add (.var .vz) (mulBound f.weaken g.weaken)) with hJ
  canorm
  papplym (mul_zero_est f.weaken g.weaken (.var .vz))
  pexact hJ

end MulZero

section WeakenFold

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- `le_R_of_le_R_pu` with its antecedent stated over the **pushed-in** weakenings `fw`, `gw`.
The two side conditions are closed by `simp` with the per-constant weaken lemmas, never by
defeq. -/
def le_R_of_le_R_pu_nf (f g : Term F Γ (realTy ι))
    (fw gw : Term F (Ty.nat :: Γ) (realTy ι)) (hf : f.weaken = fw) (hg : g.weaken = gw) :
    Derivable F al Premises
      (Formula.all Ty.nat
        (Formula.imp
          (Formula.eq0
            (Term.app2 Term.le_Q_dec
              (Term.app Term.pow2neg_Q (.var .vz))
              (Term.app2 Term.sub_Q
                (Term.app (Term.app Term.cauchyfy fw) (Term.app .succ (.var .vz)))
                (Term.app (Term.app Term.cauchyfy gw) (Term.app .succ (.var .vz)))))
            Term.zero)
          ⊥ᶠ)
       →ᶠ le_R f g) := by
  subst hf hg
  exact le_R_of_le_R_pu f g

theorem dist_weaken {ρ : Ty ι} (i : ι) :
    (Term.dist i : Term F Γ _).weaken (σ := ρ) = Term.dist i := rfl

theorem func_weaken {ρ : Ty ι} (c : κ) :
    (Term.func c : Term F Γ _).weaken (σ := ρ) = Term.func c := rfl

theorem one_R_weaken'' {ρ : Ty ι} :
    (Term.one_R : Term F Γ (realTy ι)).weaken (σ := ρ) = Term.one_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact one_R_closed_subst _

theorem add_R_weaken'' {ρ : Ty ι} :
    (Term.add_R : Term F Γ _).weaken (σ := ρ) = Term.add_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact add_R_closed_subst _

theorem mul_R_weaken'' {ρ : Ty ι} :
    (Term.mul_R : Term F Γ _).weaken (σ := ρ) = Term.mul_R := by
  rw [Term.weaken, Term.rename_eq_subst]; exact mul_R_closed_subst _

theorem rename_shift_fold {ρ : Ty ι} {τ : Ty ι} (t : Term F Γ τ) :
    Term.rename (Term.Renaming.shift (σ := ρ)) t = t.weaken := rfl

theorem rename_vs_fold {ρ : Ty ι} {τ : Ty ι} (t : Term F Γ τ) :
    Term.rename (fun {_} v => (Var.vs v : Var (ρ :: Γ) _)) t = t.weaken := rfl

/-- The complete fold set: every closed constant of the W-hyperbolic axioms loses its
weakening, `weaken` distributes over application, and only the atoms keep theirs. -/
macro "wfold" : tactic =>
  `(tactic| simp only [rename_shift_fold, rename_vs_fold, Term.app2, Term.app3, weaken_app,
      dist_weaken, func_weaken, clamp01_weaken, sub_R_weaken, one_R_weaken'',
      add_R_weaken'', mul_R_weaken''])

/-- Instance normalisation for the W-hyperbolic derivations: `rnorm`, then the two named
ℝ-formula substitution lemmas `rnorm` lacks, then the closed-constant rewrites the
`closed_subst` set lacks. -/
macro "znorm" : tactic =>
  `(tactic| (rnorm
             try simp only [eq_R_substF, le_R_substF]
             try rnorm
             try simp only [add_R_closed_subst, mul_R_closed_subst, one_R_closed_subst,
               zero_R_closed_subst]))

end WeakenFold

section WSelf

/-- **`W(x,x,λ̃) =_X x`**, at explicit `x` and `λ`. -/
def WHyperbolic.W_self_core {Γ : Ctx MetricSpace.ι} {a : Allowed}
    (x : Term WHyperbolic.F Γ xTy) (l : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy (Term.app3 WHyperbolic.W x x (.app Term.clamp01 l)) x) := by
  pmode
  papplym (eqAtType_sym_base () x (Term.app3 WHyperbolic.W x x (.app Term.clamp01 l)))
  -- (W1) at z := x, x := x, y := x, λ := l
  pfrom w1 := WHyperbolic.W1
  simp only [WHyperbolic.ax_W1, le_R_pu, Term.app3]
  pinst w1 x with w2
  znorm
  pclear w1
  pinst w2 x with w3
  znorm
  pclear w2
  pinst w3 x with w4
  znorm
  pclear w3
  pinst w4 l with w5
  znorm
  pclear w4
  wfold
  -- `≤ℝ` from its purely universal spelling, matched on the fully folded form
  papplym (le_R_of_le_R_pu_nf
    (Term.app2 (Term.dist ()) x (Term.app3 (Term.func ()) x x (.app Term.clamp01 l)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
        (Term.app2 (Term.dist ()) x x))
      (Term.app2 Term.mul_R (.app Term.clamp01 l) (Term.app2 (Term.dist ()) x x)))
    (Term.app2 (Term.dist ()) x.weaken
      (Term.app3 (Term.func ()) x.weaken x.weaken (.app Term.clamp01 l.weaken)))
    (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l.weaken))
        (Term.app2 (Term.dist ()) x.weaken x.weaken))
      (Term.app2 Term.mul_R (.app Term.clamp01 l.weaken)
        (Term.app2 (Term.dist ()) x.weaken x.weaken)))
    (by simp only [Term.app2, Term.app3, weaken_app, dist_weaken, func_weaken, clamp01_weaken])
    (by simp only [Term.app2, weaken_app, dist_weaken, clamp01_weaken,
      sub_R_weaken, one_R_weaken'', add_R_weaken'', mul_R_weaken''])) in w5 with hle
  pclear w5
  -- `0 ≤ d(x,w) ≤ RHS =ℝ 0 → d(x,w) =ℝ 0`
  pfrom z := le_zero_eq_zero_R
  pinst z (Term.app2 (Term.dist ()) x (Term.app3 (Term.func ()) x x (.app Term.clamp01 l)))
    with z1
  znorm
  pclear z
  pinst z1 (Term.app2 Term.add_R
      (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
        (Term.app2 (Term.dist ()) x x))
      (Term.app2 Term.mul_R (.app Term.clamp01 l) (Term.app2 (Term.dist ()) x x))) with z2
  znorm
  pclear z1
  papply z2
  psplit
  · psplit
    · pthm (dist_nonneg () x (Term.app3 (Term.func ()) x x (.app Term.clamp01 l)))
    · pexact hle
  · -- RHS =ℝ 0: both products vanish since d(x,x) =ℝ 0
    pfrom ae := add_eq_zero_R
    pinst ae (Term.app2 Term.mul_R (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
      (Term.app2 (Term.dist ()) x x)) with ae1
    znorm
    pclear ae
    pinst ae1 (Term.app2 Term.mul_R (.app Term.clamp01 l) (Term.app2 (Term.dist ()) x x))
      with ae2
    znorm
    pclear ae1
    papply ae2
    psplit
    · pthm (Derivable.mp (.dist_self () x)
        (mul_eq_zero_R_core (Term.app2 Term.sub_R Term.one_R (.app Term.clamp01 l))
          (Term.app2 (Term.dist ()) x x)))
    · pthm (Derivable.mp (.dist_self () x)
        (mul_eq_zero_R_core (.app Term.clamp01 l) (Term.app2 (Term.dist ()) x x)))

/-- **`⊢ ∀x^X ∀λ¹. W(x,x,λ̃) =_X x`** — the first theorem of W-hyperbolic spaces, derived
from (W1) in the object theory. -/
def WHyperbolic.W_self {Γ : Ctx MetricSpace.ι} {a : Allowed} :
    Derivable WHyperbolic.F a WHyperbolic.Premises (Γ := Γ)
      (Formula.all xTy (Formula.all rTy
        (eqAtType xTy
          (Term.app3 WHyperbolic.W (.var (.vs .vz)) (.var (.vs .vz))
            (.app Term.clamp01 (.var .vz)))
          (.var (.vs .vz))))) :=
  univ_gen (univ_gen (WHyperbolic.W_self_core (.var (.vs .vz)) (.var .vz)))

end WSelf

-- Axiom hygiene

#print axioms mul_eq_zero_R_core
#print axioms WHyperbolic.W_self
#print axioms WHyperbolic.premises_pu
#print axioms WHyperbolic.W1
#print axioms WHyperbolicModel.W_maj_at
#print axioms WHyperbolicModel.abstractMajorizability
#print axioms WHyperbolicModel.constMajorants
#print axioms WHyperbolicModel.eqXInterp
#print axioms WHyperbolicModel.codeReal_interp_dist
#print axioms WHyperbolicModel.W1_holds
#print axioms WHyperbolicModel.W2_holds
#print axioms WHyperbolicModel.W3_holds
#print axioms WHyperbolicModel.W4_holds
#print axioms WHyperbolicModel.axiomsHold
#print axioms WHyperbolicModel.spremise
#print axioms WHyperbolicModel.soundness
#print axioms WHyperbolicModel.w_metatheorem
#print axioms WHyperbolicModel.w_metatheorem_classical

end Metatheorems
