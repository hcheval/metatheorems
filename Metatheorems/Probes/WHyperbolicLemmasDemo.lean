/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.WHyperbolicLemmas
import Metatheorems.Instances
import Metatheorems.Probes.RevTriangleDemo

/-!
# Probe: the W-hyperbolic library, read back in a model

`Metatheorems/WHyperbolicLemmas.lean` derives a chain of theorems about W-hyperbolic spaces
**in the object theory**, from (W1)/(W4) plus the free `dist_*` constructors and the ℝ layer.
This file checks that they say what they claim, the way `Probes/RevTriangleDemo.lean` does
for the reverse triangle inequality: instantiate each at an **arbitrary** `WHyperbolicModel`
through `WHyperbolicModel.soundness` and read the conclusion back as a statement about
Mathlib `ℝ` and the model's own `W` and `d`.

Nothing here consults `M.W1`–`M.W4` directly: the route is object derivation →
`WHyperbolicModel.soundness` → `codeReal` bridge → Mathlib ℝ.

The `≤ℝ` read-out is `RevTriangleDemo.codeReal_le_of_interpret_le_R_pu` (imported, not
duplicated); the `=_X` read-out is `MetricModel.eq_of_eqAtType_base_gen` — separation, i.e.
`M.d_eq_zero`, which is exactly what turns object-level `d(s,t) =ℝ 0ℝ` into `s = t` on the
carrier. The parameter `λ` is a free code and the model sees `clampReal (codeReal r)`; the
discussion of that is in the notes.

Concrete instance: the last section runs the same statements at `WHyperbolicModel.ofNormed ℝ`
— Mathlib's real line as a W-hyperbolic space, with `W x y λ = (1−λ)x + λy`.

Not attempted: bound extraction from any of these (the MFI lane's area).
-/

namespace Metatheorems
namespace WHyperbolicLemmasDemo

open Formula

-- The object-level derivations, at four free variables

/-- Three free points and one free real code. De Bruijn: `x = x₃`, `y = x₂`, `z = x₁`,
`λ = x₀`. -/
abbrev Γw : Ctx MetricSpace.ι := [rTy, xTy, xTy, xTy]

def px : Term WHyperbolic.F Γw xTy := .var (.vs (.vs (.vs .vz)))
def py : Term WHyperbolic.F Γw xTy := .var (.vs (.vs .vz))
def pz : Term WHyperbolic.F Γw xTy := .var (.vs .vz)
def pl : Term WHyperbolic.F Γw rTy := .var .vz

/-- A second free code, for (W2), which speaks about two parameters. De Bruijn:
`x = x₃`, `y = x₂`, `λ = x₁`, `μ = x₀`. -/
abbrev Γ2 : Ctx MetricSpace.ι := [rTy, rTy, xTy, xTy]

def qx : Term WHyperbolic.F Γ2 xTy := .var (.vs (.vs (.vs .vz)))
def qy : Term WHyperbolic.F Γ2 xTy := .var (.vs (.vs .vz))
def ql : Term WHyperbolic.F Γ2 rTy := .var (.vs .vz)
def qm : Term WHyperbolic.F Γ2 rTy := .var .vz

def dLeft := WHyperbolic.dist_W_left (a := Allowed.extended) px py pl
def dRight := WHyperbolic.dist_W_right (a := Allowed.extended) px py pl
def dLower := WHyperbolic.dist_W_left_lower (a := Allowed.extended) px py pl
def dMonoR := WHyperbolic.dist_W_mono_right (a := Allowed.extended) px py pz pl
def dMonoL := WHyperbolic.dist_W_mono_left (a := Allowed.extended) px py pz pl
def dBetween := WHyperbolic.dist_W_between (a := Allowed.extended) px py pl
def wZero := WHyperbolic.W_zero (a := Allowed.extended) px py
def wOne := WHyperbolic.W_one (a := Allowed.extended) px py
def w3 := WHyperbolic.W3_at (a := Allowed.extended) px py pl

/-- (W2) at the two free codes, split into its two `≤ℝ` halves — the `=ℝ` read-out is
assembled from them in the model by `le_antisymm`, so no new semantic bridge is needed
beyond `RevTriangleDemo.codeReal_le_of_interpret_le_R_pu`. Both halves are object-level:
`le_R_of_eq_R_core` and `eq_R_sym_core`. -/
def w2le : Derivable WHyperbolic.F Allowed.extended WHyperbolic.Premises
    (le_R
      (Term.app2 (Term.dist ())
        (Term.app3 (Term.func ()) qx qy (.app Term.clamp01 ql))
        (Term.app3 (Term.func ()) qx qy (.app Term.clamp01 qm)))
      (Term.app2 Term.mul_R
        (.app Term.abs_R
          (Term.app2 Term.sub_R (.app Term.clamp01 ql) (.app Term.clamp01 qm)))
        (Term.app2 (Term.dist ()) qx qy))) :=
  Derivable.mp (WHyperbolic.W2_at qx qy ql qm) (le_R_of_eq_R_core _ _)

def w2ge : Derivable WHyperbolic.F Allowed.extended WHyperbolic.Premises
    (le_R
      (Term.app2 Term.mul_R
        (.app Term.abs_R
          (Term.app2 Term.sub_R (.app Term.clamp01 ql) (.app Term.clamp01 qm)))
        (Term.app2 (Term.dist ()) qx qy))
      (Term.app2 (Term.dist ())
        (Term.app3 (Term.func ()) qx qy (.app Term.clamp01 ql))
        (Term.app3 (Term.func ()) qx qy (.app Term.clamp01 qm)))) :=
  Derivable.mp (Derivable.mp (WHyperbolic.W2_at qx qy ql qm) (eq_R_sym_core _ _))
    (le_R_of_eq_R_core _ _)

-- The model side

section Model

variable (M : WHyperbolicModel)

/-- `(d(s,t))◦` passes every Cauchy check — the side condition of `codeReal_interp_sub_R`. -/
theorem isCauchyCode_interp_dist {Γ : Ctx MetricSpace.ι} (s t : Term WHyperbolic.F Γ xTy)
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    IsCauchyCode (Term.interpret M.si (Term.app2 (Term.dist ()) s t) env) := by
  rw [M.interp_dist_gen M.si (fun _ _ => rfl) s t env]
  exact fun k => Rounding.roundR_cauchy _ (M.d_nonneg _ _) k

/-- The environment: `x ↦ a`, `y ↦ b`, `z ↦ c`, `λ ↦ r`. -/
abbrev envW (a b c : M.carrier) (r : ℕ → ℕ) : Ctx.interpret (fun () => M.carrier) Γw :=
  (r, c, b, a, ())

/-- The clamped parameter the model actually sees: an arbitrary element of `[0,1]`. -/
noncomputable abbrev par (r : ℕ → ℕ) : ℝ := clampReal (codeReal r)

theorem par_mem (r : ℕ → ℕ) : 0 ≤ par r ∧ par r ≤ 1 :=
  ⟨clampReal_nonneg _, clampReal_le_one _⟩

-- The four variables denote what they should. All four hold by `rfl`; they are named so that
-- `simp only` can fire them (`Term.interpret` does not unfold under a `def`).

theorem interp_px (a b c : M.carrier) (r : ℕ → ℕ) :
    Term.interpret M.si px (envW M a b c r) = a := rfl
theorem interp_py (a b c : M.carrier) (r : ℕ → ℕ) :
    Term.interpret M.si py (envW M a b c r) = b := rfl
theorem interp_pz (a b c : M.carrier) (r : ℕ → ℕ) :
    Term.interpret M.si pz (envW M a b c r) = c := rfl
theorem interp_pl (a b c : M.carrier) (r : ℕ → ℕ) :
    Term.interpret M.si pl (envW M a b c r) = r := rfl

/-- The whole read-out set: evaluate `W`, push `codeReal` through every ℝ operation, collapse
the double clamp (`clampReal_of_mem` at an already-clamped argument), and read the four
variables off the environment. This is `WHyperbolicModel.W1_holds`'s simp set run backwards —
there it turns a model fact into an object formula, here an object formula into a model
fact. -/
macro "wreadout" h:ident : tactic =>
  `(tactic| simp only [WHyperbolicModel.interp_W, codeReal_interp_add_R,
      codeReal_interp_mul_R, codeReal_interp_sub_R, codeReal_interp_one_R,
      codeReal_interp_zero_R, codeReal_interp_clamp01, isCauchyCode_interp_clamp01,
      isCauchyCode_interp_mul_R, WHyperbolicModel.codeReal_interp_dist,
      clampReal_of_mem, clampReal_nonneg, clampReal_le_one,
      interp_px, interp_py, interp_pz, interp_pl] at $h:ident)

/-- **`d(x, W(x,y,λ)) ≤ λ·d(x,y)` in every W-hyperbolic model**, from the object-level
`dist_W_left` — half of Kohlenbach's geodesic property. -/
theorem dist_W_left_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.d a (M.W a b (par r)) ≤ par r * M.d a b := by
  have hs := M.soundness (Derivable.mp dLeft (le_R_pu_of_le_R _ _)) (envW M a b a r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **`d(y, W(x,y,λ)) ≤ (1−λ)·d(y,x)` in every W-hyperbolic model**, from `dist_W_right`.
The right-hand side carries `d(y,x)`: that is what (W1) at `z := y` gives, and the object
theory has no `=ℝ`-congruence for `·ℝ` to turn it into `d(x,y)`. Here in the model the two
are of course equal — `M.d_comm` — which is precisely why the object-level restriction is a
statement about the *ℝ layer*, not about W-hyperbolic spaces. -/
theorem dist_W_right_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.d b (M.W a b (par r)) ≤ (1 - par r) * M.d b a := by
  have hs := M.soundness (Derivable.mp dRight (le_R_pu_of_le_R _ _)) (envW M a b a r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **The reverse inequality**, from `dist_W_left_lower`:
`d(x,y) − (1−λ)·d(y,x) ≤ d(x, W(x,y,λ))`. With `M.d_comm` this reads
`λ·d(x,y) ≤ d(x, W(x,y,λ))`, which together with `dist_W_left_in_model` is Kohlenbach's
equality `d(x, W(x,y,λ)) = λ·d(x,y)` — see the `linarith` below, which does on the model side
the arithmetic the object theory cannot yet do for want of multiplicative monotonicity. -/
theorem dist_W_left_lower_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.d a b - (1 - par r) * M.d b a ≤ M.d a (M.W a b (par r)) := by
  have hs := M.soundness (Derivable.mp dLower (le_R_pu_of_le_R _ _)) (envW M a b a r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **Kohlenbach's geodesic identity `d(x, W(x,y,λ)) = λ·d(x,y)`, assembled in the model.**

Both halves come from the object theory (`dist_W_left`, `dist_W_left_lower`); the only step
done *here* rather than there is replacing `d(y,x)` by `d(x,y)` inside the product and the
ring identity `d(x,y) − (1−λ)·d(x,y) = λ·d(x,y)`. Object-level, both need an `=ℝ`-congruence
for `·ℝ`, i.e. multiplicative monotonicity of `≤ℝ`, which the ℝ layer does not have — see
`WHyperbolicLemmas.lean`'s header. So this theorem is the exact measure of what is missing:
one `linarith` over `M.d_comm`. -/
theorem dist_W_left_eq_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.d a (M.W a b (par r)) = par r * M.d a b := by
  have h1 := dist_W_left_in_model M a b r
  have h2 := dist_W_left_lower_in_model M a b r
  have hc : M.d b a = M.d a b := M.d_comm b a
  rw [hc] at h2
  nlinarith [h1, h2]

/-- **`W(x,y,0) = x` in every W-hyperbolic model**, from the object-level `W_zero`. The clamp
is the identity at `0`, so the model's parameter really is `0`. -/
theorem W_zero_in_model (a b : M.carrier) :
    M.W a b 0 = a := by
  have hs := M.soundness wZero (envW M a b a (fun _ => 0))
  have he := M.toMetricModel.eq_of_eqAtType_base_gen M.si (fun _ _ => rfl) _ _ _ hs
  simp only [WHyperbolicModel.interp_W, codeReal_interp_clamp01, codeReal_interp_zero_R,
    clampReal_of_mem (0:ℝ) le_rfl zero_le_one] at he
  exact he

/-- **`W(x,y,1) = y`**, from `W_one`. -/
theorem W_one_in_model (a b : M.carrier) :
    M.W a b 1 = b := by
  have hs := M.soundness wOne (envW M a b a (fun _ => 0))
  have he := M.toMetricModel.eq_of_eqAtType_base_gen M.si (fun _ _ => rfl) _ _ _ hs
  simp only [WHyperbolicModel.interp_W, codeReal_interp_clamp01, codeReal_interp_one_R,
    clampReal_of_mem (1:ℝ) zero_le_one le_rfl] at he
  exact he

/-- **`W(x,·,λ)` is `λ`-Lipschitz**, from `dist_W_mono_right` (i.e. from (W4)). -/
theorem dist_W_mono_right_in_model (a b c : M.carrier) (r : ℕ → ℕ) :
    M.d (M.W a b (par r)) (M.W a c (par r)) ≤ par r * M.d b c := by
  have hs := M.soundness (Derivable.mp dMonoR (le_R_pu_of_le_R _ _)) (envW M a b c r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **`W(·,y,λ)` is `(1−λ)`-Lipschitz**, from `dist_W_mono_left`. -/
theorem dist_W_mono_left_in_model (a b c : M.carrier) (r : ℕ → ℕ) :
    M.d (M.W a b (par r)) (M.W c b (par r)) ≤ (1 - par r) * M.d a c := by
  have hs := M.soundness (Derivable.mp dMonoL (le_R_pu_of_le_R _ _)) (envW M a c b r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **The geodesic detour bound**, from `dist_W_between`:
`d(x,W) + d(W,y) ≤ λ·d(x,y) + (1−λ)·d(y,x)` — which, with `M.d_comm`, is `d(x,y)`. -/
theorem dist_W_between_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.d a (M.W a b (par r)) + M.d (M.W a b (par r)) b
      ≤ par r * M.d a b + (1 - par r) * M.d b a := by
  have hs := M.soundness (Derivable.mp dBetween (le_R_pu_of_le_R _ _)) (envW M a b a r)
  have hle := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs
  wreadout hle
  exact hle

/-- **(W3) in the model**: `W(x,y,λ) = W(y,x,1−λ)`, from `W3_at` through separation. -/
theorem W3_in_model (a b : M.carrier) (r : ℕ → ℕ) :
    M.W a b (par r) = M.W b a (1 - par r) := by
  have hs := M.soundness w3 (envW M a b a r)
  have he := M.toMetricModel.eq_of_eqAtType_base_gen M.si (fun _ _ => rfl) _ _ _ hs
  simp only [WHyperbolicModel.interp_W, codeReal_interp_sub_R, codeReal_interp_one_R,
    codeReal_interp_clamp01, isCauchyCode_interp_clamp01] at he
  -- the four variables read off the environment by `rfl`, so a type ascription suffices
  have hm := par_mem r
  have he' : M.W a b (clampReal (par r)) = M.W b a (clampReal (1 - par r)) := he
  rw [clampReal_of_mem (par r) hm.1 hm.2,
    clampReal_of_mem (1 - par r) (by linarith [hm.2]) (by linarith [hm.1])] at he'
  exact he'

/-- **Extensionality of `W` in its first argument**, read back: from the object-level
`W_ext_left`, whose premise is the object formula `x =_X x'` and whose conclusion is
`W(x,y,λ) =_X W(x',y,λ)`. `eqAtType_base_holds_gen` turns the model-side `a = c` into the
object premise, `eq_of_eqAtType_base_gen` (separation) turns the object conclusion back into
a carrier equation. Nothing here consults `M.W1`–`M.W4`. -/
theorem W_ext_left_in_model (a b c : M.carrier) (r : ℕ → ℕ) (hac : a = c) :
    M.W a b (par r) = M.W c b (par r) := by
  have hs := M.soundness (WHyperbolic.W_ext_left (a := Allowed.extended) px pz py pl)
    (envW M a b c r)
  have hp := M.toMetricModel.eqAtType_base_holds_gen M.si (fun _ _ => rfl) px pz
    (envW M a b c r) hac
  have he := M.toMetricModel.eq_of_eqAtType_base_gen M.si (fun _ _ => rfl) _ _ _ (hs hp)
  simp only [WHyperbolicModel.interp_W, codeReal_interp_clamp01,
    isCauchyCode_interp_clamp01, clampReal_of_mem, clampReal_nonneg, clampReal_le_one,
    interp_px, interp_py, interp_pz, interp_pl] at he
  exact he

/-- **Extensionality of `W` in its second argument**, from `W_ext_right`. -/
theorem W_ext_right_in_model (a b c : M.carrier) (r : ℕ → ℕ) (hbc : b = c) :
    M.W a b (par r) = M.W a c (par r) := by
  have hs := M.soundness (WHyperbolic.W_ext_right (a := Allowed.extended) px py pz pl)
    (envW M a b c r)
  have hp := M.toMetricModel.eqAtType_base_holds_gen M.si (fun _ _ => rfl) py pz
    (envW M a b c r) hbc
  have he := M.toMetricModel.eq_of_eqAtType_base_gen M.si (fun _ _ => rfl) _ _ _ (hs hp)
  simp only [WHyperbolicModel.interp_W, codeReal_interp_clamp01,
    isCauchyCode_interp_clamp01, clampReal_of_mem, clampReal_nonneg, clampReal_le_one,
    interp_px, interp_py, interp_pz, interp_pl] at he
  exact he

/-- The environment for the two-parameter context `Γ2`. -/
abbrev env2 (a b : M.carrier) (r r' : ℕ → ℕ) : Ctx.interpret (fun () => M.carrier) Γ2 :=
  (r', r, b, a, ())

theorem interp_qx (a b : M.carrier) (r r' : ℕ → ℕ) :
    Term.interpret M.si qx (env2 M a b r r') = a := rfl
theorem interp_qy (a b : M.carrier) (r r' : ℕ → ℕ) :
    Term.interpret M.si qy (env2 M a b r r') = b := rfl
theorem interp_ql (a b : M.carrier) (r r' : ℕ → ℕ) :
    Term.interpret M.si ql (env2 M a b r r') = r := rfl
theorem interp_qm (a b : M.carrier) (r r' : ℕ → ℕ) :
    Term.interpret M.si qm (env2 M a b r r') = r' := rfl

/-- **(W2) in the model**: `d(W(x,y,λ), W(x,y,μ)) = |λ−μ|·d(x,y)` — Kohlenbach's axiom (W2),
read back out of the object theory as an equation on Mathlib `ℝ`. The two `≤` halves are
object-level (`w2le`, `w2ge`); `le_antisymm` joins them here. -/
theorem W2_in_model (a b : M.carrier) (r r' : ℕ → ℕ) :
    M.d (M.W a b (par r)) (M.W a b (par r')) = |par r - par r'| * M.d a b := by
  have hs1 := M.soundness (Derivable.mp w2le (le_R_pu_of_le_R _ _)) (env2 M a b r r')
  have hs2 := M.soundness (Derivable.mp w2ge (le_R_pu_of_le_R _ _)) (env2 M a b r r')
  have h1 := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs1
  have h2 := RevTriangleDemo.codeReal_le_of_interpret_le_R_pu _ _ _ hs2
  simp only [WHyperbolicModel.interp_W, codeReal_interp_mul_R, codeReal_interp_abs_R,
    codeReal_interp_sub_R, codeReal_interp_clamp01, isCauchyCode_interp_clamp01,
    WHyperbolicModel.codeReal_interp_dist, clampReal_of_mem, clampReal_nonneg,
    clampReal_le_one, interp_qx] at h1 h2
  exact le_antisymm h1 h2

end Model

-- The concrete instance: Mathlib's real line

section RealLine

/-- Mathlib `ℝ` as a W-hyperbolic space, via `WHyperbolicModel.ofNormed`. -/
noncomputable abbrev Mreal : WHyperbolicModel := WHyperbolicModel.ofNormed ℝ

/-- The geodesic identity on the real line, mined from the object-level derivation:
`|x − ((1−λ)x + λy)| = λ·|x − y|` for `λ ∈ [0,1]`. -/
example (a b : ℝ) (r : ℕ → ℕ) :
    Mreal.d a (Mreal.W a b (par r)) = par r * Mreal.d a b :=
  dist_W_left_eq_in_model Mreal a b r

/-- `W(x,y,0) = x` on the real line. -/
example (a b : ℝ) : Mreal.W a b 0 = a := W_zero_in_model Mreal a b

/-- `W(x,y,1) = y` on the real line. -/
example (a b : ℝ) : Mreal.W a b 1 = b := W_one_in_model Mreal a b

/-- Nonexpansiveness in the second argument, on the real line. -/
example (a b c : ℝ) (r : ℕ → ℕ) :
    Mreal.d (Mreal.W a b (par r)) (Mreal.W a c (par r))
      ≤ par r * Mreal.d b c :=
  dist_W_mono_right_in_model Mreal a b c r

end RealLine

#print axioms dLeft
#print axioms dRight
#print axioms dLower
#print axioms wZero
#print axioms wOne
#print axioms dist_W_left_in_model
#print axioms dist_W_right_in_model
#print axioms dist_W_left_lower_in_model
#print axioms dist_W_left_eq_in_model
#print axioms W_zero_in_model
#print axioms W_one_in_model
#print axioms dist_W_mono_right_in_model
#print axioms dist_W_mono_left_in_model
#print axioms dist_W_between_in_model
#print axioms W2_in_model
#print axioms W3_in_model
#print axioms W_ext_left_in_model
#print axioms W_ext_right_in_model

end WHyperbolicLemmasDemo
end Metatheorems
