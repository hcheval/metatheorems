/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.BaseEquality
import Metatheorems.MetricSpaces
import Metatheorems.CodeRealOps
import Metatheorems.Probes.SizeProbe

/-!
# Probe: the reverse triangle inequality, measured and checked in a model

Two questions about `BaseEquality.dist_rev_tri` / `dist_rev_tri'` / `dist_rev_tri_abs`
(2026-09-05):

1. **How big is the derivation?** `SizeProbe.derivSize` on each of the three, at the
   metric signature with three free points, and `dist_tri_chain` beside them for scale.
   These are *tree* counts of `Derivable` constructors (that is what `derivSize` is), on a
   term that shares heavily — the ℝ-layer lemmas are `def`s cited many times — so the
   numbers say how much the kernel would have to *walk*, not how much memory the term takes.

2. **Does the theorem say what it claims?** Instantiate it at an arbitrary `MetricModel`
   through `MetricModel.soundness` and read the conclusion back on Mathlib `ℝ`:
   `M.d x z − M.d y z ≤ M.d x y`, and `|M.d x z − M.d y z| ≤ M.d x y`. The wiring is the
   existing `codeReal` bridge (`CodeRealOps.lean`) plus one lemma this file adds —
   `codeReal_le_of_interpret_le_R_pu`, the converse of `interpret_le_R_pu_of_codeReal_le`:
   `≤ℝ` true in the model gives `≤` on `codeReal`. That direction did not exist because every
   axiom-discharge in the tower goes the other way (model fact ⇒ object formula true).

Not attempted here: bound extraction from any of these — the MFI lane's area.
-/

namespace Metatheorems
namespace RevTriangleDemo

open MetricSpace

-- 1. Sizes

/-- Three free points of the space. -/
abbrev Γ3 : Ctx MetricSpace.ι := [xTy, xTy, xTy]

def px : Term MetricSpace.F Γ3 xTy := .var (.vs (.vs .vz))
def py : Term MetricSpace.F Γ3 xTy := .var (.vs .vz)
def pz : Term MetricSpace.F Γ3 xTy := .var .vz

abbrev dxz : Term MetricSpace.F Γ3 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) px pz
abbrev dyz : Term MetricSpace.F Γ3 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) py pz
abbrev dxy : Term MetricSpace.F Γ3 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) px py

/-- `d(x,z) −ℝ d(y,z) ≤ℝ d(x,y)` at the metric signature, no premises consulted. -/
def revTri : Derivable MetricSpace.F Allowed.extended MetricSpace.Premises
    (le_R (Term.app2 Term.sub_R dxz dyz) dxy) :=
  dist_rev_tri () px py pz

def revTri' : Derivable MetricSpace.F Allowed.extended MetricSpace.Premises
    (le_R (Term.app2 Term.sub_R dyz dxz) dxy) :=
  dist_rev_tri' () px py pz

def revTriAbs : Derivable MetricSpace.F Allowed.extended MetricSpace.Premises
    (le_R (.app Term.abs_R (Term.app2 Term.sub_R dxz dyz)) dxy) :=
  dist_rev_tri_abs () px py pz

/-- For scale: the chained triangle inequality on the same points. -/
def triChain := dist_tri_chain (F := MetricSpace.F) (al := Allowed.extended)
  (Premises := MetricSpace.Premises) () px py pz px

/-! **`derivSize` does not terminate on any of these.** `#eval SizeProbe.derivSize revTri`
(and `triChain`, `revTri'`, `revTriAbs`) dies with `INTERNAL PANIC: out of memory` under
the 12 GB cap *while building the value*: `derivSize` is a tree count and the compiled
evaluator preserves no sharing (`SizeProbe.lean`, finding 1), so a derivation that cites the
proof-mode ℝ-layer lemmas — each `le_R_trans_core` unfolds the `leR_tail` induction, each
`lt_Q_congr` a `lt_Q_of_eq_Q_diff` script, each `add_Q_comm_inst` the closed `add_Q_comm` —
is materialised as a tree far beyond memory. The evals are therefore *not* in this file (a
file of panics is not a green build); the reproduction is the four lines

    #eval SizeProbe.derivSize triChain
    #eval SizeProbe.derivSize revTri
    #eval SizeProbe.derivSize revTri'
    #eval SizeProbe.derivSize revTriAbs

Bracketed from below (scratch runs, 2026-09-05, same cap): `Derivable.dist_tri () x y z`
counts `1`; the single ℚ leaf `zero_lt_pow2neg_Q (.var .vz)` — `0 <ℚ 2^{-n}`, one
instantiation of a closed ℚ theorem — counts **2,963,450**; and the next piece up,
`le_R_of_all dxz dxz` (a 15-line proof-mode script citing a handful of such leaves), already
overflows, as does `le_R_refl_core dxz`. So the reverse triangle inequality, which goes
through `le_R_trans_core` four times, is many orders of magnitude beyond anything a tree
count can reach. `derivSize` is a ruler for raw-constructor derivations (`LemBoundDemo`,
`ConjBoundDemo`); on anything that goes through the ℚ/ℝ tower it is the
`sizeWithoutSharing` CLAUDE.md bans, one layer down. -/

-- 2. The converse bridge: `≤ℝ` true in a model ⇒ `≤` on `codeReal`

section Bridge

variable {ι κ : Type} {F : κ → Ty ι} {X : ι → Type} {si : SpaceInterp X F} {Γ : Ctx ι}

/-- **`≤ℝ` true in the model makes `≤` hold on the denoted reals.** The converse of
`interpret_le_R_pu_of_codeReal_le`. At index `n` the object bound is `2^{-n}` and each
`codeReal` is within `2^{-(n+1)}` of its `(n+1)`-st rounding, so the difference of the
denoted reals is below `2·2^{-n}` for every `n`, hence `≤ 0`. -/
theorem codeReal_le_of_interpret_le_R_pu (f g : Term F Γ (realTy ι))
    (env : Ctx.interpret X Γ)
    (h : Formula.interpret si (le_R_pu f g) env) :
    codeReal (Term.interpret si f env) ≤ codeReal (Term.interpret si g env) := by
  rw [QBridge.interpret_le_R_pu] at h
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1:ℝ)/2 < 1)
  have hpow : (1:ℝ) / 2 ^ n < ε / 2 := by
    rw [div_pow] at hn; simpa using hn
  have h1 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si f env) (n + 1)
  have h2 := abs_qval_cauchyfyN_sub_codeReal_lt (Term.interpret si g env) (n + 1)
  rw [abs_lt] at h1 h2
  have hq := h n
  have hr : ((Rounding.qval (QBridge.cauchyfyN (Term.interpret si f env) (n + 1)) : ℚ) : ℝ)
      - ((Rounding.qval (QBridge.cauchyfyN (Term.interpret si g env) (n + 1)) : ℚ) : ℝ)
      < 1 / 2 ^ n := by
    have hc : (((Rounding.qval (QBridge.cauchyfyN (Term.interpret si f env) (n + 1))
        - Rounding.qval (QBridge.cauchyfyN (Term.interpret si g env) (n + 1)) : ℚ)) : ℝ)
        < ((1 / 2 ^ n : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at hc
    exact hc
  have hh := two_halves_R n
  linarith [h1.1, h1.2, h2.1, h2.2]

end Bridge

-- 3. The theorem, read in an arbitrary metric model

section Model

variable (M : MetricModel)

/-- `(d(s,t))◦` denotes `d(s,t)` — the metric-model instance of the lemma the space files
each carry. -/
theorem codeReal_interp_dist {Γ : Ctx MetricSpace.ι} (s t : Term MetricSpace.F Γ xTy)
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    codeReal (Term.interpret M.si (Term.app2 (Term.dist ()) s t) env)
      = M.d (Term.interpret M.si s env) (Term.interpret M.si t env) := by
  rw [M.interp_dist s t env, codeReal_roundR _ (M.d_nonneg _ _)]

/-- `(d(s,t))◦` passes every Cauchy check — what `codeReal_interp_sub_R` asks of its
subtrahend. -/
theorem isCauchyCode_interp_dist {Γ : Ctx MetricSpace.ι} (s t : Term MetricSpace.F Γ xTy)
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    IsCauchyCode (Term.interpret M.si (Term.app2 (Term.dist ()) s t) env) := by
  rw [M.interp_dist s t env]
  exact fun k => Rounding.roundR_cauchy _ (M.d_nonneg _ _) k

/-- **The reverse triangle inequality holds in every metric model**, as a statement about
Mathlib `ℝ`, obtained *from the object-level derivation* through `MetricModel.soundness` —
not from `M.d_triangle` directly. -/
theorem rev_triangle_in_model (a b c : M.carrier) :
    M.d a c - M.d b c ≤ M.d a b := by
  have hs := M.soundness (Derivable.mp revTri (le_R_pu_of_le_R _ _)) (c, b, a, ())
  have hle := codeReal_le_of_interpret_le_R_pu _ _ _ hs
  rw [codeReal_interp_sub_R _ _ _ (isCauchyCode_interp_dist M _ _ _),
    codeReal_interp_dist M, codeReal_interp_dist M, codeReal_interp_dist M] at hle
  exact hle

/-- The absolute form, likewise. -/
theorem rev_triangle_abs_in_model (a b c : M.carrier) :
    |M.d a c - M.d b c| ≤ M.d a b := by
  have hs := M.soundness (Derivable.mp revTriAbs (le_R_pu_of_le_R _ _)) (c, b, a, ())
  have hle := codeReal_le_of_interpret_le_R_pu _ _ _ hs
  rw [codeReal_interp_abs_R,
    codeReal_interp_sub_R _ _ _ (isCauchyCode_interp_dist M _ _ _),
    codeReal_interp_dist M, codeReal_interp_dist M, codeReal_interp_dist M] at hle
  exact hle

end Model

#print axioms revTri
#print axioms revTri'
#print axioms revTriAbs
#print axioms codeReal_le_of_interpret_le_R_pu
#print axioms rev_triangle_in_model
#print axioms rev_triangle_abs_in_model

end RevTriangleDemo
end Metatheorems
