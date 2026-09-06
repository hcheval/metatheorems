/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.MonotoneMemoGates

/-!
# E2 — the same statement at a W-hyperbolic space, proved two ways, mined two bounds

**Statement** (metatheorem shape, `ρ := (X ×ₜ X) ×ₜ (nat ×ₜ (nat →ₜ nat))`,
`q = ((x, z), (k, f))`):

    ∀q (  ∀u ( [d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)]ᵤ  ∧  f (S u) =₀ f u +ᵗ f u )
       →  ∃v   [d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)]ᵥ  )

`[· ≤ℝ ·]ₙ` is the quantifier-free body of `le_R_pu`, so `∀u spB` **is** the triangle
inequality on the nose (`spAll_eq`, by `rfl`, as in `Probes/TriangleBoundDemo.lean`) and the
metatheorem's own premise variable `u` is its Cauchy index. The premise is therefore *the
space axiom together with* a doubling hypothesis on the function parameter `f`; the conclusion
asks for **some** precision `v ≤ Φ q*` at which the inequality is known.

**Two proofs, two bounds — the point of the file.** Both derivations prove the *same formula*
from the *same premise* with the *same majorants* (`TriangleBoundDemo.triCm M h`, i.e. any
W-hyperbolic model with `d(a, 0_X) ≤ 5`):

| proof | how `v` is chosen | `U = V` at `x* = ((5,5),(k*,λn.n+1))` |
|---|---|---|
| `eDir` (11 constructors) | the space's own number `⌈d(x,z)⌉₀` (`forall_ax` at `D0`) | **901**, and **1273** at `x* = ((7,5),…)` |
| `eRec` (187 constructors) | the output of a **doubling induction** on `k`, using the premise's second conjunct | **1** at `k*=0`, **8** at `k*=3`, **32** at `k*=5`; unchanged at `((7,5),…)` |

So one bound is a genuine function of the **space majorants** (901 → 1273 when the majorant of
`x` goes 5 → 7 — `distMajorant` is `λn₁n₂. (n₁+n₂)∘`), and the other is a genuine
**recursion** through `MRealizer.induction` = `cm.precM` = `recMaj` (the book's `t^M`),
doubling per induction step and *provably indifferent* to the space majorants (`Vrec3` and
`Vrec3b` are both `8`). Bounds are properties of proofs, not of theorems — here at a space,
with the space axiom in the premise slot and both numbers kernel-checked.

`U` is the index at which the **triangle inequality must be known**: `Udir = 901 = Vdir`
because the direct proof consults it at `⌈d(x,z)⌉₀`; `Urec = 2^{k*}·f*(0)` because the
recursive proof consults it at the index the recursion computed (which dominates the `k*−1` of
the ℕ conjunct).

## Method notes — what was needed to make these reduce (all measured, 2026-09-06)

* **`mfi_push` then `kernel_rfl`** (`Probes/MonotoneMemoGates.lean`, Lane D1). Bare
  `kernel_rfl` is a 12 GB `std::bad_alloc` on **every** number here: the casts inside
  `ex_and_left` and `forall_map` (`forall_ax_vz`, `substF_renameF_id`) are K-checked through
  `cauchyfy`/`le_Q_dec`, which is the documented delta-expansion trap. `mfi_push` rewrites them
  to `MRealizer.transportTo` at the kernel-normalised hat type and they cost nothing.
  `forall_map` is **not** among the theorems the `mfi_memo` set unfolds by itself and has to be
  passed explicitly; with it passed, no `monotone_soundness` head involving a cast survives
  (`mfi_report`: 30–60 `transportTo`, 0 cast nodes).
* **Never let the substitution reach the matrix.** The metatheorem's `B₀`/`C₀` are written
  once, in `[u, q]`, and every use is a `forall_ax`/`exist_ax` at the *same* term, so the two
  sides are the same expression and `whnf` never enters `spB`. Reducing a substitution through
  it *is* a `whnf` timeout — measured: `(Formula.all Ty.nat triK).subst0 Term.zero =
  Formula.all Ty.nat triB` by `rfl` exhausts 200 000 heartbeats. That is why the ℕ induction
  carries the *projected* premise `∀u natB` (via `forall_map`) rather than the conjunction.
* **A `Term.add` between the recursion's output and the space number does not reduce.** The
  first version of `eRec` used the witness `⌈d(x,z)⌉₀ +ᵗ w`, to have one number depending on
  both. Kernel: `std::bad_alloc` at 12 GB, in either summand order. The object-level `Term.add`
  is a `prec` term, so its majorant runs `recMaj` — and at an argument of size ≈900 that is
  what dies. The ceiling is the **value**, not the derivation: `ContentExampleNat`'s pure-ℕ `V`
  is kernel-checked at `2^7 = 128` (≈9 s) and is out of memory at `2^8 = 256`, on the same
  145-constructor derivation (measured 2026-09-06).
  The version kept here therefore reports the two dependencies as two proofs rather than as one
  sum, which is the more informative comparison anyway.

## Honest limits

The mathematics is elementary: the conclusion is an *instance of the premise*, so nothing is
proved *about* the space that the axiom did not already say. What is established is that a real
space axiom in the premise slot, consumed at an index a **recursion** computes, carries through
to a kernel-checked numeral, and that the numeral tracks whichever of (the space majorants, the
recursion) the proof actually used.
-/

set_option Elab.async false
set_option linter.unusedTactic false

namespace Metatheorems
namespace ContentExampleSpace

open Formula ProofMode
open TriangleBoundDemo (pTy triCm)
open MonotoneLaneA (derivSizeA)

-- ============================================================================
-- Types and contexts
-- ============================================================================

abbrev fTy : Ty MetricSpace.ι := Ty.nat →ₜ Ty.nat
/-- `q = ((x, z), (k, f))`. -/
abbrev qTy : Ty MetricSpace.ι := pTy ×ₜ (Ty.nat ×ₜ fTy)

abbrev K0 : Ctx MetricSpace.ι := [qTy]
abbrev K1 : Ctx MetricSpace.ι := Ty.nat :: K0
abbrev K2 : Ctx MetricSpace.ι := Ty.nat :: K1

abbrev DS (Γ : Ctx MetricSpace.ι) (A : Formula WHyperbolic.F Γ) :=
  @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
    WHyperbolic.Premises Γ A

abbrev x0 : Term WHyperbolic.F K0 xTy := Term.fst (Term.fst (.var .vz))
abbrev z0 : Term WHyperbolic.F K0 xTy := Term.snd (Term.fst (.var .vz))
abbrev y0 : Term WHyperbolic.F K0 xTy := Term.zeroX ()
abbrev f0 : Term WHyperbolic.F K0 fTy := Term.snd (Term.snd (.var .vz))
abbrev kk0 : Term WHyperbolic.F K0 Ty.nat := Term.fst (Term.snd (.var .vz))

abbrev f1 : Term WHyperbolic.F K1 fTy := Term.snd (Term.snd (.var (.vs .vz)))
abbrev kk1 : Term WHyperbolic.F K1 Ty.nat := Term.fst (Term.snd (.var (.vs .vz)))

abbrev f2 : Term WHyperbolic.F K2 fTy := Term.snd (Term.snd (.var (.vs (.vs .vz))))
/-- The induction variable, at depth 2. -/
abbrev ik2 : Term WHyperbolic.F K2 Ty.nat := .var (.vs .vz)
abbrev v2 : Term WHyperbolic.F K2 Ty.nat := .var .vz

-- ============================================================================
-- The statement
-- ============================================================================

def dxz : Term WHyperbolic.F K0 (realTy MetricSpace.ι) := Term.app2 (Term.dist ()) x0 z0
def dsum : Term WHyperbolic.F K0 (realTy MetricSpace.ι) :=
  Term.app2 Term.add_R (Term.app2 (Term.dist ()) x0 y0) (Term.app2 (Term.dist ()) y0 z0)

/-- The quantifier-free body of `d(x,z) ≤ℝ d(x,0_X) +ℝ d(0_X,z)` at index `u`. -/
def spB : Formula WHyperbolic.F K1 :=
  Formula.imp
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy dxz.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy dsum.weaken) (Term.app .succ (.var .vz)))))
      Term.zero)
    ⊥ᶠ

/-- **`∀u spB` is the triangle inequality**, on the nose — so the premise really is the space
axiom and `u` really is its Cauchy index. -/
theorem spAll_eq : Formula.all Ty.nat spB = le_R_pu dxz dsum := rfl

/-- The doubling hypothesis on the function parameter. -/
def natB : Formula WHyperbolic.F K1 :=
  Formula.eq0 (Term.app f1 (Term.app Term.succ (.var .vz)))
    (Term.app2 Term.add (Term.app f1 (.var .vz)) (Term.app f1 (.var .vz)))

/-- `B₀ := (triangle inequality at index u) ∧ (f (S u) =₀ f u +ᵗ f u)`. -/
def bigB : Formula WHyperbolic.F K1 := spB ∧ᶠ natB

theorem bigB_qf : bigB.isQF = true := rfl
theorem bigB_vf : bigB.isVFree = true := rfl
theorem spB_qf : spB.isQF = true := rfl
theorem spB_vf : spB.isVFree = true := rfl

-- ============================================================================
-- The ℕ half: the doubling induction (`ContentExampleNat`'s, at `f := snd (snd q)`)
-- ============================================================================

def nB2 : Formula WHyperbolic.F K2 :=
  Formula.eq0 (Term.app f2 (Term.app Term.succ v2))
    (Term.app2 Term.add (Term.app f2 v2) (Term.app f2 v2))
def nC2 : Formula WHyperbolic.F K2 := Formula.eq0 (Term.app f2 ik2) v2
def nCS2 : Formula WHyperbolic.F K2 :=
  Formula.eq0 (Term.app f2 (Term.app Term.succ ik2)) v2

def A1 : Formula WHyperbolic.F K1 := Formula.all Ty.nat nB2 →ᶠ Formula.ex Ty.nat nC2
def P1 : Formula WHyperbolic.F K1 := Formula.all Ty.nat nB2
def Q1 : Formula WHyperbolic.F K1 := Formula.ex Ty.nat nC2
def R1 : Formula WHyperbolic.F K1 := Formula.ex Ty.nat nCS2

def E1f : Formula WHyperbolic.F K1 :=
  Formula.eq0 (Term.app f1 (Term.app Term.succ (.var .vz)))
    (Term.app2 Term.add (Term.app f1 (.var .vz)) (Term.app f1 (.var .vz)))
def E2f : Formula WHyperbolic.F K2 :=
  Formula.eq0 (Term.app f2 (Term.app Term.succ ik2))
    (Term.app2 Term.add (Term.app f2 ik2) (Term.app f2 ik2))

/-- The ℕ conjunct of the premise, at `u := k`. -/
def hi : DS K1 (P1 →ᶠ E1f) := Derivable.forall_ax (A := nB2) (.var .vz)

/-- The step's one arithmetic fact, a single QF-ER at `r := x₀ +ᵗ x₀`. -/
def cong2 : DS K2 (nC2 →ᶠ Formula.eq0
    (Term.app2 Term.add (Term.app f2 ik2) (Term.app f2 ik2)) (Term.app2 Term.add v2 v2)) :=
  qfer_nat_nf (A₀ := nC2) rfl rfl I_comb
    (r := Term.app2 Term.add (.var .vz) (.var .vz)) (by rfl) (by rfl)

def CS3 : Formula WHyperbolic.F (Ty.nat :: K2) :=
  Formula.eq0
    (Term.app (Term.snd (Term.snd (.var (.vs (.vs (.vs .vz))))))
      (Term.app Term.succ (.var (.vs (.vs .vz))))) (.var .vz)

/-- The witness at step `k+1` is built from the one the induction hypothesis supplies. -/
def inner3 : DS K2 (nC2 ∧ᶠ E2f →ᶠ Formula.weakenBy Ty.nat R1) :=
  Derivable.syllogism
    (pair_h and_proj2 (Derivable.syllogism and_proj1 cong2))
    (Derivable.syllogism Derivable.trans0
      (Derivable.exist_ax (Term.app2 Term.add v2 v2) CS3))

def keyEA : DS K1 (E1f ∧ᶠ Q1 →ᶠ R1) :=
  Derivable.syllogism Derivable.and_perm
    (Derivable.syllogism ex_and_left (Derivable.exist_rule inner3))
def key : DS K1 (P1 →ᶠ Q1 →ᶠ R1) := Derivable.syllogism hi (Derivable.exportation keyEA)
def stepBody : DS K1 ((P1 →ᶠ Q1) →ᶠ (P1 →ᶠ R1)) := Derivable.mp key S_comb

def dummy0 : Formula WHyperbolic.F K0 := Formula.eq0 Term.zero Term.zero

def stepW : DS K1 (Formula.weakenBy Ty.nat dummy0 →ᶠ
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp stepBody (Derivable.exportation Derivable.and_weak)
def stepD : DS K0 (Formula.all Ty.nat
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule stepW)

def C0f : Formula WHyperbolic.F K1 :=
  Formula.eq0 (Term.app (Term.snd (Term.snd (.var (.vs .vz)))) Term.zero) (.var .vz)

def baseD : DS K0 (A1.subst0 Term.zero) :=
  Derivable.mp
    (Derivable.mp Derivable.refl0 (Derivable.exist_ax (Term.app f0 Term.zero) C0f))
    (Derivable.exportation Derivable.and_weak)

def Lraw : DS K0 (Formula.all Ty.nat A1) := Derivable.induction baseD stepD

def nCk : Formula WHyperbolic.F K1 := Formula.eq0 (Term.app f1 kk1) (.var .vz)

/-- `∀u natB →ᶠ ∃w (f k =₀ w)`, at `k := fst (snd q)`. -/
def lnk : DS K0 (Formula.all Ty.nat natB →ᶠ Formula.ex Ty.nat nCk) :=
  Derivable.mp Lraw (Derivable.forall_ax kk0)

/-- The premise's ℕ conjunct, under the `∀`. -/
def projN : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.all Ty.nat natB) :=
  forall_map and_proj2
/-- The premise's space conjunct, under the `∀`. -/
def projS : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.all Ty.nat spB) :=
  forall_map and_proj1

-- ============================================================================
-- Proof (b): the index is the recursion's output
-- ============================================================================

def innerSp : DS K1 (nCk ∧ᶠ Formula.weakenBy Ty.nat (Formula.all Ty.nat spB) →ᶠ
    Formula.weakenBy Ty.nat (Formula.ex Ty.nat spB)) :=
  Derivable.syllogism (Derivable.syllogism and_proj2 (Derivable.forall_ax (.var .vz)))
    (Derivable.exist_ax (.var .vz) (spB.renameF (Term.Renaming.ext Term.Renaming.shift)))

def exStep : DS K0 (Formula.ex Ty.nat nCk ∧ᶠ Formula.all Ty.nat spB →ᶠ Formula.ex Ty.nat spB) :=
  Derivable.syllogism ex_and_left (Derivable.exist_rule innerSp)

/-- **The triangle inequality, consumed at the index the recursion computes.** -/
def innerRec : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB) :=
  Derivable.syllogism (pair_h (Derivable.syllogism projN lnk) projS) exStep

-- ============================================================================
-- Proof (a): the index is the space's own number `⌈d(x,z)⌉₀`
-- ============================================================================

abbrev D0 : Term WHyperbolic.F K0 Ty.nat := Term.app dxz Term.zero

/-- **The same conclusion, consumed at `⌈d(x,z)⌉₀`** — no induction, eleven constructors. -/
def innerDir : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB) :=
  Derivable.syllogism (Derivable.syllogism (Derivable.forall_ax (A := bigB) D0) and_proj1)
    (Derivable.exist_ax D0 spB)

-- ============================================================================
-- Both, in metatheorem shape
-- ============================================================================

def eDummy : Formula WHyperbolic.F ([] : Ctx MetricSpace.ι) := Formula.eq0 Term.zero Term.zero

def wrapW (d : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :
    DS K0 (Formula.weakenBy qTy eDummy →ᶠ
      (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  Derivable.mp d (Derivable.exportation Derivable.and_weak)

def wrap (d : DS K0 (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :
    DS [] (Formula.all qTy (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  Derivable.mp (Derivable.refl0 (t := Term.zero)) (Derivable.forall_rule (wrapW d))

def eRec : DS [] (Formula.all qTy (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  wrap innerRec
def eDir : DS [] (Formula.all qTy (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  wrap innerDir

-- 187 and 11 raw constructors.
#eval derivSizeA eRec
#eval derivSizeA eDir

-- ============================================================================
-- The numerals, at an arbitrary W-hyperbolic model with `d(a, 0_X) ≤ 5`
-- ============================================================================

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

noncomputable def rRec : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) eRec
noncomputable def rDir : MRealizer (triCm M h)
    (Formula.all qTy (Formula.all Ty.nat bigB →ᶠ Formula.ex Ty.nat spB)) :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) eDir

abbrev XM := fun (_ : Unit) => M.carrier

/-- `q* = ((n_x, n_z), (k*, λn. n+1))`. -/
def qs (nx nz k : ℕ) : Ty.interpret (XM M) qTy.hat := ((nx, nz), (k, fun (n : ℕ) => n + 1))

macro "pushRecV" : tactic =>
  `(tactic| (unfold mfiV rRec
             mfi_push [eRec, wrap, wrapW, innerRec, exStep, innerSp, lnk, Lraw, baseD, stepD,
               stepW, stepBody, key, keyEA, inner3, hi, projN, projS, forall_map]))
macro "pushRecU" : tactic =>
  `(tactic| (unfold mfiU rRec
             mfi_push [eRec, wrap, wrapW, innerRec, exStep, innerSp, lnk, Lraw, baseD, stepD,
               stepW, stepBody, key, keyEA, inner3, hi, projN, projS, forall_map]))
macro "pushDirV" : tactic =>
  `(tactic| (unfold mfiV rDir
             mfi_push [eDir, wrap, wrapW, innerDir, projS, forall_map]))
macro "pushDirU" : tactic =>
  `(tactic| (unfold mfiU rDir
             mfi_push [eDir, wrap, wrapW, innerDir, projS, forall_map]))

/-! ### Proof (b): the bound is the recursion, and does not see the space majorants -/

theorem Vrec0 : (1 : ℕ) = mfiV (triCm M h) (rRec M h) (qs M 5 5 0) := by
  pushRecV
  kernel_rfl

theorem Vrec3 : (8 : ℕ) = mfiV (triCm M h) (rRec M h) (qs M 5 5 3) := by
  pushRecV
  kernel_rfl

theorem Vrec5 : (32 : ℕ) = mfiV (triCm M h) (rRec M h) (qs M 5 5 5) := by
  pushRecV
  kernel_rfl

/-- The same `k*` at a **different space majorant**: unchanged, as it must be — the recursive
proof never looks at the points. -/
theorem Vrec3b : (8 : ℕ) = mfiV (triCm M h) (rRec M h) (qs M 7 5 3) := by
  pushRecV
  kernel_rfl

/-- `U`: the precision at which the triangle inequality must be known, on this proof — the
recursion's output. -/
theorem Urec0 : (1 : ℕ) = mfiU (triCm M h) (rRec M h) (qs M 5 5 0) := by
  pushRecU
  kernel_rfl

theorem Urec3 : (8 : ℕ) = mfiU (triCm M h) (rRec M h) (qs M 5 5 3) := by
  pushRecU
  kernel_rfl

theorem Urec3b : (8 : ℕ) = mfiU (triCm M h) (rRec M h) (qs M 7 5 3) := by
  pushRecU
  kernel_rfl

/-! ### Proof (a): the bound is the space's own number, and does not see `k*` -/

theorem Vdir0 : (901 : ℕ) = mfiV (triCm M h) (rDir M h) (qs M 5 5 0) := by
  pushDirV
  kernel_rfl

/-- …and it **moves with the space majorant**: `901` at `x* = (5,5)`, `1273` at `(7,5)`. -/
theorem Vdirb : (1273 : ℕ) = mfiV (triCm M h) (rDir M h) (qs M 7 5 0) := by
  pushDirV
  kernel_rfl

theorem Udir : (901 : ℕ) = mfiU (triCm M h) (rDir M h) (qs M 5 5 0) := by
  pushDirU
  kernel_rfl

theorem Udirb : (1273 : ℕ) = mfiU (triCm M h) (rDir M h) (qs M 7 5 0) := by
  pushDirU
  kernel_rfl

/-! ### Refutation controls -/

theorem Vrec3_ne_7 : (7 : ℕ) ≠ mfiV (triCm M h) (rRec M h) (qs M 5 5 3) := by
  rw [← Vrec3 M h]; decide
theorem Vrec3_ne_9 : (9 : ℕ) ≠ mfiV (triCm M h) (rRec M h) (qs M 5 5 3) := by
  rw [← Vrec3 M h]; decide
/-- The recursive bound really moves with `k*`. -/
theorem Vrec5_ne_8 : (8 : ℕ) ≠ mfiV (triCm M h) (rRec M h) (qs M 5 5 5) := by
  rw [← Vrec5 M h]; decide
/-- **The two proofs really give different bounds** for the same formula at the same `q*`. -/
theorem Vdir0_ne_1 : (1 : ℕ) ≠ mfiV (triCm M h) (rDir M h) (qs M 5 5 0) := by
  rw [← Vdir0 M h]; decide
theorem Vrec0_ne_901 : (901 : ℕ) ≠ mfiV (triCm M h) (rRec M h) (qs M 5 5 0) := by
  rw [← Vrec0 M h]; decide
/-- The direct bound really moves with the space majorant. -/
theorem Vdirb_ne_901 : (901 : ℕ) ≠ mfiV (triCm M h) (rDir M h) (qs M 7 5 0) := by
  rw [← Vdirb M h]; decide
theorem Udir_ne_900 : (900 : ℕ) ≠ mfiU (triCm M h) (rDir M h) (qs M 5 5 0) := by
  rw [← Udir M h]; decide

end Model

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms spAll_eq
#print axioms eRec
#print axioms eDir
#print axioms Vrec0
#print axioms Vrec3
#print axioms Vrec5
#print axioms Vrec3b
#print axioms Urec0
#print axioms Urec3
#print axioms Urec3b
#print axioms Vdir0
#print axioms Vdirb
#print axioms Udir
#print axioms Udirb
#print axioms Vrec3_ne_7
#print axioms Vrec3_ne_9
#print axioms Vrec5_ne_8
#print axioms Vdir0_ne_1
#print axioms Vrec0_ne_901
#print axioms Vdirb_ne_901
#print axioms Udir_ne_900

end ContentExampleSpace
end Metatheorems
