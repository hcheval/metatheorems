/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.MonotoneMCT

/-!
# E1 — a bound mined from a proof with content: induction + a consumed premise, at `ι = Empty`

**Statement** (metatheorem shape, `ρ := nat ×ₜ (nat →ₜ nat)`, `x = (k, f)`):

    ∀x ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f k =₀ v ) )

i.e. *if `f` doubles at every step, then `f k` is bounded* — and the metatheorem's `v ≤ Φ x*`
is that bound.

**What the proof does.** Induction on `k` (raw `Derivable.induction`), with the existential
witness at step `k+1` **built from the witness the induction hypothesis supplies**
(`ex_and_left` + `exist_rule` — the object-level ∃-elimination): `w ↦ w +ᵗ w`. The premise
`∀u B₀` is genuinely consumed, at `u := k`, once per step (`forall_ax k`), and the step's one
arithmetic fact is a single QF-ER congruence (`cong2` = `qfer_nat_nf` at `r := x₀ +ᵗ x₀`:
`f k =₀ w ⊢ f k + f k =₀ w + w`). Nothing is exhibited outright, nothing is weakened away,
and no witness term written by hand mentions `Term.prec` (the surface-recursor ban,
`ProofMode/Linter.lean`) — the iteration in the bound is produced by the extraction.

**The numbers** (`f* := λn. n+1`, so `f*(0) = 1`; kernel-checked by `kernel_rfl`, both routes):

| `x*` | `V` (witness) | `U` (premise) | `Φ = max U V` |
|---|---|---|---|
| `(3, λn.n+1)` | **8** | **2** | **8** |
| `(5, λn.n+1)` | **32** | **4** | **32** |
| `(2, λn.n+3)` | **12** | 1 | 12 |

`V(k*, f*) = 2^{k*} · f*(0)` — the doubling of the *proof* read off as an exponential in the
bound, through `MRealizer.induction` = `cm.precM` = `recMaj` (the book's `t^M`). It moves with
both components of `x*`: `8 → 32` when `k*` goes `3 → 5`, and `4 → 12` when `f*(0)` goes
`1 → 3`. `U(k*) = k* − 1` is *sharp*: the step at `k` instantiates the premise at `u := k`, for
`k = 0 … k*−1`, so `U(0) = U(1) = 0`, `U(2) = 1`, `U(3) = 2`, `U(5) = 4` — "how far into
`∀u B₀` the proof reaches", as a function of `x*`, not a copy of `V`.

## Three things this file measures that were not known

1. **The MFI route and the term route agree on `V` and disagree on `U`.**
   `closedMajorizer cmE vT (xs 3) = 8` — the *term* route (`syntactic_soundness` →
   `extractedVTerm` → `closedMajorizer`) reaches the same numeral, kernel-checked below. Its
   `U` does not: `closedMajorizer cmE uT (xs 3)` is `INTERNAL PANIC: out of memory` at the
   12 GB cap (measured; not in the file, since a file of errors is not a green build). That is
   the documented one-sidedness of the term route (`CLAUDE.md`, `ConjBoundDemo`), now seen on a
   derivation with an induction in it.
2. **Raw constructors vs the proof mode: 145 against 42,747 nodes, and only the first
   reduces.** `eFinalPm` below is *the same statement, proved by the same argument*, written
   with `pmode/pinduction/pinst/papply/pobtain/pexists/ptrans/prwby`. It elaborates fine and is
   `derivSizeA = 42,747` (295× the raw derivation, because every `pm_*` step inserts an
   `S_comb` per hypothesis in `Δ` and `prwby` a full QF-ER). Its bound reduces at `k* = 0`
   (`mfiV = 1`, after `mfi_push`, ≈8 s) and is a 12 GB `std::bad_alloc` at `k* = 1` — one step
   of the recursion. So on this example the wall is *derivation size*, i.e. the
   ×5-per-composition of `MRealizer.syllogism` (ARCHITECTURE §14.7), not the induction, not the
   premise, not the matrix.
3. **The ceiling is the VALUE, not the derivation.** On this same 145-constructor derivation
   the bound is kernel-checked at `k* = 7` (`V = 128`, ≈9 s of kernel time, `V_at_7` below) and
   is `INTERNAL PANIC: out of memory` at the 12 GB cap at `k* = 8` (`V = 256`) — measured
   2026-09-06, both by `kernel_rfl` with nothing else changed. The majorant of the object-level
   `Term.add` is a `prec` term, so `recMaj` iterates *value*-many times with nothing shared;
   that, not derivation size, is what stops the doubling at 128 here.
4. **`Φ` is a genuine recursion, not a projection.** `MonotoneMCT.indFinal` (the earlier
   `pinduction` control) has `V(k*) = k*` — the witness is the induction variable itself. Here
   the witness at `k+1` is a function *of the previous witness*, so `recMaj` iterates and the
   bound is exponential; the refutation controls below (`≠ 7`, `≠ 9`, `≠ 4`, `≠ 16`) pin it.
-/

set_option Elab.async false
set_option linter.unusedTactic false

namespace Metatheorems
namespace ContentExampleNat

open Formula ProofMode
open TinyBoundDemo (tXE tFE tSiE tEqxiE tPremE tSpremiseE)
open MonotoneMCT (cmE)
open MonotoneLaneA (derivSizeA)

-- The types and the three contexts

/-- The function parameter's type. -/
abbrev fTy : Ty Empty := Ty.nat →ₜ Ty.nat
/-- The metatheorem's quantified type: `x = (k, f)`. -/
abbrev sTy : Ty Empty := Ty.prod Ty.nat fTy

abbrev G0 : Ctx Empty := [sTy]
abbrev G1 : Ctx Empty := Ty.nat :: G0
abbrev G2 : Ctx Empty := Ty.nat :: G1

abbrev D (Γ : Ctx Empty) (A : Formula tFE Γ) :=
  @Derivable Empty Empty tFE Allowed.extended tPremE Γ A

abbrev f0 : Term tFE G0 fTy := Term.snd (.var .vz)
abbrev f1 : Term tFE G1 fTy := Term.snd (.var (.vs .vz))
abbrev f2 : Term tFE G2 fTy := Term.snd (.var (.vs (.vs .vz)))
abbrev k1 : Term tFE G1 Ty.nat := .var .vz
abbrev k2 : Term tFE G2 Ty.nat := .var (.vs .vz)
abbrev v2 : Term tFE G2 Ty.nat := .var .vz

-- The formulas

/-- `f (S u) =₀ f u +ᵗ f u` — the premise matrix, `u` the bound variable. -/
def B2 : Formula tFE G2 :=
  Formula.eq0 (Term.app f2 (Term.app Term.succ v2))
    (Term.app2 Term.add (Term.app f2 v2) (Term.app f2 v2))

/-- `f k =₀ v` — the conclusion matrix. -/
def C2 : Formula tFE G2 := Formula.eq0 (Term.app f2 k2) v2

/-- `f (S k) =₀ v` — the conclusion matrix at `k+1`. -/
def CS : Formula tFE G2 := Formula.eq0 (Term.app f2 (Term.app Term.succ k2)) v2

/-- The formula inducted on: `∀u B₀ →ᶠ ∃v (f k =₀ v)`. -/
def A1 : Formula tFE G1 := Formula.all Ty.nat B2 →ᶠ Formula.ex Ty.nat C2

def P1 : Formula tFE G1 := Formula.all Ty.nat B2
def Q1 : Formula tFE G1 := Formula.ex Ty.nat C2
def R1 : Formula tFE G1 := Formula.ex Ty.nat CS

/-- The premise instance at `u := k`. -/
def E1f : Formula tFE G1 :=
  Formula.eq0 (Term.app f1 (Term.app Term.succ k1))
    (Term.app2 Term.add (Term.app f1 k1) (Term.app f1 k1))

/-- …the same, one binder in. -/
def E2f : Formula tFE G2 :=
  Formula.eq0 (Term.app f2 (Term.app Term.succ k2))
    (Term.app2 Term.add (Term.app f2 k2) (Term.app f2 k2))

theorem E2f_eq : Formula.weakenBy Ty.nat E1f = E2f := rfl

-- The derivation — raw `Derivable` constructors, 145 of them

/-- **The premise is consumed**, at `u := k`: `(∀u B₀) →ᶠ f (S k) =₀ f k + f k`. -/
def hi : D G1 (P1 →ᶠ E1f) := Derivable.forall_ax (A := B2) k1

/-- The step's one arithmetic fact, a single QF-ER at `r := x₀ +ᵗ x₀`:
`f k =₀ v ⊢ f k + f k =₀ v + v`. -/
def cong2 : D G2 (C2 →ᶠ Formula.eq0
    (Term.app2 Term.add (Term.app f2 k2) (Term.app f2 k2)) (Term.app2 Term.add v2 v2)) :=
  qfer_nat_nf (A₀ := C2) rfl rfl I_comb
    (r := Term.app2 Term.add (.var .vz) (.var .vz)) (by rfl) (by rfl)

/-- `CS` under one more binder: `f (S k) =₀ w`, in `[w, v, k, x]`. -/
def CS3 : Formula tFE (Ty.nat :: G2) :=
  Formula.eq0
    (Term.app (Term.snd (.var (.vs (.vs (.vs .vz))))) (Term.app Term.succ (.var (.vs (.vs .vz)))))
    (.var .vz)

theorem CS3_eq : Formula.weakenBy Ty.nat R1 = Formula.ex Ty.nat CS3 := rfl

/-- **The witness is built from the induction hypothesis's witness**: under the `∃`, from
`f k =₀ v` and the premise instance, `f (S k) =₀ v +ᵗ v`, and `exist_ax` at `v +ᵗ v`. -/
def inner3 : D G2 (C2 ∧ᶠ E2f →ᶠ Formula.weakenBy Ty.nat R1) :=
  Derivable.syllogism
    (pair_h and_proj2 (Derivable.syllogism and_proj1 cong2))
    (Derivable.syllogism Derivable.trans0
      (Derivable.exist_ax (Term.app2 Term.add v2 v2) CS3))

/-- The ∃-elimination: `ex_and_left` keeps the premise instance available across it. -/
def keyEA : D G1 (E1f ∧ᶠ Q1 →ᶠ R1) :=
  Derivable.syllogism Derivable.and_perm
    (Derivable.syllogism ex_and_left (Derivable.exist_rule inner3))

def key : D G1 (P1 →ᶠ Q1 →ᶠ R1) :=
  Derivable.syllogism hi (Derivable.exportation keyEA)

/-- The induction step, `A1 →ᶠ A1[k := S k]`, by `S_comb` (the premise is used on both
sides of the implication). -/
def stepBody : D G1 ((P1 →ᶠ Q1) →ᶠ (P1 →ᶠ R1)) := Derivable.mp key S_comb

def dummy0 : Formula tFE G0 := Formula.eq0 Term.zero Term.zero

def stepW : D G1 (Formula.weakenBy Ty.nat dummy0 →ᶠ
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp stepBody (Derivable.exportation Derivable.and_weak)

def stepD : D G0 (Formula.all Ty.nat
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule stepW)

/-- The `∃`-body at `k := 0`: `f 0 =₀ v`. -/
def C0 : Formula tFE (Ty.nat :: G0) :=
  Formula.eq0 (Term.app (Term.snd (.var (.vs .vz))) Term.zero) (.var .vz)

/-- The base case: witness `f 0`. -/
def baseD : D G0 (A1.subst0 Term.zero) :=
  Derivable.mp
    (Derivable.mp Derivable.refl0 (Derivable.exist_ax (Term.app f0 Term.zero) C0))
    (Derivable.exportation Derivable.and_weak)

/-- `⊢ ∀k ( ∀u (f (S u) =₀ f u + f u) → ∃v (f k =₀ v) )`, in context `[x]`. -/
def Lraw : D G0 (Formula.all Ty.nat A1) := Derivable.induction baseD stepD

-- The metatheorem-shaped statement

/-- `B₀ := f (S u) =₀ f u +ᵗ f u`, `f := snd x`, in `[u, x]`. -/
def eB : Formula tFE [Ty.nat, sTy] :=
  Formula.eq0
    (Term.app (Term.snd (.var (.vs .vz))) (Term.app Term.succ (.var .vz)))
    (Term.app2 Term.add (Term.app (Term.snd (.var (.vs .vz))) (.var .vz))
      (Term.app (Term.snd (.var (.vs .vz))) (.var .vz)))

/-- `C₀ := f k =₀ v`, `f := snd x`, `k := fst x`, in `[v, x]`. -/
def eC : Formula tFE [Ty.nat, sTy] :=
  Formula.eq0 (Term.app (Term.snd (.var (.vs .vz))) (Term.fst (.var (.vs .vz)))) (.var .vz)

theorem eB_qf : eB.isQF = true := rfl
theorem eB_vf : eB.isVFree = true := rfl
theorem eC_qf : eC.isQF = true := rfl
theorem eC_vf : eC.isVFree = true := rfl

/-- `∀k` instantiated at `k := fst x`. -/
def innerD : D G0 (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC) :=
  Derivable.mp Lraw (Derivable.forall_ax (Term.fst (Term.var .vz)))

def eDummy : Formula tFE ([] : Ctx Empty) := Formula.eq0 Term.zero Term.zero

def eInnerW : D [sTy] (Formula.weakenBy sTy eDummy →ᶠ
    (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC)) :=
  Derivable.mp innerD (Derivable.exportation Derivable.and_weak)

/-- `⊢ ∀x ( ∀u (f (S u) =₀ f u + f u) → ∃v (f k =₀ v) )`. -/
def eFinal : D [] (Formula.all sTy (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule eInnerW)

-- 145 raw constructors.
#eval derivSizeA eFinal

-- The numerals, through the monotone functional interpretation

def rE : MRealizer cmE (Formula.all sTy (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC)) :=
  monotone_soundness tEqxiE tSpremiseE cmE eFinal

/-- `x* = (k*, λn. n+1)`, so `f*(0) = 1`. -/
def xs (k : ℕ) : Ty.interpret tXE sTy.hat := (k, fun (n : ℕ) => n + 1)
/-- `x* = (k*, λn. n+3)`, so `f*(0) = 3` — the other component of the majorant. -/
def ys (k : ℕ) : Ty.interpret tXE sTy.hat := (k, fun (n : ℕ) => n + 3)

/-- **The witness bound doubles per induction step**: `V(k*) = 2^{k*} · f*(0)`. -/
theorem V_at_3 : (8 : ℕ) = mfiV cmE rE (xs 3) := by kernel_rfl
theorem V_at_5 : (32 : ℕ) = mfiV cmE rE (xs 5) := by kernel_rfl
theorem V_at_0 : (1 : ℕ) = mfiV cmE rE (xs 0) := by kernel_rfl

/-- The largest value that still reduces on this derivation: `2^7 = 128` (≈9 s of kernel
time). At `k* = 8` the same `kernel_rfl` is out of memory at the 12 GB cap. -/
theorem V_at_7 : (128 : ℕ) = mfiV cmE rE (xs 7) := by kernel_rfl

/-- …and it tracks the *function* majorant too: `f*(0) = 3` triples every value. -/
theorem V_ys_at_0 : (3 : ℕ) = mfiV cmE rE (ys 0) := by kernel_rfl
theorem V_ys_at_2 : (12 : ℕ) = mfiV cmE rE (ys 2) := by kernel_rfl

/-- **The premise bound is sharp**: the step at `k` consults `∀u B₀` at `u := k`, for
`k = 0 … k*−1`, so `U(k*) = k* − 1`. -/
theorem U_at_0 : (0 : ℕ) = mfiU cmE rE (xs 0) := by kernel_rfl
theorem U_at_1 : (0 : ℕ) = mfiU cmE rE (xs 1) := by kernel_rfl
theorem U_at_2 : (1 : ℕ) = mfiU cmE rE (xs 2) := by kernel_rfl
theorem U_at_3 : (2 : ℕ) = mfiU cmE rE (xs 3) := by kernel_rfl
theorem U_at_5 : (4 : ℕ) = mfiU cmE rE (xs 5) := by kernel_rfl

/-- `Φ` through `monotone_general_metatheorem_at` itself — `max U V`. -/
theorem Phi_at_3 : (8 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    eB_qf eB_vf eC_qf eC_vf eFinal).val (xs 3) := by kernel_rfl

theorem Phi_at_5 : (32 : ℕ) = (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    eB_qf eB_vf eC_qf eC_vf eFinal).val (xs 5) := by kernel_rfl

-- The term route, for comparison — the witness side agrees, the counter side OOMs

noncomputable def vT : Term tFE ([] : Ctx Empty) (sTy →ₜ Ty.nat) :=
  extractedVTerm tEqxiE tSpremiseE (B₀ := eB) (C₀ := eC) eFinal

/-- **The term route reaches the same numeral on the witness side.** Its counter side
(`extractedUTerm` + `closedMajorizer`) is `INTERNAL PANIC: out of memory` at the 12 GB cap —
measured, and therefore not a declaration here. -/
theorem V_term_route_at_3 : (8 : ℕ) = closedMajorizer cmE vT (xs 3) := by kernel_rfl

-- Refutation controls — the `rfl`s reduce, they do not stick

theorem V_at_3_ne_7 : (7 : ℕ) ≠ mfiV cmE rE (xs 3) := by rw [← V_at_3]; decide
theorem V_at_3_ne_9 : (9 : ℕ) ≠ mfiV cmE rE (xs 3) := by rw [← V_at_3]; decide
/-- `V` really moves with `k*`: the `k* = 5` value is not the `k* = 3` one. -/
theorem V_at_5_ne_8 : (8 : ℕ) ≠ mfiV cmE rE (xs 5) := by rw [← V_at_5]; decide
/-- …and with `f*`: `f*(0) = 3` gives `12`, not the `4` that `f*(0) = 1` would. -/
theorem V_ys_at_2_ne_4 : (4 : ℕ) ≠ mfiV cmE rE (ys 2) := by rw [← V_ys_at_2]; decide
theorem U_at_3_ne_1 : (1 : ℕ) ≠ mfiU cmE rE (xs 3) := by rw [← U_at_3]; decide
theorem U_at_3_ne_3 : (3 : ℕ) ≠ mfiU cmE rE (xs 3) := by rw [← U_at_3]; decide
theorem Phi_at_3_ne_16 : (16 : ℕ) ≠ (monotone_general_metatheorem_at tEqxiE tSpremiseE cmE
    eB_qf eB_vf eC_qf eC_vf eFinal).val (xs 3) := by rw [← Phi_at_3]; decide

-- The same theorem, proved in the proof mode — 42,747 constructors, and it does not reduce

/-- The *same* argument written with the proof-mode tactics: `pinduction` at `Δ = []`, the
induction hypothesis applied to the premise, its witness obtained with `pobtain`, the new
witness `x₀ +ᵗ x₀` supplied with `pexists`, and the step's congruence by `prwby`.

It elaborates in ≈2 s and `#eval derivSizeA` gives **42,747** — 295× the 145 raw constructors
above (42,729 as written below), because each `pm_*` step inserts an `S_comb` per hypothesis in `Δ` and `prwby` expands
to a full QF-ER. Its bound reduces only at `k* = 0` (`mfi_push` then `kernel_rfl`, ≈8 s, giving
`mfiV = 1`); at `k* = 1` — one step of the recursion — it is a 12 GB `std::bad_alloc`. -/
def Lpm : D G0 (Formula.all Ty.nat A1) := by
  pmode
  pinduction
  · pintro h
    pexists (Term.app f0 Term.zero)
    prefl
  · pforall
    pintro ih
    pintro h
    pinst h (Term.var Var.vz) with hk
    papply ih in h with hex
    pobtain hex with hv
    pexists (Term.app2 Term.add (.var .vz) (.var .vz))
    ptrans (Term.app2 Term.add
      (Term.app (Term.snd (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
      (Term.app (Term.snd (.var (.vs (.vs .vz)))) (.var (.vs .vz))))
    · pexact hk
    · prwby hv
      prefl

#eval derivSizeA Lpm

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms eFinal
#print axioms Lpm
#print axioms V_at_3
#print axioms V_at_5
#print axioms V_at_0
#print axioms V_at_7
#print axioms V_ys_at_0
#print axioms V_ys_at_2
#print axioms U_at_0
#print axioms U_at_1
#print axioms U_at_2
#print axioms U_at_3
#print axioms U_at_5
#print axioms Phi_at_3
#print axioms Phi_at_5
#print axioms V_term_route_at_3
#print axioms V_at_3_ne_7
#print axioms V_at_3_ne_9
#print axioms V_at_5_ne_8
#print axioms V_ys_at_2_ne_4
#print axioms U_at_3_ne_1
#print axioms U_at_3_ne_3
#print axioms Phi_at_3_ne_16

end ContentExampleNat
end Metatheorems
