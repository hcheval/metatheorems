/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MonotoneMetatheorem
import Metatheorems.KernelRfl
import Metatheorems.Probes.MonotoneLaneA
import Std.Data.HashMap

/-!
# Gate G2: the monotone functional interpretation meets the proof mode, `dist_tri_chain`,
# and the `LeOrder` machinery

**Question.** `Probes/MonotoneLaneA.lean` (gate G1) evaluates `monotone_soundness` on
derivations built from raw `Derivable` constructors. Does the recursion reduce through a
derivation *with content* — one written in the proof mode, containing `Eq.mpr` casts and
the `LeOrder` engine — to a numeral? The target named by ARCHITECTURE §14.5 is
`BaseEquality.dist_tri_chain`, `d(x,w) ≤ℝ (d(x,y) +ℝ d(y,z)) +ℝ d(z,w)`.

**RESULT: MIXED.** (1) The proof-mode layer is transparent to `monotone_soundness` in the
kernel: a 449-constructor proof-mode derivation gives `U = V = 901` at `x* = (5,5)`, counter side
included (`kernel_rfl`; bare `rfl` is the wrong instrument). (2) `dist_tri_chain` itself is
unreachable by any numeric bound (its realizer is `unit`-valued throughout). (3) The transitivity
design does not reduce: the blocker is one `Eq.mpr` from `canorm` in `le_R_pu_of_le_R`, whose
K-rule check redoes the `closed_subst` computation. The three findings in full, the size table,
the stalling declarations (not in the file) and the cost table are in the notes.
-/

namespace Metatheorems
namespace MonotoneLaneB

open Formula
open TriangleBoundDemo (pTy triCm triB triFinal triWit)
open ConjBoundDemo (tB)
open MonotoneLaneA (derivSizeA)

-- Tools

-- `kernel_rfl` was defined here until 2026-09-08. It is `Metatheorems/KernelRfl.lean` now
-- (imported above), so that `Demo/` and the library can use it without importing a probe.
-- The instrument's rationale and its non-vacuity control (`e1_U_900`) are unchanged.

open Lean Meta in
/-- Transitive constant walk from a definition, through every `Metatheorems.*` definition
(theorems are not entered; `pm_*`/`seq_*` combinators are listed, not entered), reporting
each reachable definition whose body mentions `Eq.mpr`/`Eq.mp`, a `pm_*`, a `seq_*`, or a
raw `Derivable.induction`. -/
partial def walk (root : Name) : MetaM Unit := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut lines : Array String := #[]
  let mut total := 0
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let some v := ci.value? | continue
    total := total + 1
    let cs := v.getUsedConstants
    let eqmpr := cs.filter (fun c => c == ``Eq.mpr || c == ``Eq.mp)
    let pm := cs.filter (fun c => (`Metatheorems.ProofMode).isPrefixOf c &&
      ((c.toString.splitOn ".").getLast!.startsWith "pm_"))
    let sq := cs.filter (fun c => (`Metatheorems.ProofMode).isPrefixOf c &&
      ((c.toString.splitOn ".").getLast!.startsWith "seq_"))
    let ind := cs.filter (fun c => c == ``Metatheorems.Derivable.induction)
    if !eqmpr.isEmpty || !pm.isEmpty || !sq.isEmpty || !ind.isEmpty then
      lines := lines.push
        s!"{n}: eqmpr={eqmpr.size} pm={pm.size} seq={sq.size} ind={ind.size}"
    for c in cs do
      let last := (c.toString.splitOn ".").getLast!
      if (`Metatheorems).isPrefixOf c && !(last.startsWith "pm_") && !(last.startsWith "seq_") then
        match env.find? c with
        | some (.thmInfo _) => pure ()
        | some _ => stack := c :: stack
        | none => pure ()
  let body := "\n".intercalate lines.toList
  logInfo m!"walk {root}: reachable defs = {total}; flagged = {lines.size}\n{body}"

abbrev Mm := StateT (Std.HashMap USize Nat) IO

/-- Constructor count memoised on the physical address (`SizeProbe.visit`'s trick, on
`Derivable`): the memo's size afterwards is the DAG size. -/
unsafe def visitD {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Mm Nat
  | _, _, d => do
    let addr := ptrAddrUnsafe d
    if let some n := (← get).get? addr then return n
    let n ← match d with
      | .mp a b          => do let x ← visitD a; let y ← visitD b; pure (1 + x + y)
      | .syllogism a b   => do let x ← visitD a; let y ← visitD b; pure (1 + x + y)
      | .exportation a   => do let x ← visitD a; pure (1 + x)
      | .importation a   => do let x ← visitD a; pure (1 + x)
      | .expansion a     => do let x ← visitD a; pure (1 + x)
      | .forall_rule a   => do let x ← visitD a; pure (1 + x)
      | .exist_rule a    => do let x ← visitD a; pure (1 + x)
      | .univ_gen a      => do let x ← visitD a; pure (1 + x)
      | .qfer _ _ a      => do let x ← visitD a; pure (1 + x)
      | .induction a b   => do let x ← visitD a; let y ← visitD b; pure (1 + x + y)
      | _                => pure 1
    modify (·.insert addr n)
    return n

unsafe def reportD {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F}
    {Γ : Ctx ι} {A : Formula F Γ} (name : String) (d : @Derivable ι κ F al P Γ A) : IO Unit := do
  let (tree, memo) ← (visitD d).run {}
  IO.println s!"{name}: dag={memo.size} tree={tree}"

-- The statement — four points and a real, `q = ((x,y),((z,w),T))`

abbrev rT : Ty MetricSpace.ι := realTy MetricSpace.ι
abbrev qTy : Ty MetricSpace.ι := pTy ×ₜ (pTy ×ₜ rT)
abbrev QF := WHyperbolic.F

abbrev q : Term QF [qTy] qTy := .var .vz
abbrev xq : Term QF [qTy] xTy := .fst (.fst q)
abbrev yq : Term QF [qTy] xTy := .snd (.fst q)
abbrev zq : Term QF [qTy] xTy := .fst (.fst (.snd q))
abbrev wq : Term QF [qTy] xTy := .snd (.fst (.snd q))
abbrev Tq : Term QF [qTy] rT := .snd (.snd q)

def dxw : Term QF [qTy] rT := Term.app2 (Term.dist ()) xq wq

/-- `(d(x,y) +ℝ d(y,z)) +ℝ d(z,w)` — the right-hand side of `dist_tri_chain`. -/
def lassoc : Term QF [qTy] rT :=
  Term.app2 Term.add_R
    (Term.app2 Term.add_R (Term.app2 (Term.dist ()) xq yq) (Term.app2 (Term.dist ()) yq zq))
    (Term.app2 (Term.dist ()) zq wq)

/-- The quantifier-free body of `le_R_pu f g` (`Terms/Real.lean`), in context `[n, q]`. -/
def puBody (f g : Term QF [qTy] rT) : Formula QF [Ty.nat, qTy] :=
  Formula.imp
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q (.var .vz))
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy f.weaken) (Term.app .succ (.var .vz)))
          (Term.app (Term.app Term.cauchyfy g.weaken) (Term.app .succ (.var .vz)))))
      Term.zero)
    ⊥ᶠ

/-- The chained inequality's body: `[d(x,w) ≤ (d(x,y)+d(y,z))+d(z,w)]ₙ`. -/
def chainL : Formula QF [Ty.nat, qTy] := puBody dxw lassoc
/-- The transitivity design's premise body: `[(d(x,y)+d(y,z))+d(z,w) ≤ T]ₙ`. -/
def chainT : Formula QF [Ty.nat, qTy] := puBody lassoc Tq
/-- …and its conclusion body: `[d(x,w) ≤ T]ᵥ`. -/
def concT : Formula QF [Ty.nat, qTy] := puBody dxw Tq

theorem chainL_eq : Formula.all Ty.nat chainL = le_R_pu dxw lassoc := rfl
theorem chainT_eq : Formula.all Ty.nat chainT = le_R_pu lassoc Tq := rfl
theorem concT_eq : Formula.all Ty.nat concT = le_R_pu dxw Tq := rfl
theorem chainL_pu : chainL.isPurelyUniversal = true := rfl
theorem chainL_pe : chainL.isPurelyExistential = true := rfl
theorem chainL_vf : chainL.isVFree = true := rfl
theorem chainT_pu : chainT.isPurelyUniversal = true := rfl
theorem chainT_vf : chainT.isVFree = true := rfl
theorem concT_pe : concT.isPurelyExistential = true := rfl
theorem concT_vf : concT.isVFree = true := rfl

/-- The instantiation/witness term: the 0th ℚ-code of `d(x,w)`. -/
def sq : Term QF [qTy] Ty.nat := Term.app dxw Term.zero

abbrev D (Γ : Ctx MetricSpace.ι) (A : Formula QF Γ) :=
  @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended WHyperbolic.Premises Γ A

-- (a) The literal design: the chained inequality DERIVED, in the premise slot, weakened away

/-- **`dist_tri_chain`**, at the four components of `q`. Its realizer is `unit`-valued
throughout (finding 2). -/
def chain : D [qTy] (le_R dxw lassoc) := dist_tri_chain () xq yq zq wq

/-- The chained inequality in `le_R_pu` form — `∀n chainL`, by `chainL_eq`. -/
def hypPU : D [qTy] (Formula.all Ty.nat chainL) := .mp chain (le_R_pu_of_le_R dxw lassoc)

def innerA : D [qTy] (Formula.all Ty.nat chainL →ᶠ Formula.ex Ty.nat chainL) :=
  .syllogism (.forall_ax (A := chainL) sq) (.exist_ax sq chainL)
def exUnc : D [qTy] (Formula.ex Ty.nat chainL) := .mp hypPU innerA
def innerB : D [qTy] (Formula.all Ty.nat chainL →ᶠ Formula.ex Ty.nat chainL) :=
  .mp exUnc (.exportation .and_weak)
def dummy : Formula QF [] := Formula.eq0 Term.zero Term.zero
def innerBW : D [qTy] (Formula.weakenBy qTy dummy →ᶠ
    (Formula.all Ty.nat chainL →ᶠ Formula.ex Ty.nat chainL)) :=
  .mp innerB (.exportation .and_weak)
/-- `⊢ ∀q (∀n chainL → ∃v chainL)`, the premise discharged by `dist_tri_chain` and never
consulted. -/
def finalA : D [] (Formula.all qTy (Formula.all Ty.nat chainL →ᶠ Formula.ex Ty.nat chainL)) :=
  .mp .refl0 (.forall_rule innerBW)

-- (b) The transitivity design: `U` routed THROUGH `le_R_trans_core` and `dist_tri_chain`

def d1 : D [qTy] (le_R_pu lassoc Tq →ᶠ le_R lassoc Tq) := le_R_of_le_R_pu lassoc Tq
def tr : D [qTy] (le_R dxw lassoc ∧ᶠ le_R lassoc Tq →ᶠ le_R dxw Tq) :=
  le_R_trans_core dxw lassoc Tq
def d2 : D [qTy] (le_R dxw Tq →ᶠ le_R_pu dxw Tq) := le_R_pu_of_le_R dxw Tq
def step : D [qTy] (le_R lassoc Tq →ᶠ le_R dxw Tq) := .mp chain (.exportation tr)
def s1 : D [qTy] (le_R_pu lassoc Tq →ᶠ le_R dxw Tq) := .syllogism d1 step
def tail : D [qTy] (le_R_pu dxw Tq →ᶠ Formula.ex Ty.nat concT) :=
  .syllogism (.forall_ax (A := concT) sq) (.exist_ax sq concT)
def s2 : D [qTy] (le_R dxw Tq →ᶠ Formula.ex Ty.nat concT) := .syllogism d2 tail
def inner : D [qTy] (Formula.all Ty.nat chainT →ᶠ Formula.ex Ty.nat concT) := .syllogism s1 s2
def innerW : D [qTy] (Formula.weakenBy qTy dummy →ᶠ
    (Formula.all Ty.nat chainT →ᶠ Formula.ex Ty.nat concT)) :=
  .mp inner (.exportation .and_weak)
/-- `⊢ ∀q ( ∀n [(d(x,y)+d(y,z))+d(z,w) ≤ T]ₙ → ∃v [d(x,w) ≤ T]ᵥ )`. Elaborates; its `U`
does not reduce (finding 3). -/
def final : D [] (Formula.all qTy (Formula.all Ty.nat chainT →ᶠ Formula.ex Ty.nat concT)) :=
  .mp .refl0 (.forall_rule innerW)

-- (E1, E3) Proof-mode derivations, small and large matrix, premise consumed

/-- E1: the proof mode over the tautologous matrix `u =₀ u` (`ConjBoundDemo.tB`). -/
def pmFinal : D [] (Formula.all pTy (Formula.all Ty.nat tB →ᶠ Formula.ex Ty.nat tB)) := by
  pmode
  pforall
  pintro h
  pinst h triWit with h1
  pexists triWit
  pexact h1

/-- E3: the same script over the triangle-inequality body `triB`. -/
def pmFinalBig : D [] (Formula.all pTy (Formula.all Ty.nat triB →ᶠ Formula.ex Ty.nat triB)) := by
  pmode
  pforall
  pintro h
  pinst h triWit with h1
  pexists triWit
  pexact h1

-- Measurements

#eval derivSizeA pmFinal        -- 449
#eval derivSizeA pmFinalBig     -- 449
#eval derivSizeA d2             -- 650
#eval derivSizeA d1             -- 4167
-- #eval derivSizeA chain       -- INTERNAL PANIC: out of memory (12 GB)
-- #eval reportD "tr" tr        -- INTERNAL PANIC: out of memory (12 GB), while being built
#eval reportD "pmFinal" pmFinal
#eval reportD "pmFinalBig" pmFinalBig
#eval reportD "d2 (le_R_pu_of_le_R)" d2
#eval reportD "d1 (le_R_of_le_R_pu)" d1

open Lean Meta in
#eval show MetaM Unit from walk ``Metatheorems.MonotoneLaneB.pmFinal
open Lean Meta in
#eval show MetaM Unit from walk ``Metatheorems.MonotoneLaneB.final

-- The numerals

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

/-- The monotone realizer of a derivation at the W-hyperbolic model, `triCm M h`. -/
noncomputable def mr {Γ : Ctx MetricSpace.ι} {A : Formula QF Γ} (d : D Γ A) :
    MRealizer (triCm M h) A :=
  monotone_soundness M.eqXInterp M.spremise (triCm M h) d

abbrev XM := fun (_ : Unit) => M.carrier

/-- `x* = ((5,5),((5,5), λ_.1))`. -/
noncomputable def xs : Ty.interpret (XM M) qTy.hat :=
  (((5 : ℕ), (5 : ℕ)), (((5 : ℕ), (5 : ℕ)), fun _ => (1 : ℕ)))

set_option linter.unusedTactic false

-- E2: raw constructors over the large matrix (TriangleBoundDemo's derivation) through MFI —
-- the MFI reproduces the term route's `901` (`TriangleBoundDemo.triUt_is_901`), by Meta `rfl`.
theorem e2_U : (901 : ℕ) = mfiU (triCm M h) (mr M h triFinal) ((5 : ℕ), (5 : ℕ)) := by
  have hval : mfiU (triCm M h) (mr M h triFinal) ((5 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]; decide

theorem e2_V : (901 : ℕ) = mfiV (triCm M h) (mr M h triFinal) ((5 : ℕ), (5 : ℕ)) := by
  have hval : mfiV (triCm M h) (mr M h triFinal) ((5 : ℕ), (5 : ℕ))
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]; decide

-- (a): closes, by laziness (finding 2)
theorem a_V : (901 : ℕ) = mfiV (triCm M h) (mr M h finalA) (xs M) := by
  have hval : mfiV (triCm M h) (mr M h finalA) (xs M)
      = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]; decide

theorem a_U : (0 : ℕ) = mfiU (triCm M h) (mr M h finalA) (xs M) := by
  kernel_rfl

-- E1 (finding 1): the proof-mode derivation's counter side, in the kernel
theorem e1_U : (901 : ℕ) = mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

theorem e1_V : (901 : ℕ) = mfiV (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

/-- `Φ` through `monotone_general_metatheorem_at` itself. -/
theorem e1_phi : (901 : ℕ) = (monotone_general_metatheorem_at M.eqXInterp M.spremise
    (triCm M h) rfl rfl rfl rfl pmFinal).val ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

/-- `U` moves with `x*`: at `(7,5)` it is `1273` (as `TriangleBoundDemo.triUt_at_7_5`). -/
theorem e1_U_at_7_5 : (1273 : ℕ) = mfiU (triCm M h) (mr M h pmFinal) ((7 : ℕ), (5 : ℕ)) := by
  kernel_rfl

-- E3: the same script over `triB`
theorem e3_U : (901 : ℕ) = mfiU (triCm M h) (mr M h pmFinalBig) ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

theorem e3_V : (901 : ℕ) = mfiV (triCm M h) (mr M h pmFinalBig) ((5 : ℕ), (5 : ℕ)) := by
  kernel_rfl

-- Refutation controls

theorem e1_U_ne_900 : (900 : ℕ) ≠ mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
  rw [← e1_U M h]; decide

theorem e1_U_ne_902 : (902 : ℕ) ≠ mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
  rw [← e1_U M h]; decide

theorem e1_U_at_7_5_ne_901 :
    (901 : ℕ) ≠ mfiU (triCm M h) (mr M h pmFinal) ((7 : ℕ), (5 : ℕ)) := by
  rw [← e1_U_at_7_5 M h]; decide

theorem e3_U_ne_900 : (900 : ℕ) ≠ mfiU (triCm M h) (mr M h pmFinalBig) ((5 : ℕ), (5 : ℕ)) := by
  rw [← e3_U M h]; decide

theorem a_V_ne_902 : (902 : ℕ) ≠ mfiV (triCm M h) (mr M h finalA) (xs M) := by
  rw [← a_V M h]; decide

/-! The live control for `kernel_rfl` (run 2026-09-05, then reverted — a control that is not
run is not a control): claiming

    theorem e1_U_900 : (900 : ℕ) = mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
      kernel_rfl

is rejected by the kernel in 1.76 s:

    error: (kernel) declaration type mismatch, 'e1_U_900' has type
      ∀ (M : WHyperbolicModel), M.d M.ref M.zeroX ≤ ↑5 → 900 = 900
    but is expected to have type
      ∀ (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ↑5), 900 = mfiU (triCm M h) … (5, 5)

So a passing `kernel_rfl` certifies the number: the kernel really evaluated the right-hand
side and compared. -/

end Model

-- Axiom hygiene — verify by name, after a completed `lake build`

#print axioms chainL_eq
#print axioms finalA
#print axioms final
#print axioms pmFinal
#print axioms pmFinalBig
#print axioms e2_U
#print axioms e2_V
#print axioms a_V
#print axioms a_U
#print axioms e1_U
#print axioms e1_V
#print axioms e1_phi
#print axioms e1_U_at_7_5
#print axioms e3_U
#print axioms e3_V
#print axioms e1_U_ne_900
#print axioms e1_U_ne_902
#print axioms e1_U_at_7_5_ne_901
#print axioms e3_U_ne_900
#print axioms a_V_ne_902

end MonotoneLaneB
end Metatheorems
