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

**RESULT: MIXED, and sharper than pass/fail.** Three findings, each measured:

1. **The proof-mode layer is transparent to `monotone_soundness` — in the kernel.** A
   proof-mode derivation (`pmFinal`: `pforall`/`pintro`/`pinst`/`pexists`/`pexact`, i.e.
   `pm_allI`, `pm_intro`, `pm_inst`, `pm_exI`, `seq_id`; **449 constructors**, no `Eq.mpr`
   in its transitive closure) yields `U = V = 901` at `x* = (5,5)`, the *counter side*
   included, kernel-checked in **≈2.2 s** — and the same over the large `triB` matrix
   (`pmFinalBig`, 449 constructors, `U` 1.75 s, `V` 0.76 s), and through
   `monotone_general_metatheorem_at` (`Φ = 901`, 2.06 s). The term route never produced a
   counter-side numeral from any proof-mode derivation.
   **The instrument matters**: the same `U` by bare `rfl` (`Meta.isDefEq`) is a
   200 000-heartbeat `whnf` timeout whose profile is `Ty.casesOn ↦ 23488`, `Eq.rec ↦ 1331`,
   `termMajorizer ↦ 140`, `monotone_soundness ↦ 86` — type-level `Ty.interpret`
   recomputation with **no cache**, because the model `M`, `h` are free variables
   (`Meta.whnf` caches closed terms only). The kernel caches by structure. `kernel_rfl`
   below assigns `Eq.refl` and lets the kernel alone decide; its non-vacuity control is
   that the kernel **rejects** `900` (`e1_U_900`, run live: "(kernel) declaration type
   mismatch", 1.8 s).
2. **`dist_tri_chain` itself is unreachable by any numeric bound, structurally.** Its
   formula `le_R f g = ¬ lt_R g f` has `wTy = ((nat ×ₜ unit) →ₜ unit) ×ₜ ((nat ×ₜ unit) →ₜ
   unit →ₜ unit)`: every component is `unit`-valued, so no projection of its monotone
   realizer is a number, and a `unit`-valued `rfl` closes by structure eta without
   reducing anything. The brief's literal design (`finalA`: the chained inequality in the
   premise slot, *derived* by `dist_tri_chain` and weakened away) therefore reduces —
   `V = 901`, `U = 0` — **by laziness**: `whnf` never enters `dist_tri_chain`'s realizer,
   exactly as `TriangleBoundDemo.triUncUtB_is_zero` never entered `dist_tri`. Recorded, not
   claimed as a test of anything.
   The design that *does* route a number through the content is transitivity: premise
   `∀n [(d(x,y)+d(y,z))+d(z,w) ≤ T]ₙ`, conclusion `∃v [d(x,w) ≤ T]ᵥ`, via `dist_tri_chain`
   and `le_R_trans_core` (`final` below; it elaborates). There the counter of `le_R f g`
   **is** an index (`cTy (le_R f g) = (nat ×ₜ unit) ×ₜ unit`), and `U` is the index at which
   the premise inequality must be known — computed *through* `le_R_trans_core`'s engine.
3. **That design does not reduce, and the blocker is localised to one line of one lemma —
   not to the proof mode, not to induction, not to `le_R_trans_core`, not to
   `dist_tri_chain`.** The smallest piece, `le_R_pu_of_le_R` (`d2`: 650 constructors,
   DAG 622, five `pm_*`, **one `Eq.mpr` from `canorm`**), fed a challenge index `3` on
   its counter side:
   * kernel (`kernel_rfl`): **`std::bad_alloc` at the 12 GB cap after ≈1 min**;
   * `Meta` (`rfl`, `diagnostics.threshold 5`): timeout; profile `Eq.rec ↦ 187521`,
     `Term.rec ↦ 35530`, `Term.rename ↦ 30410`, `List.rec ↦ 13412`, `Var.rec ↦ 13381`,
     `Renaming.ext ↦ 12814`, `Term.subst ↦ 5045`, then **the ℚ constants being unfolded**
     — `Term.add ↦ 413`, `monus ↦ 248`, `pd ↦ 248`, `triag ↦ 205`, `sg_bar ↦ 156`,
     `inv_triag ↦ 105`, `fst_pair ↦ 81`, `le_Q_dec ↦ 35`, `rat_sign ↦ 26` … — with
     `monotone_soundness ↦ 38` (38 of 650 nodes reached).
   * the discriminating control: the **same script without `canorm`** does not elaborate —
     `pexact hn` is itself a `whnf` timeout (19.7 s). So the cast's two sides are not
     cheaply definitional: the equation is a `closed_subst` normalisation
     (`Term.subst`/`rename` through `cauchyfy`, the 1.8M-node delta expansion CLAUDE.md's
     "Build cost" section documents), which the lemma proves *without* computing. The
     kernel's K-rule reduction of `Eq.mpr` has to check the two formulas definitionally
     equal — i.e. **redo the computation the `closed_subst` lemma was written to avoid.**
   Nothing about the monotone interpretation is at fault: the profile is renaming and
   substitution traffic on the *formula indices*, before the recursion has done anything.
   The fix is not in this lane: an `Eq.mpr`-commutation lemma for `monotone_soundness`
   (the `syntactic_soundness_eqmpr` shape, `Probes/CombinatorLemmas.lean`) applied by
   `simp` with the equation *given*, or `canorm`-free proof-mode lemmas. Both are the
   Track A programme one level up.

## Sizes (`derivSizeA` = constructor count as a tree; `reportD` = pointer-identity DAG)

| derivation | tree | DAG | `Eq.mpr` in closure | note |
|---|---|---|---|---|
| `pmFinal` (E1) | 449 | see `#eval` | 0 | proof mode, matrix `u =₀ u` |
| `pmFinalBig` (E3) | 449 | see `#eval` | 0 | proof mode, matrix `triB` |
| `d2 = le_R_pu_of_le_R` | 650 | 622 | 1 (`canorm`) | the blocker |
| `d1 = le_R_of_le_R_pu` | 4167 | 3979 | 1 (`canorm`) | |
| `tr = le_R_trans_core` | — | — | 0 itself; many below | **OOM at 12 GB while being BUILT** |
| `chain = dist_tri_chain` | — | — | 0 itself | `#eval derivSizeA` OOM at 12 GB |

The OOMs are a fact about *strict runtime construction*: `Derivable`'s constructors store
their formulas, and the proof-mode combinators compute `Formula.substF`/`weakenBy` of
formulas containing `cauchyfy` at every node. The kernel is lazy and is not bound by this
(finding 1); it is bound by finding 3.

`walk` (the transitive constant walk) on `final`: **442** reachable definitions,
`pm_induction` in `leR_tail` and `pow2neg_Q_le_add_all`, raw `Derivable.induction` in the
ℕ-arithmetic lemmas, `Eq.mpr` in `le_R_pu_of_le_R`, `le_R_of_le_R_pu`, `leR_tail`,
`leR_le`, `leR_strict`, `le_R_all`, `le_R_of_all`, `le_R_add_mono_l_core` and every
`*_inst`/`*_nf` lemma.

## The stalling declarations (NOT in the file — a file of errors is not a green build)

    -- kernel: std::bad_alloc at 12 GB after ≈1 min
    noncomputable def d2c : ℕ :=
      (((mr M h d2).val 0 (xs M, ())).2 (wdef M h (le_R dxw Tq) (xs M, ())) (cnt3 M)).1.1
    theorem d2c_is_3 : (3 : ℕ) = d2c M h := by kernel_rfl

    -- Meta: (deterministic) timeout at `whnf`, profile in finding 3
    set_option diagnostics true in set_option diagnostics.threshold 5 in
    example : (3 : ℕ) = d2c M h := by unfold d2c; rfl

    -- the discriminating control: `le_R_pu_of_le_R`'s script without `canorm`
    def d2nc : D [qTy] (le_R dxw Tq →ᶠ le_R_pu dxw Tq) := by
      pmode; pintro h; pforall; pintro hn; papply h; pexists (.var .vz); pexact hn
    -- pexact: (deterministic) timeout at `whnf` (19.7 s)

    -- Meta `rfl` on E1's counter side (the kernel does it in 2.2 s):
    set_option diagnostics true in set_option diagnostics.threshold 5 in
    theorem e1_U_meta : (901 : ℕ) = mfiU (triCm M h) (mr M h pmFinal) ((5 : ℕ), (5 : ℕ)) := by
      have hval : … = Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
      …  -- timeout at `whnf`; Ty.casesOn ↦ 23488, Eq.rec ↦ 1331, termMajorizer ↦ 140,
         -- monotone_soundness ↦ 86, Term.rename ↦ 66, MRealizer.syllogism ↦ 35

## Cost (kernel type-checking, `lake env lean -D profiler=true`, 2026-09-05, scratch runs;
## in the committed file the seven `kernel_rfl` theorems type-check in 0.7–1.7 s each)

| theorem | kernel |
|---|---|
| `e1_U` (proof mode, counter side, 449 constructors) | 2.22 s |
| `e1_U_900` control (rejected) | 1.76 s |
| `e3_U` (proof mode over `triB`) | 1.75 s |
| `e3_V` | 0.76 s |
| `e1_phi` (through `monotone_general_metatheorem_at`) | 2.06 s |
| `e2_U`, `e2_V` (`triFinal`, raw constructors, Meta `rfl` + `decide`) | ≈120–140 ms elab |
| `a_V` (`finalA`, lazy) | 170 ms elab |
| `a_U` (`finalA`, lazy; by `rfl` in the scratch) | 5.9 s Meta + 1.6 s kernel |
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
