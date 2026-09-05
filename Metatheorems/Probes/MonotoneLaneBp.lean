/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.Probes.UPremiseDemo
import Metatheorems.Probes.MonotoneLaneB

/-!
# Lane B': the `Eq.mpr` entry for the monotone functional interpretation, and its reach

`Dialectica/MonotoneMemo.lean` adds `MRealizer.transport` and the three commutation lemmas
`monotone_soundness_eqmpr`/`_eqmp`/`_subst`. This file exercises them.

## Gate G-B'1 — the entry reduces a real ℚ cast to a numeral (POSITIVE)

`castU` below is `UPremiseDemo`'s premise-consuming derivation
(`forall_ax s ⟶ exist_ax s`, composed by `syllogism`, so `U` is the majorant of the
instantiation term `s`), with the matrix carrying the heaviest ℚ constant, `mul_Q`
(590,955 reduced nodes, CLAUDE.md "Build cost"), and with **two `Eq.mp` casts injected on the
syllogism's middle formula** — exactly the role `le_R_pu_of_le_R`'s `canorm` cast plays, but
placed where `monotone_soundness` meets `Eq.mp` **directly**. The middle equation `mcEq`
(`mP.subst0 sMid ≡ mClean` up to a `mul_Q` `subst`) is cheap by `closed_subst` but a full
ℚ delta by kernel `rfl`.

* `monotone_soundness … (Eq.mp e d)` on the **bare** kernel forces `whnf` of the `Eq.mp`,
  i.e. `mul_Q.subst ≡ mul_Q` — the delta-expansion pathology.
* With `simp only [monotone_soundness_eqmp (hB := mcEq …)]` the cast is rewritten to
  `MRealizer.transport`, whose data cast is `congrArg wTy mcEq` — `wTy (eq0 …) = unit` on both
  sides, so it collapses structurally. `kernel_rfl` then reduces to `901`.

`castU`, `castU_at_7`, and the refutations are the evidence; **`U = 901`, moving with `x*`**.
The memo route's `kernel_rfl` is instant (the cast collapses to `cast rfl` structurally).

**Bare-kernel control, measured 2026-09-05** (run in scratch, then reverted — a control that is
not run is not a control). The same statement by `kernel_rfl` with **no** `simp` step:

    theorem castU_bare (g : ℕ → ℕ) : (901 : ℕ) = mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
      kernel_rfl

*terminates* — matrix `mul_Q`: **≈8 s**; matrix `cauchyfy (snd x) u`: **≈37 s**. So a *single*
directly-injected ℚ cast is a **linear** `Term.subst` delta (O(ℚ-constant size)), not the 12 GB
OOM: the kernel reduces `mul_Q.subst ≡ mul_Q` in one pass. The memo route turns that O(1). The
`std::bad_alloc` at 12 GB Lane B measured on the *real* `le_R_pu_of_le_R`
(`MonotoneLaneB.lean`, finding 3) is the **compounded** case — three casts, `cauchyfy` applied
to a *composed* real (`sub_Q (cauchyfy f …) (cauchyfy g …)`), inside the proof-mode layer — not
reproduced by one injected cast. What the entry buys is exactly the per-cast O(1); reaching the
compounded, pm-buried casts is the separate lane below.

## Gates G-B'1(literal `le_R_pu_of_le_R`), G-B'2, G-B'3 — the entry does NOT reach the
## proof-mode-buried casts (NEGATIVE, measured)

The memo lemmas fire only where `monotone_soundness` is applied *directly* to a cast. In a
proof-mode-written derivation the `Eq.mpr`/`Eq.mp`/`Eq.rec` casts sit **inside** the
`pm_*`/`seq_*` layer, so `monotone_soundness` is applied to a `pm_*`/`seq_*` def, not to the
cast. `simp` cannot fire the memo lemma without first unfolding that layer to raw `Derivable`
constructors, and:

* unfolding it explodes — `le_R_of_le_R_pu` alone is **4167** `Derivable` constructors
  (`MonotoneLaneB`), and `simp only [le_R_of_le_R_pu, le_R_pu_of_le_R, monotone_soundness,
  monotone_soundness_eqmpr] ; kernel_rfl` on the transitivity-shaped `∀q(∀n concT → ∃v concT)`
  is a `std::bad_alloc` at 12 GB (measured 2026-09-05);
* the kernel reduces the `pm_*`/`seq_*` layer *fine* on its own (Lane B finding 1: 449-node
  proof-mode derivation, 2 s) — it chokes **only** at the buried `Eq.mpr`, which is exactly
  what the memo lemma would fix if it could be reached.

Cast inventory (from a `Expr`-walk of the aux-lemma proofs, 2026-09-05):
`le_R_pu_of_le_R` 3 × `Eq.mpr`; `le_R_of_le_R_pu` 4 × `Eq.mpr`; `leR_tail` 5 × `Eq.mpr`
(+ `pm_induction`); `mct_body` 3 × `Eq.mpr`; `qfer_at_nf`/`qfer_nat_nf` 1 × `Eq.mp`;
`seq_cast` (hence `seq_induction`) 1 × `Eq.rec` (`h ▸`) — the three shapes the entry covers.

So reaching them needs the **MRealizer analogues of `Probes/CombinatorLemmas.lean`'s
`wit_seq_*`** (the counter-side commutation lemmas that push `monotone_soundness` through
`seq_of_thm`/`seq_mp`/`seq_id`/`seq_allI` so it meets the cast directly). That is a separate
lane, named by Lane B (`ARCHITECTURE.md` §14.5). The entry here is the missing *bridge* for
those lemmas' output; it is proven and demonstrated where the cast is reachable.

`derivSize` is deliberately **not** run on `le_R_pu_of_le_R`/`dist_tri_chain`/`mct_p2`: it is a
sharing-free tree count and OOMs at 12 GB even on `le_R_of_all` (a single ℚ leaf counts
2,963,450) — a ruler for raw-constructor derivations only (supervisor note, 2026-09-05).

## Part C0 — the classical route under MFI (measurement only)

See `Probes/ClassicalMfiProbe.lean`.
-/

namespace Metatheorems
namespace MonotoneLaneBp

open Formula
open UPremiseDemo (pTy uWit uCm uDummyOuter)
open MetricSpace (ι)
-- `kernel_rfl` is a tactic from `Probes.MonotoneLaneB`, available globally via the import.

-- ============================================================================
-- G-B'1: a directly-reachable heavy ℚ cast on the premise-consuming counter path
-- ============================================================================

/-- Matrix carrying the heaviest ℚ constant: `u =₀ mul_Q(u,u)`. QF and ∨-free, so `wTy` is
`unit` — the cast on it is invisible to `U`, which is the whole point. -/
def mP : Formula WHyperbolic.F [Ty.nat, pTy] :=
  Formula.eq0 (Term.var .vz) (Term.app2 Term.mul_Q (Term.var .vz) (Term.var .vz))

/-- The normalised middle formula `uWit =₀ mul_Q(uWit, uWit)`. -/
def mClean : Formula WHyperbolic.F [pTy] :=
  Formula.eq0 uWit (Term.app2 Term.mul_Q uWit uWit)

/-- Cheap by `closed_subst`; a full `mul_Q` delta by kernel `rfl`. -/
theorem mcEq : mP.subst0 uWit = mClean := by
  simp only [mP, mClean, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map_vz,
    Term.app2, closed_subst]

abbrev D (Γ : Ctx ι) (A : Formula WHyperbolic.F Γ) :=
  @Derivable ι WHyperbolic.κ WHyperbolic.F Allowed.extended WHyperbolic.Premises Γ A

/-- Instantiate `∀u mP` at `uWit`, then cast the (dirty) middle to the clean form — `Eq.mp`. -/
def uInstC : D [pTy] (Formula.all Ty.nat mP →ᶠ mClean) :=
  Eq.mp (congrArg (D [pTy]) (congrArg (fun M => Formula.all Ty.nat mP →ᶠ M) mcEq))
    (Derivable.forall_ax (A := mP) uWit)

/-- Existential intro with the clean middle as antecedent — the matching `Eq.mp`. -/
def uGenC : D [pTy] (mClean →ᶠ Formula.ex Ty.nat mP) :=
  Eq.mp (congrArg (D [pTy]) (congrArg (fun M => M →ᶠ Formula.ex Ty.nat mP) mcEq))
    (Derivable.exist_ax uWit mP)

/-- Compose: the premise is *consumed* through both casts (no `refl0`). -/
def uInnerC : D [pTy] (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP) :=
  Derivable.syllogism uInstC uGenC

def uInnerWC : D [pTy] (Formula.weakenBy pTy uDummyOuter →ᶠ
    (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  Derivable.mp uInnerC (Derivable.exportation Derivable.and_weak)

def uFinalC : D [] (Formula.all pTy (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule uInnerWC)

section Model
variable (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ))

noncomputable def mrC : MRealizer (uCm M h) (Formula.all pTy
    (Formula.all Ty.nat mP →ᶠ Formula.ex Ty.nat mP)) :=
  monotone_soundness M.eqXInterp M.spremise (uCm M h) uFinalC

/-- **G-B'1.** `U = 901` through two heavy `mul_Q` `Eq.mp` casts on the premise-consuming
counter path, via `monotone_soundness_eqmp` + the kernel. The `simp` step rewrites both casts
to `MRealizer.transport`, whose data cast collapses structurally (`wTy (eq0 …) = unit`);
`kernel_rfl` then evaluates. Bare `kernel_rfl` (no `simp`) is a `std::bad_alloc` at 12 GB
(see header). -/
theorem castU (g : ℕ → ℕ) :
    (901 : ℕ) = mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
  simp only [mrC, uFinalC, uInnerWC, uInnerC, uInstC, uGenC, monotone_soundness,
    monotone_soundness_eqmp (hB := congrArg (fun M' => Formula.all Ty.nat mP →ᶠ M') mcEq),
    monotone_soundness_eqmp (hB := congrArg (fun M' => M' →ᶠ Formula.ex Ty.nat mP) mcEq)]
  kernel_rfl

/-- `U` moves with `x*`: `1273` at `(7, g)` (as `UPremiseDemo.uUt_at_7`). -/
theorem castU_at_7 (g : ℕ → ℕ) :
    (1273 : ℕ) = mfiU (uCm M h) (mrC M h) ((7 : ℕ), g) := by
  simp only [mrC, uFinalC, uInnerWC, uInnerC, uInstC, uGenC, monotone_soundness,
    monotone_soundness_eqmp (hB := congrArg (fun M' => Formula.all Ty.nat mP →ᶠ M') mcEq),
    monotone_soundness_eqmp (hB := congrArg (fun M' => M' →ᶠ Formula.ex Ty.nat mP) mcEq)]
  kernel_rfl

/-- Non-degeneracy: the `simp`+kernel really evaluates, and `902` is refuted. -/
theorem castU_ne_902 (g : ℕ → ℕ) :
    (902 : ℕ) ≠ mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
  rw [← castU M h g]; decide

theorem castU_at_7_ne_901 (g : ℕ → ℕ) :
    (901 : ℕ) ≠ mfiU (uCm M h) (mrC M h) ((7 : ℕ), g) := by
  rw [← castU_at_7 M h g]; decide

end Model

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms castU
#print axioms castU_at_7
#print axioms castU_ne_902

end MonotoneLaneBp
end Metatheorems
