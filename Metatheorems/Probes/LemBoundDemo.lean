/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Majorizability

/-!
# Demo: the simplest statement whose proof uses EXCLUDED MIDDLE

Every extraction in this project so far — `TinyBoundDemo`, `WBoundDemo`, `UPremiseDemo`,
`TriangleBoundDemo`, `ConjBoundDemo` — runs a derivation at `Allowed.extended`, i.e. one
that never uses LEM. The *classical* route (`classical_to_prenex_extended` → negative
translation → Dialectica → `extractUTermP`/`extractVTermP`) has been proved sound since
2026-09-02 and has never been run to a number. This file runs it.

## Why the LEM has to sit at a quantified formula

`Arithmetic.qf_lem` derives `A ∨ᶠ ¬ᶠA` for **quantifier-free** `A` with no appeal to
`Derivable.lem` at all — QF matrices are decidable in the object theory, and that is a
theorem, not an assumption. So a case distinction on the *matrix* is free, and putting one in
would produce a derivation that lives at `Allowed.extended` and tells us nothing about the
classical route.

The minimal genuinely-non-QF instance available in the metatheorem's own shape
`∀x (∀u B₀ → ∃v C₀)` is LEM at the **Π₁ premise** `∀u B₀`. That is what `lemStep` below uses,
and it is the whole difference between the two derivations in this file.

## The statement

Deliberately the same one `TinyBoundDemo` proves, at `ι = Empty`, `ρ := Ty.nat`:

    ∀x:nat ( ∀u:nat (u =₀ u)  →  ∃v:nat (v =₀ x) )

`B₀ := (u =₀ u)`, `C₀ := (v =₀ x)`. Reusing it is the point: the *statement* is held fixed so
that the only thing being measured is the route.

## The controlled contrast

Two derivations of **that one formula**, both at `Allowed.classical`, both fed to
`syntactic_general_metatheorem_classical_at`, both majorized by the same
`bezemConstMajorantsEmpty`:

| derivation | proof | uses `Derivable.lem`? |
|---|---|---|
| `lFinalNoLem` | exhibit the witness `x` directly, weaken the premise away | no |
| `lFinalLem`   | `lem` at `∀u B₀`, then `or_elim_rule` over the two cases | **yes** |

They differ by exactly the LEM step: `lInnerLem` is `Derivable.mp lLem (or_elim_rule lCaseL
lCaseR)` where `lCaseL` is `lInner` weakened and `lCaseR` is pure ex-falso plumbing. Same
formula, same model, same majorants — so any difference in the extracted `U`/`V` is a
property of *the proof's use of excluded middle* and of nothing else.

and a third derivation, `lFinalExt`, which is **the same term as `lFinalNoLem` at a different
`Allowed` value** — `lExD`/`lInner`/`close` are all generic in `al` — so the intuitionistic
and classical *routes* are compared on literally one proof.

This is the discipline `TriangleBoundDemo`'s review established: when comparing two
extractions, hold the premise **formula** fixed, not merely the conclusion. Here it is held
fixed twice over — same formula, and for two of the three, same derivation term.

## THE RESULT — a negative one, and excluded middle is NOT the cause

The classical route **does not reduce to a numeral, on the smallest derivation that exists.**
The bound `rfl` — `(0 : Nat) = closedMajorizer lCmE lUtNoLem 5` — is a
`(deterministic) timeout at whnf`, with no limit raised. There are therefore no numeral
theorems for the classical extractors in this file; a file of `whnf` timeouts is not a green
build. The verbatim reproduction is at the bottom of this docstring.

**A measurement error, recorded because the rule it broke is this project's own.** The first
pass reported instead that `#eval lTermSize` OOMs at 12 GB and still OOMs at 20 GB, and
concluded from that. `lTermSize` is a structural tree traversal, i.e. exactly
`sizeWithoutSharing` — which CLAUDE.md's Track A item 1 bans in favour of `Expr.numObjs`,
because the measured tree/DAG ratio in this project is ≈10⁵. So that OOM is a fact about the
*tree*, which was already known to be astronomical, and it says nothing about whether the
bound reduces. The kernel's `whnf` caches where `#eval` does not, so they are different
engines and only the `rfl` is evidence. The OOM figures are kept out of the table below for
that reason.

**But `lUtNoLem` uses no LEM.** It is `close lInner`, the same term as the control. So the
cost is the *route* — `classical_to_prenex_extended` (prenexify → negative translation →
`nn_all_nn`) followed by Dialectica on the resulting `¬¬` formula — and not the excluded
middle. Putting a `Derivable.lem` in makes no observable difference because the route is
already past the ceiling without one. That is worth stating plainly: **this file set out to
measure the price of excluded middle and instead measured the price of classicality's
*plumbing*, which dominates it.**

The control in the same file, same model, same `bezemConstMajorantsEmpty`:

| route | derivation | `U` at `x*=5` | `V` at `x*=5` |
|---|---|---|---|
| extended (`…_metatheorem_at`) | `lFinalExt` | **0** (`rfl`) | **5** (`rfl`) |
| classical (`…_classical_at`) | `lFinalNoLem` | `whnf` timeout | `whnf` timeout |
| classical, with LEM | `lFinalLem` | `whnf` timeout | `whnf` timeout |

`lVtExt_at_5_ne_4` is the non-degeneracy control for the two that do reduce (trap 12: a `rfl`
where both sides stick at a common point proves nothing).

## Where the stall actually is — measured, not guessed

`set_option diagnostics true` on the stalling `rfl`. **Read this at threshold 5, not 500** —
the first pass of this analysis used 500, concluded from the resulting top-three that "nothing
from the negative translation appears at all, `whnf` never gets that far", and wrote that into
this file and into CLAUDE.md. It was false: the machinery was there, under the threshold. A
filtered view is not a small view of the truth, it is a different claim.

The full profile (threshold 5):

    Eq.rec ↦ 6312        Term.rec ↦ 1985       Term.rename ↦ 1930
    Formula.rec ↦ 138    Term.weaken ↦ 132     Formula.neg ↦ 74
    wTy ↦ 59             termMajorizer ↦ 55    cTy ↦ 43
    Formula.renameF ↦ 36 Derivable.rec ↦ 27    Derivable.castAllowed ↦ 18
    Formula.weakenBy ↦ 18  SRealizer ↦ 9       syntactic_soundness ↦ 9
    SRealizer.imp ↦ 7

**What this actually says.** `whnf` *is* inside `syntactic_soundness`'s recursion — and it has
managed **9 unfoldings of it, 27 of `Derivable.rec`**, before exhausting the entire
200,000-heartbeat budget. So the stall is not "before the translation" and not "at the
translation"; it is an enormous **per-derivation-node** cost: roughly 700 `Eq.rec` and 215
`Term.rename` for each single step of the soundness recursion. The derivation is walked at
about nine nodes per full heartbeat budget.

**`Derivable.castAllowed ↦ 18` is classicality-specific** — it is step 4 of
`classical_to_prenex_extended`, the `Allowed.classical → Allowed.extended` cast, and it
rebuilds the derivation as it goes. So the claim this file previously made, that the classical
route carries *no* classicality-specific cost, is **not supported**; that machinery is in the
profile.

**The shared-blocker guess is REFUTED, by the obvious discriminating test.** The top-three
signature does resemble the Stage-B stall of CLAUDE.md's Track A item 1
(`Eq.rec ↦ 60474`, `Term.rec ↦ 10847`, `Term.rename ↦ 10504`), and this file briefly argued
from that resemblance that one fix would unblock both. But `Eq.rec` is generic — essentially
every dependent reduction routes through it — so a shared profile is weak evidence of a
shared cause. The test that separates them is **sidedness**:

- The intuitionistic stall is **one-sided**. `ConjBoundDemo.cVtTwice_at_5_9` evaluates the
  *witness* functional `V` of the stalling two-instantiation derivation to a literal `1709`;
  only the counter side sticks. `SeqMpBoundProbe`'s three commutation lemmas are likewise
  witness-path only, and its header says so explicitly: the counter components "were not
  touched, and that is exactly where the duplication lives".
- The classical stall is **two-sided**. `(5 : Nat) = closedMajorizer lCmE lVtNoLem 5` — the
  *witness* side, LEM-free — is also a `whnf` timeout.

So the classical route costs something the counter-side debt does not explain, and paying that
debt should not be expected to unblock it. `Derivable.castAllowed ↦ 18` in the profile is a
concrete candidate for the difference, since it rebuilds the whole derivation; that is a
hypothesis and has not been tested.

The type level is **not** the explanation, and that part was checked: `tySize (wTy stmt) = 19`
against `tySize (wTy pstmt') = 93`, `cTy` 7 against 39 — a factor of ≈5, nothing.

**And note what has NOT been tried here: the technique that actually works.** A bare `rfl` is
not how this project has ever extracted a numeral from a large term. `seq_mp_11_numeral`
(`Probes/SeqMpBoundProbe.lean`) produces a kernel-checked literal from a term measured at
≈7×10¹² nodes at context depth 11 — via a **simp set of commutation lemmas**, so the term is
never materialized at all. Everything above is evidence about `rfl`, and `rfl` is known to be
the wrong instrument at this scale. Before drawing any conclusion about feasibility here, run
the simp route.

## Reproduction

The stalling theorems are necessarily not in this file. Paste into a scratch file importing
this one to re-run either half:

    set_option diagnostics true in
    set_option diagnostics.threshold 500 in
    theorem probeU : (0 : Nat) = closedMajorizer lCmE lUtNoLem (5 : Nat) := by rfl
-/

namespace Metatheorems
namespace LemBoundDemo

open Formula

-- ============================================================================
-- The `ι = Empty` model — same recipe as `TinyBoundDemo`, distinct names
-- ============================================================================

/-- The carrier family for pure `WE-HA^ω`: no base types. -/
def lXE : Empty → Type := fun i => i.elim
/-- The function-constant signature for pure `WE-HA^ω`: none. -/
def lFE : Empty → Ty Empty := fun i => i.elim

def lSiE : SpaceInterp lXE lFE where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

def lEqxiE : EqXInterp lXE lFE lSiE where
  realize             := fun i => i.elim
  extract             := fun i => i.elim
  dist_comm_holds     := fun i => i.elim
  dist_tri_holds      := fun i => i.elim

/-- No premises, so the premise realizer is vacuous. -/
def lPremE : PremiseSet lFE := fun _ => False

def lSpremiseE : ∀ (Γ' : Ctx Empty) (B : Formula lFE Γ'), lPremE ⟨Γ', B⟩ → SRealizer lSiE B :=
  fun _ _ h => h.elim

/-- NT-stability, vacuous for the same reason: the classical route needs every premise to
imply its own negative translation, and there are no premises. -/
def lNts : NTStableD lPremE := fun _ _ h => h.elim

-- ============================================================================
-- The statement
-- ============================================================================

/-- `B₀ := u =₀ u`, in context `[u:nat, x:nat]`. -/
def lB0 : Formula lFE [Ty.nat, Ty.nat] := Formula.eq0 (.var .vz) (.var .vz)

/-- `C₀ := v =₀ x`, in context `[v:nat, x:nat]`. -/
def lC0 : Formula lFE [Ty.nat, Ty.nat] := Formula.eq0 (.var .vz) (.var (.vs .vz))

theorem lB0_qf : lB0.isQF = true := rfl
theorem lB0_vf : lB0.isVFree = true := rfl
theorem lC0_qf : lC0.isQF = true := rfl
theorem lC0_vf : lC0.isVFree = true := rfl

/-- The Π₁ premise `∀u B₀`, in context `[x:nat]`. **This is the formula the LEM is taken at**,
and it is where the whole interest of the file sits: it is not quantifier-free, so
`qf_lem` does not apply to it and `Derivable.lem` is genuinely invoked. -/
abbrev lA : Formula lFE [Ty.nat] := Formula.all Ty.nat lB0

/-- The conclusion `∃v C₀`, in context `[x:nat]`. -/
abbrev lE : Formula lFE [Ty.nat] := Formula.ex Ty.nat lC0

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def lDummyOuter : Formula lFE ([] : Ctx Empty) := Formula.eq0 Term.zero Term.zero

-- ============================================================================
-- The shared, LEM-free core
-- ============================================================================

/-- `∃v C₀` is derivable unconditionally in context `[x:nat]`: instantiate `v := x` and the
matrix becomes `x =₀ x`.

**Generic in `al`** — it uses only structural constructors. That genericity is what makes the
control below exact: one derivation *term*, run at `Allowed.extended` and at
`Allowed.classical`, so the two routes are compared on literally the same proof. -/
def lExD {al : Allowed} : @Derivable Empty Empty lFE al lPremE [Ty.nat] lE :=
  Derivable.mp Derivable.refl0 (Derivable.exist_ax (Term.var Var.vz) lC0)

/-- `(∀u B₀) →ᶠ (∃v C₀)`, the premise simply never used. This is the LEM-free proof. -/
def lInner {al : Allowed} : @Derivable Empty Empty lFE al lPremE [Ty.nat] (lA →ᶠ lE) :=
  Derivable.mp lExD (Derivable.exportation Derivable.and_weak)

-- ============================================================================
-- The LEM step
-- ============================================================================

/-- **The excluded middle instance.** `Derivable.lem` is guarded by `allowed.lem = true`,
which `Allowed.classical` supplies and `Allowed.extended` does not — so this declaration is
the reason everything below must route through the *classical* metatheorem.

Note the formula: `lA` is `∀u (u =₀ u)`, a Π₁ formula. `Arithmetic.qf_lem` would give this
for free if `lA` were quantifier-free; it is not. -/
def lLem : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] (lA ∨ᶠ ¬ᶠlA) :=
  Derivable.lem rfl

/-- Left case: given `∀u B₀`, prove `∀u B₀ → ∃v C₀`. The K-combinator applied to `lInner`. -/
def lCaseL : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat]
    (lA →ᶠ (lA →ᶠ lE)) :=
  Derivable.mp lInner (Derivable.exportation Derivable.and_weak)

/-- Right case: given `¬(∀u B₀)`, prove `∀u B₀ → ∃v C₀` — by ex falso.

`¬ᶠlA` **is** `lA →ᶠ ⊥ᶠ` by definition of `Formula.neg`, so `I_comb` at `¬ᶠlA` already has
the shape `¬ᶠlA →ᶠ lA →ᶠ ⊥ᶠ`; `importation` turns it into `¬ᶠlA ∧ᶠ lA →ᶠ ⊥ᶠ`, `exfalso`
lands anywhere, and `exportation` restores the curried form. -/
def lCaseR : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat]
    (¬ᶠlA →ᶠ (lA →ᶠ lE)) :=
  Derivable.exportation
    (Derivable.syllogism (Derivable.importation (I_comb (A := ¬ᶠlA))) Derivable.exfalso)

/-- The classical proof of the inner implication: case-split on `lA ∨ ¬lA`. -/
def lInnerLem : @Derivable Empty Empty lFE Allowed.classical lPremE [Ty.nat] (lA →ᶠ lE) :=
  Derivable.mp lLem (or_elim_rule lCaseL lCaseR)

-- ============================================================================
-- The two final derivations of the SAME formula
-- ============================================================================

/-- Weaken by the dummy premise so `forall_rule` can generalize over `x`. Generic in `al`. -/
private def close {al : Allowed}
    (d : @Derivable Empty Empty lFE al lPremE [Ty.nat] (lA →ᶠ lE)) :
    @Derivable Empty Empty lFE al lPremE []
      (Formula.all Ty.nat (Formula.all Ty.nat lB0 →ᶠ Formula.ex Ty.nat lC0)) :=
  let weakened : @Derivable Empty Empty lFE al lPremE [Ty.nat]
      (Formula.weakenBy Ty.nat lDummyOuter →ᶠ (lA →ᶠ lE)) :=
    Derivable.mp d (Derivable.exportation Derivable.and_weak)
  Derivable.mp (Derivable.refl0 (t := Term.zero)) (Derivable.forall_rule weakened)

/-- **The control**: the LEM-free derivation at `Allowed.extended`, i.e. through the
*intuitionistic* metatheorem. -/
def lFinalExt : @Derivable Empty Empty lFE Allowed.extended lPremE []
    (Formula.all Ty.nat (Formula.all Ty.nat lB0 →ᶠ Formula.ex Ty.nat lC0)) :=
  close lInner

/-- The very same derivation term at `Allowed.classical`, i.e. through the *classical*
metatheorem. `lFinalExt` and this differ in **nothing but the `Allowed` value**. -/
def lFinalNoLem : @Derivable Empty Empty lFE Allowed.classical lPremE []
    (Formula.all Ty.nat (Formula.all Ty.nat lB0 →ᶠ Formula.ex Ty.nat lC0)) :=
  close lInner

/-- **The derivation that uses excluded middle.** Same formula as the other two. -/
def lFinalLem : @Derivable Empty Empty lFE Allowed.classical lPremE []
    (Formula.all Ty.nat (Formula.all Ty.nat lB0 →ᶠ Formula.ex Ty.nat lC0)) :=
  close lInnerLem

-- ============================================================================
-- Through the CLASSICAL metatheorem
-- ============================================================================

/-- The constant majorants at `ι = Empty`. -/
def lCmE := bezemConstMajorantsEmpty lSiE

/-- The classical metatheorem, applied to the LEM-using derivation. The bound is a `Subtype`,
so `Φ` is data — this is `syntactic_general_metatheorem_classical_at`'s first client. -/
def lemBound :
    { Φ : Ty.interpret lXE Ty.nat.hat → Nat //
      ∀ (x : Ty.interpret lXE Ty.nat) (x_star : Ty.interpret lXE Ty.nat.hat),
        (bezemAbstractEmpty lSiE).toRel.maj Ty.nat x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret lSiE lB0 (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret lSiE lC0 (v, (x, ())) } :=
  syntactic_general_metatheorem_classical_at lEqxiE lNts lSpremiseE lCmE
    lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem

-- ============================================================================
-- The extracted functionals, as closed terms
-- ============================================================================

/-- `U` for the LEM-using proof. -/
def lUtLem : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedUTermP lEqxiE lNts lSpremiseE lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem

/-- `V` for the LEM-using proof. -/
def lVtLem : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedVTermP lEqxiE lNts lSpremiseE lB0_qf lB0_vf lC0_qf lC0_vf lFinalLem

/-- `U` for the LEM-free proof, through the same classical pipeline. -/
def lUtNoLem : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedUTermP lEqxiE lNts lSpremiseE lB0_qf lB0_vf lC0_qf lC0_vf lFinalNoLem

/-- `V` for the LEM-free proof, through the same classical pipeline. -/
def lVtNoLem : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedVTermP lEqxiE lNts lSpremiseE lB0_qf lB0_vf lC0_qf lC0_vf lFinalNoLem

-- ============================================================================
-- The control: the SAME derivation term through the INTUITIONISTIC route
-- ============================================================================

/-- `U` for the control — the same derivation, at `Allowed.extended`. -/
def lUtExt : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedUTerm lEqxiE lSpremiseE lFinalExt

/-- `V` for the control. -/
def lVtExt : Term lFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractedVTerm lEqxiE lSpremiseE lFinalExt

/-- The control's `U`-majorant at `5`, a kernel-checked literal. `B₀ := u =₀ u` never consults
`x`, so the premise need not be tested anywhere: `0`. -/
theorem lUtExt_at_5 : (0 : ℕ) = closedMajorizer lCmE lUtExt (5 : ℕ) := by rfl

/-- The control's `V`-majorant at `5`: `C₀ := v =₀ x` forces `v = x`, so `V` is the identity. -/
theorem lVtExt_at_5 : (5 : ℕ) = closedMajorizer lCmE lVtExt (5 : ℕ) := by rfl

/-- Non-degeneracy: the `rfl`s above really do reduce, rather than both sides sticking at a
common unreduced point. Claiming `4` is *refutable*, by `decide`. -/
theorem lVtExt_at_5_ne_4 : ¬ ((4 : ℕ) = closedMajorizer lCmE lVtExt (5 : ℕ)) := by decide

/-- A local term-size measure, for sizing a realizer *before* asking the kernel to reduce it.
Never run this on anything MCT-sized; see `Probes/BoundProbe.lean`. -/
def lTermSize {Γ : Ctx Empty} {τ : Ty Empty} : Term lFE Γ τ → Nat
  | .var _      => 1
  | .app f a    => 1 + lTermSize f + lTermSize a
  | .lam b      => 1 + lTermSize b
  | .zero       => 1
  | .succ       => 1
  | .prec _     => 1
  | .func _     => 1
  | .zeroX _    => 1
  | .dist _     => 1
  | .unitI      => 1
  | .mkPair a b => 1 + lTermSize a + lTermSize b
  | .fst p      => 1 + lTermSize p
  | .snd p      => 1 + lTermSize p

/-! ## Hygiene

Added 2026-09-07 (`docs/CLAIMS_AUDIT.md` C11). This file had no `#print axioms`, so the axiom
lists quoted for its numerals were prose rather than build output. It already carries its own
refutation control (`lVtExt_at_5_ne_4`).

Only the *extended* pair is checkable: the classical extractors do not reduce at all, which is
this probe's finding, so there is nothing to print for them. -/

#print axioms lUtExt_at_5
#print axioms lVtExt_at_5
#print axioms lVtExt_at_5_ne_4

end LemBoundDemo
end Metatheorems
