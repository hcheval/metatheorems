/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Majorizability

/-!
# Demo: a genuinely tiny derivation, all the way to a kernel-checked numeral bound

`Probes/BoundProbe.lean` measured that the realizer `syntactic_soundness` produces for
`ProofMode.mct_p2` (36 `Derivable` constructors via a proof-mode script) is too large to
`#eval`, even at `ι = Empty`. This file asks the natural follow-up: is *any* derivation small
enough to carry through the WHOLE pipeline — `syntactic_soundness` → `extractUTerm`/
`extractVTerm` → `closedMajorizer` (with `bezemConstMajorantsEmpty`) — to a literal,
kernel-checked numeral, closed by `rfl`/`simp`, not `#eval`?

## The statement

At `ι = Empty`, `ρ := Ty.nat`:

    ∀x:nat (∀u:nat (u = u) → ∃v:nat (v = x))

i.e. `B₀ := (u =₀ u)` and `C₀ := (v =₀ x)`. Mathematically this is about as degenerate as a
statement of the metatheorem's shape can be — `B₀` doesn't even depend on `x`, and the
witness for `C₀` is just `x` itself — but it is genuinely of shape `∀x(∀u B₀ → ∃v C₀)`, `B₀`
and `C₀` are both QF and ∨-free (`Formula.eq0` is atomic, so `isQF`/`isVFree` are `rfl`), and
the derivation below is built from raw `Derivable` constructors, not the proof mode.

## The derivation, by hand

The trick throughout is `weaken_intro_h`'s pattern (private in `PureFOLLemmas.lean`, so
reproduced inline as `Derivable.mp _ (Derivable.exportation Derivable.and_weak)`): from
`h : Derivable A`, get `Derivable (B →ᶠ A)` for *any* `B`, since `A` doesn't need `B`'s
hypothesis at all.

1. `Formula.ex Ty.nat C₀` is derivable unconditionally in context `[nat]` (i.e. with `x`
   free): `exist_ax (var vz) C₀` gives `(C₀.subst0 (var vz) →ᶠ ex nat C₀)`, and
   `C₀.subst0 (var vz)` — substituting `x` for `v` — is exactly `x =₀ x`, i.e. `refl0`.
2. Weaken that into `(∀u B₀) →ᶠ (∃v C₀)` — the antecedent is simply never used.
3. Weaken again into `(dummy) →ᶠ ((∀u B₀) →ᶠ (∃v C₀))` so `forall_rule` can generalize over
   `x` from an unconditional dummy premise `0 =₀ 0`.
4. `forall_rule` then `mp` with `refl0 : Derivable (0 =₀ 0)` closes it.

Twelve raw `Derivable` constructors total: `mp`×4, `exportation`×2, `and_weak`×2, `refl0`×2,
`exist_ax`×1, `forall_rule`×1.
-/

namespace Metatheorems
namespace TinyBoundDemo

open Formula

-- ============================================================================
-- The `ι = Empty` model — same recipe as `BoundProbe`, distinct names to avoid any
-- cross-lane collision (this file does not import `BoundProbe.lean`).
-- ============================================================================

/-- The carrier family for pure `WE-HA^ω`: no base types. -/
def tXE : Empty → Type := fun i => i.elim
/-- The function-constant signature for pure `WE-HA^ω`: none. -/
def tFE : Empty → Ty Empty := fun i => i.elim

def tSiE : SpaceInterp tXE tFE where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

def tEqxiE : EqXInterp tXE tFE tSiE where
  realize             := fun i => i.elim
  extract             := fun i => i.elim
  dist_comm_holds     := fun i => i.elim
  dist_tri_holds      := fun i => i.elim

/-- No premises, so the premise realizer is vacuous. -/
def tPremE : PremiseSet tFE := fun _ => False

def tSpremiseE : ∀ (Γ' : Ctx Empty) (B : Formula tFE Γ'), tPremE ⟨Γ', B⟩ → SRealizer tSiE B :=
  fun _ _ h => h.elim

-- ============================================================================
-- The statement: ∀x:nat (∀u:nat (u = u) → ∃v:nat (v = x))
-- ============================================================================

/-- `B₀ := u =₀ u`, in context `[u:nat, x:nat]`. Doesn't depend on `x` at all. -/
def tB0 : Formula tFE [Ty.nat, Ty.nat] := Formula.eq0 (.var .vz) (.var .vz)

/-- `C₀ := v =₀ x`, in context `[v:nat, x:nat]`. -/
def tC0 : Formula tFE [Ty.nat, Ty.nat] := Formula.eq0 (.var .vz) (.var (.vs .vz))

theorem tB0_qf : tB0.isQF = true := rfl
theorem tB0_vf : tB0.isVFree = true := rfl
theorem tC0_qf : tC0.isQF = true := rfl
theorem tC0_vf : tC0.isVFree = true := rfl

/-- The unconditional dummy premise `0 =₀ 0`, used only to feed `forall_rule`. -/
def tDummyOuter : Formula tFE ([] : Ctx Empty) := Formula.eq0 Term.zero Term.zero

-- ============================================================================
-- The derivation, by hand, raw `Derivable` constructors only
-- ============================================================================

/-- Step 1: `∃v C₀` is derivable unconditionally in context `[x:nat]`. -/
def tExDerivation :
    @Derivable Empty Empty tFE Allowed.extended tPremE [Ty.nat] (Formula.ex Ty.nat tC0) :=
  Derivable.mp Derivable.refl0 (Derivable.exist_ax (Term.var Var.vz) tC0)

/-- Step 2: weaken into `(∀u B₀) →ᶠ (∃v C₀)`, in context `[x:nat]`. -/
def tInner :
    @Derivable Empty Empty tFE Allowed.extended tPremE [Ty.nat]
      (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0) :=
  Derivable.mp tExDerivation (Derivable.exportation Derivable.and_weak)

/-- Step 3: weaken again by the dummy premise, so `forall_rule` can fire. -/
def tInnerWeakened :
    @Derivable Empty Empty tFE Allowed.extended tPremE [Ty.nat]
      (Formula.weakenBy Ty.nat tDummyOuter →ᶠ
        (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) :=
  Derivable.mp tInner (Derivable.exportation Derivable.and_weak)

/-- Step 4: `forall_rule`, then discharge the dummy premise with `refl0`.

The final shape is exactly `Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat
C₀))` with `ρ := Ty.nat` — what `syntactic_general_metatheorem` expects. -/
def tFinal :
    @Derivable Empty Empty tFE Allowed.extended tPremE []
      (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule tInnerWeakened)

-- ============================================================================
-- Through the metatheorem
-- ============================================================================

/-- The bound extraction theorem, applied to `tFinal`. Purely a sanity check that everything
above really does have the shape the metatheorem wants; not used for the numeral computation
below (that goes through the pipeline pieces directly, to name the intermediate closed terms). -/
theorem tinyBound :
    ∃ Φ : Ty.interpret tXE Ty.nat.hat → Nat,
      ∀ (x : Ty.interpret tXE Ty.nat) (x_star : Ty.interpret tXE Ty.nat.hat),
        (bezemAbstractEmpty tSiE).toRel.maj Ty.nat x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret tSiE tB0 (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret tSiE tC0 (v, (x, ())) :=
  syntactic_general_metatheorem tEqxiE tSpremiseE (bezemAbstractEmpty tSiE)
    tB0_qf tB0_vf tC0_qf tC0_vf tFinal

-- ============================================================================
-- The realizer and the two extracted functionals, as closed terms
-- ============================================================================

/-- The syntactic realizer of `tFinal`. Per `BoundProbe`'s finding, this `def` elaborates and
type-checks instantly — the cost is specific to forcing full evaluation, not to naming it. -/
def tRealizer : SRealizer tSiE
    (Formula.all Ty.nat (Formula.all Ty.nat tB0 →ᶠ Formula.ex Ty.nat tC0)) :=
  syntactic_soundness tEqxiE tSpremiseE tFinal

/-- The extracted `U` functional, as a closed `Term`. -/
def tUt : Term tFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractUTerm (ρ := Ty.nat) (B₀ := tB0) (C₀ := tC0) tRealizer.val

/-- The extracted `V` functional, as a closed `Term`. -/
def tVt : Term tFE ([] : Ctx Empty) (Ty.nat →ₜ Ty.nat) :=
  extractVTerm (ρ := Ty.nat) (B₀ := tB0) (C₀ := tC0) tRealizer.val

-- ============================================================================
-- The majorant, as data — and the literal numeral, kernel-checked
-- ============================================================================

/-- The constant majorants at `ι = Empty` (`bezemConstMajorantsEmpty`), instantiated at
`tSiE`. This is what makes `closedMajorizer` compute at all. -/
def tCmE := bezemConstMajorantsEmpty tSiE

/-- **The point of the file.** `U`'s majorant, evaluated at the closed input `5`, is the
literal numeral `0` — kernel-checked by `rfl`, no `#eval` anywhere in this statement or its
proof. `U` majorizes the bound on `u` that the premise `∀u B₀` must be checked up to; since
`B₀ := u =₀ u` never actually uses `x`, that bound is uniformly `0`.

Measured: `termSize tRealizer.val = 292`, `termSize tUt = 302` (a capped, `ulimit`-wrapped
`#eval` of `TinyBoundDemo.termSize`, done only to size the term *before* attempting this
`rfl` — never on anything MCT-sized). At that size bare `rfl` returns in a few seconds with no
memory cap needed at all; the safety wrapping below is precautionary, not because this
particular `rfl` is known to be expensive. -/
theorem tUt_bound_at_5 : (0 : ℕ) = closedMajorizer tCmE tUt (5 : ℕ) := by rfl

/-- `V`'s majorant, evaluated at `5`, is `5`: `C₀ := v =₀ x` forces `v = x`, so the majorant
of `V` is (extensionally) the identity, and `closedMajorizer` computes it exactly. Also
kernel-checked by `rfl`. -/
theorem tVt_bound_at_5 : (5 : ℕ) = closedMajorizer tCmE tVt (5 : ℕ) := by rfl

/-!
### Where the pipeline stops scaling — measured, not `#eval`-ed blind

The two `rfl`s above go through on the 12-constructor derivation `tFinal` with no trouble at
all — the realizer is 292 nodes, nowhere near the pathology `BoundProbe.lean` found for
`mct_p2`. The natural follow-up is: how much bigger can the derivation get before this stops
working? A `ulimit`-capped `#eval` of `TinyBoundDemo.termSize` on a version of the pipeline
padded with `n` extra no-op derivation layers (each layer: `Derivable.syllogism I_comb`,
i.e. 4 raw constructors — `syllogism` plus `I_comb`'s own `syllogism`+`and_contract`+
`and_weak` — composed onto `tInner` before the rest of the pipeline runs unchanged) gives:

| padding layers (×4 constructors) | extracted `U` term size |
|---|---|
| 0 (this file's `tUt`) | 302 |
| 1  | 2,297 |
| 2  | 6,287 |
| 3  | 14,267 |
| 4  | 30,227 |
| 5  | 62,147 |
| 8  | 509,027 |
| 10 | 2,041,187 |
| 12 | 8,169,827 |
| 20 | `INTERNAL PANIC: out of memory` (capped at 16 GB virtual, `ulimit -v 16000000`) |

**The growth is roughly ×2 per padding layer** (4 raw `Derivable` constructors), not linear —
each `syllogism I_comb` composition duplicates the realizer built so far, the same
no-sharing pathology CLAUDE.md's "Build cost" section documents for `Term.subst` on
`Term.add_Q`, one layer up on *proof* terms rather than *interpretations*
(`BoundProbe.lean` already noted this is the same family of blow-up). Extrapolating the
measured ×2/layer rate: 20 layers (80 extra constructors, ~92 raw constructors total) lands
around 2×10⁹ nodes, consistent with the observed OOM at a 16 GB cap.

**So the concrete calibration for this pipeline, at `ι = Empty`, on a derivation of this
particular shape:** a derivation with realizer size in the low hundreds of nodes (this file's
12-constructor `tFinal`) sails through `rfl` in seconds; by ~12 padding layers (realizer
~8×10⁶ nodes) a plain `#eval` of `termSize` alone already takes real memory, and a
`syllogism`/`I_comb`-shaped derivation becomes infeasible somewhere around 15–20 extra
layers. This is a *much* smaller derivation than `mct_p2`'s proof-mode script (which does not
even survive `#eval termSize` at all, per `BoundProbe.lean`), so the practical ceiling for
this pipeline sits well below "the size of an interesting metatheorem instance" and squarely
in "small enough to hand-derive with raw constructors, one screen of code" — exactly the
territory this file's `tFinal` occupies. Note also that the growth measured here is an
artifact of the *particular* padding construction (naive `syllogism`-composition duplicates
its argument); a derivation of the same raw constructor count built with more sharing (e.g.
reusing a `let`-bound sub-derivation via `obtain`, per CLAUDE.md rule 4) would likely scale
very differently — this measures one specific failure mode, not a universal bound on
constructor count. -/

end TinyBoundDemo
end Metatheorems
