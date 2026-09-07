/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Monotone

/-!
# The `Eq.mpr` entry for the monotone functional interpretation

The normalising proof-mode tactics (`anorm`/`canorm`/`qfer_*_nf`) rewrite the *goal formula*
of a `SeqD`/`Derivable` goal and leave a Lean-level cast — `Eq.mpr`, `Eq.mp`, or `h ▸`
(`Eq.rec`) — in the derivation term (see `Probes/CombinatorLemmas.lean`'s `Eq.mpr` paragraph
and `syntactic_soundness_eqmpr`). To reduce `monotone_soundness … (Eq.mpr h d)` the kernel
must bring `Eq.mpr h d` to a constructor, i.e. decide `Derivable … B ≡ Derivable … B'`, i.e.
`B ≡ B'` — which runs `Term.subst` through the ℚ constants (the delta-expansion pathology of
CLAUDE.md's "Build cost"). On the ℝ lemmas that is a kernel `std::bad_alloc` at 12 GB
(measured in `Probes/MonotoneLaneB.lean`).

`MRealizer.transport` and the three commutation lemmas here are the MFI analogue of
`syntactic_soundness_eqmpr`: applied as rewrite rules **with the formula equation given**, they
turn `monotone_soundness … (Eq.mpr h d)` into `MRealizer.transport h' (monotone_soundness … d)`,
so the cast is rewritten away and **never reduced**.

## Why the transport is cheap

`MRealizer cm A`'s **data** — the majorant `tstar` — lives at `Ty.interpret X (wTy A).hat`, and
`wTy` depends only on a formula's logical skeleton, never on its terms. The casts these tactics
leave differ in the *terms* of a formula (a `subst`/`rename` normalisation), not the skeleton,
so `wTy B ≡ wTy B'` **structurally**, cheaply, without touching `cauchyfy`/`le_Q_dec`. Hence the
data cast is `congrArg wTy h` composed with `Ty.interpret X ·.hat` — its two type sides are
definitionally equal and the kernel collapses it, exactly as `Term.castTy (congrArg wTy …)`
collapses on the term route. The **Prop** component is transported by `subst h` (proof
irrelevance).

**Reach.** These lemmas fire only where `monotone_soundness` is applied *directly* to a cast.
On a proof-mode-written derivation the casts are buried under the `pm_*`/`seq_*` layer, so
reaching them needs the MRealizer analogues of `Probes/CombinatorLemmas.lean`'s `wit_seq_*` —
that is what `Dialectica/MonotoneSeq.lean` supplies. See `Probes/MonotoneLaneBp.lean` for what
this entry does and does not reach on its own, with measurements.
-/

namespace Metatheorems

open Formula

section Memo

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {Premises : PremiseSet F}

/-- **Transport a monotone realizer along a formula equation.** The data component `tstar`
is cast by `congrArg wTy h`, whose two type sides `Ty.interpret X (wTy B).hat` /
`Ty.interpret X (wTy B').hat` are definitionally equal whenever `B`, `B'` share their logical
skeleton — which is exactly the case for a `subst`/`rename` normalisation — so the cast
collapses in the kernel with no ℚ delta. The `Prop` component is transported by `subst h`
(proof irrelevance). -/
def MRealizer.transport {cm : ConstMajorants am} {Γ : Ctx ι} {B B' : Formula F Γ}
    (h : B = B') (r : MRealizer cm B) : MRealizer cm B' :=
  ⟨fun n e => cast (congrArg (fun ρ : Ty ι => Ty.interpret X ρ.hat) (congrArg wTy h)) (r.val n e),
   by subst h; exact r.property⟩

/-- `transport rfl` is the identity (definitionally — the cast is `cast rfl`). Recorded so a
`simp` set can normalise a residual `transport rfl`. -/
@[simp] theorem MRealizer.transport_rfl {cm : ConstMajorants am} {Γ : Ctx ι} {B : Formula F Γ}
    (r : MRealizer cm B) : MRealizer.transport (rfl : B = B) r = r := rfl

variable (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am)

/-- **The `Eq.mpr` entry** — `anorm`/`canorm`/`prw_norm` leave this. Given the formula equation
`hB`, `monotone_soundness` of the cast is `transport` of the sub-realizer; the cast is rewritten
away, never reduced. Mirror of `syntactic_soundness_eqmpr`. -/
theorem monotone_soundness_eqmpr {Γ : Ctx ι} {B B' : Formula F Γ} (hB : B = B')
    (e' : Derivable F Allowed.extended Premises B = Derivable F Allowed.extended Premises B')
    (d : Derivable F Allowed.extended Premises B') :
    monotone_soundness eqxi spremise cm (Eq.mpr e' d)
      = MRealizer.transport hB.symm (monotone_soundness eqxi spremise cm d) := by
  subst hB; rfl

/-- The `Eq.mp` entry — the direction `forall_ax_vz`/`qfer_at_nf`/`qfer_nat_nf` produce. -/
theorem monotone_soundness_eqmp {Γ : Ctx ι} {B B' : Formula F Γ} (hB : B = B')
    (e' : Derivable F Allowed.extended Premises B = Derivable F Allowed.extended Premises B')
    (d : Derivable F Allowed.extended Premises B) :
    monotone_soundness eqxi spremise cm (Eq.mp e' d)
      = MRealizer.transport hB (monotone_soundness eqxi spremise cm d) := by
  subst hB; rfl

/-- The `h ▸ d` entry — the `Eq.rec` `seq_cast` (hence `seq_induction`) produces. -/
theorem monotone_soundness_subst {Γ : Ctx ι} {B B' : Formula F Γ} (hB : B = B')
    (d : Derivable F Allowed.extended Premises B) :
    monotone_soundness eqxi spremise cm (hB ▸ d)
      = MRealizer.transport hB (monotone_soundness eqxi spremise cm d) := by
  subst hB; rfl

end Memo

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms MRealizer.transport
#print axioms monotone_soundness_eqmpr
#print axioms monotone_soundness_eqmp
#print axioms monotone_soundness_subst

end Metatheorems
