/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.MCT
import Metatheorems.Majorizability
import Metatheorems.Probes.BoundProbe

/-!
# Probe: can `termMajorizer` be pushed through `mct_p2` COMPOSITIONALLY?

`Probes/BoundProbe.lean` established that a naive `#eval` of `syntactic_soundness`'s output on
`mct_p2` (even the RAW realizer, before any extraction wrapping) exhausts 8-10 GB — the cost is
inside `syntactic_soundness`'s structural recursion, not in `extractUTerm`'s wrapping.

This file asks the follow-up question `BoundProbe.lean` posed at its end: is there a
COMPOSITIONAL route — named equation lemmas, each unfolding a small bounded amount, citing
sub-lemmas rather than re-deriving — that gets a kernel-checked numeral anyway, the way
`QValBridge.lean` does for `Term.interpret` of the ℚ layer?

## The key structural fact this file is built on

Every `SRealizer` combinator in `Dialectica/Syntactic.lean` (`sMP`, `sSyllogism`, `sInduction`,
`sForallAx`, `sUnivGen`, …) builds its `.val` (the realizing `Term`) **compositionally**: by
`.app`/`.fst`/`.snd`/`.mkPair`/`.lam`/`Term.weaken`/`Term.castTy` wrapping of the sub-realizers'
`.val` fields, **never** by unfolding what those sub-`.val`s actually are. And
`syntactic_soundness` itself (Syntactic.lean:1098) is *exactly* `sXYZ (recursive calls)` per
`Derivable` constructor — no additional wrapping.

So in principle `termMajorizer` (Majorizability.lean, which recurses on `Term`'s constructors
directly: `var, app, lam, zero, succ, prec, func, zeroX, dist, unitI, mkPair, fst, snd`) should
be able to walk straight through `syntactic_soundness (mct_p2 ...)` and stop at *leaves* —
`cm.zeroM`, `cm.succM`, `cm.precM`, `Ctx.lookupHat` — without ever needing to fully reduce a
`Term.weaken`/`Term.castTy` chain to expose its constructors. The one thing missing to make that
literal was a lemma saying `termMajorizer` commutes with `Term.weaken`/`Term.castTy` — nothing
of that shape existed before this file, because `ConstMajorants`/`termMajorizer` are new today.

That lemma (`termMajorizer_weaken` below) is a **generic, one-time, structural-induction proof**
— the same shape as `Term.interpret_weaken` (`Semantics.lean:172`), which already exists for
`Term.interpret` and this file is the `termMajorizer` analogue of. It costs nothing per
use-site; every combinator gets it for free via `simp`.

NOT imported by `Metatheorems.lean`, per the `Probes/` convention.
-/

namespace Metatheorems
namespace BoundLemmasP2

-- ============================================================================
-- Part 1: the enabling lemmas — termMajorizer commutes with weaken/castTy
-- ============================================================================

section Enabling

variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

/-- General form, mirroring `Term.interpret_rename_gen` (`Semantics.lean:145`) exactly:
`termMajorizer` commutes with any renaming whose `env_star`s agree on `Ctx.lookupHat`. -/
theorem termMajorizer_rename_gen (cm : ConstMajorants am) :
    ∀ {Γ Δ : Ctx ι} {ρ : Ty ι} (r : Term.Renaming Γ Δ) (t : Term F Γ ρ) (n : ℕ)
    (env_starΔ : Ctx.interpret X (Δ.map Ty.hat)) (env_starΓ : Ctx.interpret X (Γ.map Ty.hat)),
    (∀ {σ} (v : Var Γ σ), Ctx.lookupHat (r v) env_starΔ = Ctx.lookupHat v env_starΓ) →
    termMajorizer cm (t.rename r) n env_starΔ = termMajorizer cm t n env_starΓ := by
  intro Γ Δ ρ r t
  induction t generalizing Δ with
  | var v => intro n env_starΔ env_starΓ h; exact h v
  | app f a ihf iha =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ihf r n env_starΔ env_starΓ h,
      iha r n env_starΔ env_starΓ h]
  | lam body ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer]
    funext x
    exact ih (Term.Renaming.ext r) n (x, env_starΔ) (x, env_starΓ) (fun v => by
      cases v with
      | vz => rfl
      | vs w => exact h w)
  | zero | succ | prec | func | zeroX | dist | unitI => intros; rfl
  | mkPair a b iha ihb =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, iha r n env_starΔ env_starΓ h,
      ihb r n env_starΔ env_starΓ h]
  | fst p ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ih r n env_starΔ env_starΓ h]
  | snd p ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ih r n env_starΔ env_starΓ h]

/-- **The enabling lemma.** `termMajorizer` commutes with `Term.weaken` — an `O(1)` fact per
use-site, never requiring `Term.weaken` to be reduced to expose its constructors. This is what
makes every `SRealizer` combinator (`sSyllogism`, `sInduction`, `sForallAx`, `sUnivGen`, …)
transparent to `termMajorizer`: their `.val` fields are built from `Term.weaken`-wrapping of
sub-realizers, and this lemma lets `simp` push straight through that wrapping to the
sub-realizer's own `termMajorizer`, instead of forcing the wrapped term to whnf. -/
@[simp] theorem termMajorizer_weaken (cm : ConstMajorants am) {Γ : Ctx ι} {ρ σ : Ty ι}
    (t : Term F Γ ρ) (n : ℕ) (x_star : Ty.interpret X σ.hat)
    (env_star : Ctx.interpret X (Γ.map Ty.hat)) :
    termMajorizer cm (Term.weaken t (σ := σ)) n (x_star, env_star)
      = termMajorizer cm t n env_star :=
  termMajorizer_rename_gen cm Term.Renaming.shift t n (x_star, env_star) env_star (fun _ => rfl)

/-- `termMajorizer` commutes with `Term.castTy` — trivial, since `castTy` is a bare `cast` at
matching-on-the-nose types. -/
@[simp] theorem termMajorizer_castTy (cm : ConstMajorants am) {Γ : Ctx ι} {ρ τ : Ty ι}
    (h : ρ = τ) (t : Term F Γ ρ) (n : ℕ) (env_star : Ctx.interpret X (Γ.map Ty.hat)) :
    termMajorizer cm (Term.castTy h t) n env_star
      = cast (congrArg (fun ρ => Ty.interpret X ρ.hat) h) (termMajorizer cm t n env_star) := by
  cases h; rfl

end Enabling

-- ============================================================================
-- Part 2: CORRECTED — the compositional route does NOT get past the proof-mode layer
-- ============================================================================

/-! **This section replaces an earlier, WRONG version of itself.** An earlier draft of this
file claimed a theorem `realizerE_termMajorizer_reduces`, proved by
`conv_lhs => simp only […]; conv_rhs => simp only […]` with no closing tactic, demonstrated
that `termMajorizer` walks all the way through `syntactic_soundness (mct_p2 …)` to a normal
form. **That claim was false**, caught by a second pair of eyes (not by this session):
`conv_lhs`/`conv_rhs` with no trailing `rfl` succeeds whenever both sides get stuck at the
*same* point, regardless of whether real progress was made — the same "vacuous, not evidence"
trap this file had already caught once (the bare-`simp only` version, still described
correctly below), recurring one layer deeper, hidden by the `conv` wrapping. A control theorem
with the identical shape but a deliberately insufficient 2-lemma simp set compiled just as
cleanly, with the same axiom list, confirming the trap.

**What the goal state actually shows** (checked directly via `lean_goal` at the end of the
`conv_lhs` block, not inferred from build success): after unfolding
`realizerE → mctE → mct_p2 → mct_body → mct_descent`, the term exposed is

```
termMajorizer cmE
  (syntactic_soundness eqxiE spremiseE
    (ProofMode.pm_enter (ProofMode.pm_allI (ProofMode.pm_have (ProofMode.pm_cut "d"
      (ProofMode.pm_have (ProofMode.pm_induction … (ProofMode.pm_allI (ProofMode.pm_intro "ih" …
        (ProofMode.pm_cut "hstep" … (ProofMode.pm_cases "heq" "hne" …
          (ProofMode.pm_cut "sd" …
            (ProofMode.seq_id ProofMode.HVar.hz.hs.hs.hs.hs.hs.hs.hs.hs.hs.hs) …
```

i.e. `syntactic_soundness`'s pattern match **never fires**: its argument is not a literal
`Derivable` constructor (`.mp`, `.syllogism`, `.forall_rule`, `.induction`, …) but the entire
unexpanded `ProofMode.pm_*` tactic-combinator tree — `pm_enter`, `pm_allI`, `pm_have`,
`pm_induction`, `pm_intro`, `pm_cut`, `pm_mp`, `pm_rw_at`, `pm_cases`, `pm_inst`, `pm_exI`,
`pm_andE₁`/`pm_andE₂`, `pm_trans`, `pm_sym`, `ProofMode.seq_id`, `qfer_at_nf`,
`qfer_no_premise_at_nf`, `qf_lem`, `antitone_chain`, `strict_drop`, none of which were in the
simp set. So every `sMP`/`sSyllogism`/`sInduction`/… lemma in this file's Part 1 discussion is
irrelevant here — the reduction is stuck one whole layer above `Derivable`, not inside it, and
the extraction-step finding from the earlier draft (which built on top of this false premise)
does not stand either: nothing in this file established that `syntactic_soundness` itself gets
through `mct_p2`'s real derivation, so nothing was actually localized to `extractUTerm`.

## Why this is a substantially bigger problem, not just "add the missing lemma names"

`mct_p2` is built through `ProofMode/Packing.lean`'s `Seq`/`HCtx`/`HVar` layer, and unlike
`Term.weaken`/`Term.castTy` (which this file's `termMajorizer_weaken`/`termMajorizer_castTy`
handle in `O(1)` per site, because they never need to inspect what is *inside* the wrapped
value), that layer has genuine **multiplicative** structure:

- `seq_mp : Seq Δ (A →ᶠ B) → Seq Δ A → Seq Δ B` recurses on the *entire* hypothesis context
  `Δ`, inserting one `S_comb`-based combinator per element of `Δ` at every call
  (`Packing.lean:85-94`).
- `seq_id` (hypothesis lookup, what `ProofMode.seq_id ProofMode.HVar.hz.hs.hs…` above is)
  applies `seq_mono K_comb` once per `.hs` in the `HVar` index (`Packing.lean:137-141`), and
  each of *those* calls is itself a `seq_mp` over the context at that point.

So a single hypothesis lookup at de Bruijn depth `k` inside a context of size `n` costs on the
order of `k · n` combinator applications, and the goal dump above shows both growing: an
11-deep `.hs` chain, and hypothesis contexts that keep extending through nested `pm_cut`s
(`"sd4"`, `"sd5"`, `"hle"`, `"ih1"`, `"ih2"`, `"hex"`, …). Unfolding the ~20 `seq_*` combinators
in `Packing.lean` plus the ~30 `pm_*` tactics in `Tactics.lean` plus `qfer_at_nf`/
`qfer_no_premise_at_nf`/`qf_lem`/`antitone_chain`/`strict_drop` was not attempted to
completion: it is a materially larger undertaking than the `Term.weaken`/`Term.castTy` fix
(which needed exactly two lemmas, each proved once, each `O(1)` per use), and the multiplicative
shape above means there is a real chance it reproduces the same memory blowup `BoundProbe.lean`
measured — one layer earlier than either that probe or this file's earlier (wrong) draft placed
it, and for a structurally different reason (context-size multiplication in a Hilbert-to-sequent
packaging layer, not term duplication under application).

## The honest state of this file

- **Part 1 (`termMajorizer_weaken`/`termMajorizer_castTy`) is correct and unaffected** — those
  are ordinary structural-induction proofs about `termMajorizer` and `Term.rename`/`Term.weaken`
  in general, verified the normal way (no `conv` involved), and hold regardless of what happens
  to `mct_p2`.
- **No claim in this file establishes that the compositional route reaches `mct_p2`'s actual
  `Derivable` structure, let alone a numeral.** The furthest confirmed progress is unfolding
  `mct_p2`'s tactic-produced term down to its `ProofMode.pm_*`/`seq_*` skeleton — real, but well
  short of `syntactic_soundness` ever pattern-matching on anything.
- **This is a genuine negative finding**, more precise than the (retracted) extraction-based one:
  the compositional route, as built here, does not get past the proof-mode abstraction layer,
  and closing that gap is open work of uncertain and possibly large cost, not a short follow-up.
-/

noncomputable def cmE := bezemConstMajorantsEmpty BoundProbe.siE

end BoundLemmasP2
end Metatheorems
