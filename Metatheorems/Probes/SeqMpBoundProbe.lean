/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.BoundLemmasP2

/-!
# Probe: does `termMajorizer` commute with the proof-mode primitives?

`Probes/BoundLemmasP2.lean` proved that `termMajorizer` commutes with `Term.weaken`/`Term.castTy`
in `O(1)` per site, and then found that pushing it through `mct_p2` stalls at the proof-mode
packaging layer (`ProofMode/Packing.lean`), whose `seq_mp` recurses over the whole hypothesis
context. This file asks the follow-up: can `termMajorizer` be made to commute with the three
primitives everything in that layer is built from — `seq_of_thm`, `seq_id`, `seq_mp` — by a
generic lemma each, the way `termMajorizer_weaken` did for `Term.weaken`?

## Summary of what was found

**Negative, measured (Part 1):** the realizer `syntactic_soundness` produces for a *single*
`S_comb` — the combinator `seq_mp` inserts once per context element — cannot even be
materialised: `termSize` of it exhausts a 12 GB cap. So does `seq_mp` at context size 1 with
trivial arguments. The cause is not `seq_mp`'s context recursion (that is "only" `×2` per
context element) but the `SRealizer` combinators underneath it: `sSyllogism` copies its first
argument's realizer three times and its second twice, `sExportation`/`sImportation` copy theirs
three times, and `S_comb` nests those ~12 deep. Numbers below.

**Positive, kernel-checked (Part 2):** none of that has to be looked at. Every copy those
combinators make sits in the **counter** component of the realizer, and the **witness**
component is closed under first projection. So, with the sub-realizers as *variables*, each
combinator gets a one-line "witness-projection" lemma (`wapp_sSyllogism`, …), `S_comb`'s
majorant collapses to the semantic `S` (`wapp_S`, at fully abstract `A B C`), and all three
primitives commute:

| primitive | lemma | content |
|---|---|---|
| `seq_of_thm` | `wit_seq_of_thm` | a theorem lifted into context ignores the hypothesis witnesses |
| `seq_id`     | `wit_seq_id`     | hypothesis lookup is projection out of the hypothesis witnesses |
| `seq_mp`     | `wit_seq_mp`     | modus ponens in context is witness application |

`seq_mp_11_numeral` is the demonstration: a literal `0` out of a `seq_mp` at context size 11
(`mct_p2`'s depth), by `simp only` with the lemmas above, in the same file that measured the
underlying term at ~10¹¹ nodes. The kernel never reduces the term; the lemmas are structural
on the *derivation* (~200 nodes at that depth), not on the realizer.

**Scope, stated plainly:** these lemmas are about the witness path *only* — the `wit`/`wapp`
projections. The counter components (where `extractUTerm` reads its `U`) were not touched, and
that is exactly where the duplication lives, so nothing here says `U` is cheap. See "What is
NOT established" at the end.

NOT imported by `Metatheorems.lean`, per the `Probes/` convention.
-/

namespace Metatheorems
namespace SeqMpBoundProbe

open ProofMode BoundProbe BoundLemmasP2 Formula

-- ============================================================================
-- Part 1: measurement — how big is what `seq_mp` produces?
-- ============================================================================

/-- Structural node count of a derivation: the ten constructors with sub-derivations are
counted recursively, every other constructor is one node. Companion to `BoundProbe.termSize`;
exists to measure this probe, not as library API. -/
def derivSize {ι : Type} {F : ι → Ty ι} {a : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → Derivable F a P A → Nat
  | _, _, .mp h₁ h₂         => 1 + derivSize h₁ + derivSize h₂
  | _, _, .syllogism h₁ h₂  => 1 + derivSize h₁ + derivSize h₂
  | _, _, .exportation h    => 1 + derivSize h
  | _, _, .importation h    => 1 + derivSize h
  | _, _, .expansion h      => 1 + derivSize h
  | _, _, .forall_rule h    => 1 + derivSize h
  | _, _, .exist_rule h     => 1 + derivSize h
  | _, _, .univ_gen h       => 1 + derivSize h
  | _, _, .qfer _ _ h       => 1 + derivSize h
  | _, _, .induction h₁ h₂  => 1 + derivSize h₁ + derivSize h₂
  | _, _, _                 => 1

/-- Number of leaf-realizer copies in `(syntactic_soundness h).val`, read off the source of
`Dialectica/Syntactic.lean`: `sMP` uses each argument's realizer once (`.app (.fst hAB.val)
hA.val`); `sSyllogism` uses `hAB.val` three times (`.fst` twice, `.snd` once) and `hBC.val`
twice; `sExportation` and `sImportation` use their argument three times; `sExpansion` twice.
The remaining recursive constructors are off this probe's path and are counted once, so this
is a lower bound there. Every leaf counts 1; the measured leaf realizers here are 9–78 nodes. -/
def leafCopies {ι : Type} {F : ι → Ty ι} {a : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → Derivable F a P A → Nat
  | _, _, .mp h₁ h₂         => leafCopies h₁ + leafCopies h₂
  | _, _, .syllogism h₁ h₂  => 3 * leafCopies h₁ + 2 * leafCopies h₂
  | _, _, .exportation h    => 3 * leafCopies h
  | _, _, .importation h    => 3 * leafCopies h
  | _, _, .expansion h      => 2 * leafCopies h
  | _, _, .forall_rule h    => leafCopies h
  | _, _, .exist_rule h     => leafCopies h
  | _, _, .univ_gen h       => leafCopies h
  | _, _, .qfer _ _ h       => leafCopies h
  | _, _, .induction h₁ h₂  => leafCopies h₁ + leafCopies h₂
  | _, _, _                 => 1

/-- The trivial hypothesis formula `0 =₀ 0`: quantifier-free, `wTy T = cTy T = unit`. -/
abbrev T : Formula FEmpty ([] : Ctx Empty) := Formula.eq0 Term.zero Term.zero

/-- The goal formula `∃v:nat (v =₀ 0)`, chosen so the witness type is `nat ×ₜ unit` and a
numeral can come out of the majorant. -/
abbrev B : Formula FEmpty ([] : Ctx Empty) :=
  Formula.ex Ty.nat (Formula.eq0 (Term.var Var.vz) Term.zero)

abbrev D (Γ : Ctx Empty) (A : Formula FEmpty Γ) : Type :=
  @Derivable Empty Empty FEmpty Allowed.extended PremE Γ A

def hT : D [] T := .refl0
def hB : D [] B := .mp .refl0 (.exist_ax Term.zero (Formula.eq0 (Term.var Var.vz) Term.zero))
def hTB : D [] (T →ᶠ B) := .mp hB (.exportation .and_weak)

/-- The hypothesis context of size `k`: `k` copies of `T`. -/
def ctx (k : Nat) : HCtx FEmpty ([] : Ctx Empty) := List.replicate k T

/-- One `seq_mp` at context size `k`, with the two smallest possible arguments. -/
def deriv (k : Nat) : Seq FEmpty Allowed.extended PremE (ctx k) B :=
  seq_mp (seq_of_thm hTB) (seq_of_thm hT)

/-- Its syntactic realizer. -/
def real (k : Nat) : SRealizer siE (pack (ctx k) B) :=
  syntactic_soundness eqxiE spremiseE (deriv k)

-- The pieces, for sizing.
def sT  := syntactic_soundness eqxiE spremiseE hT
def sTB := syntactic_soundness eqxiE spremiseE hTB
def dI : D [] (T →ᶠ T) := I_comb
def dK : D [] (T →ᶠ T →ᶠ T) := K_comb
def dS_TTT : D [] ((T →ᶠ T →ᶠ T) →ᶠ (T →ᶠ T) →ᶠ T →ᶠ T) := S_comb
/-- The `S_comb` instance `seq_mp` at `Δ = [T]` actually uses for `hAB : Seq [T] (T →ᶠ B)`. -/
def dS_TTB : D [] ((T →ᶠ T →ᶠ B) →ᶠ (T →ᶠ T) →ᶠ T →ᶠ B) :=
  S_comb (A := T) (B := T) (C := B)
def sI     := syntactic_soundness eqxiE spremiseE dI
def sK     := syntactic_soundness eqxiE spremiseE dK
def sS_TTT := syntactic_soundness eqxiE spremiseE dS_TTT
def sS_TTB := syntactic_soundness eqxiE spremiseE dS_TTB

-- Inside S_comb: the pieces of `eval_h`/`pair_h`, at the all-unit instance.
def dAndWeak : D [] (T ∧ᶠ T →ᶠ T) := .and_weak
def dAndPerm : D [] (T ∧ᶠ T →ᶠ T ∧ᶠ T) := .and_perm
def dAndContract : D [] (T →ᶠ T ∧ᶠ T) := .and_contract
def dAndIntro : D [] (T →ᶠ T →ᶠ T ∧ᶠ T) := and_intro
def dPairH : D [] (T →ᶠ T ∧ᶠ T) := pair_h (H := T) (X := T) (Y := T) I_comb I_comb
def dEvalH : D [] (T →ᶠ T) := eval_h (H := T) (A := T) (B := T) K_comb I_comb
def sAndWeak' := syntactic_soundness eqxiE spremiseE dAndWeak
def sAndPerm' := syntactic_soundness eqxiE spremiseE dAndPerm
def sAndContract' := syntactic_soundness eqxiE spremiseE dAndContract
def sAndIntro' := syntactic_soundness eqxiE spremiseE dAndIntro
def sPairH := syntactic_soundness eqxiE spremiseE dPairH
def sEvalH := syntactic_soundness eqxiE spremiseE dEvalH

/-! ### The measurements

All taken by `#eval` from scratch files importing this module, every invocation wrapped as
`ulimit -v 12000000; timeout 300 lake env lean …` and run one at a time (the machine has 16 GB).
**Do not add live `#eval`s of `termSize` on `sS_*`/`real k` to this file** — two of them are
known to exhaust the cap, and `BoundProbe.lean` records what an uncapped one did.

**Derivation sizes** (`derivSize`): `hT` 1, `hTB` 6, `I_comb` 3, `K_comb` 2, `and_intro` 4,
`pair_h` 23, `eval_h` 27, **`S_comb` 82** (at either instance). One `seq_mp` at context size
`k`, `derivSize (deriv k)` for `k = 0..11`:

    8, 97, 272, 619, 1310, 2689, 5444, 10951, 21962, 43981, 88016, 176083

— ratio → 2, i.e. `G(k) = 2·G(k-1) + |seq_of_thm_{k-1} S_comb|`, exactly `seq_mp`'s double
recursion (`Packing.lean:91-94`). This is the ordinary exponential cost of the *iterated*
deduction theorem; it lives entirely at the `Derivable` level, before any realizer exists.

**Realizer sizes** (`termSize (… ).val`): `sT` 1, `sTB` 71, `sAndWeak'` 9, `sAndPerm'` 14,
`sAndContract'` 78, `sK` 58, `sI` 272, `sAndIntro'` 1,489, **`sPairH` 231,930**,
**`sEvalH` 709,662**, `real 0` 74; and

    termSize sS_TTT.val   →  INTERNAL PANIC: out of memory   (12 GB cap, 31 s)
    termSize (real 1).val →  INTERNAL PANIC: out of memory   (12 GB cap, 34 s)

So a *single* `S_comb` realizer — 82 derivation nodes, every type `unit` — does not fit in
12 GB, and neither does `seq_mp` at context size **1** with trivial arguments. `sI = 272`
shows the mechanism at the smallest scale: `3·78 + 2·9 + 20` glue, the three-plus-two copies
`sSyllogism` makes of its arguments.

**Leaf-copy counts** (`leafCopies`), the estimator that stands in where the term cannot be
built: `I_comb` 5, `K_comb` 3, `and_intro` 15, `pair_h` 2,733, `eval_h` 8,121,
**`S_comb` 41,932,269**; `leafCopies (deriv k)` for `k = 0..11`:

    6, 41932281, 125796828, 293525919, 628984098, 1299900453, 2641733160,
    5325398571, 10692729390, 21427391025, 42896714292, 85835360823

The estimator is validated where the real term exists: `pair_h` 2,733 copies against 231,930
measured nodes (84.9 nodes per leaf copy) and `eval_h` 8,121 against 709,662 (87.4 per copy),
consistent with the 9–78-node leaf realizers plus glue. At that rate one `S_comb` is
≈3.6×10⁹ nodes, and `seq_mp` at `mct_p2`'s context depth 11 is ≈7×10¹² — per call.

**Why the earlier estimate was too optimistic.** `BoundLemmasP2.lean` attributed the cost to
`seq_mp`'s `×|Δ|` recursion and guessed that `S_comb`-style combinators "force genuine
duplication" in `termMajorizer`. Both halves need correcting: the recursion is `×2^|Δ|`, not
`×|Δ|`, and it is not the dominant term anyway — the `4×10⁷` base from one `S_comb` is, and
that comes from `sSyllogism`/`sExportation`/`sImportation` at the `SRealizer` level, the same
family as the `×2`-per-layer `TinyBoundDemo.lean` measured for `syllogism I_comb`. And
`termMajorizer` does *not* duplicate anything here: `sMP`'s realizer is `.app (.fst _) _`,
so `termMajorizer` commutes with each `Derivable.mp` by bare `rfl` (`tm_sMP` below, checked with
variable sub-realizers). The hypothesis that `S_comb` is "not transparent" to `termMajorizer`
the way `weaken` is was wrong in an instructive way: transparency was never the problem, the
count of sites was. -/

-- ============================================================================
-- Part 2: the witness side commutes — three lemmas, one per primitive
-- ============================================================================

/-! ### The idea

A Meta-level `rfl` on `(((closedMajorizer cmE sS_TTB.val).1 f).1 g).1 a = (f.1 a).1 (g.1 a)`
hits the heartbeat limit (not raised). That is the elaborator's `whnf` walking the term; the
kernel's lazy projection semantics are not what `rfl` at the elaborator exercises.

The discipline that works is the project's own: **one combinator per lemma, sub-realizers as
variables.** `SRealizer.imp f g _` has `.val = .mkPair f g`; the witness component `f` of
every combinator on `S_comb`'s path (`sSyllogism`, `sExportation`, `sImportation`, `sAndWeak`,
`sAndPerm`, `sAndContract`) mentions its sub-realizers **only through `.fst`** — every second
and third copy is in `g`, the counter transformer. So a lemma about the *first projection*
of the majorant, stated with the sub-realizer's majorant as an opaque `termMajorizer cm h.val
n e`, never expands `h.val`, needs `termMajorizer_weaken` for the binder crossings, and is
`O(1)` per site. Chained, they collapse `S_comb` to the semantic `S` and then `seq_mp`,
`seq_id`, `seq_of_thm` to what they mean.

Two named projections, `wapp` and `wfst`, keep the lemmas matching on **formulas** rather than
on `Ty.interpret` types: stated with a bare `.1`, `simp` reduces the projection to a raw
`Expr.proj` and then cannot see the product at reducible transparency ("invalid projection …
from type `Ty.interpret ?X (wTy (∃ᶠ …)).hat`"), so the lemma silently fails to fire. -/

section Wit
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} (cm : ConstMajorants am) {Γ : Ctx ι}

/-- Witness application: the first component of a majorant at an implication's witness type,
applied. -/
def wapp {A B : Formula F Γ} (r : Ty.interpret X (wTy (A →ᶠ B)).hat)
    (a : Ty.interpret X (wTy A).hat) : Ty.interpret X (wTy B).hat := r.1 a

/-- The existential witness: first component of a majorant at `wTy (∃x A) = ρ ×ₜ wTy A`. -/
def wfst {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (w : Ty.interpret X (wTy (Formula.ex ρ A)).hat) : Ty.interpret X ρ.hat := w.1

variable (n : ℕ) (e : Ctx.interpret X (Γ.map Ty.hat))

/-- `Derivable.mp` is free: `sMP`'s realizer is `.app (.fst hAB.val) hA.val`, no `weaken`. -/
theorem tm_sMP {A B : Formula F Γ} (hA : SRealizer si A) (hAB : SRealizer si (A →ᶠ B)) :
    termMajorizer cm (sMP hA hAB).val n e
      = wapp (termMajorizer cm hAB.val n e) (termMajorizer cm hA.val n e) := rfl

theorem wapp_sAndWeak {A B : Formula F Γ} (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) :
    wapp (termMajorizer cm (sAndWeak (si := si) (A := A) (B := B)).val n e) p = p.1 := rfl

theorem wapp_sAndPerm {A B : Formula F Γ} (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) :
    wapp (termMajorizer cm (sAndPerm (si := si) (A := A) (B := B)).val n e) p = (p.2, p.1) :=
  rfl

/-- The one combinator whose *counter* needs `matrixTerm`; its witness is just the diagonal. -/
theorem wapp_sAndContract {A : Formula F Γ} (p : Ty.interpret X (wTy A).hat) :
    wapp (termMajorizer cm (sAndContract (si := si) (A := A)).val n e) p = (p, p) := rfl

theorem wapp_sSyllogism {A B C : Formula F Γ}
    (hAB : SRealizer si (A →ᶠ B)) (hBC : SRealizer si (B →ᶠ C)) (a : Ty.interpret X (wTy A).hat) :
    wapp (termMajorizer cm (sSyllogism hAB hBC).val n e) a
      = wapp (termMajorizer cm hBC.val n e) (wapp (termMajorizer cm hAB.val n e) a) := by
  simp only [wapp, sSyllogism, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem wapp_sExportation {A B C : Formula F Γ} (h : SRealizer si (A ∧ᶠ B →ᶠ C))
    (a : Ty.interpret X (wTy A).hat) (b : Ty.interpret X (wTy B).hat) :
    wapp (wapp (termMajorizer cm (sExportation h).val n e) a) b
      = wapp (termMajorizer cm h.val n e) (a, b) := by
  simp only [wapp, sExportation, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem wapp_sImportation {A B C : Formula F Γ} (h : SRealizer si (A →ᶠ B →ᶠ C))
    (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) :
    wapp (termMajorizer cm (sImportation h).val n e) p
      = wapp (wapp (termMajorizer cm h.val n e) p.1) p.2 := by
  simp only [wapp, sImportation, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem wfst_wapp_sExistAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (A.subst0 t)).hat) :
    wfst (wapp (termMajorizer cm (sExistAx (si := si) (A := A) t).val n e) w)
      = termMajorizer cm t n e := by
  simp only [wfst, wapp, sExistAx, SRealizer.imp, termMajorizer, termMajorizer_weaken]

variable {P : PremiseSet F} (eqxi : EqXInterp X F si)
    (sp : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)

/-- **`S_comb`'s majorant is the semantic `S`**, on the witness side, at fully abstract
`A B C`. The `simp` set is `S_comb`'s definition plus the seven projection lemmas; the
`4×10⁷`-copy realizer is never built. -/
theorem wapp_S {A B C : Formula F Γ}
    (f : Ty.interpret X (wTy (A →ᶠ B →ᶠ C)).hat) (g : Ty.interpret X (wTy (A →ᶠ B)).hat)
    (a : Ty.interpret X (wTy A).hat) :
    wapp (wapp (wapp (termMajorizer cm (syntactic_soundness eqxi sp
      (S_comb (a := Allowed.extended) (Premises := P) (A := A) (B := B) (C := C))).val n e) f) g) a
      = wapp (wapp f a) (wapp g a) := by
  simp only [S_comb, eval_h, pair_h, syntactic_soundness, wapp_sExportation,
    wapp_sSyllogism, wapp_sImportation, wapp_sAndWeak, wapp_sAndPerm, wapp_sAndContract]

/-- The hypothesis witnesses of a context: one majorant-typed value per formula in `Δ`. -/
def HWit (X : ι → Type) : HCtx F Γ → Type
  | []     => Unit
  | A :: Δ => Ty.interpret X (wTy A).hat × HWit X Δ

/-- Witness projection through a packed context: apply the witness component to each
hypothesis witness in turn. `pack (A₀ :: Δ) B` is `pack Δ (A₀ →ᶠ B)` definitionally, which is
what makes the recursion typecheck without a cast. -/
def wit : (Δ : HCtx F Γ) → {B : Formula F Γ} →
    Ty.interpret X (wTy (pack Δ B)).hat → HWit X Δ → Ty.interpret X (wTy B).hat
  | [],      _, w, _         => w
  | A₀ :: Δ, B, w, (a₀, as)  => wapp (wit Δ (B := A₀ →ᶠ B) w as) a₀

/-- Look a hypothesis witness up by its de Bruijn index. -/
def HWit.lookup : {Δ : HCtx F Γ} → {A : Formula F Γ} → HVar Δ A → HWit X Δ →
    Ty.interpret X (wTy A).hat
  | _ :: _, _, .hz,   (a, _)  => a
  | _ :: _, _, .hs v, (_, as) => HWit.lookup v as

/-- **`seq_of_thm` commutes**: a theorem lifted into context `Δ` ignores the hypothesis
witnesses. Per element of `Δ` one `weaken_intro_h = .mp h (.exportation .and_weak)`, i.e. one
`K`; the `show` spells that out because `weaken_intro_h` is private to `Packing.lean`. -/
theorem wit_seq_of_thm : ∀ (Δ : HCtx F Γ) {B : Formula F Γ}
    (h : Derivable F Allowed.extended P B) (as : HWit X Δ),
    wit Δ (termMajorizer cm (syntactic_soundness eqxi sp (seq_of_thm (Δ := Δ) h)).val n e) as
      = termMajorizer cm (syntactic_soundness eqxi sp h).val n e
  | [],     _, _, _        => rfl
  | A :: Δ, B, h, (a, as) => by
      change wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp
        (seq_of_thm (Δ := Δ) (Derivable.mp h (.exportation .and_weak)))).val n e) as) a = _
      rw [wit_seq_of_thm Δ]
      simp only [syntactic_soundness, tm_sMP, wapp_sExportation, wapp_sAndWeak]

/-- **`seq_mp` commutes**: modus ponens in context is witness application. The `cons` case is
the two recursive `seq_mp`s plus `wapp_S`; the `[]` case is `tm_sMP`, i.e. `rfl`. -/
theorem wit_seq_mp : ∀ (Δ : HCtx F Γ) {A B : Formula F Γ}
    (hAB : Seq F Allowed.extended P Δ (A →ᶠ B)) (hA : Seq F Allowed.extended P Δ A)
    (as : HWit X Δ),
    wit Δ (termMajorizer cm (syntactic_soundness eqxi sp (seq_mp hAB hA)).val n e) as
      = wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp hAB).val n e) as)
             (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp hA).val n e) as)
  | [],      _, _, _,   _,  _        => rfl
  | A₀ :: Δ, A, B, hAB, hA, (a₀, as) => by
      change wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp
          (seq_mp (Δ := Δ) (seq_mp (Δ := Δ)
            (seq_of_thm (Δ := Δ) (S_comb (A := A₀) (B := A) (C := B))) hAB) hA)).val n e) as) a₀
        = wapp (wapp (wit Δ (B := A₀ →ᶠ A →ᶠ B)
                  (termMajorizer cm (syntactic_soundness eqxi sp hAB).val n e) as) a₀)
               (wapp (wit Δ (B := A₀ →ᶠ A)
                  (termMajorizer cm (syntactic_soundness eqxi sp hA).val n e) as) a₀)
      rw [wit_seq_mp Δ, wit_seq_mp Δ, wit_seq_of_thm cm n e eqxi sp Δ, wapp_S]

/-- **`seq_id` commutes**: hypothesis lookup is projection. `hz` is `seq_of_thm I_comb`
(`I = S K K` here is `syllogism and_contract and_weak`, whose witness is `(a, a).1`); `hs v`
is `seq_mono K_comb (seq_id v) = seq_mp (seq_of_thm K_comb) (seq_id v)`. -/
theorem wit_seq_id : ∀ (Δ : HCtx F Γ) {A : Formula F Γ} (v : HVar Δ A) (as : HWit X Δ),
    wit Δ (termMajorizer cm (syntactic_soundness eqxi sp (seq_id (Δ := Δ) v)).val n e) as
      = HWit.lookup v as
  | A :: Δ, _, .hz, (a, as) => by
      change wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp
        (seq_of_thm (Δ := Δ) (I_comb (A := A)))).val n e) as) a = a
      rw [wit_seq_of_thm cm n e eqxi sp Δ]
      simp only [I_comb, syntactic_soundness, wapp_sSyllogism, wapp_sAndContract, wapp_sAndWeak]
  | B :: Δ, A, .hs v, (b, as) => by
      change wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp
        (seq_mp (Δ := Δ) (seq_of_thm (Δ := Δ) (K_comb (A := A) (B := B)))
          (seq_id (Δ := Δ) v))).val n e) as) b = HWit.lookup v as
      rw [wit_seq_mp cm n e eqxi sp Δ, wit_seq_of_thm cm n e eqxi sp Δ, wit_seq_id Δ v]
      simp only [K_comb, syntactic_soundness, wapp_sExportation, wapp_sAndWeak]

end Wit

/-- **The demonstration.** A literal `0` out of `seq_mp` at context size 11 — the depth of
`mct_p2`'s deepest `HVar` chain — kernel-checked, from a term this file measured at
≈7×10¹² nodes (`leafCopies (deriv 11) = 85,835,360,823`, ×85). Nothing is unfolded below
`wit_seq_mp`/`wit_seq_of_thm`; the rest is the seven-node derivation `hTB` and the leaf
`sExistAx Term.zero`, whose witness is `cm.zeroM n = 0`. The context is only ever touched
through `Δ := ctx 11` as an opaque list — the statement would go through at `ctx 1000`
unchanged. -/
theorem seq_mp_11_numeral (as : HWit XEmpty (ctx 11)) :
    (0 : ℕ) = wfst (wit (ctx 11) (closedMajorizer cmE (real 11).val) as) := by
  simp only [closedMajorizer, real, deriv, wit_seq_mp, wit_seq_of_thm, hTB, hT, hB,
    syntactic_soundness, tm_sMP, wapp_sExportation, wapp_sAndWeak, wfst_wapp_sExistAx,
    termMajorizer, cmE, bezemConstMajorantsEmpty]

/-! ### What is established, and how

- **Part 1's numbers** are direct, capped `#eval` measurements, each in its own process; the
  two OOMs are reproducible and the `leafCopies` predictions are consistent with the measured
  sizes where both exist. The `×2` recurrence is read off `Packing.lean` and confirmed by
  the `derivSize` column. The `≈3.6×10⁹`/`≈7×10¹²` figures are the estimator times the
  measured nodes-per-copy; they are *inferred*, not measured.
- **Part 2's lemmas** are ordinary theorems: every tactic block ends in `rfl` or in a `simp
  only` that closes the goal, so a `conv`-without-closer trap of the kind `BoundLemmasP2.lean`
  fell into cannot occur; the `lean_goal` status at the end of `wapp_S`, `wit_seq_mp`'s `cons`
  case and `seq_mp_11_numeral` was checked to be `complete` after the build, and the axiom
  block below is the record. Whole file: ~8 s on top of the imports.
- **`tm_sMP` is `rfl` with variable sub-realizers**, which is the precise sense in which
  "`termMajorizer` commutes with `seq_mp`'s raw `Derivable` combinator in `O(1)`" is true.

### What is NOT established

- **Only the witness path.** `wit`/`wapp`/`wfst` read first components. The counter
  components — `sSyllogism`'s `g`, where `hAB.val` appears twice, `sAndContract`'s
  `natCase (matrixTerm …)` whose majorant goes through `cm.precM`/`recMaj` — have no lemmas
  here. `extractUTerm` reads its `U` from a `.snd` (`Dialectica/Syntactic.lean:104`), so the
  metatheorem's `U` bound is on the untouched side. A counter-side lemma per combinator is
  the same shape but its right-hand side mentions sub-majorants more than once, so the
  *semantic* normal form would grow multiplicatively with depth unless intermediate values
  are named; whether that is a problem in practice is the next probe.
- **Only the three primitives.** `mct_p2` also goes through `Derivable.induction`,
  `forall_rule`/`univ_gen`/`exist_rule`, `qfer` (`qfer_at_nf`, `qfer_no_premise_at_nf`),
  `qf_lem`, `antitone_chain`, `strict_drop`; `sInduction`, `sForallRule`, `sQfer`, … each
  need their own projection lemma, and the `pm_*` tactic definitions in `Tactics.lean` need
  to be unfolded to the primitives (they are `def`s, so `simp only` naming them should do it,
  but this was not tried).
- **The hypothesis of an earlier note is retracted, not confirmed:** `S_comb` *is* transparent
  to `termMajorizer` — see `wapp_S`. The blow-up is in the realizer term's counter half, and
  the witness side of `termMajorizer` never visits it. -/

#print axioms tm_sMP
#print axioms wapp_S
#print axioms wit_seq_of_thm
#print axioms wit_seq_id
#print axioms wit_seq_mp
#print axioms seq_mp_11_numeral

end SeqMpBoundProbe
end Metatheorems
