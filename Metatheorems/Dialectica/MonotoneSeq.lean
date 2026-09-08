/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.MfiMemoAttr
import Metatheorems.Dialectica.MonotoneMemo
import Metatheorems.ProofMode.Tactics
import Metatheorems.ProofMode.Rewrite

/-!
# `monotone_soundness` through the proof-mode packaging layer

`Dialectica/MonotoneMemo.lean` gives the `Eq.mpr` entry for `monotone_soundness`; it fires
only where the recursion meets a cast *directly*. In a proof-mode-written derivation the casts
sit under `ProofMode/Packing.lean`'s `seq_*` combinators and `Tactics.lean`'s `pm_*` wrappers,
and unfolding that layer by `simp` is what explodes (`Probes/MonotoneLaneBp.lean`). This module
is the MFI analogue of `Probes/CombinatorLemmas.lean`'s `wit_seq_*` programme: for each
packaging combinator, a lemma

    monotone_soundness … (seq_mp hAB hA) = MRealizer.seqMp … Δ (ms hAB) (ms hA)

whose right-hand side is an explicit `MRealizer` combinator, **Δ-generic** (proved by
structural recursion on the hypothesis context `Δ`, exactly as `wit_seq_mp` is), and never
mentioning the sub-derivation. Applied as rewrite rules (the `mfi_memo` simp set, declared in
`Dialectica/MfiMemoAttr.lean`), they carry `monotone_soundness` through the layer *without
unfolding it* until it meets a raw constructor (where its own equations fire) or a cast (where the
`MonotoneMemo` entry fires). The kernel then reduces the semantic combinators, which are
recursions on `Δ` over the hand-written hat-side λ-terms of `Monotone.lean`.

## What is here

* **Leaf combinators** — the packaging layer's closed kernel theorems, as monotone realizers:
  `kComb` (`K_comb`), `iComb` (`I_comb`), `sComb` (`S_comb`), `fipComb` (`forall_imp_pull`),
  `eipComb` (`exist_imp_pull`), `fipushComb` (`forall_imp_push`), `fmSComb`
  (`forall_mono S_comb`). The last five are `monotone_soundness` of the closed derivation —
  a fixed 80-node term the kernel reduces once and caches.
* **Δ-recursive combinators** mirroring `Packing.lean`/`Induction.lean` one-for-one:
  `seqOfThm`, `seqMp`, `seqId`, `seqAllI`, `seqInduction`; `seq_cast` is `transport`.
* **The entries** (`@[mfi_memo]`): `ms_seq_of_thm`, `ms_seq_mp`, `ms_seq_id`, `ms_seq_allI`,
  `ms_seq_cast`, `ms_seq_induction`, `ms_seq_mono` — the Δ-generic ones — and one `rfl`
  restatement per derived `seq_*` / `pm_*`, so a term written by the tactics rewrites to the
  primitives in one pass. Plus `ms_eqmp_congr`, the cast entry for the shape
  `Eq.mp (congrArg (Derivable F al P ·) hB) d` that `qfer_*_nf`, `lam*_correct_nf`,
  `forall_ax_vz`, `forall_ax_inst` leave — the formula equation is *in the term*, so nothing
  has to be supplied; and the three `MonotoneMemo` lemmas are tagged in.

## `seq_induction` — why it is not the obstacle it was on the term side

`seq_induction` changes the formula it inducts on with depth (`A' := A₀↑ →ᶠ A`), which is what
stopped `sInduction` on the term route: the *witness type* changes, so no fixed type carries a
Δ-generic statement. Here the statement is about `MRealizer cm (pack Δ (∀n A))` for **every**
`A`, and `MRealizer.induction` is already generic in `A` — so `seqInduction` is the same
recursion on `Δ` with `A` generalised, and `ms_seq_induction` is proved by that recursion. The
two `seq_cast`s become `transport`s along `congrArg (pack Δ) _`, whose type sides are
definitionally equal (`wTy` ignores terms), so they cost nothing in the kernel.

## What the `Eq.mpr` of `anorm`/`canorm` still needs

Those casts are `Eq.mpr (le_R_pu_of_le_R._proof_i …) d` with the equation abstracted into an
auxiliary theorem of type `SeqD … B = SeqD … B'`: the formula equation is **not** in the term,
and `Derivable`'s type-constructor injectivity is not available. `monotone_soundness_eqmpr`
takes `hB` as a hypothesis, so it is applied with a discharger — the same normaliser that
produced the cast: `simp (disch := canorm) only [mfi_memo, …]`. See `Probes/MonotoneMemoGates.lean`.

NB. Every lemma's right-hand side elaborates `monotone_soundness … h` with the implicit
formula read off `h`'s own type (`pack Δ B`), which is also what the next lemma's left-hand
side expects; the residual spelling differences (`le_R_pu f g` against its unfolded
`Formula.all …`, from the way `refine pm_allI ?_` unifies) are absorbed because `isDefEq`
checks *implicit* arguments at default transparency after the explicit ones.
-/

namespace Metatheorems

open Formula ProofMode

section Seq

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {P : PremiseSet F}
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) {Γ : Ctx ι}

local notation "ms" => monotone_soundness eqxi spremise cm

-- ============================================================================
-- Leaf combinators: the packaging layer's closed kernel theorems, as monotone realizers
-- ============================================================================

/-- `monotone_soundness K_comb`, spelled out: `.exportation cm (ofSRealizer sAndWeak)`. -/
def MRealizer.kComb (A B : Formula F Γ) : MRealizer cm (A →ᶠ B →ᶠ A) :=
  .exportation cm (.ofSRealizer cm sAndWeak)

/-- `monotone_soundness I_comb`, spelled out. -/
def MRealizer.iComb (A : Formula F Γ) : MRealizer cm (A →ᶠ A) :=
  .syllogism cm (.andContract cm A) (.ofSRealizer cm sAndWeak)

/-- `monotone_soundness S_comb` — the combinator `seq_mp` inserts once per hypothesis. Kept
folded: the kernel reduces the 82-node closed derivation once. -/
def MRealizer.sComb (A B C : Formula F Γ) :
    MRealizer cm ((A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) :=
  ms (S_comb (a := Allowed.extended) (Premises := P) (A := A) (B := B) (C := C))

/-- `monotone_soundness forall_imp_pull` — what `seq_allI` inserts once per hypothesis. -/
def MRealizer.fipComb (ρ : Ty ι) (B : Formula F Γ) (A : Formula F (ρ :: Γ)) :
    MRealizer cm (Formula.all ρ (Formula.weakenBy ρ B →ᶠ A) →ᶠ (B →ᶠ Formula.all ρ A)) :=
  ms (forall_imp_pull (a := Allowed.extended) (Premises := P) (B := B) (A := A))

/-- `monotone_soundness exist_imp_pull` — `seq_exE`'s kernel theorem. -/
def MRealizer.eipComb (ρ : Ty ι) (B : Formula F Γ) (A : Formula F (ρ :: Γ)) :
    MRealizer cm (Formula.all ρ (A →ᶠ Formula.weakenBy ρ B) →ᶠ (Formula.ex ρ A →ᶠ B)) :=
  ms (exist_imp_pull (a := Allowed.extended) (Premises := P) (B := B) (A := A))

/-- `monotone_soundness forall_imp_push` — `seq_induction`'s first kernel theorem. -/
def MRealizer.fipushComb (ρ : Ty ι) (B : Formula F Γ) (Y : Formula F (ρ :: Γ)) :
    MRealizer cm ((B →ᶠ Formula.all ρ Y) →ᶠ Formula.all ρ (Formula.weakenBy ρ B →ᶠ Y)) :=
  ms (forall_imp_push (a := Allowed.extended) (Premises := P) (B := B) (X := Y))

/-- `monotone_soundness (forall_mono S_comb)` — `seq_induction`'s second kernel theorem. -/
def MRealizer.fmSComb (ρ : Ty ι) (A B C : Formula F (ρ :: Γ)) :
    MRealizer cm (Formula.all ρ (A →ᶠ B →ᶠ C) →ᶠ Formula.all ρ ((A →ᶠ B) →ᶠ A →ᶠ C)) :=
  ms (forall_mono (a := Allowed.extended) (Premises := P)
    (S_comb (a := Allowed.extended) (Premises := P) (A := A) (B := B) (C := C)))

-- ============================================================================
-- The Δ-recursive combinators, mirroring `Packing.lean` / `Induction.lean`
-- ============================================================================

/-- `seq_of_thm`, semantically: one `K` per hypothesis. -/
def MRealizer.seqOfThm : (Δ : HCtx F Γ) → {B : Formula F Γ} →
    MRealizer cm B → MRealizer cm (pack Δ B)
  | [],     _, r => r
  | A :: Δ, B, r => seqOfThm Δ (B := A →ᶠ B) (.mp cm r (kComb cm B A))

/-- `seq_mp`, semantically: `seq_mp`'s own double recursion, with `S_comb`'s realizer. -/
def MRealizer.seqMp : (Δ : HCtx F Γ) → {A B : Formula F Γ} →
    MRealizer cm (pack Δ (A →ᶠ B)) → MRealizer cm (pack Δ A) → MRealizer cm (pack Δ B)
  | [],      _, _, f, g => .mp cm g f
  | A₀ :: Δ, A, B, f, g =>
      seqMp Δ (A := A₀ →ᶠ A) (B := A₀ →ᶠ B)
        (seqMp Δ (A := A₀ →ᶠ A →ᶠ B) (B := (A₀ →ᶠ A) →ᶠ A₀ →ᶠ B)
          (seqOfThm cm Δ (sComb eqxi spremise cm A₀ A B)) f)
        g

/-- `seq_id`, semantically. -/
def MRealizer.seqId : {Δ : HCtx F Γ} → {A : Formula F Γ} → HVar Δ A → MRealizer cm (pack Δ A)
  | A :: Δ, _, .hz   => seqOfThm cm Δ (B := A →ᶠ A) (iComb cm A)
  | B :: Δ, A, .hs v =>
      seqMp eqxi spremise cm Δ (A := A) (B := B →ᶠ A)
        (seqOfThm cm Δ (kComb cm A B)) (seqId v)

/-- `seq_allI`, semantically. -/
def MRealizer.seqAllI {ρ : Ty ι} : (Δ : HCtx F Γ) → {A : Formula F (ρ :: Γ)} →
    MRealizer cm (pack (Δ.map (Formula.weakenBy ρ)) A) →
    MRealizer cm (pack Δ (Formula.all ρ A))
  | [],      _, h =>
      .mp cm (iComb cm (⊥ᶠ →ᶠ ⊥ᶠ))
        (.forallRule cm (.mp cm h (kComb cm _ _)))
  | A₀ :: Δ, A, h =>
      seqMp eqxi spremise cm Δ (seqOfThm cm Δ (fipComb eqxi spremise cm ρ A₀ A))
        (seqAllI Δ (A := Formula.weakenBy ρ A₀ →ᶠ A) h)

/-- `seq_induction`, semantically — the recursion on `Δ` with the inducted formula
generalised, its two `seq_cast`s as `transport`s. -/
def MRealizer.seqInduction : (Δ : HCtx F Γ) → {A : Formula F (Ty.nat :: Γ)} →
    MRealizer cm (pack Δ (A.subst0 Term.zero)) →
    MRealizer cm (pack Δ (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0))) →
    MRealizer cm (pack Δ (Formula.all Ty.nat A))
  | [],      _, base, step => .induction cm base step
  | A₀ :: Δ, A, base, step =>
      let A' : Formula F (Ty.nat :: Γ) := Formula.weakenBy Ty.nat A₀ →ᶠ A
      let base' : MRealizer cm (pack Δ (A'.subst0 Term.zero)) :=
        .transport (congrArg (pack Δ) (congrArg (· →ᶠ A.subst0 Term.zero)
          (Formula.subst0_weakenBy A₀ Term.zero).symm)) base
      let step' : MRealizer cm (pack Δ
          (Formula.all Ty.nat (A' →ᶠ Formula.substVar0 A' succVar0))) :=
        .transport (congrArg (pack Δ)
          (congrArg (Formula.all Ty.nat)
            (congrArg (fun Z => A' →ᶠ (Z →ᶠ Formula.substVar0 A succVar0))
              (Formula.substVar0_weakenBy A₀ succVar0).symm)))
          (seqMp eqxi spremise cm Δ
            (seqOfThm cm Δ (fmSComb eqxi spremise cm Ty.nat (Formula.weakenBy Ty.nat A₀) A
              (Formula.substVar0 A succVar0)))
            (seqMp eqxi spremise cm Δ
              (seqOfThm cm Δ (fipushComb eqxi spremise cm Ty.nat A₀
                (A →ᶠ Formula.substVar0 A succVar0)))
              step))
      seqMp eqxi spremise cm Δ (seqOfThm cm Δ (fipComb eqxi spremise cm Ty.nat A₀ A))
        (seqInduction Δ (A := A') base' step')

-- ============================================================================
-- The entries, Δ-generic
-- ============================================================================

/-- **`seq_of_thm` commutes.** -/
@[mfi_memo] theorem ms_seq_of_thm : ∀ (Δ : HCtx F Γ) {B : Formula F Γ}
    (h : Derivable F Allowed.extended P B),
    ms (seq_of_thm (Δ := Δ) h) = MRealizer.seqOfThm cm Δ (ms h)
  | [],     _, _ => rfl
  | A :: Δ, B, h => by
      change ms (seq_of_thm (Δ := Δ) (Derivable.mp h (.exportation .and_weak)))
        = MRealizer.seqOfThm cm Δ (B := A →ᶠ B) (.mp cm (ms h) (MRealizer.kComb cm B A))
      rw [ms_seq_of_thm Δ]
      rfl

/-- **`seq_mp` commutes.** The `cons` case is the two recursive `seq_mp`s plus `seq_of_thm`
at `S_comb`; nothing is unfolded below the combinators. -/
@[mfi_memo] theorem ms_seq_mp : ∀ (Δ : HCtx F Γ) {A B : Formula F Γ}
    (hAB : Seq F Allowed.extended P Δ (A →ᶠ B)) (hA : Seq F Allowed.extended P Δ A),
    ms (seq_mp hAB hA) = MRealizer.seqMp eqxi spremise cm Δ (ms hAB) (ms hA)
  | [],      _, _, _,   _  => rfl
  | A₀ :: Δ, A, B, hAB, hA => by
      change ms (seq_mp (Δ := Δ) (seq_mp (Δ := Δ)
          (seq_of_thm (Δ := Δ) (S_comb (A := A₀) (B := A) (C := B))) hAB) hA)
        = MRealizer.seqMp eqxi spremise cm Δ (A := A₀ →ᶠ A) (B := A₀ →ᶠ B)
            (MRealizer.seqMp eqxi spremise cm Δ (A := A₀ →ᶠ A →ᶠ B) (B := (A₀ →ᶠ A) →ᶠ A₀ →ᶠ B)
              (MRealizer.seqOfThm cm Δ (MRealizer.sComb eqxi spremise cm A₀ A B)) (ms hAB))
            (ms hA)
      rw [ms_seq_mp Δ, ms_seq_mp Δ, ms_seq_of_thm eqxi spremise cm Δ]
      rfl

/-- **`seq_id` commutes.** -/
@[mfi_memo] theorem ms_seq_id : ∀ {Δ : HCtx F Γ} {A : Formula F Γ} (v : HVar Δ A),
    ms (seq_id (Δ := Δ) v) = MRealizer.seqId eqxi spremise cm v
  | A :: Δ, _, .hz => by
      change ms (seq_of_thm (Δ := Δ) (I_comb (A := A)))
        = MRealizer.seqOfThm cm Δ (B := A →ᶠ A) (MRealizer.iComb cm A)
      rw [ms_seq_of_thm eqxi spremise cm Δ]
      rfl
  | B :: Δ, A, .hs v => by
      change ms (seq_mp (Δ := Δ) (seq_of_thm (Δ := Δ) (K_comb (A := A) (B := B)))
          (seq_id (Δ := Δ) v))
        = MRealizer.seqMp eqxi spremise cm Δ (A := A) (B := B →ᶠ A)
            (MRealizer.seqOfThm cm Δ (MRealizer.kComb cm A B))
            (MRealizer.seqId eqxi spremise cm v)
      rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ, ms_seq_id v]
      rfl

/-- **`seq_allI` commutes.** -/
@[mfi_memo] theorem ms_seq_allI : ∀ (Δ : HCtx F Γ) {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F Allowed.extended P (Δ.map (Formula.weakenBy ρ)) A),
    ms (seq_allI h) = MRealizer.seqAllI eqxi spremise cm Δ (ms h)
  | [],      ρ, A, h => by
      change ms (Derivable.mp I_comb (.forall_rule (B := (⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ)) (A := A)
          (.mp h (.exportation .and_weak))))
        = MRealizer.mp cm (MRealizer.iComb cm (⊥ᶠ →ᶠ ⊥ᶠ))
            (.forallRule cm (.mp cm (ms h) (MRealizer.kComb cm _ _)))
      rfl
  | A₀ :: Δ, ρ, A, h => by
      change ms (seq_mp (Δ := Δ) (seq_of_thm (Δ := Δ) forall_imp_pull)
          (seq_allI (Δ := Δ) (A := Formula.weakenBy ρ A₀ →ᶠ A) h))
        = MRealizer.seqMp eqxi spremise cm Δ
            (MRealizer.seqOfThm cm Δ (MRealizer.fipComb eqxi spremise cm ρ A₀ A))
            (MRealizer.seqAllI eqxi spremise cm Δ (A := Formula.weakenBy ρ A₀ →ᶠ A) (ms h))
      rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ, ms_seq_allI Δ]
      rfl

/-- **`seq_cast` commutes**: a transport along `congrArg (pack Δ) h`. -/
@[mfi_memo] theorem ms_seq_cast {Δ : HCtx F Γ} {Y Z : Formula F Γ} (h : Y = Z)
    (d : Seq F Allowed.extended P Δ Y) :
    ms (seq_cast h d) = MRealizer.transport (congrArg (pack Δ) h) (ms d) := by
  subst h; rfl

/-- **`seq_mono` commutes** (it is `seq_mp (seq_of_thm h)`). -/
@[mfi_memo] theorem ms_seq_mono {Δ : HCtx F Γ} {A A' : Formula F Γ}
    (h : Derivable F Allowed.extended P (A →ᶠ A')) (d : Seq F Allowed.extended P Δ A) :
    ms (seq_mono h d)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms h)) (ms d) := by
  change ms (seq_mp (seq_of_thm h) d) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]

/-- **`seq_induction` commutes**, Δ-generically, with the inducted formula generalised. -/
@[mfi_memo] theorem ms_seq_induction : ∀ (Δ : HCtx F Γ) {A : Formula F (Ty.nat :: Γ)}
    (base : Seq F Allowed.extended P Δ (A.subst0 Term.zero))
    (step : Seq F Allowed.extended P Δ
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0))),
    ms (seq_induction base step)
      = MRealizer.seqInduction eqxi spremise cm Δ (ms base) (ms step)
  | [],      _, _,    _    => rfl
  | A₀ :: Δ, A, base, step => by
      rw [seq_induction, MRealizer.seqInduction]
      simp only [ms_seq_mono eqxi spremise cm, ms_seq_cast eqxi spremise cm, ms_seq_induction Δ]
      rfl

-- ============================================================================
-- The cast entry for `Eq.mp (congrArg (Derivable F al P ·) hB) d`
-- ============================================================================

/-- The shape `qfer_at_nf`/`qfer_nat_nf`/`qfer_no_premise_*_nf`/`lam*_correct_nf`/
`forall_ax_vz`/`forall_ax_inst` leave: the formula equation is *in* the term, so this fires
with nothing supplied. -/
@[mfi_memo] theorem ms_eqmp_congr {B B' : Formula F Γ} (hB : B = B')
    (d : Derivable F Allowed.extended P B) :
    ms (Eq.mp (congrArg (Derivable F Allowed.extended P ·) hB) d)
      = MRealizer.transport hB (ms d) := by
  subst hB; rfl

/-- The same for `Eq.mpr`. -/
@[mfi_memo] theorem ms_eqmpr_congr {B B' : Formula F Γ} (hB : B = B')
    (d : Derivable F Allowed.extended P B') :
    ms (Eq.mpr (congrArg (Derivable F Allowed.extended P ·) hB) d)
      = MRealizer.transport hB.symm (ms d) := by
  subst hB; rfl

-- ============================================================================
-- The derived `seq_*` and the `pm_*` layer: `rfl` restatements
-- ============================================================================

/-! Each of these is definitional; they are stated so that `simp only [mfi_memo]` rewrites a
tactic-written term to the primitives above in one pass. `SeqD` is reducible, so a `pm_*`
term's implicit formula is `pack Δ B`, exactly what the primitives' statements carry. -/

section Derived
variable {ns : List String}

@[mfi_memo] theorem ms_seq_intro {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P (A :: Δ) B) : ms (seq_intro h) = ms h := rfl
@[mfi_memo] theorem ms_seq_revert {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ (A →ᶠ B)) : ms (seq_revert (A := A) h) = ms h := rfl
@[mfi_memo] theorem ms_seq_cut {Δ : HCtx F Γ} {A B : Formula F Γ}
    (hA : Seq F Allowed.extended P Δ A) (hB : Seq F Allowed.extended P (A :: Δ) B) :
    ms (seq_cut hA hB) = MRealizer.seqMp eqxi spremise cm Δ (ms hB) (ms hA) :=
  ms_seq_mp eqxi spremise cm Δ hB hA
@[mfi_memo] theorem ms_seq_lift₂ {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : Derivable F Allowed.extended P (A →ᶠ B →ᶠ C))
    (hA : Seq F Allowed.extended P Δ A) (hB : Seq F Allowed.extended P Δ B) :
    ms (seq_lift₂ h hA hB)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms h)) (ms hA))
          (ms hB) := by
  change ms (seq_mp (seq_mp (seq_of_thm h) hA) hB) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
@[mfi_memo] theorem ms_seq_lift₃ {Δ : HCtx F Γ} {A B C D : Formula F Γ}
    (h : Derivable F Allowed.extended P (A →ᶠ B →ᶠ C →ᶠ D))
    (hA : Seq F Allowed.extended P Δ A) (hB : Seq F Allowed.extended P Δ B)
    (hC : Seq F Allowed.extended P Δ C) :
    ms (seq_lift₃ h hA hB hC)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms h)) (ms hA)) (ms hB))
          (ms hC) := by
  change ms (seq_mp (seq_mp (seq_mp (seq_of_thm h) hA) hB) hC) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ,
    ms_seq_of_thm eqxi spremise cm Δ]
@[mfi_memo] theorem ms_seq_andI {Δ : HCtx F Γ} {A B : Formula F Γ}
    (hA : Seq F Allowed.extended P Δ A) (hB : Seq F Allowed.extended P Δ B) :
    ms (seq_andI hA hB)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (ms and_intro)) (ms hA)) (ms hB) :=
  ms_seq_lift₂ eqxi spremise cm and_intro hA hB
@[mfi_memo] theorem ms_seq_andE₁ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ (A ∧ᶠ B)) :
    ms (seq_andE₁ h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms and_proj1)) (ms h) :=
  ms_seq_mono eqxi spremise cm and_proj1 h
@[mfi_memo] theorem ms_seq_andE₂ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ (A ∧ᶠ B)) :
    ms (seq_andE₂ h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms and_proj2)) (ms h) :=
  ms_seq_mono eqxi spremise cm and_proj2 h
@[mfi_memo] theorem ms_seq_orI₁ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ A) :
    ms (seq_orI₁ (B := B) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms .or_weak)) (ms h) :=
  ms_seq_mono eqxi spremise cm .or_weak h
@[mfi_memo] theorem ms_seq_orI₂ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ B) :
    ms (seq_orI₂ (A := A) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms or_inr)) (ms h) :=
  ms_seq_mono eqxi spremise cm or_inr h
@[mfi_memo] theorem ms_seq_orE {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : Seq F Allowed.extended P Δ (A ∨ᶠ B))
    (hA : Seq F Allowed.extended P (A :: Δ) C) (hB : Seq F Allowed.extended P (B :: Δ) C) :
    ms (seq_orE hAB hA hB)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms or_elim_internal))
            (ms hA)) (ms hB)) (ms hAB) :=
  ms_seq_lift₃ eqxi spremise cm or_elim_internal hA hB hAB
@[mfi_memo] theorem ms_seq_exfalso {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : Seq F Allowed.extended P Δ ⊥ᶠ) :
    ms (seq_exfalso (A := A) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms .exfalso)) (ms h) :=
  ms_seq_mono eqxi spremise cm .exfalso h
@[mfi_memo] theorem ms_seq_weaken {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P Δ B) :
    ms (seq_weaken (A := A) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms K_comb)) (ms h) :=
  ms_seq_mono eqxi spremise cm K_comb h
@[mfi_memo] theorem ms_seq_contract {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : Seq F Allowed.extended P (A :: A :: Δ) B) :
    ms (seq_contract h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms contract)) (ms h) :=
  ms_seq_mono eqxi spremise cm contract h
@[mfi_memo] theorem ms_seq_exchange {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : Seq F Allowed.extended P (A :: B :: Δ) C) :
    ms (seq_exchange h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms flip_comb)) (ms h) :=
  ms_seq_mono eqxi spremise cm flip_comb h
@[mfi_memo] theorem ms_seq_allE {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F Allowed.extended P Δ (Formula.all ρ A)) (t : Term F Γ ρ) :
    ms (seq_allE h t)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sForallAx t))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.forall_ax t) h
@[mfi_memo] theorem ms_seq_allE_here {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : Seq F Allowed.extended P Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    ms (seq_allE_here h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms forall_ax_vz)) (ms h) :=
  ms_seq_mono eqxi spremise cm forall_ax_vz h
@[mfi_memo] theorem ms_seq_exI {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F Allowed.extended P Δ (A.subst0 t)) :
    ms (seq_exI t h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sExistAx t))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.exist_ax t A) h
@[mfi_memo] theorem ms_seq_bound {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F Allowed.extended P Δ (A.subst0 t)) :
    ms (seq_bound t h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sExistAx t))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.exist_ax t A) h
@[mfi_memo] theorem ms_seq_exE {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} {B : Formula F Γ}
    (hex : Seq F Allowed.extended P Δ (Formula.ex ρ A))
    (hbody : Seq F Allowed.extended P (A :: Δ.map (Formula.weakenBy ρ)) (Formula.weakenBy ρ B)) :
    ms (seq_exE hex hbody)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (MRealizer.eipComb eqxi spremise cm ρ B A))
          (MRealizer.seqAllI eqxi spremise cm Δ (A := A →ᶠ Formula.weakenBy ρ B) (ms hbody)))
          (ms hex) := by
  change ms (seq_mp (seq_mp (seq_of_thm exist_imp_pull) (seq_allI (Δ := Δ) hbody)) hex) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ,
    ms_seq_allI eqxi spremise cm Δ]
  rfl

-- the `pm_*` wrappers (`Tactics.lean`), each definitionally one of the above
@[mfi_memo] theorem ms_pm_enter {A : Formula F Γ} (h : SeqD [] F Allowed.extended P [] A) :
    ms (pm_enter h) = ms h := rfl
@[mfi_memo] theorem ms_pm_intro (nm : String) {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD (nm :: ns) F Allowed.extended P (A :: Δ) B) :
    ms (pm_intro (ns := ns) nm h) = ms h := rfl
@[mfi_memo] theorem ms_pm_rename {ns' : List String} {Δ : HCtx F Γ} {B : Formula F Γ}
    (h : SeqD ns' F Allowed.extended P Δ B) : ms (pm_rename (ns := ns) h) = ms h := rfl
@[mfi_memo] theorem ms_pm_revert {n : String} {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ (A →ᶠ B)) :
    ms (pm_revert (n := n) h) = ms h := rfl
@[mfi_memo] theorem ms_pm_have {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : Derivable F Allowed.extended P A) :
    ms (pm_have (ns := ns) (Δ := Δ) h) = MRealizer.seqOfThm cm Δ (ms h) :=
  ms_seq_of_thm eqxi spremise cm Δ h
@[mfi_memo] theorem ms_pm_mp {Δ : HCtx F Γ} {A B : Formula F Γ}
    (hAB : SeqD ns F Allowed.extended P Δ (A →ᶠ B)) (hA : SeqD ns F Allowed.extended P Δ A) :
    ms (pm_mp hAB hA) = MRealizer.seqMp eqxi spremise cm Δ (ms hAB) (ms hA) :=
  ms_seq_mp eqxi spremise cm Δ hAB hA
@[mfi_memo] theorem ms_pm_cut (nm : String) {Δ : HCtx F Γ} {A C : Formula F Γ}
    (hA : SeqD ns F Allowed.extended P Δ A)
    (k : SeqD (nm :: ns) F Allowed.extended P (A :: Δ) C) :
    ms (pm_cut nm hA k) = MRealizer.seqMp eqxi spremise cm Δ (ms k) (ms hA) :=
  ms_seq_mp eqxi spremise cm Δ k hA
@[mfi_memo] theorem ms_pm_split {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h₁ : SeqD ns F Allowed.extended P Δ A) (h₂ : SeqD ns F Allowed.extended P Δ B) :
    ms (pm_split h₁ h₂)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (ms and_intro)) (ms h₁)) (ms h₂) :=
  ms_seq_lift₂ eqxi spremise cm and_intro h₁ h₂
@[mfi_memo] theorem ms_pm_left {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ A) :
    ms (pm_left (B := B) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms .or_weak)) (ms h) :=
  ms_seq_mono eqxi spremise cm .or_weak h
@[mfi_memo] theorem ms_pm_right {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ B) :
    ms (pm_right (A := A) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms or_inr)) (ms h) :=
  ms_seq_mono eqxi spremise cm or_inr h
@[mfi_memo] theorem ms_pm_cases (nm m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F Allowed.extended P Δ (A ∨ᶠ B))
    (h₁ : SeqD (nm :: ns) F Allowed.extended P (A :: Δ) C)
    (h₂ : SeqD (m :: ns) F Allowed.extended P (B :: Δ) C) :
    ms (pm_cases nm m hAB h₁ h₂)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms or_elim_internal))
            (ms h₁)) (ms h₂)) (ms hAB) :=
  ms_seq_lift₃ eqxi spremise cm or_elim_internal h₁ h₂ hAB
@[mfi_memo] theorem ms_pm_andE₁ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ (A ∧ᶠ B)) :
    ms (pm_andE₁ h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms and_proj1)) (ms h) :=
  ms_seq_mono eqxi spremise cm and_proj1 h
@[mfi_memo] theorem ms_pm_andE₂ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ (A ∧ᶠ B)) :
    ms (pm_andE₂ h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms and_proj2)) (ms h) :=
  ms_seq_mono eqxi spremise cm and_proj2 h
@[mfi_memo] theorem ms_pm_andcut (nm m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F Allowed.extended P Δ (A ∧ᶠ B))
    (k : SeqD (nm :: m :: ns) F Allowed.extended P (A :: B :: Δ) C) :
    ms (pm_andcut nm m hAB k)
      = MRealizer.seqMp eqxi spremise cm Δ (A := B) (B := C)
          (MRealizer.seqMp eqxi spremise cm (B :: Δ) (A := A) (B := C) (ms k)
            (MRealizer.seqMp eqxi spremise cm (B :: Δ) (A := A ∧ᶠ B) (B := A)
              (MRealizer.seqOfThm cm (B :: Δ) (ms and_proj1))
              (MRealizer.seqMp eqxi spremise cm Δ (A := A ∧ᶠ B) (B := B →ᶠ A ∧ᶠ B)
                (MRealizer.seqOfThm cm Δ (ms K_comb)) (ms hAB))))
          (MRealizer.seqMp eqxi spremise cm Δ (A := A ∧ᶠ B) (B := B)
            (MRealizer.seqOfThm cm Δ (ms and_proj2)) (ms hAB)) := by
  change ms (seq_mp (Δ := Δ) (A := B) (B := C)
      (seq_mp (Δ := B :: Δ) (A := A) (B := C) k
        (seq_mp (Δ := B :: Δ) (A := A ∧ᶠ B) (B := A) (seq_of_thm and_proj1)
          (seq_mp (Δ := Δ) (A := A ∧ᶠ B) (B := B →ᶠ A ∧ᶠ B) (seq_of_thm K_comb) hAB)))
      (seq_mp (Δ := Δ) (A := A ∧ᶠ B) (B := B) (seq_of_thm and_proj2) hAB)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm (B :: Δ),
    ms_seq_mp eqxi spremise cm (B :: Δ), ms_seq_mp eqxi spremise cm Δ,
    ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm (B :: Δ),
    ms_seq_of_thm eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
@[mfi_memo] theorem ms_pm_exfalso {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ ⊥ᶠ) :
    ms (pm_exfalso (A := A) h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms .exfalso)) (ms h) :=
  ms_seq_mono eqxi spremise cm .exfalso h
@[mfi_memo] theorem ms_pm_conj (nm : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hA : SeqD ns F Allowed.extended P Δ A) (hB : SeqD ns F Allowed.extended P Δ B)
    (k : SeqD (nm :: ns) F Allowed.extended P ((A ∧ᶠ B) :: Δ) C) :
    ms (pm_conj nm hA hB k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
            (MRealizer.seqOfThm cm Δ (ms and_intro)) (ms hA)) (ms hB)) := by
  change ms (seq_mp k (seq_mp (seq_mp (seq_of_thm and_intro) hA) hB)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ,
    ms_seq_of_thm eqxi spremise cm Δ]
@[mfi_memo] theorem ms_pm_impcut (nm : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ (A →ᶠ B)) (hA : SeqD ns F Allowed.extended P Δ A)
    (k : SeqD (nm :: ns) F Allowed.extended P (B :: Δ) C) :
    ms (pm_impcut nm h hA k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (MRealizer.seqMp eqxi spremise cm Δ (ms h) (ms hA)) := by
  change ms (seq_mp k (seq_mp h hA)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ]
@[mfi_memo] theorem ms_pm_allI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F Allowed.extended P (Δ.map (Formula.weakenBy ρ)) A) :
    ms (pm_allI h) = MRealizer.seqAllI eqxi spremise cm Δ (ms h) :=
  ms_seq_allI eqxi spremise cm Δ h
@[mfi_memo] theorem ms_pm_allE_here {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F Allowed.extended P Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    ms (pm_allE_here h)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms forall_ax_vz)) (ms h) :=
  ms_seq_mono eqxi spremise cm forall_ax_vz h
@[mfi_memo] theorem ms_pm_allE_here_cut (nm : String) {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)}
    {A C : Formula F (ρ :: Γ)}
    (h : SeqD ns F Allowed.extended P Δ (Formula.weakenBy ρ (Formula.all ρ A)))
    (k : SeqD (nm :: ns) F Allowed.extended P (A :: Δ) C) :
    ms (pm_allE_here_cut nm h k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqOfThm cm Δ (ms forall_ax_vz))
            (ms h)) := by
  change ms (seq_mp k (seq_mp (seq_of_thm forall_ax_vz) h)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
@[mfi_memo] theorem ms_pm_exI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F Allowed.extended P Δ (A.subst0 t)) :
    ms (pm_exI t h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sExistAx t))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.exist_ax t A) h
@[mfi_memo] theorem ms_pm_bound {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F Allowed.extended P Δ (A.subst0 t)) :
    ms (pm_bound t h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sExistAx t))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.exist_ax t A) h
@[mfi_memo] theorem ms_pm_exE (nm : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    {B : Formula F Γ}
    (hex : SeqD ns F Allowed.extended P Δ (Formula.ex ρ A))
    (hbody : SeqD (nm :: ns) F Allowed.extended P
      (A :: Δ.map (Formula.weakenBy ρ)) (Formula.weakenBy ρ B)) :
    ms (pm_exE nm hex hbody)
      = MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (MRealizer.eipComb eqxi spremise cm ρ B A))
          (MRealizer.seqAllI eqxi spremise cm Δ (A := A →ᶠ Formula.weakenBy ρ B) (ms hbody)))
          (ms hex) :=
  ms_seq_exE eqxi spremise cm hex hbody
@[mfi_memo] theorem ms_pm_inst (nm : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    {C : Formula F Γ} (t : Term F Γ ρ) (h : SeqD ns F Allowed.extended P Δ (Formula.all ρ A))
    (k : SeqD (nm :: ns) F Allowed.extended P (A.subst0 t :: Δ) C) :
    ms (pm_inst nm t h k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (MRealizer.seqMp eqxi spremise cm Δ
            (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sForallAx t))) (ms h)) := by
  change ms (seq_mp k (seq_mp (seq_of_thm (.forall_ax t)) h)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
  rfl
@[mfi_memo] theorem ms_pm_refl {Δ : HCtx F Γ} {t : Term F Γ Ty.nat} :
    ms (pm_refl (ns := ns) (Δ := Δ) (t := t) : SeqD ns F Allowed.extended P Δ _)
      = MRealizer.seqOfThm cm Δ (.ofSRealizer cm sRefl0) :=
  ms_seq_of_thm eqxi spremise cm Δ .refl0
@[mfi_memo] theorem ms_pm_sym {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat}
    (h : SeqD ns F Allowed.extended P Δ (Formula.eq0 t s)) :
    ms (pm_sym h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm sSym0)) (ms h) :=
  ms_seq_mono eqxi spremise cm .sym0 h
@[mfi_memo] theorem ms_pm_trans {Δ : HCtx F Γ} {s u : Term F Γ Ty.nat} (t : Term F Γ Ty.nat)
    (h₁ : SeqD ns F Allowed.extended P Δ (Formula.eq0 s t))
    (h₂ : SeqD ns F Allowed.extended P Δ (Formula.eq0 t u)) :
    ms (pm_trans t h₁ h₂)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm sTrans0))
          (MRealizer.seqMp eqxi spremise cm Δ (MRealizer.seqMp eqxi spremise cm Δ
            (MRealizer.seqOfThm cm Δ (ms and_intro)) (ms h₁)) (ms h₂)) := by
  change ms (seq_mp (seq_of_thm .trans0) (seq_mp (seq_mp (seq_of_thm and_intro) h₁) h₂)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ,
    ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
  rfl
@[mfi_memo] theorem ms_pm_rw_at (nm : String) {Δ : HCtx F Γ} {Pt P' Q Q' : Term F Γ Ty.nat}
    {C : Formula F Γ}
    (congP : SeqD ns F Allowed.extended P Δ (Formula.eq0 Pt P'))
    (congQ : SeqD ns F Allowed.extended P Δ (Formula.eq0 Q Q'))
    (hf : SeqD ns F Allowed.extended P Δ (Formula.eq0 Pt Q))
    (k : SeqD (nm :: ns) F Allowed.extended P (Formula.eq0 P' Q' :: Δ) C) :
    ms (pm_rw_at nm congP congQ hf k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (ms (pm_trans Pt (pm_sym congP) (pm_trans Q hf congQ))) :=
  ms_seq_mp eqxi spremise cm Δ k _
@[mfi_memo] theorem ms_pm_sym_at (nm : String) {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat}
    {C : Formula F Γ}
    (h : SeqD ns F Allowed.extended P Δ (Formula.eq0 s t))
    (k : SeqD (nm :: ns) F Allowed.extended P (Formula.eq0 t s :: Δ) C) :
    ms (pm_sym_at nm h k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k) (ms (pm_sym h)) :=
  ms_seq_mp eqxi spremise cm Δ k _
@[mfi_memo] theorem ms_pm_induction {Δ : HCtx F Γ} {A : Formula F (Ty.nat :: Γ)}
    (base : SeqD ns F Allowed.extended P Δ (A.subst0 Term.zero))
    (step : SeqD ns F Allowed.extended P Δ
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0))) :
    ms (pm_induction base step)
      = MRealizer.seqInduction eqxi spremise cm Δ (ms base) (ms step) :=
  ms_seq_induction eqxi spremise cm Δ base step
@[mfi_memo] theorem ms_pm_markov {Δ : HCtx F Γ} {ρ : Ty ι} {A₀ : Formula F (ρ :: Γ)}
    (hm : Allowed.extended.markov = true) (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : SeqD ns F Allowed.extended P Δ (¬ᶠ¬ᶠ(Formula.ex ρ A₀))) :
    ms (pm_markov hm hqf hvf h)
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (.ofSRealizer cm (sMarkov hqf hvf))) (ms h) :=
  ms_seq_mono eqxi spremise cm (.markov hm hqf hvf) h
@[mfi_memo] theorem ms_pm_qfac (nm : String) {ρ τ : Ty ι} {Δ : HCtx F Γ}
    {A₀ : Formula F (τ :: ρ :: Γ)} {C : Formula F Γ}
    (hq : Allowed.extended.qfac = true) (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : SeqD ns F Allowed.extended P Δ (Formula.all ρ (Formula.ex τ A₀)))
    (k : SeqD (nm :: ns) F Allowed.extended P
      (Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀)) :: Δ) C) :
    ms (pm_qfac nm hq hqf hvf h k)
      = MRealizer.seqMp eqxi spremise cm Δ (ms k)
          (MRealizer.seqMp eqxi spremise cm Δ
            (MRealizer.seqOfThm cm Δ (.ofSRealizer cm sAC)) (ms h)) := by
  change ms (seq_mp k (seq_mp (seq_of_thm (.qfac hq hqf hvf)) h)) = _
  rw [ms_seq_mp eqxi spremise cm Δ, ms_seq_mp eqxi spremise cm Δ, ms_seq_of_thm eqxi spremise cm Δ]
  rfl

end Derived

end Seq

-- ============================================================================
-- Transport through the REDUCED hat type — what the kernel needs
-- ============================================================================

/-! `MRealizer.transport hB r` casts the majorant along
`Ty.interpret X (wTy B).hat = Ty.interpret X (wTy B').hat`. To reduce that cast the kernel
runs its K-rule, which checks the two sides definitionally equal — and the kernel's
`is_def_eq` on two applications of the same constant tries the **arguments first**, i.e.
`wTy B =?= wTy B'`, i.e. `B =?= B'`: the formula before the normalisation against the formula
after it, a `Term.subst`/`rename` computation through the closed ℚ constants on *both* sides,
whose argument-first attempts at every node make it quadratic (`std::bad_alloc` at 12 GB on
`le_R_pu_of_le_R`, measured with the transports in place). `wTy` itself never
looks at a formula's terms, so this is entirely avoidable: route the cast through the
*reduced* hat type `τ` — a bare `Ty` constructor tree — and the kernel, comparing
`wTy B` against a constructor, can only *evaluate* `wTy B`, never compare two formulas.
`mfiTransportNF` computes `τ` at the elaborator (a `Ty`-level `whnf`) and rewrites every
`transport` in the goal to `transportTo`. -/

section TransportTo

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {cm : ConstMajorants am} {Γ : Ctx ι}

/-- `transport` with the cast routed through an explicit hat type `τ`, meant to be the
constructor-form value of `wTy B'`. -/
def MRealizer.transportTo {B B' : Formula F Γ} (hB : B = B') (τ : Ty ι) (hτ : wTy B' = τ)
    (r : MRealizer cm B) : MRealizer cm B' :=
  ⟨fun n e =>
    cast (congrArg (fun ρ : Ty ι => Ty.interpret X ρ.hat) hτ.symm)
      (cast (congrArg (fun ρ : Ty ι => Ty.interpret X ρ.hat) ((congrArg wTy hB).trans hτ))
        (r.val n e)),
   by subst hB; subst hτ; exact r.property⟩

theorem MRealizer.transport_eq_transportTo {B B' : Formula F Γ} (hB : B = B') (τ : Ty ι)
    (hτ : wTy B' = τ) (r : MRealizer cm B) :
    MRealizer.transport hB r = MRealizer.transportTo hB τ hτ r := by
  subst hB; subst hτ; rfl

end TransportTo

open Lean Meta in
/-- Normalise a `Ty`-valued expression to a constructor tree, **with the kernel's `whnf`** at
every node. `Meta.reduce` leaves `wTy _` untouched — measured: the transport was then handed
`τ := wTy B'` verbatim and nothing was gained. Recurses into `arr`/`prod`; the index of
`base` is left as it is. Anything the kernel cannot bring to a constructor is returned as is. -/
partial def tyNF (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let lctx ← getLCtx
  let e' := match Kernel.whnf env lctx e with
    | .ok e' => e'
    | .error _ => e
  match e'.getAppFn with
  | .const n _ =>
    let a := e'.getAppArgs
    if (n == ``Ty.arr || n == ``Ty.prod) && a.size == 3 then
      return mkAppN e'.getAppFn #[a[0]!, ← tyNF a[1]!, ← tyNF a[2]!]
    else return e'
  | _ => return e'

open Lean Meta in
/-- Rewrite `MRealizer.transport hB r` to `MRealizer.transportTo hB τ rfl r` with `τ` the
constructor-tree value of `wTy B'` (`tyNF`). The proof of `wTy B' = τ` is `Eq.refl τ` under an
expected-type hint: the kernel checks it by evaluating `wTy B'` against a constructor tree,
never by comparing two formulas. -/
simproc mfiTransportNF (MRealizer.transport _ _) := fun e => do
  unless e.isAppOfArity ``MRealizer.transport 12 do return .continue
  let args := e.getAppArgs
  let ι := args[0]!; let κ := args[1]!; let F := args[3]!; let Γ := args[7]!
  let B' := args[9]!
  let wB' := mkAppN (mkConst ``wTy) #[ι, κ, F, Γ, B']
  let τ ← tyNF wB'
  let hτ ← mkExpectedTypeHint (← mkEqRefl τ) (← mkEq wB' τ)
  let e' := mkAppN (mkConst ``MRealizer.transportTo) (args[:10] ++ #[args[10]!, τ, hτ, args[11]!])
  let pf := mkAppN (mkConst ``MRealizer.transport_eq_transportTo)
    (args[:10] ++ #[args[10]!, τ, hτ, args[11]!])
  return .done { expr := e', proof? := some pf }

attribute [mfi_memo] mfiTransportNF

-- ============================================================================
-- Casts INSIDE the closed kernel theorems — expose them to the rewrite
-- ============================================================================

/-! The packaging layer's kernel theorems are not cast-free: `forall_ax_vz` is an `Eq.mp`
around `Derivable.forall_ax`, along `(A.renameF (ext shift)).subst0 (var vz) = A`, and
`forall_imp_pull`/`forall_imp_push`/`exist_imp_pull`/`forall_mono` all contain it. Kept folded
(`fipComb := ms forall_imp_pull`), the kernel meets that `Eq.mp` and K-checks its equation —
`substF σ (renameF ρ A) ≡ A`, a linear traversal through every closed ℚ constant of `A`, per
hypothesis carried under a `∀` (measured: `pintro h; pforall; pexact h` over `le_R dxw Tq`
alone is a 12 GB `std::bad_alloc`). So the rewrite must reach *inside* them: the
Δ-recursive combinators unfold at a literal `Δ`, the named combinators unfold to
`monotone_soundness` of their theorem, the theorems unfold, and `forall_ax_vz` gets its own
transport entry. -/

section Expose

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {P : PremiseSet F}
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) {Γ : Ctx ι}

local notation "ms" => monotone_soundness eqxi spremise cm

/-- `forall_ax_vz` is `Eq.mp` of `forall_ax` at `var vz`; its transport, exposed. -/
@[mfi_memo] theorem ms_forall_ax_vz {ρ : Ty ι} {A : Formula F (ρ :: Γ)} :
    ms (forall_ax_vz (a := Allowed.extended) (Premises := P) (ρ := ρ) (A := A))
      = MRealizer.transport
          (congrArg ((Formula.all ρ A).weakenBy ρ →ᶠ ·) (Formula.subst0_weakenUnder A))
          (.ofSRealizer cm (sForallAx (.var .vz))) := by
  unfold forall_ax_vz
  rw [ms_eqmp_congr eqxi spremise cm
    (congrArg ((Formula.all ρ A).weakenBy ρ →ᶠ ·) (Formula.subst0_weakenUnder A))]
  rfl

/-- `Formula.subst0_weakenUnder` with `subst0` unfolded — the shape `ex_and_left`'s cast
carries (`simp only [Formula.subst0] at h` inside it). -/
theorem substF_subst0map_weakenUnder {ρ : Ty ι} (A : Formula F (ρ :: Γ)) :
    Formula.substF (Term.subst0_map (.var .vz : Term F (ρ :: Γ) ρ))
      (Formula.renameF (Term.Renaming.ext Term.Renaming.shift) A) = A :=
  Formula.subst0_weakenUnder A

@[mfi_memo] theorem MRealizer.seqAllI_nil {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : MRealizer cm (pack (([] : HCtx F Γ).map (Formula.weakenBy ρ)) A)) :
    MRealizer.seqAllI eqxi spremise cm [] h
      = .mp cm (MRealizer.iComb cm (⊥ᶠ →ᶠ ⊥ᶠ))
          (.forallRule cm (.mp cm h (MRealizer.kComb cm _ _))) := rfl
@[mfi_memo] theorem MRealizer.seqAllI_cons {ρ : Ty ι} (A₀ : Formula F Γ) (Δ : HCtx F Γ)
    {A : Formula F (ρ :: Γ)}
    (h : MRealizer cm (pack ((A₀ :: Δ).map (Formula.weakenBy ρ)) A)) :
    MRealizer.seqAllI eqxi spremise cm (A₀ :: Δ) h
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (MRealizer.fipComb eqxi spremise cm ρ A₀ A))
          (MRealizer.seqAllI eqxi spremise cm Δ (A := Formula.weakenBy ρ A₀ →ᶠ A) h) := rfl
@[mfi_memo] theorem MRealizer.seqInduction_nil {A : Formula F (Ty.nat :: Γ)}
    (base : MRealizer cm (pack ([] : HCtx F Γ) (A.subst0 Term.zero)))
    (step : MRealizer cm (pack ([] : HCtx F Γ)
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0)))) :
    MRealizer.seqInduction eqxi spremise cm [] base step = .induction cm base step := rfl
@[mfi_memo] theorem MRealizer.seqInduction_cons (A₀ : Formula F Γ) (Δ : HCtx F Γ)
    {A : Formula F (Ty.nat :: Γ)}
    (base : MRealizer cm (pack (A₀ :: Δ) (A.subst0 Term.zero)))
    (step : MRealizer cm (pack (A₀ :: Δ)
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0)))) :
    MRealizer.seqInduction eqxi spremise cm (A₀ :: Δ) base step
      = MRealizer.seqMp eqxi spremise cm Δ
          (MRealizer.seqOfThm cm Δ (MRealizer.fipComb eqxi spremise cm Ty.nat A₀ A))
          (MRealizer.seqInduction eqxi spremise cm Δ (A := Formula.weakenBy Ty.nat A₀ →ᶠ A)
            (.transport (congrArg (pack Δ) (congrArg (· →ᶠ A.subst0 Term.zero)
              (Formula.subst0_weakenBy A₀ Term.zero).symm)) base)
            (.transport (congrArg (pack Δ)
              (congrArg (Formula.all Ty.nat)
                (congrArg (fun Z => (Formula.weakenBy Ty.nat A₀ →ᶠ A) →ᶠ
                    (Z →ᶠ Formula.substVar0 A succVar0))
                  (Formula.substVar0_weakenBy A₀ succVar0).symm)))
              (MRealizer.seqMp eqxi spremise cm Δ
                (MRealizer.seqOfThm cm Δ (MRealizer.fmSComb eqxi spremise cm Ty.nat
                  (Formula.weakenBy Ty.nat A₀) A (Formula.substVar0 A succVar0)))
                (MRealizer.seqMp eqxi spremise cm Δ
                  (MRealizer.seqOfThm cm Δ (MRealizer.fipushComb eqxi spremise cm Ty.nat A₀
                    (A →ᶠ Formula.substVar0 A succVar0)))
                  step)))) := rfl

@[mfi_memo] theorem MRealizer.fipComb_eq (ρ : Ty ι) (B : Formula F Γ) (A : Formula F (ρ :: Γ)) :
    MRealizer.fipComb eqxi spremise cm ρ B A
      = ms (forall_imp_pull (a := Allowed.extended) (Premises := P) (B := B) (A := A)) := rfl
@[mfi_memo] theorem MRealizer.eipComb_eq (ρ : Ty ι) (B : Formula F Γ) (A : Formula F (ρ :: Γ)) :
    MRealizer.eipComb eqxi spremise cm ρ B A
      = ms (exist_imp_pull (a := Allowed.extended) (Premises := P) (B := B) (A := A)) := rfl
@[mfi_memo] theorem MRealizer.fipushComb_eq (ρ : Ty ι) (B : Formula F Γ) (Y : Formula F (ρ :: Γ)) :
    MRealizer.fipushComb eqxi spremise cm ρ B Y
      = ms (forall_imp_push (a := Allowed.extended) (Premises := P) (B := B) (X := Y)) := rfl
@[mfi_memo] theorem MRealizer.fmSComb_eq (ρ : Ty ι) (A B C : Formula F (ρ :: Γ)) :
    MRealizer.fmSComb eqxi spremise cm ρ A B C
      = ms (forall_mono (a := Allowed.extended) (Premises := P)
          (S_comb (a := Allowed.extended) (Premises := P) (A := A) (B := B) (C := C))) := rfl

end Expose

/-! The kernel theorems themselves unfold under the set, so the rewrite reaches
`forall_ax_vz` inside them. `pair_h` is unfolded because `forall_imp_pull`/`exist_imp_pull`
pass `forall_ax_vz` through it; `S_comb`, `I_comb`, `K_comb`, `and_proj*`, `mp_form` are
cast-free and stay folded. -/
attribute [mfi_memo] forall_imp_pull forall_imp_push exist_imp_pull forall_mono imp_mono_right
  pair_h

/-! **`monotone_soundness`'s own equations, as theorems.** The recursion must reach the raw
constructors *propositionally*: `simp only [monotone_soundness]` (the unfold target) reduces
by smart unfolding, which at `ms (Eq.mp e d)` runs Meta's K-rule through the cast once and
hands the kernel a *definitional* step it must re-run — the 12 GB `std::bad_alloc` on
`pintro h; pforall; pexact h`. The equation theorems below carry explicit proofs
when simp is run with `implicitDefEqProofs := false`; that pass kernel-checks in milliseconds
on the same derivation. So: **never pass `monotone_soundness` itself to `simp`; use the set,
with `(config := { implicitDefEqProofs := false })`.** -/
attribute [mfi_memo] monotone_soundness.eq_1 monotone_soundness.eq_2 monotone_soundness.eq_3
  monotone_soundness.eq_4 monotone_soundness.eq_5 monotone_soundness.eq_6 monotone_soundness.eq_7
  monotone_soundness.eq_8 monotone_soundness.eq_9 monotone_soundness.eq_10
  monotone_soundness.eq_11 monotone_soundness.eq_12 monotone_soundness.eq_13
  monotone_soundness.eq_14 monotone_soundness.eq_15 monotone_soundness.eq_16
  monotone_soundness.eq_17 monotone_soundness.eq_18 monotone_soundness.eq_19
  monotone_soundness.eq_20 monotone_soundness.eq_21 monotone_soundness.eq_22
  monotone_soundness.eq_23 monotone_soundness.eq_24 monotone_soundness.eq_25
  monotone_soundness.eq_26 monotone_soundness.eq_27 monotone_soundness.eq_28
  monotone_soundness.eq_29 monotone_soundness.eq_30 monotone_soundness.eq_31
  monotone_soundness.eq_32 monotone_soundness.eq_33 monotone_soundness.eq_34
  monotone_soundness.eq_35 monotone_soundness.eq_36 monotone_soundness.eq_37
  monotone_soundness.eq_38 monotone_soundness.eq_39

/-! The three cast entries of `MonotoneMemo.lean` belong to the set. **Not**
`MRealizer.transport_rfl`: as a rewrite rule its implicit `B'` unifies with `B` at default
transparency, which is exactly the comparison of a formula before and after normalisation
that the casts exist to avoid — measured as an `isDefEq` heartbeat timeout inside `simp`. -/
attribute [mfi_memo] monotone_soundness_eqmpr monotone_soundness_eqmp monotone_soundness_subst

section ExAndLeft

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {P : PremiseSet F}
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) {Γ : Ctx ι}

local notation "ms" => monotone_soundness eqxi spremise cm

/-- `ex_and_left` (inside `exist_imp_pull`, i.e. under every `pobtain`) is
`importation (exist_rule (exportation (Eq.mp _ (exist_ax (var vz) _))))`; its transport,
exposed. Placed after the equation theorems are in the set, which the proof runs — without the
`transportTo` simproc (the two transports differ only in their proof) — discharging the one side
condition with `substF_subst0map_weakenUnder`. -/
@[mfi_memo] theorem ms_ex_and_left {ρ : Ty ι} {A : Formula F (ρ :: Γ)} {B : Formula F Γ} :
    ms (ex_and_left (a := Allowed.extended) (Premises := P) (A := A) (B := B))
      = .importation cm (.existRule cm (.exportation cm
          (MRealizer.transport
            (congrArg (· →ᶠ Formula.ex ρ (Formula.renameF (Term.Renaming.ext Term.Renaming.shift)
              (A ∧ᶠ Formula.weakenBy ρ B)))
              (substF_subst0map_weakenUnder (A ∧ᶠ Formula.weakenBy ρ B)))
            (.ofSRealizer cm (sExistAx
              (A := Formula.renameF (Term.Renaming.ext Term.Renaming.shift)
                (A ∧ᶠ Formula.weakenBy ρ B)) (.var .vz)))))) := by
  unfold ex_and_left
  simp (config := { implicitDefEqProofs := false }) only [mfi_memo, -mfiTransportNF]
  rw [ms_eqmp_congr eqxi spremise cm
    (congrArg (· →ᶠ Formula.ex ρ (Formula.renameF (Term.Renaming.ext Term.Renaming.shift)
      (A ∧ᶠ Formula.weakenBy ρ B)))
      (substF_subst0map_weakenUnder (A ∧ᶠ Formula.weakenBy ρ B)))]
  rfl

end ExAndLeft

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms MRealizer.seqOfThm
#print axioms MRealizer.seqMp
#print axioms MRealizer.seqId
#print axioms MRealizer.seqAllI
#print axioms MRealizer.seqInduction
#print axioms ms_seq_of_thm
#print axioms ms_seq_mp
#print axioms ms_seq_id
#print axioms ms_seq_allI
#print axioms ms_seq_cast
#print axioms ms_seq_mono
#print axioms ms_seq_induction
#print axioms ms_eqmp_congr
#print axioms ms_eqmpr_congr
#print axioms ms_seq_exE
#print axioms ms_pm_andcut
#print axioms ms_pm_induction

end Metatheorems
