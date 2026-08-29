/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.PureFOLLemmas

namespace Metatheorems
namespace ProofMode

/-!
# The packaging kit

`Derivable` is Hilbert-style: `Γ` is the *term-variable* context, not a list of assumed
formulas, and there is no assumption mechanism at all. A proof mode therefore cannot target
the kernel directly. This file builds the derived sequent layer it targets instead.

A hypothesis context is reified as a list of formulas and a sequent is *packaged* into a
nested implication:

    Δ = [A₁, …, Aₙ]  ⊢  B     means     ⊢ Aₙ →ᶠ … →ᶠ A₁ →ᶠ B

Every lemma below is an ordinary Lean function producing a kernel derivation. The kernel is
frozen; no tactic ever constructs kernel terms directly.

## Deviation from the handoff, deliberate

The handoff specifies `pack Δ B := Δ.foldr (· →ᶠ ·) B`, under which the *head* of `Δ` is
the *outermost* antecedent. With that convention `Seq (A :: Δ) B` and `Seq Δ (A →ᶠ B)`
differ by a permutation of antecedents, so `intro` and `revert` each cost an exchange
lemma — contradicting the handoff's own "they are the identity".

Folding the other way — the head of `Δ` is the *innermost* antecedent, i.e. the most
recently introduced hypothesis — makes

    Seq (A :: Δ) B   and   Seq Δ (A →ᶠ B)

*definitionally equal*, so `seq_intro` and `seq_revert` really are `id`. That also makes
`HVar` indexing agree with the usual de Bruijn convention (index 0 = most recent). The
display layer reverses `Δ` for presentation; nothing else is affected.

## Names

Names live only in the tactic state, never in `Seq`. This layer sees positions.
-/

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

open Formula

/-- `⊢ B →ᶠ A` from `⊢ A`. (Private copies: the originals are private in both
`PureFOLLemmas` and `Arithmetic`, and this file should not import the latter.) -/
private def weaken_intro_h {Γ : Ctx ι} {A B : Formula F Γ}
    (h : Derivable F EqX a Premises A) : Derivable F EqX a Premises (B →ᶠ A) :=
  .mp h (.exportation .and_weak)

/-- The reified hypothesis context: formulas in the same term context. -/
abbrev HCtx (F : ι → Ty ι) (Γ : Ctx ι) := List (Formula F Γ)

/-- Package a hypothesis context into nested implications. The head of `Δ` becomes the
innermost antecedent. -/
def pack : HCtx F Γ → Formula F Γ → Formula F Γ
  | [],     B => B
  | A :: Δ, B => pack Δ (A →ᶠ B)

/-- The sequent judgment. -/
abbrev Seq (F : ι → Ty ι)
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ)
    (a : Allowed) (Premises : PremiseSet F) {Γ : Ctx ι}
    (Δ : HCtx F Γ) (B : Formula F Γ) : Type :=
  Derivable F EqX a Premises (pack Δ B)

-- ============================================================================
-- The two primitives everything else is built from
-- ============================================================================

/-- A theorem holds in any hypothesis context. -/
def seq_of_thm : {Δ : HCtx F Γ} → {B : Formula F Γ} →
    Derivable F EqX a Premises B → Seq F EqX a Premises Δ B
  | [],     _, h => h
  | A :: Δ, B, h => seq_of_thm (Δ := Δ) (B := A →ᶠ B) (weaken_intro_h h)

/-- Modus ponens, in context. Proved by recursion on `Δ`: at each step the goal is an
implication with the same antecedent on both sides, so `S_comb` does the work. -/
def seq_mp : {Δ : HCtx F Γ} → {A B : Formula F Γ} →
    Seq F EqX a Premises Δ (A →ᶠ B) → Seq F EqX a Premises Δ A →
    Seq F EqX a Premises Δ B
  | [],      _, _, hAB, hA => .mp hA hAB
  | A₀ :: Δ, A, B, hAB, hA =>
      -- `Seq (A₀ :: Δ) X` is `Seq Δ (A₀ →ᶠ X)`; distribute the antecedent with `S_comb`.
      seq_mp (Δ := Δ) (A := A₀ →ᶠ A) (B := A₀ →ᶠ B)
        (seq_mp (Δ := Δ) (A := A₀ →ᶠ A →ᶠ B) (B := (A₀ →ᶠ A) →ᶠ A₀ →ᶠ B)
          (seq_of_thm (S_comb (A := A₀) (B := A) (C := B))) hAB)
        hA

-- ============================================================================
-- Derived plumbing
-- ============================================================================

/-- Weaken the goal along a theorem. -/
def seq_mono {Δ : HCtx F Γ} {A A' : Formula F Γ}
    (h : Derivable F EqX a Premises (A →ᶠ A')) :
    Seq F EqX a Premises Δ A → Seq F EqX a Premises Δ A' :=
  seq_mp (seq_of_thm h)

/-- Apply a two-premise theorem in context. -/
def seq_lift₂ {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : Derivable F EqX a Premises (A →ᶠ B →ᶠ C)) :
    Seq F EqX a Premises Δ A → Seq F EqX a Premises Δ B → Seq F EqX a Premises Δ C :=
  fun hA hB => seq_mp (seq_mp (seq_of_thm h) hA) hB

/-- Apply a three-premise theorem in context. -/
def seq_lift₃ {Δ : HCtx F Γ} {A B C D : Formula F Γ}
    (h : Derivable F EqX a Premises (A →ᶠ B →ᶠ C →ᶠ D)) :
    Seq F EqX a Premises Δ A → Seq F EqX a Premises Δ B →
    Seq F EqX a Premises Δ C → Seq F EqX a Premises Δ D :=
  fun hA hB hC => seq_mp (seq_mp (seq_mp (seq_of_thm h) hA) hB) hC

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Introduce a hypothesis. Definitionally the identity — see the note above. -/
def seq_intro {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises (A :: Δ) B → Seq F EqX a Premises Δ (A →ᶠ B) := id

/-- Revert a hypothesis. Definitionally the identity. -/
def seq_revert {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ (A →ᶠ B) → Seq F EqX a Premises (A :: Δ) B := id

/-- A de Bruijn index into the hypothesis context: `hz` is the most recent hypothesis. -/
inductive HVar : HCtx F Γ → Formula F Γ → Type
  | hz {Δ : HCtx F Γ} {A : Formula F Γ} : HVar (A :: Δ) A
  | hs {Δ : HCtx F Γ} {A B : Formula F Γ} : HVar Δ A → HVar (B :: Δ) A

/-- Hypothesis lookup. -/
def seq_id : {Δ : HCtx F Γ} → {A : Formula F Γ} →
    HVar Δ A → Seq F EqX a Premises Δ A
  | A :: Δ, _, .hz    => seq_of_thm (Δ := Δ) (B := A →ᶠ A) I_comb
  | B :: Δ, A, .hs v  =>
      seq_mono (Δ := Δ) (A := A) (A' := B →ᶠ A) K_comb (seq_id (Δ := Δ) v)

/-- Add an unused hypothesis. -/
def seq_weaken {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ B → Seq F EqX a Premises (A :: Δ) B :=
  seq_mono K_comb

/-- Contract a duplicated hypothesis. -/
def seq_contract {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises (A :: A :: Δ) B → Seq F EqX a Premises (A :: Δ) B :=
  seq_mono contract

/-- Exchange the two most recent hypotheses. -/
def seq_exchange {Δ : HCtx F Γ} {A B C : Formula F Γ} :
    Seq F EqX a Premises (A :: B :: Δ) C → Seq F EqX a Premises (B :: A :: Δ) C :=
  seq_mono flip_comb

/-- Drop a hypothesis from *anywhere* in the context.

`seq_weaken` only reaches the most recent hypothesis. The general case is a recursion on the
part of the context above the one being dropped: `Seq (C :: Δ) B` is `Seq Δ (C →ᶠ B)`, so
peeling `Δ₁` moves those hypotheses into the goal formula and leaves the target position at
the top, where `seq_weaken` applies. -/
def seq_clear : (Δ₁ : HCtx F Γ) → {A : Formula F Γ} → {Δ₂ : HCtx F Γ} → {B : Formula F Γ} →
    Seq F EqX a Premises (Δ₁ ++ Δ₂) B → Seq F EqX a Premises (Δ₁ ++ A :: Δ₂) B
  | [],      _, _, _, h => seq_weaken h
  | C :: Δ₁, A, Δ₂, B, h => seq_clear (A := A) Δ₁ (Δ₂ := Δ₂) (B := C →ᶠ B) h

/-- Exchange two adjacent hypotheses *anywhere* in the context. Same recursion. -/
def seq_swap : (Δ₁ : HCtx F Γ) → {A B : Formula F Γ} → {Δ₂ : HCtx F Γ} → {C : Formula F Γ} →
    Seq F EqX a Premises (Δ₁ ++ A :: B :: Δ₂) C →
    Seq F EqX a Premises (Δ₁ ++ B :: A :: Δ₂) C
  | [],      _, _, _, _, h => seq_exchange h
  | D :: Δ₁, A, B, Δ₂, C, h => seq_swap (A := A) (B := B) Δ₁ (Δ₂ := Δ₂) (C := D →ᶠ C) h

/-- Cut. -/
def seq_cut {Δ : HCtx F Γ} {A B : Formula F Γ}
    (hA : Seq F EqX a Premises Δ A) (hB : Seq F EqX a Premises (A :: Δ) B) :
    Seq F EqX a Premises Δ B :=
  seq_mp (seq_intro hB) hA

-- ============================================================================
-- Conjunction, disjunction, absurdity
-- ============================================================================

def seq_andI {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ A → Seq F EqX a Premises Δ B →
    Seq F EqX a Premises Δ (A ∧ᶠ B) :=
  seq_lift₂ and_intro

def seq_andE₁ {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ (A ∧ᶠ B) → Seq F EqX a Premises Δ A :=
  seq_mono and_proj1

def seq_andE₂ {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ (A ∧ᶠ B) → Seq F EqX a Premises Δ B :=
  seq_mono and_proj2

def seq_orI₁ {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ A → Seq F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_mono .or_weak

def seq_orI₂ {Δ : HCtx F Γ} {A B : Formula F Γ} :
    Seq F EqX a Premises Δ B → Seq F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_mono or_inr

/-- `∨`-elimination, internalized: `(A → C) → (B → C) → (A ∨ B) → C`.

The kernel's `or_elim_rule` acts on derivations, not under an implication, so the
internal form has to be derived. Distributing the hypothesis over the disjunction is
what makes it go through. -/
def or_elim_internal {Γ : Ctx ι} {A B C : Formula F Γ} :
    Derivable F EqX a Premises ((A →ᶠ C) →ᶠ (B →ᶠ C) →ᶠ (A ∨ᶠ B) →ᶠ C) := by
  -- with `H := (A →ᶠ C) ∧ᶠ (B →ᶠ C)`, distribute `H` over `A ∨ᶠ B`
  refine .exportation (.exportation ?_)
  refine .syllogism and_or_dist (or_elim_rule ?_ ?_)
  · -- ((A →ᶠ C) ∧ᶠ (B →ᶠ C)) ∧ᶠ A ⊢ C
    exact .importation (.syllogism .and_weak mp_form)
  · -- ((A →ᶠ C) ∧ᶠ (B →ᶠ C)) ∧ᶠ B ⊢ C
    exact .importation (.syllogism and_proj2 mp_form)

def seq_orE {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : Seq F EqX a Premises Δ (A ∨ᶠ B))
    (hA : Seq F EqX a Premises (A :: Δ) C)
    (hB : Seq F EqX a Premises (B :: Δ) C) :
    Seq F EqX a Premises Δ C :=
  seq_lift₃ or_elim_internal (seq_intro hA) (seq_intro hB) hAB

def seq_exfalso {Δ : HCtx F Γ} {A : Formula F Γ} :
    Seq F EqX a Premises Δ ⊥ᶠ → Seq F EqX a Premises Δ A :=
  seq_mono .exfalso

-- ============================================================================
-- Quantifiers
-- ============================================================================

/-- Pull a `∀` out past a hypothesis that does not mention the bound variable.

This is what makes `seq_allI` work: the kernel's `forall_rule` carries exactly one side
formula, so introducing a `∀` under a whole hypothesis context means peeling the context
one hypothesis at a time through this. -/
def forall_imp_pull {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises
      (Formula.all ρ (Formula.weakenBy ρ B →ᶠ A) →ᶠ (B →ᶠ Formula.all ρ A)) :=
  .exportation (.forall_rule
    (.syllogism (pair_h (.syllogism .and_weak
        (forall_ax_vz (ρ := ρ) (A := Formula.weakenBy ρ B →ᶠ A))) and_proj2)
      (.importation mp_form)))

/-- `∀`-introduction. The eigenvariable condition is discharged by the indices: the whole
hypothesis context weakens into `ρ :: Γ`, so nothing in `Δ` can mention the new variable. -/
def seq_allI {ρ : Ty ι} : {Δ : HCtx F Γ} → {A : Formula F (ρ :: Γ)} →
    Seq F EqX a Premises (Δ.map (Formula.weakenBy ρ)) A →
    Seq F EqX a Premises Δ (Formula.all ρ A)
  | [],      A, h =>
      have taut : Derivable F EqX a Premises ((⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ)) := I_comb
      .mp taut (.forall_rule (B := (⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ)) (A := A)
        (weaken_intro_h (B := Formula.weakenBy ρ (⊥ᶠ →ᶠ ⊥ᶠ)) h))
  | A₀ :: Δ, A, h =>
      seq_mono (Δ := Δ) (A := Formula.all ρ (Formula.weakenBy ρ A₀ →ᶠ A))
        (A' := A₀ →ᶠ Formula.all ρ A) forall_imp_pull
        (seq_allI (Δ := Δ) (A := Formula.weakenBy ρ A₀ →ᶠ A) h)

/-- `∀`-elimination. -/
def seq_allE {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F EqX a Premises Δ (Formula.all ρ A)) (t : Term F Γ ρ) :
    Seq F EqX a Premises Δ (A.subst0 t) :=
  seq_mono (.forall_ax t) h

/-- Instantiate a weakened `∀` at the bound variable.

After `seq_allI` the context consists of weakened hypotheses; a `∀`-hypothesis among them
is used through this, not through `seq_id`. The tactic layer will want it under `apply`. -/
def seq_allE_here {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : Seq F EqX a Premises Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    Seq F EqX a Premises Δ A :=
  seq_mono forall_ax_vz h

/-- `∃`-introduction. **The sole `∃`-introduction path** — the linter tags this. -/
def seq_exI {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F EqX a Premises Δ (A.subst0 t)) :
    Seq F EqX a Premises Δ (Formula.ex ρ A) :=
  seq_mono (.exist_ax t A) h

/-- Pull an `∃` out past a hypothesis, internalized. -/
def exist_imp_pull {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)} :
    Derivable F EqX a Premises
      (Formula.all ρ (A →ᶠ Formula.weakenBy ρ B) →ᶠ (Formula.ex ρ A →ᶠ B)) :=
  .exportation (.syllogism .and_perm (.syllogism ex_and_left
    (.exist_rule (.syllogism (pair_h (.syllogism and_proj2
        (forall_ax_vz (ρ := ρ) (A := A →ᶠ Formula.weakenBy ρ B))) .and_weak)
      (.importation mp_form)))))

/-- `∃`-elimination. The witness enters as the new outermost term variable, so `Δ` and the
conclusion both weaken. -/
def seq_exE {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} {B : Formula F Γ}
    (hex : Seq F EqX a Premises Δ (Formula.ex ρ A))
    (hbody : Seq F EqX a Premises (A :: Δ.map (Formula.weakenBy ρ)) (Formula.weakenBy ρ B)) :
    Seq F EqX a Premises Δ B :=
  seq_lift₂ exist_imp_pull
    (seq_allI (Δ := Δ) (A := A →ᶠ Formula.weakenBy ρ B) hbody) hex

end ProofMode
end Metatheorems
