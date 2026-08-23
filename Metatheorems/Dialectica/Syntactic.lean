/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs
import Metatheorems.Majorizability

namespace Metatheorems

/-!
# Syntactic Dialectica witnesses

`dialecticaWitness`/`dialecticaCounter` produce Lean *types*, so realizers are Lean values
with no syntax attached. That is what severs the bounding half of the metatheorem: the
majorization lemma (`all_closed_terms_majorizable`) applies to closed `Term`s, and a Lean
function is not one.

Here we mirror those definitions at the object level:

* `wTy A`, `cTy A` — the witness and counter types **as `Ty ι`**;
* `interpret_wTy`, `interpret_cTy` — their interpretations are *definitionally* the
  original Lean types, so nothing downstream needs a cast;
* `syntacticRealizerCtx` — a realizer is a `Term` whose interpretation satisfies the
  (unchanged, semantic) Dialectica matrix.

This is the "syntactic witness, semantic soundness" split: the witness carries syntax, so
it can be majorized; the correctness statement stays where it already is.
-/

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Witness and counter types, object-level
-- ============================================================================

mutual

/-- The *type* `Ty ι` of witnesses for `A`'s Dialectica translation. -/
def wTy : {Γ : Ctx ι} → Formula F Γ → Ty ι
  | _, .bot       => .unit
  | _, .eq0 _ _   => .unit
  | _, .and A B   => wTy A ×ₜ wTy B
  | _, .or  A B   => Ty.nat ×ₜ (wTy A ×ₜ wTy B)
  | _, .imp A B   => (wTy A →ₜ wTy B) ×ₜ (wTy A →ₜ cTy B →ₜ cTy A)
  | _, .ex  ρ A   => ρ ×ₜ wTy A
  | _, .all ρ A   => ρ →ₜ wTy A

/-- The *type* `Ty ι` of counters for `A`'s Dialectica translation. -/
def cTy : {Γ : Ctx ι} → Formula F Γ → Ty ι
  | _, .bot       => .unit
  | _, .eq0 _ _   => .unit
  | _, .and A B   => cTy A ×ₜ cTy B
  | _, .or  A B   => cTy A ×ₜ cTy B
  | _, .imp A B   => wTy A ×ₜ cTy B
  | _, .ex  _ A   => cTy A
  | _, .all ρ A   => ρ ×ₜ cTy A

end

-- ============================================================================
-- The interpretations agree, definitionally
-- ============================================================================

mutual

/-- `Ty.interpret X (wTy A)` *is* `𝕎 X A`. -/
theorem interpret_wTy {X : ι → Type} :
    ∀ {Γ : Ctx ι} (A : Formula F Γ), Ty.interpret X (wTy A) = 𝕎 X A
  | _, .bot       => rfl
  | _, .eq0 _ _   => rfl
  | _, .and A B   => by
      show (Ty.interpret X (wTy A) × Ty.interpret X (wTy B)) = _
      rw [interpret_wTy A, interpret_wTy B]; rfl
  | _, .or  A B   => by
      show (Nat × (Ty.interpret X (wTy A) × Ty.interpret X (wTy B))) = _
      rw [interpret_wTy A, interpret_wTy B]; rfl
  | _, .imp A B   => by
      show ((Ty.interpret X (wTy A) → Ty.interpret X (wTy B)) ×
            (Ty.interpret X (wTy A) → Ty.interpret X (cTy B) → Ty.interpret X (cTy A))) = _
      rw [interpret_wTy A, interpret_wTy B, interpret_cTy A, interpret_cTy B]; rfl
  | _, .ex  ρ A   => by
      show (Ty.interpret X ρ × Ty.interpret X (wTy A)) = _
      rw [interpret_wTy A]; rfl
  | _, .all ρ A   => by
      show (Ty.interpret X ρ → Ty.interpret X (wTy A)) = _
      rw [interpret_wTy A]; rfl

/-- `Ty.interpret X (cTy A)` *is* `ℂ X A`. -/
theorem interpret_cTy {X : ι → Type} :
    ∀ {Γ : Ctx ι} (A : Formula F Γ), Ty.interpret X (cTy A) = ℂ X A
  | _, .bot       => rfl
  | _, .eq0 _ _   => rfl
  | _, .and A B   => by
      show (Ty.interpret X (cTy A) × Ty.interpret X (cTy B)) = _
      rw [interpret_cTy A, interpret_cTy B]; rfl
  | _, .or  A B   => by
      show (Ty.interpret X (cTy A) × Ty.interpret X (cTy B)) = _
      rw [interpret_cTy A, interpret_cTy B]; rfl
  | _, .imp A B   => by
      show (Ty.interpret X (wTy A) × Ty.interpret X (cTy B)) = _
      rw [interpret_wTy A, interpret_cTy B]; rfl
  | _, .ex  _ A   => interpret_cTy A
  | _, .all ρ A   => by
      show (Ty.interpret X ρ × Ty.interpret X (cTy A)) = _
      rw [interpret_cTy A]; rfl

end

-- ============================================================================
-- Syntactic defaults
-- ============================================================================

/-- A canonical closed inhabitant of every type, at the term level. -/
def Term.defaultOf : (ρ : Ty ι) → Term F Γ ρ
  | .nat      => .zero
  | .base i   => .zeroX i
  | .unit     => .unitI
  | .arr _ τ  => .lam (Term.defaultOf τ)
  | .prod ρ τ => .mkPair (Term.defaultOf ρ) (Term.defaultOf τ)

/-- Syntactic counterpart of `dialecticaDefaultWitness`. -/
def defaultWTerm (A : Formula F Γ) : Term F Γ (wTy A) := Term.defaultOf _

/-- Syntactic counterpart of `dialecticaDefaultCounter`. -/
def defaultCTerm (A : Formula F Γ) : Term F Γ (cTy A) := Term.defaultOf _

-- ============================================================================
-- Realizers as terms
-- ============================================================================

/-- A realizer whose witness is a **term**. The matrix is the unchanged semantic one,
applied to the term's interpretation: syntactic witness, semantic soundness. -/
def syntacticRealizerCtx {X : ι → Type} (si : SpaceInterp X F)
    (A : Formula F Γ) (env : Ctx.interpret X Γ) : Type :=
  { t : Term F Γ (wTy A) //
      ∀ y : ℂ X A,
        dialecticaMatrix si A env ((interpret_wTy (X := X) A) ▸ Term.interpret si t env) y }

-- ============================================================================
-- The point: the extracted functionals are closed terms
-- ============================================================================

section Extract

variable {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]}

/-- The witness term for `∀x (∀u B₀ → ∃v C₀)` has type
`ρ →ₜ (𝕎(∀u B₀) →ₜ 𝕎(∃v C₀)) ×ₜ (𝕎(∀u B₀) →ₜ ℂ(∃v C₀) →ₜ ℂ(∀u B₀))`. -/
private abbrev stmt : Formula F ([] : Ctx ι) :=
  .all ρ (.imp (.all Ty.nat B₀) (.ex Ty.nat C₀))

/-- `V` — where the witness is produced — as a **closed term** of type `ρ →ₜ nat`. -/
def extractVTerm (w : Term F ([] : Ctx ι) (wTy (stmt (ρ := ρ) (B₀ := B₀) (C₀ := C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  .lam (.fst (.app (.fst (.app (Term.weaken w) (.var .vz))) (defaultWTerm _)))

/-- `U` — where the premise must be tested — as a **closed term** of type `ρ →ₜ nat`. -/
def extractUTerm (w : Term F ([] : Ctx ι) (wTy (stmt (ρ := ρ) (B₀ := B₀) (C₀ := C₀)))) :
    Term F ([] : Ctx ι) (ρ →ₜ Ty.nat) :=
  .lam (.fst (.app (.app (.snd (.app (Term.weaken w) (.var .vz))) (defaultWTerm _))
    (defaultCTerm _)))

/-- **The root cause, fixed.** Both extracted functionals are closed terms, so
`all_closed_terms_majorizable` supplies their majorants outright — no per-derivation
obligation, and no total majorizer. Compare `metatheorem_core_of_majorants`, whose
`U_star`/`V_star` arguments these discharge. -/
theorem extract_majorants {X : ι → Type} {si : SpaceInterp X F}
    (am : AbstractMajorizability si)
    (w : Term F ([] : Ctx ι) (wTy (stmt (ρ := ρ) (B₀ := B₀) (C₀ := C₀)))) :
    (∃ U_star : Ty.interpret X (ρ →ₜ Ty.nat).hat,
      am.toRel.maj (ρ →ₜ Ty.nat) U_star (Term.interpret si (extractUTerm w) ())) ∧
    (∃ V_star : Ty.interpret X (ρ →ₜ Ty.nat).hat,
      am.toRel.maj (ρ →ₜ Ty.nat) V_star (Term.interpret si (extractVTerm w) ())) :=
  ⟨majorant_of_closed_term am _, majorant_of_closed_term am _⟩

end Extract

end Metatheorems
