/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs
import Metatheorems.Majorizability
import Metatheorems.Arithmetic

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

-- ============================================================================
-- The matrix, on object-level witness/counter types
-- ============================================================================

/-- `dialecticaMatrix` retyped against `wTy`/`cTy`.

Identical clause by clause; only the *types* of the witness and counter differ, and by
`interpret_wTy`/`interpret_cTy` those agree with the originals. Working here rather than
through a cast keeps every downstream statement transport-free. -/
def sMatrix {X : ι → Type} (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (A : Formula F Γ) → Ctx.interpret X Γ →
    Ty.interpret X (wTy A) → Ty.interpret X (cTy A) → Prop
  | _, .bot,     _,   _,  _  => False
  | _, .eq0 s t, env, _,  _  => Term.interpret si s env = Term.interpret si t env
  | _, .and A B, env, w,  y  => sMatrix si A env w.1 y.1 ∧ sMatrix si B env w.2 y.2
  | _, .or  A B, env, w,  y  =>
      (w.1 = (0 : Nat) → sMatrix si A env w.2.1 y.1) ∧
      (w.1 ≠ (0 : Nat) → sMatrix si B env w.2.2 y.2)
  | _, .imp A B, env, w,  y  =>
      sMatrix si A env y.1 (w.2 y.1 y.2) → sMatrix si B env (w.1 y.1) y.2
  | _, .ex  _ A, env, w,  y  => sMatrix si A (w.1, env) w.2 y
  | _, .all _ A, env, w,  y  => sMatrix si A (y.1, env) (w y.1) y.2

/-- A Dialectica realizer whose witness is a **closed-over term**: one `Term`, valid in
every environment. -/
def SRealizer {X : ι → Type} (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) : Type :=
  { t : Term F Γ (wTy A) //
      ∀ (env : Ctx.interpret X Γ) (y : Ty.interpret X (cTy A)),
        sMatrix si A env (Term.interpret si t env) y }

-- ============================================================================
-- A minimal object-level conditional, and the two evaluation lemmas it needs
-- ============================================================================

variable {X : ι → Type}

/-- `natCase n a b` is `a` when `n` is zero and `b` otherwise. Built from the recursor,
so it needs no arithmetic beyond `prec`. -/
def Term.natCase {ρ : Ty ι} (n : Term F Γ Ty.nat) (a b : Term F Γ ρ) : Term F Γ ρ :=
  Term.app3 (.prec ρ) a (.lam (.lam (Term.weaken (Term.weaken b)))) n

theorem interpret_natCase_zero {si : SpaceInterp X F} {ρ : Ty ι}
    (n : Term F Γ Ty.nat) (a b : Term F Γ ρ) (env : Ctx.interpret X Γ)
    (h : Term.interpret si n env = (0 : Nat)) :
    Term.interpret si (Term.natCase n a b) env = Term.interpret si a env := by
  simp only [Term.natCase, Term.app3, Term.interpret]
  rw [h]; rfl

theorem interpret_natCase_succ {si : SpaceInterp X F} {ρ : Ty ι}
    (n : Term F Γ Ty.nat) (a b : Term F Γ ρ) (env : Ctx.interpret X Γ)
    (m : Nat) (h : Term.interpret si n env = Nat.succ m) :
    Term.interpret si (Term.natCase n a b) env = Term.interpret si b env := by
  simp only [Term.natCase, Term.app3, Term.interpret]
  rw [h]
  show Term.interpret si (Term.weaken (Term.weaken b)) (_, _, env) = _
  rw [Term.interpret_weaken, Term.interpret_weaken]

theorem interpret_pd_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.pd (F := F) (Γ := Δ)) env = Nat.pred := by
  funext n
  simp only [Term.pd, Term.app3, Term.interpret]
  cases n <;> rfl

private theorem rec_pred_eq_sub (x : Nat) :
    ∀ n : Nat, (Nat.rec x (fun _ ih => Nat.pred ih) n : Nat) = x - n
  | 0     => rfl
  | m + 1 => by
      show Nat.pred (Nat.rec x (fun _ ih => Nat.pred ih) m) = x - (m + 1)
      rw [rec_pred_eq_sub x m, Nat.sub_succ]

theorem interpret_monus_app {si : SpaceInterp X F} (s t : Term F Γ Ty.nat)
    (env : Ctx.interpret X Γ) :
    Term.interpret si (Term.app2 Term.monus s t) env
      = Term.interpret si s env - Term.interpret si t env := by
  simp only [Term.app2, Term.monus, Term.app3, Term.interpret, Ctx.lookup, interpret_pd_fun]
  exact rec_pred_eq_sub _ _

-- ============================================================================
-- The matrix as a term (needed only for contraction)
-- ============================================================================

/-- A term computing the characteristic function of `sMatrix`: it evaluates to `0`
exactly when the matrix holds.

Dialectica needs this in one place only — contraction `A → A ∧ A`, whose counter
component must pick whichever of two counters defeats the witness. Everything else is
plumbing. -/
def matrixTerm : {Γ : Ctx ι} → (A : Formula F Γ) →
    Term F Γ (wTy A) → Term F Γ (cTy A) → Term F Γ Ty.nat
  | _, .bot,     _, _ => .app .succ .zero
  | _, .eq0 s t, _, _ =>
      Term.natCase (Term.app2 Term.monus s t) (Term.app2 Term.monus t s) (.app .succ .zero)
  | _, .and A B, w, y =>
      Term.natCase (matrixTerm A (.fst w) (.fst y)) (matrixTerm B (.snd w) (.snd y))
        (.app .succ .zero)
  | _, .or  A B, w, y =>
      Term.natCase (.fst w)
        (matrixTerm A (.fst (.snd w)) (.fst y))
        (matrixTerm B (.snd (.snd w)) (.snd y))
  | _, .imp A B, w, y =>
      Term.natCase (matrixTerm A (.fst y) (.app (.app (.snd w) (.fst y)) (.snd y)))
        (matrixTerm B (.app (.fst w) (.fst y)) (.snd y))
        .zero
  | _, .ex  _ A, w, y =>
      (matrixTerm A (Term.weaken (.snd w)) (Term.weaken y)).subst0 (.fst w)
  | _, .all _ A, w, y =>
      (matrixTerm A (.app (Term.weaken w) (.var .vz)) (Term.weaken (.snd y))).subst0 (.fst y)

/-- Case analysis on `natCase`, packaged for use below. -/
private theorem natCase_cases {si : SpaceInterp X F} {ρ : Ty ι}
    (n : Term F Γ Ty.nat) (a b : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    (Term.interpret si n env = (0 : Nat) ∧
      Term.interpret si (Term.natCase n a b) env = Term.interpret si a env) ∨
    (Term.interpret si n env ≠ (0 : Nat) ∧
      Term.interpret si (Term.natCase n a b) env = Term.interpret si b env) := by
  rcases Classical.em ((Term.interpret si n env : Nat) = (0 : Nat)) with hz | hz
  · exact Or.inl ⟨hz, interpret_natCase_zero n a b env hz⟩
  · refine Or.inr ⟨hz, ?_⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
    exact interpret_natCase_succ n a b env m hm

/-- **`matrixTerm` computes the matrix.** -/
theorem matrixTerm_correct {si : SpaceInterp X F} :
    ∀ {Γ : Ctx ι} (A : Formula F Γ) (w : Term F Γ (wTy A)) (y : Term F Γ (cTy A))
      (env : Ctx.interpret X Γ),
      Term.interpret si (matrixTerm A w y) env = (0 : Nat) ↔
        sMatrix si A env (Term.interpret si w env) (Term.interpret si y env)
  | _, .bot, w, y, env => by
      simp only [matrixTerm, sMatrix, Term.interpret]
      exact ⟨fun h => absurd h (Nat.succ_ne_zero _), False.elim⟩
  | _, .eq0 s t, w, y, env => by
      simp only [matrixTerm, sMatrix]
      rcases natCase_cases (si := si) (Term.app2 Term.monus s t)
        (Term.app2 Term.monus t s) (.app .succ .zero) env with ⟨hz, he⟩ | ⟨hz, he⟩ <;>
        rw [he] <;> rw [interpret_monus_app] at hz
      · rw [interpret_monus_app, Nat.sub_eq_zero_iff_le]
        rw [Nat.sub_eq_zero_iff_le] at hz
        exact ⟨fun h => Nat.le_antisymm hz h, fun h => h ▸ Nat.le_refl _⟩
      · simp only [Term.interpret]
        refine ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd ?_ hz⟩
        rw [h]; exact Nat.sub_self _
  | _, .and A B, w, y, env => by
      simp only [matrixTerm, sMatrix, Term.interpret]
      rcases natCase_cases (si := si) (matrixTerm A (.fst w) (.fst y))
        (matrixTerm B (.snd w) (.snd y)) (.app .succ .zero) env with ⟨hz, he⟩ | ⟨hz, he⟩ <;>
        rw [he]
      · simp only [matrixTerm_correct A (.fst w) (.fst y) env] at hz
        rw [matrixTerm_correct B (.snd w) (.snd y) env]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
      · rw [ne_eq, matrixTerm_correct A (.fst w) (.fst y) env] at hz
        exact ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h.1 hz⟩
  | _, .or A B, w, y, env => by
      simp only [matrixTerm, sMatrix, Term.interpret]
      rcases natCase_cases (si := si) (.fst w)
        (matrixTerm A (.fst (.snd w)) (.fst y))
        (matrixTerm B (.snd (.snd w)) (.snd y)) env with ⟨hz, he⟩ | ⟨hz, he⟩ <;>
        rw [he] <;> simp only [Term.interpret] at hz
      · rw [matrixTerm_correct A _ _ env]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨fun _ => h, fun hne => absurd hz hne⟩, fun h => h.1 hz⟩
      · rw [matrixTerm_correct B _ _ env]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨fun he0 => absurd he0 hz, fun _ => h⟩, fun h => h.2 hz⟩
  | _, .imp A B, w, y, env => by
      simp only [matrixTerm, sMatrix, Term.interpret]
      rcases natCase_cases (si := si)
        (matrixTerm A (.fst y) (.app (.app (.snd w) (.fst y)) (.snd y)))
        (matrixTerm B (.app (.fst w) (.fst y)) (.snd y)) .zero env with ⟨hz, he⟩ | ⟨hz, he⟩ <;>
        rw [he]
      · simp only [matrixTerm_correct A _ _ env] at hz
        rw [matrixTerm_correct B _ _ env]
        simp only [Term.interpret]
        exact ⟨fun h _ => h, fun h => h hz⟩
      · rw [ne_eq, matrixTerm_correct A _ _ env] at hz
        exact ⟨fun _ h => absurd h hz, fun _ => rfl⟩
  | _, .ex ρ A, w, y, env => by
      simp only [matrixTerm, sMatrix]
      rw [Term.interpret_subst0, matrixTerm_correct A _ _ _]
      simp only [Term.interpret_weaken, Term.interpret]
  | _, .all ρ A, w, y, env => by
      simp only [matrixTerm, sMatrix]
      rw [Term.interpret_subst0, matrixTerm_correct A _ _ _]
      simp only [Term.interpret_weaken, Term.interpret, Ctx.lookup]

end Metatheorems
