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
        dialecticaMatrix si A env (Term.interpret si t env) y }

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

/-- A Dialectica realizer whose witness is a **closed-over term**: one `Term`, valid in
every environment. -/
def SRealizer {X : ι → Type} (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) : Type :=
  { t : Term F Γ (wTy A) //
      ∀ (env : Ctx.interpret X Γ) (y : Ty.interpret X (cTy A)),
        dialecticaMatrix si A env (Term.interpret si t env) y }

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

/-- A term computing the characteristic function of `dialecticaMatrix`: it evaluates to `0`
exactly when the matrix holds.

Dialectica needs this in one place only — contraction `A → A ∧ A`, whose counter component
must pick whichever of two counters defeats the witness. Everything else is plumbing.

The renaming argument is what lets it be used *under binders*: in `and_contract` the
witness and counter are lambda-bound variables, so they live in a context extending the
one `A` was written in. -/
def matrixTerm : {Γ Δ : Ctx ι} → Term.Renaming Γ Δ → (A : Formula F Γ) →
    Term F Δ (wTy A) → Term F Δ (cTy A) → Term F Δ Ty.nat
  | _, _, _, .bot,     _, _ => .app .succ .zero
  | _, _, r, .eq0 s t, _, _ =>
      Term.natCase (Term.app2 Term.monus (s.rename r) (t.rename r))
        (Term.app2 Term.monus (t.rename r) (s.rename r)) (.app .succ .zero)
  | _, _, r, .and A B, w, y =>
      Term.natCase (matrixTerm r A (.fst w) (.fst y)) (matrixTerm r B (.snd w) (.snd y))
        (.app .succ .zero)
  | _, _, r, .or  A B, w, y =>
      Term.natCase (.fst w)
        (matrixTerm r A (.fst (.snd w)) (.fst y))
        (matrixTerm r B (.snd (.snd w)) (.snd y))
  | _, _, r, .imp A B, w, y =>
      Term.natCase (matrixTerm r A (.fst y) (.app (.app (.snd w) (.fst y)) (.snd y)))
        (matrixTerm r B (.app (.fst w) (.fst y)) (.snd y))
        .zero
  | _, _, r, .ex  _ A, w, y =>
      (matrixTerm (Term.Renaming.ext r) A (Term.weaken (.snd w)) (Term.weaken y)).subst0 (.fst w)
  | _, _, r, .all _ A, w, y =>
      (matrixTerm (Term.Renaming.ext r) A
        (.app (Term.weaken w) (.var .vz)) (Term.weaken (.snd y))).subst0 (.fst y)

/-- Case analysis on `natCase`, packaged for use below. -/
private theorem natCase_cases {si : SpaceInterp X F} {ρ : Ty ι}
    (n : Term F Γ Ty.nat) (a b : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    (Term.interpret si n env = 0 ∧
      Term.interpret si (Term.natCase n a b) env = Term.interpret si a env) ∨
    (Term.interpret si n env ≠ 0 ∧
      Term.interpret si (Term.natCase n a b) env = Term.interpret si b env) := by
  rcases Classical.em ((Term.interpret si n env : Nat) = 0) with hz | hz
  · exact Or.inl ⟨hz, interpret_natCase_zero n a b env hz⟩
  · refine Or.inr ⟨hz, ?_⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
    exact interpret_natCase_succ n a b env m hm

/-- **`matrixTerm` computes the matrix.** -/
theorem matrixTerm_correct {si : SpaceInterp X F} :
    ∀ {Γ Δ : Ctx ι} (r : Term.Renaming Γ Δ) (A : Formula F Γ)
      (w : Term F Δ (wTy A)) (y : Term F Δ (cTy A))
      (envΔ : Ctx.interpret X Δ) (envΓ : Ctx.interpret X Γ),
      (∀ {σ} (v : Var Γ σ), Ctx.lookup (r v) envΔ = Ctx.lookup v envΓ) →
      (Term.interpret si (matrixTerm r A w y) envΔ = 0 ↔
        dialecticaMatrix si A envΓ (Term.interpret si w envΔ) (Term.interpret si y envΔ))
  | _, _, _, .bot, w, y, envΔ, envΓ, _ => by
      simp only [matrixTerm, dialecticaMatrix, Term.interpret]
      exact ⟨fun h => absurd h (Nat.succ_ne_zero _), False.elim⟩
  | _, _, r, .eq0 s t, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix]
      have hs := Term.interpret_rename_gen si r s envΔ envΓ hr
      have ht := Term.interpret_rename_gen si r t envΔ envΓ hr
      rcases natCase_cases (si := si) (Term.app2 Term.monus (s.rename r) (t.rename r))
        (Term.app2 Term.monus (t.rename r) (s.rename r)) (.app .succ .zero) envΔ
        with ⟨hz, he⟩ | ⟨hz, he⟩ <;> rw [he] <;>
        rw [interpret_monus_app, hs, ht] at hz
      · rw [interpret_monus_app, hs, ht, Nat.sub_eq_zero_iff_le]
        rw [Nat.sub_eq_zero_iff_le] at hz
        exact ⟨fun h => Nat.le_antisymm hz h, fun h => h ▸ Nat.le_refl _⟩
      · simp only [Term.interpret]
        refine ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd ?_ hz⟩
        rw [h]; exact Nat.sub_self _
  | _, _, r, .and A B, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix, Term.interpret]
      rcases natCase_cases (si := si) (matrixTerm r A (.fst w) (.fst y))
        (matrixTerm r B (.snd w) (.snd y)) (.app .succ .zero) envΔ
        with ⟨hz, he⟩ | ⟨hz, he⟩ <;> rw [he]
      · simp only [matrixTerm_correct r A (.fst w) (.fst y) envΔ envΓ hr] at hz
        rw [matrixTerm_correct r B (.snd w) (.snd y) envΔ envΓ hr]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
      · rw [ne_eq, matrixTerm_correct r A (.fst w) (.fst y) envΔ envΓ hr] at hz
        exact ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h.1 hz⟩
  | _, _, r, .or A B, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix, Term.interpret]
      rcases natCase_cases (si := si) (.fst w)
        (matrixTerm r A (.fst (.snd w)) (.fst y))
        (matrixTerm r B (.snd (.snd w)) (.snd y)) envΔ
        with ⟨hz, he⟩ | ⟨hz, he⟩ <;> rw [he] <;> simp only [Term.interpret] at hz
      · rw [matrixTerm_correct r A _ _ envΔ envΓ hr]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨fun _ => h, fun hne => absurd hz hne⟩, fun h => h.1 hz⟩
      · rw [matrixTerm_correct r B _ _ envΔ envΓ hr]
        simp only [Term.interpret]
        exact ⟨fun h => ⟨fun he0 => absurd he0 hz, fun _ => h⟩, fun h => h.2 hz⟩
  | _, _, r, .imp A B, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix, Term.interpret]
      rcases natCase_cases (si := si)
        (matrixTerm r A (.fst y) (.app (.app (.snd w) (.fst y)) (.snd y)))
        (matrixTerm r B (.app (.fst w) (.fst y)) (.snd y)) .zero envΔ
        with ⟨hz, he⟩ | ⟨hz, he⟩ <;> rw [he]
      · simp only [matrixTerm_correct r A _ _ envΔ envΓ hr] at hz
        rw [matrixTerm_correct r B _ _ envΔ envΓ hr]
        simp only [Term.interpret]
        exact ⟨fun h _ => h, fun h => h hz⟩
      · rw [ne_eq, matrixTerm_correct r A _ _ envΔ envΓ hr] at hz
        exact ⟨fun _ h => absurd h hz, fun _ => rfl⟩
  | _, _, r, .ex ρ A, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix]
      rw [Term.interpret_subst0,
        matrixTerm_correct (Term.Renaming.ext r) A _ _ _
          (Term.interpret si (.fst w) envΔ, envΓ) ?_]
      · simp only [Term.interpret_weaken, Term.interpret]
      · intro σ v
        cases v with
        | vz => rfl
        | vs v' => simpa [Term.Renaming.ext, Ctx.lookup] using hr v'
  | _, _, r, .all ρ A, w, y, envΔ, envΓ, hr => by
      simp only [matrixTerm, dialecticaMatrix]
      rw [Term.interpret_subst0,
        matrixTerm_correct (Term.Renaming.ext r) A _ _ _
          (Term.interpret si (.fst y) envΔ, envΓ) ?_]
      · simp only [Term.interpret_weaken, Term.interpret, Ctx.lookup]
      · intro σ v
        cases v with
        | vz => rfl
        | vs v' => simpa [Term.Renaming.ext, Ctx.lookup] using hr v'

end Metatheorems
