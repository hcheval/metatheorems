/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs
import Metatheorems.Majorizability
import Metatheorems.Arithmetic

namespace Metatheorems

open Formula

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

/-- Transport a term along an equality of types. `wTy (A.subst0 t) = wTy A` is a theorem,
not `rfl`, so the quantifier rules need this — exactly as the semantic development needs
`cast` in the same places. -/
def Term.castTy {ρ σ : Ty ι} (h : ρ = σ) (t : Term F Γ ρ) : Term F Γ σ :=
  cast (congrArg (Term F Γ) h) t

theorem interpret_castTy {si : SpaceInterp X F} {ρ σ : Ty ι} (h : ρ = σ)
    (t : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    Term.interpret si (Term.castTy h t) env
      = cast (congrArg (Ty.interpret X) h) (Term.interpret si t env) := by
  cases h; rfl


/-- Interpreting a substitution built from a renaming just relocates the environment. -/
theorem interpretSubst_of_renaming {si : SpaceInterp X F} :
    ∀ {Γ Δ : Ctx ι} (r : Term.Renaming Γ Δ) (envΔ : Ctx.interpret X Δ)
      (envΓ : Ctx.interpret X Γ),
      (∀ {σ} (v : Var Γ σ), Ctx.lookup (r v) envΔ = Ctx.lookup v envΓ) →
      Ctx.interpretSubst si (fun v => Term.var (r v)) envΔ = envΓ
  | [],      _, _, _,    _, _ => rfl
  | _ :: Γ', _, r, envΔ, envΓ, h => by
      show (Term.interpret si (Term.var (r .vz)) envΔ,
            Ctx.interpretSubst si (fun v => Term.var (r (.vs v))) envΔ) = envΓ
      have h1 : Term.interpret si (Term.var (r .vz)) envΔ = envΓ.1 := h .vz
      have h2 := interpretSubst_of_renaming (si := si) (fun v => r (.vs v)) envΔ envΓ.2
        (fun v => h (.vs v))
      rw [h1, h2]
      rfl


-- ============================================================================
-- Per-rule syntactic realizers
-- ============================================================================

section Rules

variable {si : SpaceInterp X F}

/-- Build a realizer of an implication from its two components. The Dialectica clause for
`→` is exactly "given a counter `(w, y)`, if the antecedent's matrix holds at `w` against
the counter `g w y`, then the consequent's holds at `f w` against `y`". -/
def SRealizer.imp {A B : Formula F Γ}
    (f : Term F Γ (wTy A →ₜ wTy B)) (g : Term F Γ (wTy A →ₜ cTy B →ₜ cTy A))
    (h : ∀ (env : Ctx.interpret X Γ) (w : Ty.interpret X (wTy A))
           (y : Ty.interpret X (cTy B)),
        dialecticaMatrix si A env w (Term.interpret si g env w y) →
        dialecticaMatrix si B env (Term.interpret si f env w) y) :
    SRealizer si (A →ᶠ B) :=
  ⟨.mkPair f g, fun env y => h env y.1 y.2⟩

/-- `⊥ → A`. -/
def sExfalso {A : Formula F Γ} : SRealizer si (⊥ᶠ →ᶠ A) :=
  SRealizer.imp (.lam (Term.weaken (defaultWTerm A))) (.lam (.lam .unitI))
    (fun _ _ _ hf => absurd hf (by simp [dialecticaMatrix]))

/-- `A ∧ B → A`. -/
def sAndWeak {A B : Formula F Γ} : SRealizer si (A ∧ᶠ B →ᶠ A) :=
  SRealizer.imp (.lam (.fst (.var .vz)))
    (.lam (.lam (.mkPair (.var .vz) (Term.weaken (Term.weaken (defaultCTerm B))))))
    (fun _ _ _ h => h.1)

/-- `A ∧ B → B ∧ A`. -/
def sAndPerm {A B : Formula F Γ} : SRealizer si (A ∧ᶠ B →ᶠ B ∧ᶠ A) :=
  SRealizer.imp (.lam (.mkPair (.snd (.var .vz)) (.fst (.var .vz))))
    (.lam (.lam (.mkPair (.snd (.var .vz)) (.fst (.var .vz)))))
    (fun _ _ _ h => ⟨h.2, h.1⟩)

/-- `A → A ∨ B`: tag `0` selects the left disjunct. -/
def sOrWeak {A B : Formula F Γ} : SRealizer si (A →ᶠ A ∨ᶠ B) :=
  SRealizer.imp
    (.lam (.mkPair .zero (.mkPair (.var .vz) (Term.weaken (defaultWTerm B)))))
    (.lam (.lam (.fst (.var .vz))))
    (fun _ _ _ h => ⟨fun _ => h, fun hne => absurd rfl hne⟩)

/-- `A ∨ B → B ∨ A`. -/
def sOrPerm {A B : Formula F Γ} : SRealizer si (A ∨ᶠ B →ᶠ B ∨ᶠ A) :=
  SRealizer.imp
    (.lam (.mkPair (Term.natCase (.fst (.var .vz)) (.app .succ .zero) .zero)
      (.mkPair (.snd (.snd (.var .vz))) (.fst (.snd (.var .vz))))))
    (.lam (.lam (.mkPair (.snd (.var .vz)) (.fst (.var .vz)))))
    (fun env w y h => by
      simp only [dialecticaMatrix, Term.interpret] at h ⊢
      rcases Classical.em ((w.1 : Nat) = 0) with hz | hz
      · rw [interpret_natCase_zero _ _ _ _ (by simpa [Term.interpret] using hz)]
        exact ⟨fun hc => absurd hc (by simp [Term.interpret]), fun _ => h.1 hz⟩
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [interpret_natCase_succ _ _ _ _ m (by simpa [Term.interpret] using hm)]
        exact ⟨fun _ => h.2 hz, fun hc => absurd (by simp [Term.interpret]) hc⟩)

/-- `A ∨ A → A`. -/
def sOrContract {A : Formula F Γ} : SRealizer si (A ∨ᶠ A →ᶠ A) :=
  SRealizer.imp
    (.lam (Term.natCase (.fst (.var .vz)) (.fst (.snd (.var .vz))) (.snd (.snd (.var .vz)))))
    (.lam (.lam (.mkPair (.var .vz) (.var .vz))))
    (fun env w y h => by
      simp only [dialecticaMatrix, Term.interpret] at h ⊢
      rcases Classical.em ((w.1 : Nat) = 0) with hz | hz
      · rw [interpret_natCase_zero _ _ _ _ (by simpa [Term.interpret] using hz)]
        simpa [Term.interpret] using h.1 hz
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [interpret_natCase_succ _ _ _ _ m (by simpa [Term.interpret] using hm)]
        simpa [Term.interpret] using h.2 hz)

/-- Modus ponens. -/
def sMP {A B : Formula F Γ} (hA : SRealizer si A) (hAB : SRealizer si (A →ᶠ B)) :
    SRealizer si B :=
  ⟨.app (.fst hAB.val) hA.val,
   fun env y => hAB.property env (Term.interpret si hA.val env, y) (hA.property env _)⟩

/-- Syllogism. -/
def sSyllogism {A B C : Formula F Γ}
    (hAB : SRealizer si (A →ᶠ B)) (hBC : SRealizer si (B →ᶠ C)) :
    SRealizer si (A →ᶠ C) :=
  SRealizer.imp
    (.lam (.app (Term.weaken (.fst hBC.val)) (.app (Term.weaken (.fst hAB.val)) (.var .vz))))
    (.lam (.lam (.app (.app (Term.weaken (Term.weaken (.snd hAB.val))) (.var (.vs .vz)))
      (.app (.app (Term.weaken (Term.weaken (.snd hBC.val)))
          (.app (Term.weaken (Term.weaken (.fst hAB.val))) (.var (.vs .vz))))
        (.var .vz)))))
    (fun env w y h => by
      simp only [Term.interpret, Term.interpret_weaken] at h ⊢
      exact hBC.property env (_, y) (hAB.property env (w, _) h))

/-- Exportation: `A ∧ B → C` gives `A → B → C`. -/
def sExportation {A B C : Formula F Γ} (h : SRealizer si (A ∧ᶠ B →ᶠ C)) :
    SRealizer si (A →ᶠ B →ᶠ C) :=
  SRealizer.imp
    (.lam (.mkPair
      (.lam (.app (Term.weaken (Term.weaken (.fst h.val)))
        (.mkPair (.var (.vs .vz)) (.var .vz))))
      (.lam (.lam (.snd (.app (.app (Term.weaken (Term.weaken (Term.weaken (.snd h.val))))
        (.mkPair (.var (.vs (.vs .vz))) (.var (.vs .vz)))) (.var .vz)))))))
    (.lam (.lam (.fst (.app (.app (Term.weaken (Term.weaken (.snd h.val)))
      (.mkPair (.var (.vs .vz)) (.fst (.var .vz)))) (.snd (.var .vz))))))
    (fun env w y hm => by
      simp only [Term.interpret, Term.interpret_weaken] at hm ⊢
      exact fun hB => h.property env ((w, y.1), y.2) ⟨hm, hB⟩)

/-- Importation: `A → B → C` gives `A ∧ B → C`. -/
def sImportation {A B C : Formula F Γ} (h : SRealizer si (A →ᶠ B →ᶠ C)) :
    SRealizer si (A ∧ᶠ B →ᶠ C) :=
  SRealizer.imp
    (.lam (.app (.fst (.app (Term.weaken (.fst h.val)) (.fst (.var .vz)))) (.snd (.var .vz))))
    (.lam (.lam (.mkPair
      (.app (.app (Term.weaken (Term.weaken (.snd h.val))) (.fst (.var (.vs .vz))))
        (.mkPair (.snd (.var (.vs .vz))) (.var .vz)))
      (.app (.app (.snd (.app (Term.weaken (Term.weaken (.fst h.val)))
          (.fst (.var (.vs .vz))))) (.snd (.var (.vs .vz)))) (.var .vz)))))
    (fun env w y hm => by
      simp only [Term.interpret, Term.interpret_weaken] at hm ⊢
      exact h.property env (w.1, w.2, y) hm.1 hm.2)


/-- Contraction `A → A ∧ A` — the one rule that needs `matrixTerm`: the counter component
must return whichever of the two counters actually defeats the witness. -/
def sAndContract {A : Formula F Γ} : SRealizer si (A →ᶠ A ∧ᶠ A) :=
  SRealizer.imp (.lam (.mkPair (.var .vz) (.var .vz)))
    (.lam (.lam (Term.natCase
      (matrixTerm (fun v => .vs (.vs v)) A (.var (.vs .vz)) (.fst (.var .vz)))
      (.snd (.var .vz)) (.fst (.var .vz)))))
    (fun env w y hm => by
      have hlk : ∀ {σ : Ty ι} (v : Var Γ σ),
          Ctx.lookup ((fun v => Var.vs (Var.vs v)) v) (y, w, env) = Ctx.lookup v env :=
        fun _ => rfl
      have hcorr := matrixTerm_correct (si := si) (fun v => Var.vs (Var.vs v)) A
        (.var (.vs .vz)) (.fst (.var .vz)) (y, w, env) env hlk
      simp only [Term.interpret, Ctx.lookup] at hcorr hm ⊢
      rcases Classical.em (dialecticaMatrix si A env w y.1) with hy | hy
      · rw [interpret_natCase_zero _ _ _ _ (hcorr.mpr hy)] at hm
        simp only [Term.interpret, Ctx.lookup] at hm
        exact ⟨hy, hm⟩
      · obtain ⟨m, hmm⟩ := Nat.exists_eq_succ_of_ne_zero (fun hc => hy (hcorr.mp hc))
        rw [interpret_natCase_succ _ _ _ _ m hmm] at hm
        simp only [Term.interpret, Ctx.lookup] at hm
        exact absurd hm hy)

/-- Expansion: `A → B` gives `C ∨ A → C ∨ B`. -/
def sExpansion {A B C : Formula F Γ} (h : SRealizer si (A →ᶠ B)) :
    SRealizer si (C ∨ᶠ A →ᶠ C ∨ᶠ B) :=
  SRealizer.imp
    (.lam (.mkPair (.fst (.var .vz)) (.mkPair (.fst (.snd (.var .vz)))
      (.app (Term.weaken (.fst h.val)) (.snd (.snd (.var .vz)))))))
    (.lam (.lam (.mkPair (.fst (.var .vz))
      (.app (.app (Term.weaken (Term.weaken (.snd h.val)))
        (.snd (.snd (.var (.vs .vz))))) (.snd (.var .vz))))))
    (fun env w y hm => by
      simp only [dialecticaMatrix, Term.interpret, Term.interpret_weaken] at hm ⊢
      exact ⟨hm.1, fun hne => h.property env (w.2.2, y.2) (hm.2 hne)⟩)

/-- Reflexivity of `=₀`. -/
def sRefl0 {t : Term F Γ Ty.nat} : SRealizer si (Formula.eq0 t t) :=
  ⟨.unitI, fun _ _ => rfl⟩

/-- Symmetry of `=₀`. -/
def sSym0 {s t : Term F Γ Ty.nat} :
    SRealizer si (Formula.eq0 s t →ᶠ Formula.eq0 t s) :=
  SRealizer.imp (.lam .unitI) (.lam (.lam .unitI)) (fun _ _ _ h => h.symm)

/-- Transitivity of `=₀`. -/
def sTrans0 {s t u : Term F Γ Ty.nat} :
    SRealizer si (Formula.eq0 s t ∧ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u) :=
  SRealizer.imp (.lam .unitI) (.lam (.lam (.mkPair .unitI .unitI)))
    (fun _ _ _ h => h.1.trans h.2)


/-- `∀`-axiom: `∀x A → A[t/x]`. -/
def sForallAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ) :
    SRealizer si (Formula.all ρ A →ᶠ A.subst0 t) :=
  let hw : wTy (A.subst0 t) = wTy A := (wTy_cTy_substF A (Term.subst0_map t)).1
  let hc : cTy (A.subst0 t) = cTy A := (wTy_cTy_substF A (Term.subst0_map t)).2
  SRealizer.imp
    (.lam (Term.castTy hw.symm (.app (.var .vz) (Term.weaken t))))
    (.lam (.lam (.mkPair (Term.weaken (Term.weaken t)) (Term.castTy hc (.var .vz)))))
    (fun env w y hm => by
      simp only [Term.interpret, Term.interpret_weaken, interpret_castTy, Ctx.lookup] at hm ⊢
      have key := (dialecticaMatrix_subst0 si A t env
        (w (Term.interpret si t env)) (cast (congrArg (Ty.interpret X) hc) y)).mpr hm
      rwa [cast_cancel (dialecticaCounter_subst0 A t)] at key)


/-- `∃`-axiom: `A[t/x] → ∃x A`. -/
def sExistAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ) :
    SRealizer si (A.subst0 t →ᶠ Formula.ex ρ A) :=
  let hw : wTy (A.subst0 t) = wTy A := (wTy_cTy_substF A (Term.subst0_map t)).1
  let hc : cTy (A.subst0 t) = cTy A := (wTy_cTy_substF A (Term.subst0_map t)).2
  SRealizer.imp
    (.lam (.mkPair (Term.weaken t) (Term.castTy hw (.var .vz))))
    (.lam (.lam (Term.castTy hc.symm (.var .vz))))
    (fun env w y hm => by
      simp only [Term.interpret, Term.interpret_weaken, interpret_castTy, Ctx.lookup] at hm ⊢
      have key := (dialecticaMatrix_subst0 si A t env
        (cast (congrArg (Ty.interpret X) hw) w) y).mp
      rw [cast_cancel (dialecticaWitness_subst0 A t)] at key
      exact key hm)

/-- Universal generalization. -/
def sUnivGen {ρ : Ty ι} {A : Formula F Γ} (r : SRealizer si A) :
    SRealizer si (Formula.all ρ (A.weakenBy ρ)) :=
  let hw : wTy (A.weakenBy ρ) = wTy A := (wTy_cTy_renameF A Term.Renaming.shift).1
  ⟨.lam (Term.castTy hw.symm (Term.weaken r.val)),
   fun env y => by
     simp only [dialecticaMatrix, Term.interpret, Term.interpret_weaken, interpret_castTy]
     refine (dialecticaMatrix_weaken si A env y.1 _ y.2).mpr ?_
     rw [cast_cancel (dialecticaWitness_weaken ρ A).symm]
     exact r.property env _⟩


/-- `∀n. S n ≠ 0`. -/
def sSuccNeZero : SRealizer si (Γ := Γ)
    (Formula.all Ty.nat (Formula.eq0 (.app .succ (.var .vz)) .zero →ᶠ ⊥ᶠ)) :=
  ⟨.lam (.mkPair (.lam .unitI) (.lam (.lam .unitI))),
   fun env y => by
     simp only [dialecticaMatrix, Term.interpret, Ctx.lookup]
     exact fun h => Nat.succ_ne_zero _ h⟩

/-- `∀m n. S m = S n → m = n`. -/
def sSuccInj : SRealizer si (Γ := Γ)
    (Formula.all Ty.nat (Formula.all Ty.nat
      (Formula.eq0 (.app .succ (.var (.vs .vz))) (.app .succ (.var .vz))
        →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz)))) :=
  ⟨.lam (.lam (.mkPair (.lam .unitI) (.lam (.lam .unitI)))),
   fun env y => by
     simp only [dialecticaMatrix, Term.interpret, Ctx.lookup]
     exact fun h => Nat.succ.inj h⟩


/-- `∀`-rule: from `B.weakenBy ρ → A` infer `B → ∀x A`.

Note the syntactic version needs no `∀ env` on the hypothesis: one term in context
`ρ :: Γ` already works at every environment, which is what the semantic version had to
simulate by quantifying. -/
def sForallRule {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : SRealizer si (Formula.weakenBy ρ B →ᶠ A)) :
    SRealizer si (B →ᶠ Formula.all ρ A) :=
  let hw : wTy (Formula.weakenBy ρ B) = wTy B := (wTy_cTy_renameF B Term.Renaming.shift).1
  let hc : cTy (Formula.weakenBy ρ B) = cTy B := (wTy_cTy_renameF B Term.Renaming.shift).2
  let rn : Term.Renaming (ρ :: Γ) (ρ :: wTy B :: Γ) :=
    Term.Renaming.ext Term.Renaming.shift
  let sb : Term.Subst F (ρ :: Γ) (cTy (Formula.all ρ A) :: wTy B :: Γ) := fun v =>
    match v with
    | .vz   => .fst (.var .vz)
    | .vs w => .var (.vs (.vs w))
  let hf := h.val.rename rn
  let hg := h.val.subst sb
  SRealizer.imp
    (.lam (.lam (.app (.fst hf) (Term.castTy hw.symm (.var (.vs .vz))))))
    (.lam (.lam (Term.castTy hc
      (.app (.app (.snd hg) (Term.castTy hw.symm (.var (.vs .vz)))) (.snd (.var .vz))))))
    (fun env w y hm => by
      have hrn : ∀ (u : Ty.interpret X ρ) (v : Ty.interpret X (wTy B)),
          Term.interpret si hf (u, v, env) = Term.interpret si h.val (u, env) :=
        fun u v => Term.interpret_rename_gen si rn h.val (u, v, env) (u, env)
          (fun x => by cases x <;> rfl)
      have hsb : ∀ (p : Ty.interpret X (cTy (Formula.all ρ A)))
          (v : Ty.interpret X (wTy B)),
          Term.interpret si hg (p, v, env) = Term.interpret si h.val (p.1, env) := by
        intro p v
        rw [Term.interpret_substF]
        congr 1
        show Ctx.interpretSubst si (fun {_} => sb) (p, v, env) = (p.1, env)
        show (Term.interpret si (sb .vz) (p, v, env),
              Ctx.interpretSubst si (fun w => sb (.vs w)) (p, v, env)) = (p.1, env)
        have hid : (fun {τ : Ty ι} (w : Var Γ τ) => sb (.vs w))
            = (fun {τ : Ty ι} (w : Var Γ τ) => Term.var (Var.vs (Var.vs w))) := rfl
        rw [hid, interpretSubst_of_renaming (si := si) (fun w => Var.vs (Var.vs w))
          (p, v, env) env (fun _ => rfl)]
        rfl
      simp only [Term.interpret, interpret_castTy, Ctx.lookup, hrn, hsb] at hm ⊢
      refine h.property (y.1, env) (cast (congrArg (Ty.interpret X) hw.symm) w, y.2) ?_
      refine (dialecticaMatrix_weaken si B env y.1 _ _).mpr ?_
      rw [cast_cancel (dialecticaWitness_weaken ρ B).symm]
      simpa using hm)


end Rules

end Metatheorems
