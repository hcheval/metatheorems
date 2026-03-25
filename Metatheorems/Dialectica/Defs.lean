/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable

/-!
# Dialectica Definitions and Matrix Lemmas

Definitions and structural lemmas for Gödel's Dialectica interpretation
(Chapter 3, Definition 3.0.1). The soundness theorem lives in
`Dialectica/Lemmas.lean` (per-case proofs) and `Dialectica.lean` (assembly).

## Main Definitions

* `dialecticaWitness` / `dialecticaCounter` — Lean types for witnesses and counters.
* `dialecticaMatrix` — The quantifier-free matrix A_D as a Lean Prop.
* `dialecticaRealizerCtx` / `dialecticaRealizer` — Subtype packaging witness + proof.
* `EqXInterp` — Interface for base-type equality predicates.
-/

open Formula

-- ============================================================================
-- Witness and Counter types (Definition 3.0.1)
-- ============================================================================

mutual

/-- The Lean type of witnesses for A's Dialectica translation (Def. 3.0.1). -/
def dialecticaWitness {ι : Type} (X : ι → Type) {F : ι → Ty ι} {Γ : Ctx ι} :
    Formula F Γ → Type
  | .bot        => Unit
  | .eq0 _ _    => Unit
  | .and A B    => dialecticaWitness X A × dialecticaWitness X B
  | .or  A B    => Bool × dialecticaWitness X A × dialecticaWitness X B
  | .imp A B    => (dialecticaWitness X A → dialecticaWitness X B) ×
                   (dialecticaWitness X A → dialecticaCounter X B → dialecticaCounter X A)
  | .ex  ρ A    => interpTy X ρ × dialecticaWitness X A
  | .all ρ A    => interpTy X ρ → dialecticaWitness X A

/-- The Lean type of counters for A's Dialectica translation (Def. 3.0.1). -/
def dialecticaCounter {ι : Type} (X : ι → Type) {F : ι → Ty ι} {Γ : Ctx ι} :
    Formula F Γ → Type
  | .bot        => Unit
  | .eq0 _ _    => Unit
  | .and A B    => dialecticaCounter X A × dialecticaCounter X B
  | .or  A B    => dialecticaCounter X A × dialecticaCounter X B
  | .imp A B    => dialecticaWitness X A × dialecticaCounter X B
  | .ex  _ A    => dialecticaCounter X A
  | .all ρ A    => interpTy X ρ × dialecticaCounter X A

end

-- ============================================================================
-- The quantifier-free matrix (Definition 3.0.1)
-- ============================================================================

/-- The Dialectica matrix A_D as a Lean proposition (Def. 3.0.1).

Takes an environment `env : interpCtx X Γ` to evaluate the formula's free
variables, witnesses, and counters. -/
def dialecticaMatrix {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (A : Formula F Γ) → interpCtx X Γ →
    dialecticaWitness X A → dialecticaCounter X A → Prop
  | _, .bot,      _,   _,  _  => False
  | _, .eq0 s t,  env, _,  _  => interpTerm si s env = interpTerm si t env
  | _, .and A B,  env, xw, yc =>
      dialecticaMatrix si A env xw.1 yc.1 ∧ dialecticaMatrix si B env xw.2 yc.2
  | _, .or  A B,  env, xw, yc =>
      (xw.1 = true  → dialecticaMatrix si A env xw.2.1 yc.1) ∧
      (xw.1 = false → dialecticaMatrix si B env xw.2.2 yc.2)
  | _, .imp A B,  env, xw, yc =>
      dialecticaMatrix si A env yc.1 (xw.2 yc.1 yc.2) →
      dialecticaMatrix si B env (xw.1 yc.1) yc.2
  | _, .ex  _ A,  env, xw, yc =>
      dialecticaMatrix si A (xw.1, env) xw.2 yc
  | _, .all _ A,  env, xw, yc =>
      dialecticaMatrix si A (yc.1, env) (xw yc.1) yc.2

-- ============================================================================
-- Decidability of the matrix
-- ============================================================================

/-- `dialecticaMatrix si A env w y` is decidable for every formula `A`.
    The only atomic case is `eq0`, which gives `ℕ`-equality (decidable);
    all connectives preserve decidability, and `all`/`ex` reduce to a
    single-point evaluation (no quantification).

    Defined by structural recursion on `A` in term mode (rather than
    `induction A generalizing`) because the context `Γ` is indexed into
    `A`'s type and changes in the `all`/`ex` arms. -/
instance dialecticaMatrix_decidable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ)
    (env : interpCtx X Γ) (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
    Decidable (dialecticaMatrix si A env w y) :=
  match A, env, w, y with
  | .bot,     _, _, _ => isFalse id
  | .eq0 s t, env, _, _ => Nat.decEq _ _
  | .and A B, env, w, y => by
      haveI := dialecticaMatrix_decidable si A env w.1 y.1
      haveI := dialecticaMatrix_decidable si B env w.2 y.2
      simp only [dialecticaMatrix]
      exact inferInstance
  | .or A B, env, w, y => by
      haveI := dialecticaMatrix_decidable si A env w.2.1 y.1
      haveI := dialecticaMatrix_decidable si B env w.2.2 y.2
      haveI : Decidable (w.1 = true  → dialecticaMatrix si A env w.2.1 y.1) :=
        if ht : w.1 = true then
          if hd : dialecticaMatrix si A env w.2.1 y.1 then isTrue  (fun _ => hd)
          else isFalse (fun h => hd (h ht))
        else isTrue (fun h => absurd h ht)
      haveI : Decidable (w.1 = false → dialecticaMatrix si B env w.2.2 y.2) :=
        if hf : w.1 = false then
          if hd : dialecticaMatrix si B env w.2.2 y.2 then isTrue  (fun _ => hd)
          else isFalse (fun h => hd (h hf))
        else isTrue (fun h => absurd h hf)
      simp only [dialecticaMatrix]
      exact inferInstance
  | .imp A B, env, w, y => by
      haveI := dialecticaMatrix_decidable si A env y.1 (w.2 y.1 y.2)
      haveI := dialecticaMatrix_decidable si B env (w.1 y.1) y.2
      exact if ha : dialecticaMatrix si A env y.1 (w.2 y.1 y.2) then
              if hb : dialecticaMatrix si B env (w.1 y.1) y.2 then isTrue (fun _ => hb)
              else isFalse (fun h => hb (h ha))
            else isTrue (fun h => absurd h ha)
  | .all _ A, env, w, y => dialecticaMatrix_decidable si A (y.1, env) (w y.1) y.2
  | .ex  _ A, env, w, y => dialecticaMatrix_decidable si A (w.1, env) w.2 y

-- ============================================================================
-- Convenience
-- ============================================================================

/-- The Dialectica realizer for a formula A in context Γ at environment env.
    This is a *subtype* (not a Prop): the computational witness together with
    a proof it satisfies the matrix for all counters. Because `dialecticaRealizerCtx`
    lives in `Type`, the witness can be extracted computably via `.val`. -/
def dialecticaRealizerCtx {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) (env : interpCtx X Γ) : Type :=
  { x : dialecticaWitness X A //
    ∀ (y : dialecticaCounter X A), dialecticaMatrix si A env x y }

/-- The Dialectica realizer for a closed formula (env = ()). -/
def dialecticaRealizer {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) (A : Formula F ([] : Ctx ι)) : Type :=
  dialecticaRealizerCtx si A ()

-- ============================================================================
-- Subsingleton instances for QF ∨-free formulas
-- ============================================================================

/-- For QF ∨-free formulas, the witness and counter types are subsingletons.
    This is needed for Markov's principle and IP. -/
theorem dialecticaWitness_subsingleton {ι : Type} {X : ι → Type}
    {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) (hvf : A.isVFree = true) :
    Subsingleton (dialecticaWitness X A) ∧
    Subsingleton (dialecticaCounter X A) := by
  induction A with
  | bot =>
    exact ⟨⟨fun _ _ => rfl⟩, ⟨fun _ _ => rfl⟩⟩
  | eq0 _ _ =>
    exact ⟨⟨fun _ _ => rfl⟩, ⟨fun _ _ => rfl⟩⟩
  | and A B ihA ihB =>
    simp [Formula.isQF, Formula.isVFree] at hqf hvf
    obtain ⟨hqA, hqB⟩ := hqf
    obtain ⟨hvA, hvB⟩ := hvf
    obtain ⟨swA, scA⟩ := ihA hqA hvA
    obtain ⟨swB, scB⟩ := ihB hqB hvB
    exact ⟨⟨fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ => by
             rw [swA.elim a₁ a₂, swB.elim b₁ b₂]⟩,
           ⟨fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ => by
             rw [scA.elim a₁ a₂, scB.elim b₁ b₂]⟩⟩
  | or _ _ _ _ =>
    simp [Formula.isVFree] at hvf
  | imp A B ihA ihB =>
    simp [Formula.isQF, Formula.isVFree] at hqf hvf
    obtain ⟨hqA, hqB⟩ := hqf
    obtain ⟨hvA, hvB⟩ := hvf
    obtain ⟨swA, scA⟩ := ihA hqA hvA
    obtain ⟨swB, scB⟩ := ihB hqB hvB
    simp only [dialecticaWitness, dialecticaCounter]
    exact ⟨⟨fun ⟨f₁,g₁⟩ ⟨f₂,g₂⟩ => by
             congr 1
             · exact funext (fun x => swB.elim (f₁ x) (f₂ x))
             · exact funext (fun x => funext (fun y =>
                 scA.elim (g₁ x y) (g₂ x y)))⟩,
           ⟨fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ => by
             rw [swA.elim a₁ a₂, scB.elim b₁ b₂]⟩⟩
  | all _ _ _ => simp [Formula.isQF] at hqf
  | ex _ _ _ => simp [Formula.isQF] at hqf

/-- For QF ∨-free formulas, construct default witness and counter values.
    These are unique by `dialecticaWitness_subsingleton`. -/
def dialecticaDefault {ι : Type} {X : ι → Type}
    {F : ι → Ty ι} {Γ : Ctx ι} :
    (A : Formula F Γ) → A.isQF = true → A.isVFree = true →
    dialecticaWitness X A × dialecticaCounter X A
  | .bot, _, _ => ((), ())
  | .eq0 .., _, _ => ((), ())
  | .and A B, hqf, hvf =>
    let hqA : A.isQF = true := by simp [Formula.isQF] at hqf; exact hqf.1
    let hqB : B.isQF = true := by simp [Formula.isQF] at hqf; exact hqf.2
    let hvA : A.isVFree = true := by simp [Formula.isVFree] at hvf; exact hvf.1
    let hvB : B.isVFree = true := by simp [Formula.isVFree] at hvf; exact hvf.2
    let dA := dialecticaDefault A hqA hvA
    let dB := dialecticaDefault B hqB hvB
    ((dA.1, dB.1), (dA.2, dB.2))
  | .or .., _, hvf => absurd hvf (by simp [Formula.isVFree])
  | .imp A B, hqf, hvf =>
    let hqA : A.isQF = true := by simp [Formula.isQF] at hqf; exact hqf.1
    let hqB : B.isQF = true := by simp [Formula.isQF] at hqf; exact hqf.2
    let hvA : A.isVFree = true := by simp [Formula.isVFree] at hvf; exact hvf.1
    let hvB : B.isVFree = true := by simp [Formula.isVFree] at hvf; exact hvf.2
    let dA := dialecticaDefault A hqA hvA
    let dB := dialecticaDefault B hqB hvB
    ((fun _ => dB.1, fun _ _ => dA.2), (dA.1, dB.2))
  | .all .., hqf, _ => absurd hqf (by simp [Formula.isQF])
  | .ex .., hqf, _ => absurd hqf (by simp [Formula.isQF])

-- ============================================================================
-- Type invariance under substitution
-- ============================================================================

/-- Both witness and counter types are invariant under formula substitution.
    Proved together by mutual induction (imp uses both). -/
theorem dialectica_types_substF {ι : Type} {X : ι → Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (s : Term.Subst F Γ Δ),
    dialecticaWitness X (A.substF s) = dialecticaWitness X A ∧
    dialecticaCounter X (A.substF s) = dialecticaCounter X A := by
  induction A with
  | bot => intro Δ s; exact ⟨rfl, rfl⟩
  | eq0 _ _ => intro Δ s; exact ⟨rfl, rfl⟩
  | and _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    simp only [Formula.substF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB], by rw [hcA, hcB]⟩
  | or _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    simp only [Formula.substF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB], by rw [hcA, hcB]⟩
  | imp _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    simp only [Formula.substF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB, hcA, hcB], by rw [hwA, hcB]⟩
  | all _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Subst.ext s)
    simp only [Formula.substF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA], by rw [hcA]⟩
  | ex _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Subst.ext s)
    simp only [Formula.substF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA], by rw [hcA]⟩

/-- Corollaries: type invariance under subst0 and weaken. -/
theorem dialecticaWitness_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    dialecticaWitness X (A.subst0 t) = dialecticaWitness X A :=
  (dialectica_types_substF A (Term.subst0_map t)).1

theorem dialecticaCounter_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    dialecticaCounter X (A.subst0 t) = dialecticaCounter X A :=
  (dialectica_types_substF A (Term.subst0_map t)).2

-- ============================================================================
-- Type invariance under renaming (needed for ∀/∃-rule)
-- ============================================================================

/-- Both witness and counter types are invariant under formula renaming.
    Proved by induction mirroring dialectica_types_substF. -/
theorem dialectica_types_renameF {ι : Type} {X : ι → Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (r : Renaming Γ Δ),
    dialecticaWitness X (A.renameF r) = dialecticaWitness X A ∧
    dialecticaCounter X (A.renameF r) = dialecticaCounter X A := by
  induction A with
  | bot => intro Δ r; exact ⟨rfl, rfl⟩
  | eq0 _ _ => intro Δ r; exact ⟨rfl, rfl⟩
  | and _ _ ihA ihB =>
    intro Δ r
    obtain ⟨hwA, hcA⟩ := ihA r; obtain ⟨hwB, hcB⟩ := ihB r
    simp only [Formula.renameF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB], by rw [hcA, hcB]⟩
  | or _ _ ihA ihB =>
    intro Δ r
    obtain ⟨hwA, hcA⟩ := ihA r; obtain ⟨hwB, hcB⟩ := ihB r
    simp only [Formula.renameF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB], by rw [hcA, hcB]⟩
  | imp _ _ ihA ihB =>
    intro Δ r
    obtain ⟨hwA, hcA⟩ := ihA r; obtain ⟨hwB, hcB⟩ := ihB r
    simp only [Formula.renameF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA, hwB, hcA, hcB], by rw [hwA, hcB]⟩
  | all _ _ ihA =>
    intro Δ r
    obtain ⟨hwA, hcA⟩ := ihA (Renaming.ext r)
    simp only [Formula.renameF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA], by rw [hcA]⟩
  | ex _ _ ihA =>
    intro Δ r
    obtain ⟨hwA, hcA⟩ := ihA (Renaming.ext r)
    simp only [Formula.renameF, dialecticaWitness, dialecticaCounter]
    exact ⟨by rw [hwA], by rw [hcA]⟩

/-- Type invariance under weakening (corollary). -/
theorem dialecticaWitness_weaken {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {Γ : Ctx ι} (ρ : Ty ι) (A : Formula F Γ) :
    dialecticaWitness X (A.weakenBy ρ) = dialecticaWitness X A :=
  (dialectica_types_renameF A Renaming.shift).1

theorem dialecticaCounter_weaken {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {Γ : Ctx ι} (ρ : Ty ι) (A : Formula F Γ) :
    dialecticaCounter X (A.weakenBy ρ) = dialecticaCounter X A :=
  (dialectica_types_renameF A Renaming.shift).2

-- ============================================================================
-- Matrix commutativity under renaming
-- ============================================================================

/-- Projecting from a cast product: fst. -/
private lemma cast_prod_fst {α₁ α₂ β₁ β₂ : Type}
    (h : (α₁ × α₂) = (β₁ × β₂)) (h₁ : α₁ = β₁) (h₂ : α₂ = β₂)
    (p : α₁ × α₂) :
    (cast h p).1 = cast h₁ p.1 := by subst h₁; subst h₂; rfl

/-- Projecting from a cast product: snd. -/
private lemma cast_prod_snd {α₁ α₂ β₁ β₂ : Type}
    (h : (α₁ × α₂) = (β₁ × β₂)) (h₁ : α₁ = β₁) (h₂ : α₂ = β₂)
    (p : α₁ × α₂) :
    (cast h p).2 = cast h₂ p.2 := by subst h₁; subst h₂; rfl

/-- Applying a cast function type. -/
private lemma cast_fun_apply {α β₁ β₂ : Type}
    (h : (α → β₁) = (α → β₂)) (hβ : β₁ = β₂)
    (f : α → β₁) (x : α) :
    (cast h f) x = cast hβ (f x) := by subst hβ; rfl

/-- Applying a cast function type where both domain and codomain change. -/
private lemma cast_fun_apply2 {α₁ α₂ β₁ β₂ : Type}
    (hα : α₁ = α₂) (hβ : β₁ = β₂) (h : (α₁ → β₁) = (α₂ → β₂))
    (f : α₁ → β₁) (x : α₂) :
    (cast h f) x = cast hβ (f (cast hα.symm x)) := by
  subst hα; subst hβ; exact congr_fun (eq_of_heq (cast_heq h f)) x

/-- Casting back and forth is the identity. -/
lemma cast_cancel {α β : Type} (h : α = β) (a : α) :
    cast h.symm (cast h a) = a :=
  eq_of_heq ((cast_heq h.symm (cast h a)).trans (cast_heq h a))

/-- Evaluate interpCtxSubst for Renaming.ext applied to var-renaming. -/
private lemma interpCtxSubst_ext_var {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {ρ' : Ty ι}
    (r : Renaming Γ Δ) (z : interpTy X ρ') (env : interpCtx X Δ) :
    interpCtxSubst si
      (fun v => Term.var ((Renaming.ext r) v) :
        Term.Subst F (ρ' :: Γ) (ρ' :: Δ)) (z, env) =
    (z, interpCtxSubst si
      (fun v => Term.var (r v) : Term.Subst F Γ Δ) env) := by
  simp only [interpCtxSubst, Renaming.ext, interpTerm, lookupVar]
  congr 1
  have h1 : (fun {τ : Ty ι} (w : Var Γ τ) => (Term.var (Var.vs (r w)) : Term F (ρ' :: Δ) τ)) =
             (fun {τ : Ty ι} (w : Var Γ τ) => (Term.var (r w) : Term F Δ τ).weaken) := by
    funext τ w; rfl
  rw [h1]
  exact interpCtxSubst_weaken_eq si (fun v => Term.var (r v)) env z

/-- The Dialectica matrix commutes with formula renaming.
    Key lemma needed for forall-rule, exists-rule, and weakening.

    We prove this by mutual induction with the type invariance, avoiding
    separate cast decomposition. The proof uses the fact that
    `dialecticaWitness`/`dialecticaCounter`/`dialecticaMatrix` all unfold
    structurally on `A.renameF r` and `A` in the same way. -/
theorem dialecticaMatrix_renameF {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (r : Renaming Γ Δ) (env : interpCtx X Δ)
      (w : dialecticaWitness X (A.renameF r))
      (y : dialecticaCounter X (A.renameF r)),
    dialecticaMatrix si (A.renameF r) env w y ↔
    dialecticaMatrix si A (interpCtxSubst si (fun v => .var (r v)) env)
      (cast (dialectica_types_renameF (X := X) A r).1 w)
      (cast (dialectica_types_renameF (X := X) A r).2 y) := by
  induction A with
  | bot => intros; exact Iff.rfl
  | eq0 a b =>
    intro Δ r env _ _
    simp only [Formula.renameF, dialecticaMatrix, cast_eq]
    rw [interpTerm_rename, interpTerm_rename]
  | and A1 A2 ihA ihB =>
    intro Δ r env w y
    -- LHS unfolds: dM(A1.ren, env, w.1, y.1) ∧ dM(A2.ren, env, w.2, y.2)
    -- RHS unfolds: dM(A1, env', (cast big w).1, (cast big y).1) ∧ ...
    -- Rewrite cast projections to component casts, then apply IH.
    set_option linter.unusedSimpArgs false in
    simp only [Formula.renameF, dialecticaMatrix,
      cast_prod_fst _ (dialectica_types_renameF (X := X) A1 r).1
        (dialectica_types_renameF (X := X) A2 r).1,
      cast_prod_snd _ (dialectica_types_renameF (X := X) A1 r).1
        (dialectica_types_renameF (X := X) A2 r).1,
      cast_prod_fst _ (dialectica_types_renameF (X := X) A1 r).2
        (dialectica_types_renameF (X := X) A2 r).2,
      cast_prod_snd _ (dialectica_types_renameF (X := X) A1 r).2
        (dialectica_types_renameF (X := X) A2 r).2]
    exact and_congr (ihA r env w.1 y.1) (ihB r env w.2 y.2)
  | or A1 A2 ihA ihB =>
    intro Δ r env w y
    have hwA := (dialectica_types_renameF (X := X) A1 r).1
    have hwB := (dialectica_types_renameF (X := X) A2 r).1
    have hcA := (dialectica_types_renameF (X := X) A1 r).2
    have hcB := (dialectica_types_renameF (X := X) A2 r).2
    have hWpair : (dialecticaWitness X (A1.renameF r) × dialecticaWitness X (A2.renameF r)) =
                  (dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
    have hWbig : (Bool × dialecticaWitness X (A1.renameF r) × dialecticaWitness X (A2.renameF r)) =
                 (Bool × dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
    have hCbig : (dialecticaCounter X (A1.renameF r) × dialecticaCounter X (A2.renameF r)) =
                 (dialecticaCounter X A1 × dialecticaCounter X A2) := by rw [hcA, hcB]
    -- Relate projections of cast to cast of projections
    have hw1 : (cast hWbig w).1 = w.1 := cast_prod_fst hWbig rfl hWpair w
    have hw21 : (cast hWbig w).2.1 = cast hwA w.2.1 := by
      have h2 := cast_prod_snd hWbig rfl hWpair w
      have := cast_prod_fst hWpair hwA hwB w.2
      rw [← h2] at this; exact this
    have hw22 : (cast hWbig w).2.2 = cast hwB w.2.2 := by
      have h2 := cast_prod_snd hWbig rfl hWpair w
      have := cast_prod_snd hWpair hwA hwB w.2
      rw [← h2] at this; exact this
    have hy1 : (cast hCbig y).1 = cast hcA y.1 := cast_prod_fst hCbig hcA hcB y
    have hy2 : (cast hCbig y).2 = cast hcB y.2 := cast_prod_snd hCbig hcA hcB y
    simp only [Formula.renameF, dialecticaMatrix]
    rw [hw1, hw21, hw22, hy1, hy2]
    exact and_congr
      (forall_congr' fun h => ihA r env w.2.1 y.1)
      (forall_congr' fun h => ihB r env w.2.2 y.2)
  | imp A1 A2 ihA ihB =>
    intro Δ r env w y
    have hwA := (dialectica_types_renameF (X := X) A1 r).1
    have hwB := (dialectica_types_renameF (X := X) A2 r).1
    have hcA := (dialectica_types_renameF (X := X) A1 r).2
    have hcB := (dialectica_types_renameF (X := X) A2 r).2
    have hW1 : (dialecticaWitness X (A1.renameF r) → dialecticaWitness X (A2.renameF r)) =
               (dialecticaWitness X A1 → dialecticaWitness X A2) := by rw [hwA, hwB]
    have hW2 : (dialecticaWitness X (A1.renameF r) → dialecticaCounter X (A2.renameF r) → dialecticaCounter X (A1.renameF r)) =
               (dialecticaWitness X A1 → dialecticaCounter X A2 → dialecticaCounter X A1) := by rw [hwA, hcA, hcB]
    have hC2Inner : (dialecticaCounter X (A2.renameF r) → dialecticaCounter X (A1.renameF r)) =
                    (dialecticaCounter X A2 → dialecticaCounter X A1) := by rw [hcA, hcB]
    simp only [Formula.renameF, dialecticaMatrix,
      cast_prod_fst _ hW1 hW2, cast_prod_snd _ hW1 hW2,
      cast_prod_fst _ hwA hcB, cast_prod_snd _ hwA hcB]
    rw [cast_fun_apply2 hwA hwB hW1 w.1 (cast hwA y.1), cast_cancel hwA y.1]
    rw [cast_fun_apply2 hwA hC2Inner hW2 w.2 (cast hwA y.1), cast_cancel hwA y.1]
    rw [cast_fun_apply2 hcB hcA hC2Inner (w.2 y.1) (cast hcB y.2), cast_cancel hcB y.2]
    exact Iff.intro
      (fun h h1 => (ihB r env _ _).mp (h ((ihA r env _ _).mpr h1)))
      (fun h h1 => (ihB r env _ _).mpr (h ((ihA r env _ _).mp h1)))
  | all ρ' A' ihA =>
    intro Δ r env w y
    simp only [Formula.renameF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).2,
      cast_prod_snd _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).2,
      cast_fun_apply _ (dialectica_types_renameF (X := X) A' (Renaming.ext r)).1,
      cast_eq]
    rw [ihA (Renaming.ext r) (y.1, env) (w y.1) y.2]
    rw [interpCtxSubst_ext_var]
  | ex ρ' A' ihA =>
    intro Δ r env w y
    simp only [Formula.renameF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).1,
      cast_prod_snd _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).1,
      cast_eq]
    rw [ihA (Renaming.ext r) (w.1, env) w.2 y]
    rw [interpCtxSubst_ext_var]

-- ============================================================================
-- Matrix commutativity under substitution
-- ============================================================================

/-- The Dialectica matrix commutes with formula substitution.
    Key: cast witnesses/counters via the type invariance equalities. -/
theorem dialecticaMatrix_substF {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (s : Term.Subst F Γ Δ) (env : interpCtx X Δ)
      (w : dialecticaWitness X A) (y : dialecticaCounter X A),
    dialecticaMatrix si (A.substF s) env
      (cast (dialectica_types_substF A s).1.symm w)
      (cast (dialectica_types_substF A s).2.symm y) ↔
    dialecticaMatrix si A (interpCtxSubst si s env) w y := by
  induction A with
  | bot => intro Δ s env w y; exact Iff.rfl
  | eq0 a b =>
    intro Δ s env _ _
    simp only [Formula.substF, dialecticaMatrix, cast_eq]
    constructor
    · intro h; rwa [interpTerm_substF, interpTerm_substF] at h
    · intro h; rwa [interpTerm_substF, interpTerm_substF]
  | and A1 A2 ihA ihB =>
    intro Δ s env w y
    set_option linter.unusedSimpArgs false in
    simp only [Formula.substF, dialecticaMatrix,
      cast_prod_fst _ (dialectica_types_substF A1 s).1.symm
        (dialectica_types_substF A2 s).1.symm,
      cast_prod_snd _ (dialectica_types_substF A1 s).1.symm
        (dialectica_types_substF A2 s).1.symm,
      cast_prod_fst _ (dialectica_types_substF A1 s).2.symm
        (dialectica_types_substF A2 s).2.symm,
      cast_prod_snd _ (dialectica_types_substF A1 s).2.symm
        (dialectica_types_substF A2 s).2.symm]
    exact and_congr (ihA s env w.1 y.1) (ihB s env w.2 y.2)
  | or A1 A2 ihA ihB =>
    intro Δ s env w y
    have hwA := (dialectica_types_substF (X := X) A1 s).1
    have hwB := (dialectica_types_substF (X := X) A2 s).1
    have hcA := (dialectica_types_substF (X := X) A1 s).2
    have hcB := (dialectica_types_substF (X := X) A2 s).2
    have hWpair : (dialecticaWitness X (A1.substF s) × dialecticaWitness X (A2.substF s)) =
                  (dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
    have hWbig : (Bool × dialecticaWitness X (A1.substF s) × dialecticaWitness X (A2.substF s)) =
                 (Bool × dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
    have hCbig : (dialecticaCounter X (A1.substF s) × dialecticaCounter X (A2.substF s)) =
                 (dialecticaCounter X A1 × dialecticaCounter X A2) := by rw [hcA, hcB]
    have hw1 : (cast hWbig.symm w).1 = w.1 := cast_prod_fst hWbig.symm rfl hWpair.symm w
    have hw21 : (cast hWbig.symm w).2.1 = cast hwA.symm w.2.1 := by
      have h2 := cast_prod_snd hWbig.symm rfl hWpair.symm w
      have := cast_prod_fst hWpair.symm hwA.symm hwB.symm w.2
      rw [← h2] at this; exact this
    have hw22 : (cast hWbig.symm w).2.2 = cast hwB.symm w.2.2 := by
      have h2 := cast_prod_snd hWbig.symm rfl hWpair.symm w
      have := cast_prod_snd hWpair.symm hwA.symm hwB.symm w.2
      rw [← h2] at this; exact this
    have hy1 : (cast hCbig.symm y).1 = cast hcA.symm y.1 := cast_prod_fst hCbig.symm hcA.symm hcB.symm y
    have hy2 : (cast hCbig.symm y).2 = cast hcB.symm y.2 := cast_prod_snd hCbig.symm hcA.symm hcB.symm y
    simp only [Formula.substF, dialecticaMatrix]
    rw [hw1, hw21, hw22, hy1, hy2]
    exact and_congr
      (forall_congr' fun _ => ihA s env w.2.1 y.1)
      (forall_congr' fun _ => ihB s env w.2.2 y.2)
  | imp A1 A2 ihA ihB =>
    intro Δ s env w y
    have hwA := (dialectica_types_substF (X := X) A1 s).1
    have hwB := (dialectica_types_substF (X := X) A2 s).1
    have hcA := (dialectica_types_substF (X := X) A1 s).2
    have hcB := (dialectica_types_substF (X := X) A2 s).2
    have hW1 : (dialecticaWitness X (A1.substF s) → dialecticaWitness X (A2.substF s)) =
               (dialecticaWitness X A1 → dialecticaWitness X A2) := by rw [hwA, hwB]
    have hW2 : (dialecticaWitness X (A1.substF s) →
                dialecticaCounter X (A2.substF s) → dialecticaCounter X (A1.substF s)) =
               (dialecticaWitness X A1 → dialecticaCounter X A2 → dialecticaCounter X A1) := by
      rw [hwA, hcA, hcB]
    have hC2Inner : (dialecticaCounter X (A2.substF s) → dialecticaCounter X (A1.substF s)) =
                    (dialecticaCounter X A2 → dialecticaCounter X A1) := by rw [hcA, hcB]
    simp only [Formula.substF, dialecticaMatrix,
      cast_prod_fst _ hW1.symm hW2.symm, cast_prod_snd _ hW1.symm hW2.symm,
      cast_prod_fst _ hwA.symm hcB.symm, cast_prod_snd _ hwA.symm hcB.symm]
    rw [cast_fun_apply2 hwA.symm hwB.symm hW1.symm w.1 (cast hwA.symm y.1), cast_cancel hwA.symm y.1]
    rw [cast_fun_apply2 hwA.symm hC2Inner.symm hW2.symm w.2 (cast hwA.symm y.1), cast_cancel hwA.symm y.1]
    rw [cast_fun_apply2 hcB.symm hcA.symm hC2Inner.symm (w.2 y.1) (cast hcB.symm y.2), cast_cancel hcB.symm y.2]
    exact Iff.intro
      (fun h h1 => (ihB s env _ _).mp (h ((ihA s env _ _).mpr h1)))
      (fun h h1 => (ihB s env _ _).mpr (h ((ihA s env _ _).mp h1)))
  | all ρ A' ihA =>
    intro Δ s env w y
    simp only [Formula.substF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).2.symm,
      cast_prod_snd _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).2.symm,
      cast_fun_apply _ (dialectica_types_substF A' (Term.Subst.ext s)).1.symm,
      cast_eq]
    have key := ihA (Term.Subst.ext s) (y.1, env) (w y.1) y.2
    rw [interpCtxSubst_ext] at key
    exact key
  | ex ρ A' ihA =>
    intro Δ s env w y
    simp only [Formula.substF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).1.symm,
      cast_prod_snd _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).1.symm,
      cast_eq]
    have key := ihA (Term.Subst.ext s) (w.1, env) w.2 y
    rw [interpCtxSubst_ext] at key
    exact key

theorem dialecticaMatrix_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) (env : interpCtx X Γ)
    (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
    dialecticaMatrix si (A.subst0 t) env
      (cast (dialecticaWitness_subst0 A t).symm w)
      (cast (dialecticaCounter_subst0 A t).symm y) ↔
    dialecticaMatrix si A (interpTerm si t env, env) w y := by
  have h := dialecticaMatrix_substF si A (Term.subst0_map t) env w y
  rwa [interpCtxSubst_subst0_map] at h

theorem dialecticaMatrix_substVar0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ)
    (v : interpTy X ρ) (env : interpCtx X Γ)
    (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
    dialecticaMatrix si (A.substVar0 t) (v, env)
      (cast (dialectica_types_substF A (Term.substVar0_map t)).1.symm w)
      (cast (dialectica_types_substF A (Term.substVar0_map t)).2.symm y) ↔
    dialecticaMatrix si A (interpTerm si t (v, env), env) w y := by
  have h := dialecticaMatrix_substF si A (Term.substVar0_map t) (v, env) w y
  rwa [interpCtxSubst_substVar0_map] at h

-- ============================================================================
-- Matrix commutativity under weakening (needed for ∀/∃-rule)
-- ============================================================================

/-- The Dialectica matrix is invariant under formula weakening.
    Witnesses/counters for A.weakenBy ρ correspond to those for A,
    and the matrix value at (v, env) equals that at env. -/
theorem dialecticaMatrix_weaken {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F Γ)
    (env : interpCtx X Γ) (v : interpTy X ρ)
    (w : dialecticaWitness X (A.weakenBy ρ))
    (y : dialecticaCounter X (A.weakenBy ρ)) :
    dialecticaMatrix si (A.weakenBy ρ) (v, env) w y ↔
    dialecticaMatrix si A env
      (cast (dialecticaWitness_weaken ρ A) w)
      (cast (dialecticaCounter_weaken ρ A) y) := by
  -- weakenBy ρ = weaken = renameF Renaming.shift
  -- so we can apply dialecticaMatrix_renameF with r = Renaming.shift
  -- weakenBy ρ A = A.renameF Renaming.shift definitionally
  -- Apply dialecticaMatrix_renameF with r = Renaming.shift
  have key := dialecticaMatrix_renameF si A (Renaming.shift (σ := ρ)) (v, env) w y
  -- key : ... ↔ dialecticaMatrix si A (interpCtxSubst ... (v, env)) (cast ... w) (cast ... y)
  -- Need: interpCtxSubst si (fun v => .var (Var.vs v)) (v, env) = env
  have henv : interpCtxSubst si
      (fun {τ} (x : Var Γ τ) =>
        Term.var (Renaming.shift x) : Term.Subst F Γ (ρ :: Γ))
      (v, env) = env := by
    simp only [Renaming.shift]
    have h1 : (fun {τ : Ty ι} (x : Var Γ τ) =>
                (Term.var (Var.vs x) : Term F (ρ :: Γ) τ)) =
              (fun {τ : Ty ι} (x : Var Γ τ) =>
                (Term.var x : Term F Γ τ).weaken) := by
      funext τ x; rfl
    rw [h1, interpCtxSubst_weaken_eq, interpCtxSubst_id]
  rw [henv] at key
  exact key

-- ============================================================================
-- EqX interface for the Dialectica proof (Def. of "purely universal" EqX)
-- ============================================================================

/-- The Dialectica interface for base-type equality predicates.

For the Dialectica soundness proof to work, each `EqX i s t` must be
"trivially Dialectica-realized" — i.e., the document's condition that
`=_{X_i}` is a purely universal formula. This structure packages the
five conditions needed in the inductive argument:

1. The witness type is a subsingleton (so witnesses are canonical).
2. A canonical witness exists.
3. A canonical counter exists.
4. Semantic equality implies a Dialectica realizer ("soundness of EqX").
5. A Dialectica realizer implies semantic equality ("completeness of EqX").

Concrete theories (e.g. metric spaces) supply an `EqXInterp` instance
for their chosen equality predicate. -/
structure EqXInterp {ι : Type} (X : ι → Type) (F : ι → Ty ι)
    (si : SpaceInterp X F)
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) →
           Formula F Γ) where
  /-- The witness type for `EqX i s t` is a subsingleton (purely universal). -/
  witnessSubsingleton : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)),
      Subsingleton (dialecticaWitness X (EqX i s t))
  /-- A canonical Dialectica witness for `EqX i s t`. -/
  witnessDefault : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)),
      dialecticaWitness X (EqX i s t)
  /-- A canonical Dialectica counter for `EqX i s t`. -/
  counterDefault : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)),
      dialecticaCounter X (EqX i s t)
  /-- From semantic equality, build a Dialectica realizer for `EqX i s t`. -/
  realize : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)) (env : interpCtx X Γ),
      interpTerm si s env = interpTerm si t env →
      dialecticaRealizerCtx si (EqX i s t) env
  /-- From a Dialectica realizer for `EqX i s t`, recover semantic equality. -/
  extract : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)) (env : interpCtx X Γ),
      dialecticaRealizerCtx si (EqX i s t) env →
      interpTerm si s env = interpTerm si t env

