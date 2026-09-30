/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable


namespace Metatheorems

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

-- Witness and Counter types (Definition 3.0.1)

mutual

/-- The **object-level** type of witnesses for `A`'s Dialectica translation, so that a
realizer is a `Term`. -/
def wTy : {Γ : Ctx ι} → Formula F Γ → Ty ι
  | _, .bot      => .unit
  | _, .eq0 _ _  => .unit
  | _, .and A B  => wTy A ×ₜ wTy B
  | _, .or  A B  => Ty.nat ×ₜ (wTy A ×ₜ wTy B)
  | _, .imp A B  => (wTy A →ₜ wTy B) ×ₜ (wTy A →ₜ cTy B →ₜ cTy A)
  | _, .ex  ρ A  => ρ ×ₜ wTy A
  | _, .all ρ A  => ρ →ₜ wTy A

/-- The **object-level** type of counters for `A`'s Dialectica translation. -/
def cTy : {Γ : Ctx ι} → Formula F Γ → Ty ι
  | _, .bot      => .unit
  | _, .eq0 _ _  => .unit
  | _, .and A B  => cTy A ×ₜ cTy B
  | _, .or  A B  => cTy A ×ₜ cTy B
  | _, .imp A B  => wTy A ×ₜ cTy B
  | _, .ex  _ A  => cTy A
  | _, .all ρ A  => ρ ×ₜ cTy A

end

/-- The Lean type of witnesses: the interpretation of the object-level witness type.
Definitionally the clause-by-clause definition — `Unit`, products, function spaces. -/
@[reducible] def dialecticaWitness {ι κ : Type} (X : ι → Type) {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) : Type := Ty.interpret X (wTy A)

/-- The Lean type of counters. -/
@[reducible] def dialecticaCounter {ι κ : Type} (X : ι → Type) {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) : Type := Ty.interpret X (cTy A)

notation "𝕎" => dialecticaWitness
notation "ℂ" => dialecticaCounter

-- Default inhabitants (computable; replace Nonempty.some)

/-- Every `Ty.interpret X ρ` has a computable default: 0 for Nat, zeroInterp for base types,
    constant function for arrow types. -/
def Ty.interpret_default {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) : (ρ : Ty ι) → Ty.interpret X ρ
  | .nat    => Nat.zero
  | .base i => si.zeroInterp i
  | .arr ρ τ => fun _ => Ty.interpret_default si τ
  | .unit    => ()
  | .prod ρ τ => (Ty.interpret_default si ρ, Ty.interpret_default si τ)

mutual
/-- Computable default witness for any formula's Dialectica translation. -/
def dialecticaDefaultWitness {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} : (A : Formula F Γ) → dialecticaWitness X A
  | .bot      => ()
  | .eq0 _ _  => ()
  | .and A B  => (dialecticaDefaultWitness si A, dialecticaDefaultWitness si B)
  | .or  A B  => (0, dialecticaDefaultWitness si A, dialecticaDefaultWitness si B)
  | .imp A B  => (fun _ => dialecticaDefaultWitness si B,
                  fun _ _ => dialecticaDefaultCounter si A)
  | .ex  ρ A  => (Ty.interpret_default si ρ, dialecticaDefaultWitness si A)
  | .all _ A  => fun _ => dialecticaDefaultWitness si A

/-- Computable default counter for any formula's Dialectica translation. -/
def dialecticaDefaultCounter {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} : (A : Formula F Γ) → dialecticaCounter X A
  | .bot      => ()
  | .eq0 _ _  => ()
  | .and A B  => (dialecticaDefaultCounter si A, dialecticaDefaultCounter si B)
  | .or  A B  => (dialecticaDefaultCounter si A, dialecticaDefaultCounter si B)
  | .imp A B  => (dialecticaDefaultWitness si A, dialecticaDefaultCounter si B)
  | .ex  _ A  => dialecticaDefaultCounter si A
  | .all ρ A  => (Ty.interpret_default si ρ, dialecticaDefaultCounter si A)
end

-- The quantifier-free matrix (Definition 3.0.1)

/-- The Dialectica matrix A_D as a Lean proposition (Def. 3.0.1).

Takes an environment `env : Ctx.interpret X Γ` to evaluate the formula's free
variables, witnesses, and counters. -/
def dialecticaMatrix {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (A : Formula F Γ) → Ctx.interpret X Γ →
    dialecticaWitness X A → dialecticaCounter X A → Prop
  | _, .bot,      _,   _,  _  => False
  | _, .eq0 s t,  env, _,  _  => Term.interpret si s env = Term.interpret si t env
  | _, .and A B,  env, xw, yc =>
      dialecticaMatrix si A env xw.1 yc.1 ∧ dialecticaMatrix si B env xw.2 yc.2
  | _, .or  A B,  env, xw, yc =>
      (xw.1 = 0 → dialecticaMatrix si A env xw.2.1 yc.1) ∧
      (xw.1 ≠ 0 → dialecticaMatrix si B env xw.2.2 yc.2)
  | _, .imp A B,  env, xw, yc =>
      dialecticaMatrix si A env yc.1 (xw.2 yc.1 yc.2) →
      dialecticaMatrix si B env (xw.1 yc.1) yc.2
  | _, .ex  _ A,  env, xw, yc =>
      dialecticaMatrix si A (xw.1, env) xw.2 yc
  | _, .all _ A,  env, xw, yc =>
      dialecticaMatrix si A (yc.1, env) (xw yc.1) yc.2

-- Decidability of the matrix

/-- `dialecticaMatrix si A env w y` is decidable for every formula `A`.
    The only atomic case is `eq0`, which gives `ℕ`-equality (decidable);
    all connectives preserve decidability, and `all`/`ex` reduce to a
    single-point evaluation (no quantification). -/
instance dialecticaMatrix_decidable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ)
    (env : Ctx.interpret X Γ) (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
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
      haveI : Decidable (w.1 = 0 → dialecticaMatrix si A env w.2.1 y.1) :=
        if ht : w.1 = 0 then
          if hd : dialecticaMatrix si A env w.2.1 y.1 then isTrue  (fun _ => hd)
          else isFalse (fun h => hd (h ht))
        else isTrue (fun h => absurd h ht)
      haveI : Decidable (w.1 ≠ 0 → dialecticaMatrix si B env w.2.2 y.2) :=
        if hf : w.1 ≠ 0 then
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

-- Convenience

/-- The Dialectica realizer for a formula A in context Γ at environment env.
    This is a *subtype* (not a Prop): the computational witness together with
    a proof it satisfies the matrix for all counters. Because `dialecticaRealizerCtx`
    lives in `Type`, the witness can be extracted computably via `.val`. -/
def dialecticaRealizerCtx {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) (env : Ctx.interpret X Γ) : Type :=
  { x : dialecticaWitness X A //
    ∀ (y : dialecticaCounter X A), dialecticaMatrix si A env x y }

/-- The Dialectica realizer for a closed formula (env = ()). -/
def dialecticaRealizer {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) (A : Formula F ([] : Ctx ι)) : Type :=
  dialecticaRealizerCtx si A ()

-- Subsingleton instances for QF ∨-free formulas

/-- For QF ∨-free formulas, the witness and counter types are subsingletons.
    This is needed for Markov's principle and IP. -/
theorem dialecticaWitness_subsingleton {ι κ : Type} {X : ι → Type}
    {F : κ → Ty ι} {Γ : Ctx ι}
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
def dialecticaDefault {ι κ : Type} {X : ι → Type}
    {F : κ → Ty ι} {Γ : Ctx ι} :
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

-- Type invariance under substitution

/-- Object-level type invariance under substF. -/
theorem wTy_cTy_substF {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (s : Term.Subst F Γ Δ),
    wTy (A.substF s) = wTy A ∧ cTy (A.substF s) = cTy A := by
  induction A with
  | bot => intro Δ s; exact ⟨rfl, rfl⟩
  | eq0 _ _ => intro Δ s; exact ⟨rfl, rfl⟩
  | and _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.substF, wTy, hwA, hwB], by simp only [Formula.substF, cTy, hcA, hcB]⟩
  | or _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.substF, wTy, hwA, hwB], by simp only [Formula.substF, cTy, hcA, hcB]⟩
  | imp _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.substF, wTy, hwA, hwB, hcA, hcB],
           by simp only [Formula.substF, cTy, hwA, hcB]⟩
  | all _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Subst.ext s)
    exact ⟨by simp only [Formula.substF, wTy, hwA], by simp only [Formula.substF, cTy, hcA]⟩
  | ex _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Subst.ext s)
    exact ⟨by simp only [Formula.substF, wTy, hwA], by simp only [Formula.substF, cTy, hcA]⟩

/-- Witness and counter types are invariant under substF. -/
theorem dialectica_types_substF {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) {Δ : Ctx ι} (s : Term.Subst F Γ Δ) :
    dialecticaWitness X (A.substF s) = dialecticaWitness X A ∧
    dialecticaCounter X (A.substF s) = dialecticaCounter X A :=
  ⟨congrArg _ (wTy_cTy_substF A s).1, congrArg _ (wTy_cTy_substF A s).2⟩

/-- Corollaries: type invariance under subst0 and weaken. -/
theorem dialecticaWitness_subst0 {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    dialecticaWitness X (A.subst0 t) = dialecticaWitness X A :=
  (dialectica_types_substF A (Term.subst0_map t)).1

theorem dialecticaCounter_subst0 {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) :
    dialecticaCounter X (A.subst0 t) = dialecticaCounter X A :=
  (dialectica_types_substF A (Term.subst0_map t)).2

-- Type invariance under renaming (needed for ∀/∃-rule)

/-- Object-level type invariance under renameF. -/
theorem wTy_cTy_renameF {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (s : Term.Renaming Γ Δ),
    wTy (A.renameF s) = wTy A ∧ cTy (A.renameF s) = cTy A := by
  induction A with
  | bot => intro Δ s; exact ⟨rfl, rfl⟩
  | eq0 _ _ => intro Δ s; exact ⟨rfl, rfl⟩
  | and _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.renameF, wTy, hwA, hwB], by simp only [Formula.renameF, cTy, hcA, hcB]⟩
  | or _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.renameF, wTy, hwA, hwB], by simp only [Formula.renameF, cTy, hcA, hcB]⟩
  | imp _ _ ihA ihB =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA s; obtain ⟨hwB, hcB⟩ := ihB s
    exact ⟨by simp only [Formula.renameF, wTy, hwA, hwB, hcA, hcB],
           by simp only [Formula.renameF, cTy, hwA, hcB]⟩
  | all _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Renaming.ext s)
    exact ⟨by simp only [Formula.renameF, wTy, hwA], by simp only [Formula.renameF, cTy, hcA]⟩
  | ex _ _ ihA =>
    intro Δ s
    obtain ⟨hwA, hcA⟩ := ihA (Term.Renaming.ext s)
    exact ⟨by simp only [Formula.renameF, wTy, hwA], by simp only [Formula.renameF, cTy, hcA]⟩

/-- Witness and counter types are invariant under renameF. -/
theorem dialectica_types_renameF {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) {Δ : Ctx ι} (s : Term.Renaming Γ Δ) :
    dialecticaWitness X (A.renameF s) = dialecticaWitness X A ∧
    dialecticaCounter X (A.renameF s) = dialecticaCounter X A :=
  ⟨congrArg _ (wTy_cTy_renameF A s).1, congrArg _ (wTy_cTy_renameF A s).2⟩

theorem dialecticaWitness_weaken {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {Γ : Ctx ι} (ρ : Ty ι) (A : Formula F Γ) :
    dialecticaWitness X (A.weakenBy ρ) = dialecticaWitness X A :=
  (dialectica_types_renameF A Renaming.shift).1

theorem dialecticaCounter_weaken {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {Γ : Ctx ι} (ρ : Ty ι) (A : Formula F Γ) :
    dialecticaCounter X (A.weakenBy ρ) = dialecticaCounter X A :=
  (dialectica_types_renameF A Renaming.shift).2

-- Matrix commutativity under renaming

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

/-- Evaluate Ctx.interpretSubst for Renaming.ext applied to var-renaming. -/
private lemma Ctx.interpretSubst_ext_var {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} {ρ' : Ty ι}
    (r : Renaming Γ Δ) (z : Ty.interpret X ρ') (env : Ctx.interpret X Δ) :
    Ctx.interpretSubst si
      (fun v => Term.var ((Renaming.ext r) v) :
        Term.Subst F (ρ' :: Γ) (ρ' :: Δ)) (z, env) =
    (z, Ctx.interpretSubst si
      (fun v => Term.var (r v) : Term.Subst F Γ Δ) env) := by
  simp only [Ctx.interpretSubst, Term.Renaming.ext, Term.interpret, Ctx.lookup]
  congr 1
  exact Ctx.interpretSubst_weaken_eq si (fun v => Term.var (r v)) env z

/-- The Dialectica matrix commutes with formula renaming.
    Key lemma needed for forall-rule, exists-rule, and weakening. -/
theorem dialecticaMatrix_renameF {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (r : Renaming Γ Δ) (env : Ctx.interpret X Δ)
      (w : dialecticaWitness X (A.renameF r))
      (y : dialecticaCounter X (A.renameF r)),
    dialecticaMatrix si (A.renameF r) env w y ↔
    dialecticaMatrix si A (Ctx.interpretSubst si (fun v => .var (r v)) env)
      (cast (dialectica_types_renameF (X := X) A r).1 w)
      (cast (dialectica_types_renameF (X := X) A r).2 y) := by
  induction A with
  | bot => intros; exact Iff.rfl
  | eq0 a b =>
    intro Δ r env _ _
    simp only [Formula.renameF, dialecticaMatrix, cast_eq]
    rw [Term.interpret_rename, Term.interpret_rename]
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
    have hWbig : (Nat × dialecticaWitness X (A1.renameF r) × dialecticaWitness X (A2.renameF r)) =
                 (Nat × dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
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
    rw [Ctx.interpretSubst_ext_var]
  | ex ρ' A' ihA =>
    intro Δ r env w y
    simp only [Formula.renameF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).1,
      cast_prod_snd _ rfl (dialectica_types_renameF (X := X) A' (Renaming.ext r)).1,
      cast_eq]
    rw [ihA (Renaming.ext r) (w.1, env) w.2 y]
    rw [Ctx.interpretSubst_ext_var]

-- Matrix commutativity under substitution

/-- The Dialectica matrix commutes with formula substitution.
    Key: cast witnesses/counters via the type invariance equalities. -/
theorem dialecticaMatrix_substF {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) :
    ∀ {Δ : Ctx ι} (s : Term.Subst F Γ Δ) (env : Ctx.interpret X Δ)
      (w : dialecticaWitness X A) (y : dialecticaCounter X A),
    dialecticaMatrix si (A.substF s) env
      (cast (dialectica_types_substF A s).1.symm w)
      (cast (dialectica_types_substF A s).2.symm y) ↔
    dialecticaMatrix si A (Ctx.interpretSubst si s env) w y := by
  induction A with
  | bot => intro Δ s env w y; exact Iff.rfl
  | eq0 a b =>
    intro Δ s env _ _
    simp only [Formula.substF, dialecticaMatrix, cast_eq]
    constructor
    · intro h; rwa [Term.interpret_substF, Term.interpret_substF] at h
    · intro h; rwa [Term.interpret_substF, Term.interpret_substF]
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
    have hWbig : (Nat × dialecticaWitness X (A1.substF s) × dialecticaWitness X (A2.substF s)) =
                 (Nat × dialecticaWitness X A1 × dialecticaWitness X A2) := by rw [hwA, hwB]
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
    rw [Ctx.interpretSubst_ext] at key
    exact key
  | ex ρ A' ihA =>
    intro Δ s env w y
    simp only [Formula.substF, dialecticaMatrix,
      cast_prod_fst _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).1.symm,
      cast_prod_snd _ rfl (dialectica_types_substF A' (Term.Subst.ext s)).1.symm,
      cast_eq]
    have key := ihA (Term.Subst.ext s) (w.1, env) w.2 y
    rw [Ctx.interpretSubst_ext] at key
    exact key

theorem dialecticaMatrix_subst0 {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F Γ ρ) (env : Ctx.interpret X Γ)
    (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
    dialecticaMatrix si (A.subst0 t) env
      (cast (dialecticaWitness_subst0 A t).symm w)
      (cast (dialecticaCounter_subst0 A t).symm y) ↔
    dialecticaMatrix si A (Term.interpret si t env, env) w y := by
  have h := dialecticaMatrix_substF si A (Term.subst0_map t) env w y
  rwa [Ctx.interpretSubst_subst0_map] at h

theorem dialecticaMatrix_substVar0 {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ)
    (v : Ty.interpret X ρ) (env : Ctx.interpret X Γ)
    (w : dialecticaWitness X A) (y : dialecticaCounter X A) :
    dialecticaMatrix si (A.substVar0 t) (v, env)
      (cast (dialectica_types_substF A (Term.substVar0_map t)).1.symm w)
      (cast (dialectica_types_substF A (Term.substVar0_map t)).2.symm y) ↔
    dialecticaMatrix si A (Term.interpret si t (v, env), env) w y := by
  have h := dialecticaMatrix_substF si A (Term.substVar0_map t) (v, env) w y
  rwa [Ctx.interpretSubst_substVar0_map] at h

-- Matrix commutativity under weakening (needed for ∀/∃-rule)

/-- The Dialectica matrix is invariant under formula weakening.
    Witnesses/counters for A.weakenBy ρ correspond to those for A,
    and the matrix value at (v, env) equals that at env. -/
theorem dialecticaMatrix_weaken {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F Γ)
    (env : Ctx.interpret X Γ) (v : Ty.interpret X ρ)
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
  -- key : ... ↔ dialecticaMatrix si A (Ctx.interpretSubst ... (v, env)) (cast ... w) (cast ... y)
  -- Need: Ctx.interpretSubst si (fun v => .var (Var.vs v)) (v, env) = env
  have henv : Ctx.interpretSubst si
      (fun {τ} (x : Var Γ τ) =>
        Term.var (Renaming.shift x) : Term.Subst F Γ (ρ :: Γ))
      (v, env) = env := by
    simp only [Term.Renaming.shift]
    have h1 : (fun {τ : Ty ι} (x : Var Γ τ) =>
                (Term.var (Var.vs x) : Term F (ρ :: Γ) τ)) =
              (fun {τ : Ty ι} (x : Var Γ τ) =>
                (Term.var x : Term F Γ τ).weaken) := by
      funext τ x; rfl
    rw [h1, Ctx.interpretSubst_weaken_eq, Ctx.interpretSubst_id]
  rw [henv] at key
  exact key

-- Realizers for purely universal, ∨-free formulas

/-- For a **quantifier-free ∨-free** formula, the Dialectica matrix is the formula's own
semantic interpretation — at *every* witness and *every* counter, because both types are
subsingletons (`dialecticaWitness_subsingleton`). Same statement as
`dialecticaMatrix_iff_interpFormula` (`MetatheoremPrereqs.lean`), available lower down. -/
theorem dialecticaMatrix_iff_interp_qf {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) (hvf : A.isVFree = true)
    (env : Ctx.interpret X Γ) (w : 𝕎 X A) (c : ℂ X A) :
    dialecticaMatrix si A env w c ↔ Formula.interpret si A env :=
  match A, hqf, hvf, env, w, c with
  | .bot, _, _, _, _, _ => Iff.rfl
  | .eq0 .., _, _, _, _, _ => Iff.rfl
  | .and A B, hqf, hvf, env, (wA, wB), (cA, cB) => by
    simp only [Formula.isQF, Formula.isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    exact Iff.and
      (dialecticaMatrix_iff_interp_qf si A hqf.1 hvf.1 env wA cA)
      (dialecticaMatrix_iff_interp_qf si B hqf.2 hvf.2 env wB cB)
  | .or .., _, hvf, _, _, _ => by simp [Formula.isVFree] at hvf
  | .imp A B, hqf, hvf, env, (f, g), (wA, cB) => by
    simp only [Formula.isQF, Formula.isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    constructor
    · intro h hA
      have := (dialecticaMatrix_iff_interp_qf si A hqf.1 hvf.1 env wA (g wA cB)).mpr hA
      exact (dialecticaMatrix_iff_interp_qf si B hqf.2 hvf.2 env (f wA) cB).mp (h this)
    · intro h hM
      have := (dialecticaMatrix_iff_interp_qf si A hqf.1 hvf.1 env wA (g wA cB)).mp hM
      exact (dialecticaMatrix_iff_interp_qf si B hqf.2 hvf.2 env (f wA) cB).mpr (h this)

/-- **A purely universal ∨-free formula is Dialectica-realized by its own truth.** Its
witness type is a singleton, so all the content is the hypothesis `htrue`.
`srealizer_of_pu` (`Dialectica/Syntactic.lean`) is the syntactic counterpart. -/
def realizer_of_pu {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (B : Formula F Γ) →
      B.isPurelyUniversal = true → B.isVFree = true →
      (∀ env : Ctx.interpret X Γ, Formula.interpret si B env) →
      ∀ env : Ctx.interpret X Γ, dialecticaRealizerCtx si B env
  | _, .all _ A, hpu, hvf, htrue, env =>
      have r : ∀ v, dialecticaRealizerCtx si A (v, env) := fun v =>
        realizer_of_pu si A hpu hvf (fun e => htrue e.2 e.1) (v, env)
      ⟨fun v => (r v).val, fun y => (r y.1).property y.2⟩
  | _, .and A B, hpu, hvf, htrue, env =>
      have hpuA : A.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.1
      have hpuB : B.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.2
      have hvfA : A.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.1
      have hvfB : B.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.2
      have rA : dialecticaRealizerCtx si A env :=
        realizer_of_pu si A hpuA hvfA (fun e => (htrue e).1) env
      have rB : dialecticaRealizerCtx si B env :=
        realizer_of_pu si B hpuB hvfB (fun e => (htrue e).2) env
      ⟨(rA.val, rB.val), fun y => ⟨rA.property y.1, rB.property y.2⟩⟩
  | _, .bot, hpu, hvf, htrue, env =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr (htrue env)⟩
  | _, .eq0 _ _, hpu, hvf, htrue, env =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr (htrue env)⟩
  | _, .or _ _, hpu, hvf, htrue, env =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr (htrue env)⟩
  | _, .imp _ _, hpu, hvf, htrue, env =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr (htrue env)⟩
  | _, .ex _ _, hpu, hvf, htrue, env =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr (htrue env)⟩

/-- `realizer_of_pu` at a **single** environment: truth at `env` suffices. -/
def realizer_of_pu_at {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (B : Formula F Γ) →
      B.isPurelyUniversal = true → B.isVFree = true →
      (env : Ctx.interpret X Γ) → Formula.interpret si B env →
      dialecticaRealizerCtx si B env
  | _, .all _ A, hpu, hvf, env, htrue =>
      have r : ∀ v, dialecticaRealizerCtx si A (v, env) := fun v =>
        realizer_of_pu_at si A hpu hvf (v, env) (htrue v)
      ⟨fun v => (r v).val, fun y => (r y.1).property y.2⟩
  | _, .and A B, hpu, hvf, env, htrue =>
      have hpuA : A.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.1
      have hpuB : B.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.2
      have hvfA : A.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.1
      have hvfB : B.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.2
      have rA : dialecticaRealizerCtx si A env :=
        realizer_of_pu_at si A hpuA hvfA env htrue.1
      have rB : dialecticaRealizerCtx si B env :=
        realizer_of_pu_at si B hpuB hvfB env htrue.2
      ⟨(rA.val, rB.val), fun y => ⟨rA.property y.1, rB.property y.2⟩⟩
  | _, .bot, hpu, hvf, env, htrue =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr htrue⟩
  | _, .eq0 _ _, hpu, hvf, env, htrue =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr htrue⟩
  | _, .or _ _, hpu, hvf, env, htrue =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr htrue⟩
  | _, .imp _ _, hpu, hvf, env, htrue =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr htrue⟩
  | _, .ex _ _, hpu, hvf, env, htrue =>
      ⟨dialecticaDefaultWitness si _,
       fun c => (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ c).mpr htrue⟩

/-- The converse of `realizer_of_pu_at`: for a purely universal ∨-free formula, a realizer
gives back the formula's truth in the model. -/
def interp_of_realizer_pu {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (B : Formula F Γ) →
      B.isPurelyUniversal = true → B.isVFree = true →
      (env : Ctx.interpret X Γ) → dialecticaRealizerCtx si B env →
      Formula.interpret si B env
  | _, .all _ A, hpu, hvf, env, r => fun v =>
      interp_of_realizer_pu si A hpu hvf (v, env)
        ⟨r.val v, fun y => r.property ⟨v, y⟩⟩
  | _, .and A B, hpu, hvf, env, r =>
      have hpuA : A.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.1
      have hpuB : B.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.2
      have hvfA : A.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.1
      have hvfB : B.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.2
      ⟨interp_of_realizer_pu si A hpuA hvfA env
          ⟨r.val.1, fun y => (r.property (y, dialecticaDefaultCounter si B)).1⟩,
       interp_of_realizer_pu si B hpuB hvfB env
          ⟨r.val.2, fun y => (r.property (dialecticaDefaultCounter si A, y)).2⟩⟩
  | _, .bot, hpu, hvf, env, r =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ _).mp
        (r.property (dialecticaDefaultCounter si _))
  | _, .eq0 _ _, hpu, hvf, env, r =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ _).mp
        (r.property (dialecticaDefaultCounter si _))
  | _, .or _ _, hpu, hvf, env, r =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ _).mp
        (r.property (dialecticaDefaultCounter si _))
  | _, .imp _ _, hpu, hvf, env, r =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ _).mp
        (r.property (dialecticaDefaultCounter si _))
  | _, .ex _ _, hpu, hvf, env, r =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env _ _).mp
        (r.property (dialecticaDefaultCounter si _))

-- The matrix of a ∀-formula / an ∃-formula against its truth (Kohlenbach 17.52 shapes)

/-- **A true purely universal ∨-free formula has a true matrix at EVERY witness and every
counter.** Used for a ∀-formula premise matrix `B∀` (Kohlenbach 17.52). -/
theorem dialecticaMatrix_of_interp_pu {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (B : Formula F Γ) →
      B.isPurelyUniversal = true → B.isVFree = true →
      (env : Ctx.interpret X Γ) → Formula.interpret si B env →
      ∀ (w : 𝕎 X B) (y : ℂ X B), dialecticaMatrix si B env w y
  | _, .all _ A, hpu, hvf, env, htrue, w, y =>
      dialecticaMatrix_of_interp_pu si A hpu hvf (y.1, env) (htrue y.1) (w y.1) y.2
  | _, .and A B, hpu, hvf, env, htrue, w, y =>
      have hpuA : A.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.1
      have hpuB : B.isPurelyUniversal = true := by
        simp only [Formula.isPurelyUniversal, Bool.and_eq_true] at hpu; exact hpu.2
      have hvfA : A.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.1
      have hvfB : B.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.2
      ⟨dialecticaMatrix_of_interp_pu si A hpuA hvfA env htrue.1 w.1 y.1,
       dialecticaMatrix_of_interp_pu si B hpuB hvfB env htrue.2 w.2 y.2⟩
  | _, .bot, hpu, hvf, env, htrue, w, y =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env w y).mpr htrue
  | _, .eq0 _ _, hpu, hvf, env, htrue, w, y =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env w y).mpr htrue
  | _, .or _ _, hpu, hvf, env, htrue, w, y =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env w y).mpr htrue
  | _, .imp _ _, hpu, hvf, env, htrue, w, y =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env w y).mpr htrue
  | _, .ex _ _, hpu, hvf, env, htrue, w, y =>
      (dialecticaMatrix_iff_interp_qf si _ hpu hvf env w y).mpr htrue

/-- **A purely existential ∨-free formula whose matrix holds at some witness, against ANY
counter, is true.** The dual of `dialecticaMatrix_of_interp_pu`; used for an ∃-formula
conclusion matrix `C∃` (Kohlenbach 17.52). -/
theorem interp_of_dialecticaMatrix_pe {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) :
    {Γ : Ctx ι} → (C : Formula F Γ) →
      C.isPurelyExistential = true → C.isVFree = true →
      (env : Ctx.interpret X Γ) → (w : 𝕎 X C) → (y : ℂ X C) →
      dialecticaMatrix si C env w y → Formula.interpret si C env
  | _, .ex _ A, hpe, hvf, env, w, y, hm =>
      ⟨w.1, interp_of_dialecticaMatrix_pe si A hpe hvf (w.1, env) w.2 y hm⟩
  | _, .and A B, hpe, hvf, env, w, y, hm =>
      have hpeA : A.isPurelyExistential = true := by
        simp only [Formula.isPurelyExistential, Bool.and_eq_true] at hpe; exact hpe.1
      have hpeB : B.isPurelyExistential = true := by
        simp only [Formula.isPurelyExistential, Bool.and_eq_true] at hpe; exact hpe.2
      have hvfA : A.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.1
      have hvfB : B.isVFree = true := by
        simp only [Formula.isVFree, Bool.and_eq_true] at hvf; exact hvf.2
      ⟨interp_of_dialecticaMatrix_pe si A hpeA hvfA env w.1 y.1 hm.1,
       interp_of_dialecticaMatrix_pe si B hpeB hvfB env w.2 y.2 hm.2⟩
  | _, .bot, hpe, hvf, env, w, y, hm =>
      (dialecticaMatrix_iff_interp_qf si _ hpe hvf env w y).mp hm
  | _, .eq0 _ _, hpe, hvf, env, w, y, hm =>
      (dialecticaMatrix_iff_interp_qf si _ hpe hvf env w y).mp hm
  | _, .or _ _, hpe, hvf, env, w, y, hm =>
      (dialecticaMatrix_iff_interp_qf si _ hpe hvf env w y).mp hm
  | _, .imp _ _, hpe, hvf, env, w, y, hm =>
      (dialecticaMatrix_iff_interp_qf si _ hpe hvf env w y).mp hm
  | _, .all _ _, hpe, hvf, env, w, y, hm =>
      (dialecticaMatrix_iff_interp_qf si _ hpe hvf env w y).mp hm

/-- Quantifier-free formulas are purely universal. -/
theorem Formula.isPurelyUniversal_of_qf {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) : A.isPurelyUniversal = true := by
  cases A with
  | and A B =>
    simp only [Formula.isQF, Bool.and_eq_true] at hqf
    simp only [Formula.isPurelyUniversal, Bool.and_eq_true]
    exact ⟨Formula.isPurelyUniversal_of_qf A hqf.1, Formula.isPurelyUniversal_of_qf B hqf.2⟩
  | all _ _ => exact absurd hqf (by simp [Formula.isQF])
  | bot => exact hqf
  | eq0 _ _ => exact hqf
  | or _ _ => exact hqf
  | imp _ _ => exact hqf
  | ex _ _ => exact hqf

/-- Quantifier-free formulas are purely existential. -/
theorem Formula.isPurelyExistential_of_qf {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) : A.isPurelyExistential = true := by
  cases A with
  | and A B =>
    simp only [Formula.isQF, Bool.and_eq_true] at hqf
    simp only [Formula.isPurelyExistential, Bool.and_eq_true]
    exact ⟨Formula.isPurelyExistential_of_qf A hqf.1, Formula.isPurelyExistential_of_qf B hqf.2⟩
  | ex _ _ => exact absurd hqf (by simp [Formula.isQF])
  | bot => exact hqf
  | eq0 _ _ => exact hqf
  | or _ _ => exact hqf
  | imp _ _ => exact hqf
  | all _ _ => exact hqf

-- Base-type equality is *defined*, so its Dialectica data is computable

/-! `eqAtType (.base i) s t ≡ eq_R (d_i s t) 0ℝ` is `Formula.all .nat <QF>`, so `wTy` of it
is `nat →ₜ unit` and `cTy` is `nat ×ₜ unit` by `rfl`. Its canonical witness, counter and the
subsingleton fact are therefore definitions; `eqAtTypeBaseRealizeTerm` is in
`Dialectica/Syntactic.lean`. -/

theorem wTy_eqAtType_base {ι κ : Type} {F : κ → Ty ι} (i : ι) {Γ : Ctx ι}
    (s t : Term F Γ (Ty.base i)) :
    wTy (eqAtType (Ty.base i) s t) = (Ty.nat →ₜ Ty.unit) := rfl

theorem cTy_eqAtType_base {ι κ : Type} {F : κ → Ty ι} (i : ι) {Γ : Ctx ι}
    (s t : Term F Γ (Ty.base i)) :
    cTy (eqAtType (Ty.base i) s t) = (Ty.nat ×ₜ Ty.unit) := rfl

/-- The canonical Dialectica witness for equality at a base type: the witness type is
`ℕ → Unit`, so `fun _ => ()` is the only inhabitant. -/
def eqAtTypeBaseWitness {ι κ : Type} (X : ι → Type) {F : κ → Ty ι} (i : ι) {Γ : Ctx ι}
    (s t : Term F Γ (Ty.base i)) : dialecticaWitness X (eqAtType (Ty.base i) s t) :=
  fun _ => ()

/-- The canonical Dialectica counter for equality at a base type: the counter type is
`ℕ × Unit`. -/
def eqAtTypeBaseCounter {ι κ : Type} (X : ι → Type) {F : κ → Ty ι} (i : ι) {Γ : Ctx ι}
    (s t : Term F Γ (Ty.base i)) : dialecticaCounter X (eqAtType (Ty.base i) s t) :=
  (0, ())

/-- The witness type for equality at a base type is a subsingleton — it is `ℕ → Unit`. -/
theorem eqAtTypeBaseWitness_subsingleton {ι κ : Type} (X : ι → Type) {F : κ → Ty ι} (i : ι)
    {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)) :
    Subsingleton (dialecticaWitness X (eqAtType (Ty.base i) s t)) :=
  ⟨fun _ _ => funext fun _ => rfl⟩

-- EqX interface for the Dialectica proof (Def. of "purely universal" EqX)

/-- The Dialectica interface for base-type equality at each base type `X_i`. It asks only for
model facts — things true of the space and not derivable from the syntax.

The four fields:

1. `realize` — semantic equality gives a Dialectica realizer; needs `d(x,x) = 0`.
2. `extract` — a realizer gives semantic equality; needs *separation*, `d(x,y) = 0 → x = y`.
3. `dist_comm_holds` — the model fact behind `Derivable.dist_comm`.
4. `dist_tri_holds` — the model fact behind `Derivable.dist_tri`.

Concrete theories (e.g. metric spaces) supply an `EqXInterp` for their model. -/
structure EqXInterp {ι κ : Type} (X : ι → Type) (F : κ → Ty ι)
    (si : SpaceInterp X F) where
  /-- From semantic equality, build a Dialectica realizer for `EqX i s t`. -/
  realize : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)) (env : Ctx.interpret X Γ),
      Term.interpret si s env = Term.interpret si t env →
      dialecticaRealizerCtx si (eqAtType (Ty.base i) s t) env
  /-- From a Dialectica realizer for `EqX i s t`, recover semantic equality. -/
  extract : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)) (env : Ctx.interpret X Γ),
      dialecticaRealizerCtx si (eqAtType (Ty.base i) s t) env →
      Term.interpret si s env = Term.interpret si t env
  /-- `si.distInterp i` is symmetric, in the sense the object language asserts — the model
      fact behind the constructor `Derivable.dist_comm`. The realizer and realizing term are
      built from it (`EqXInterp.dist_comm_realize`, `sDistComm`). -/
  dist_comm_holds : ∀ (i : ι) {Γ : Ctx ι} (x y : Term F Γ (Ty.base i))
      (env : Ctx.interpret X Γ),
      Formula.interpret si
        (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env
  /-- `si.distInterp i` satisfies the triangle inequality. The counterpart of
      `Derivable.dist_tri`, owed for the same reason as `dist_comm_holds`. -/
  dist_tri_holds : ∀ (i : ι) {Γ : Ctx ι} (x y z : Term F Γ (Ty.base i))
      (env : Ctx.interpret X Γ),
      Formula.interpret si
        (le_R_pu (Term.app2 (Term.dist i) x z)
          (Term.app2 Term.add_R
            (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))) env

/-- Symmetry of the distance, as a Dialectica realizer, derived from the model fact
`dist_comm_holds` by `realizer_of_pu`. -/
def EqXInterp.dist_comm_realize {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (eqxi : EqXInterp X F si)
    (i : ι) {Γ : Ctx ι} (x y : Term F Γ (Ty.base i)) (env : Ctx.interpret X Γ) :
    dialecticaRealizerCtx si
      (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env :=
  realizer_of_pu si _ rfl rfl (eqxi.dist_comm_holds i x y) env

/-- The triangle inequality, as a Dialectica realizer. Derived from `dist_tri_holds`
exactly as `dist_comm_realize` is. -/
def EqXInterp.dist_tri_realize {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (eqxi : EqXInterp X F si)
    (i : ι) {Γ : Ctx ι} (x y z : Term F Γ (Ty.base i)) (env : Ctx.interpret X Γ) :
    dialecticaRealizerCtx si
      (le_R_pu (Term.app2 (Term.dist i) x z)
        (Term.app2 Term.add_R
          (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))) env :=
  realizer_of_pu si _ rfl rfl (eqxi.dist_tri_holds i x y z) env

end Metatheorems
