/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics


namespace Metatheorems

/-!
# Strong Majorizability (total majorizer)

This file defines the "strong" version of majorizability where every semantic
value is majorizable (via a total `majorizer` function), following the Lean 3
formalization. This is stronger than `AbstractMajorizability` (which only
guarantees constants are majorizable), but is the natural assumption for
the general metatheorem.

## Main Definitions

* `Majorizability` — structure with a total majorizer on all semantic values
-/

-- ============================================================================
-- Majorizability (strong version with total majorizer)
-- ============================================================================

/-- The majorizability *relation* and the two properties the metatheorem uses.

This is everything `metatheorem_core` needs apart from the majorants themselves, and
unlike `Majorizability` below it is inhabited — see `bezemRel`. -/
structure MajorizabilityRel {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) where
  /-- The majorizability relation at type ρ: `maj ρ x_star x` means x* ≥*_ρ x. -/
  maj : (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ → Prop
  /-- Property 1: respects the natural number order. -/
  maj_le : ∀ {n m : Nat}, maj .nat n m → n ≥ m
  /-- Property 2: respects term application. -/
  maj_app : ∀ {ρ τ : Ty ι}
    {f_star : Ty.interpret X (ρ →ₜ τ).hat} {f : Ty.interpret X (ρ →ₜ τ)}
    {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ},
    maj (ρ →ₜ τ) f_star f → maj ρ x_star x → maj τ (f_star x_star) (f x)

/-- Majorizability with a total majorizer on all semantic values.

This is the "strong" version: instead of proving each constant is majorizable
and deriving closed terms, we directly assume every element of the type
structure has a majorant. This matches the Lean 3 formalization and makes
the general metatheorem straightforward to state.

**Caution.** Over the full set-theoretic type structure the `majorizer` field is not
satisfiable for any relation that is genuinely a majorization: at type `(nat →ₜ nat) →ₜ nat`
one would need, for each `Φ`, a `Φ*` with `Φ* f* ≥ Φ f` whenever `f*` majorizes `f`; taking
`f* = id` the majorized `f` range over all `f` with `f n ≤ n`, an infinite set on which an
arbitrary `Φ` is unbounded. Degenerate choices (e.g. `maj := Eq` when `ρ.hat = ρ`) do satisfy
it, but then the bound depends on `x` itself and carries no uniformity. Prefer
`MajorizabilityRel` plus explicit majorants — `metatheorem_core_of_majorants`. -/
structure Majorizability {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) extends MajorizabilityRel si where
  /-- Total majorizer: every semantic value has a majorant. -/
  majorizer : {ρ : Ty ι} → Ty.interpret X ρ → Ty.interpret X ρ.hat
  /-- The majorizer actually majorizes. -/
  majorizer_maj : ∀ {ρ : Ty ι} (x : Ty.interpret X ρ), maj ρ (majorizer x) x

-- ============================================================================
-- The Bezem relation: a concrete `MajorizabilityRel`
-- ============================================================================

/-- The majorizability relation **restricted to hat types**: `hatMaj ρ a b` is the document's
`a ≽ᵃ_ρ̂ b`.

Both arguments live in `Ty.interpret X ρ.hat`, which is legitimate because `Ty.hat` is
idempotent (`Ty.hat_idempotent`) — the "star side" of `≽ᵃ_ρ̂` is `ρ̂̂ = ρ̂`. Indexing by `ρ`
rather than by `ρ̂` is what keeps the definition **cast-free**: `ρ̂.hat = ρ̂` is a propositional
equality, not a definitional one, so a literal `bezemMaj base ρ.hat` would need a transport
at every use.

Note it does not mention `base` at all: at a base type `ρ̂ = nat`, so the space-specific
clause has already disappeared. `hatMaj` is therefore a purely type-directed relation on the
nat-based part of the structure. -/
def hatMaj {ι : Type} {X : ι → Type} :
    (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ.hat → Prop
  | .nat,     n,       m => @GE.ge Nat _ n m
  | .base _,  n,       m => @GE.ge Nat _ n m
  | .arr ρ τ, f_star,  f =>
      (∀ (x_star x : Ty.interpret X ρ.hat),
          hatMaj ρ x_star x → hatMaj τ (f_star x_star) (f x))
      ∧ (∀ (x_star x : Ty.interpret X ρ.hat),
          hatMaj ρ x_star x → hatMaj τ (f_star x_star) (f_star x))
  | .unit,    _,       _ => True
  | .prod ρ τ, p_star, p => hatMaj ρ p_star.1 p.1 ∧ hatMaj τ p_star.2 p.2

/-- Bezem's strong majorizability `≽ᵃ`, parametric in the relation used at the base types.

At `nat` it is `≥`; at an arrow it is the document's **conjunction**
(`particular-cases-metric-spaces.tex:19`)

    x ≽ᵃ_{ρ→τ} y  :≡  ∀z',z (z' ≽ᵃ_ρ z → x z' ≽ᵃ_τ y z)
                    ∧  ∀z',z (z' ≽ᵃ_ρ̂ z → x z' ≽ᵃ_τ̂ x z)     -- self-majorization

the second conjunct being `hatMaj (ρ →ₜ τ) f_star f_star` spelled out. `Ty.hat` sends every
base type to `nat`, so `base i` relates a natural to a point of `X i` — that is Def. 6.0.1's
"majorized by a natural relative to a reference point", and it is exactly the
space-specific datum.

**Widened to two clauses on 2026-09-02** (it used to carry only the first conjunct, i.e.
Howard majorizability). The self-majorization clause is what makes `bezem_prec_maj` provable:
the document's induction (`.tex:82–96`) gives `R n y* z* ≽ R n y z` at *equal* `n`, while
`maj` at `nat →ₜ ρ` demands `n* ≥ n → …`, and the bridge is `hatMaj_of_bezemMaj` plus
`bezemMaj_of_hatMaj`. -/
def bezemMaj {ι : Type} {X : ι → Type} (base : (i : ι) → Nat → X i → Prop) :
    (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ → Prop
  | .nat,     n,       m => @GE.ge Nat _ n m
  | .base i,  n,       x => base i n x
  | .arr ρ τ, f_star,  f =>
      (∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
          bezemMaj base ρ x_star x → bezemMaj base τ (f_star x_star) (f x))
      ∧ (∀ (x_star x : Ty.interpret X ρ.hat),
          hatMaj ρ x_star x → hatMaj τ (f_star x_star) (f_star x))
  -- `unit` is a singleton, so nothing to bound; a product is bounded componentwise
  | .unit,    _,       _ => True
  | .prod ρ τ, p_star, p => bezemMaj base ρ p_star.1 p.1 ∧ bezemMaj base τ p_star.2 p.2

/-- The self-majorization clause of `bezemMaj` at an arrow type, packaged as `hatMaj`. -/
theorem bezemMaj_arr_self {ι : Type} {X : ι → Type} {base : (i : ι) → Nat → X i → Prop}
    {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat} {f : Ty.interpret X (ρ →ₜ τ)}
    (h : bezemMaj base (ρ →ₜ τ) f_star f) : hatMaj (ρ →ₜ τ) f_star f_star :=
  ⟨h.2, h.2⟩

-- ============================================================================
-- Structural lemmas about `hatMaj` and the two-clause `bezemMaj`
-- ============================================================================

section BezemLemmas

variable {ι : Type} {X : ι → Type}

/-- `≽ᵃ_ρ̂` entails self-majorization on the left. This is the whole point of the second
conjunct: at an arrow type the two conjuncts of `hatMaj` coincide when the right-hand
argument is the left one. -/
theorem hatMaj_self : ∀ (ρ : Ty ι) (a b : Ty.interpret X ρ.hat), hatMaj ρ a b → hatMaj ρ a a := by
  intro ρ
  induction ρ with
  | nat => intro a _ _; exact Nat.le_refl a
  | base _ => intro a _ _; exact Nat.le_refl a
  | unit => intro _ _ _; trivial
  | arr ρ τ _ _ => intro _ _ h; exact ⟨h.2, h.2⟩
  | prod ρ τ ihρ ihτ => intro a b h; exact ⟨ihρ _ _ h.1, ihτ _ _ h.2⟩

/-- `≽ᵃ` at hat types is transitive. -/
theorem hatMaj_trans : ∀ (ρ : Ty ι) (a b c : Ty.interpret X ρ.hat),
    hatMaj ρ a b → hatMaj ρ b c → hatMaj ρ a c := by
  intro ρ
  induction ρ with
  | nat => intro _ _ _ h₁ h₂; exact Nat.le_trans h₂ h₁
  | base _ => intro _ _ _ h₁ h₂; exact Nat.le_trans h₂ h₁
  | unit => intro _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c h₁ h₂
    refine ⟨fun x_star x hx => ?_, h₁.2⟩
    exact ihτ _ _ _ (h₁.1 x_star x_star (hatMaj_self ρ _ _ hx)) (h₂.1 x_star x hx)
  | prod ρ τ ihρ ihτ =>
    intro a b c h₁ h₂
    exact ⟨ihρ _ _ _ h₁.1 h₂.1, ihτ _ _ _ h₁.2 h₂.2⟩

/-- A majorant majorizes itself, at hat types. This is the fact the second conjunct was
introduced to supply, and it is what lets `hatMaj` information be produced from a plain
majorization hypothesis. -/
theorem hatMaj_of_bezemMaj {base : (i : ι) → Nat → X i → Prop} :
    ∀ (ρ : Ty ι) (a : Ty.interpret X ρ.hat) (b : Ty.interpret X ρ),
      bezemMaj base ρ a b → hatMaj ρ a a := by
  intro ρ
  induction ρ with
  | nat => intro a _ _; exact Nat.le_refl a
  | base _ => intro a _ _; exact Nat.le_refl a
  | unit => intro _ _ _; trivial
  | arr ρ τ _ _ => intro _ _ h; exact ⟨h.2, h.2⟩
  | prod ρ τ ihρ ihτ => intro a b h; exact ⟨ihρ _ _ h.1, ihτ _ _ h.2⟩

/-- Monotonicity of the base-type relation in its numeric argument. Needed to compose a
hat-level majorization with a genuine one; it holds for the metric relation
`base i n x :≡ n ≥ d(a, x)`. -/
abbrev BaseMono (base : (i : ι) → Nat → X i → Prop) : Prop :=
  ∀ (i : ι) (n m : Nat) (x : X i), n ≥ m → base i m x → base i n x

/-- **Mixed transitivity.** `a ≽ᵃ_ρ̂ b` and `b ≽ᵃ_ρ c` give `a ≽ᵃ_ρ c`. This is the bridge the
recursor majorant needs, and it is unavailable without the self-majorization conjunct. -/
theorem bezemMaj_of_hatMaj {base : (i : ι) → Nat → X i → Prop} (hbase : BaseMono base) :
    ∀ (ρ : Ty ι) (a b : Ty.interpret X ρ.hat) (c : Ty.interpret X ρ),
      hatMaj ρ a b → bezemMaj base ρ b c → bezemMaj base ρ a c := by
  intro ρ
  induction ρ with
  | nat => intro _ _ _ h₁ h₂; exact Nat.le_trans h₂ h₁
  | base i => intro _ _ _ h₁ h₂; exact hbase i _ _ _ h₁ h₂
  | unit => intro _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c h₁ h₂
    refine ⟨fun x_star x hx => ?_, h₁.2⟩
    exact ihτ _ _ _ (h₁.1 x_star x_star (hatMaj_of_bezemMaj ρ _ _ hx)) (h₂.1 x_star x hx)
  | prod ρ τ ihρ ihτ =>
    intro a b c h₁ h₂
    exact ⟨ihρ _ _ _ h₁.1 h₂.1, ihτ _ _ _ h₁.2 h₂.2⟩

end BezemLemmas

/-- `bezemMaj` satisfies the two properties the metatheorem uses. Both come from the *first*
conjunct, which is why the widening leaves `general_metatheorem` untouched. -/
def bezemRel {ι : Type} {X : ι → Type} {F : ι → Ty ι} (si : SpaceInterp X F)
    (base : (i : ι) → Nat → X i → Prop) : MajorizabilityRel si where
  maj := bezemMaj base
  maj_le h := by simpa [bezemMaj] using h
  maj_app hf hx := hf.1 _ _ hx

-- ============================================================================
-- Pointwise maximum at hat types (for the recursor majorant)
-- ============================================================================

section MaxT

variable {ι : Type} {X : ι → Type}

/-- Pointwise maximum on the nat-based part of the type structure. Defined only at hat
types, which is all the recursor majorant needs — `ρ̂` is built from `nat`, `unit`, `→` and
`×`, so a maximum exists componentwise. -/
def maxT : (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ.hat → Ty.interpret X ρ.hat
  | .nat,      a, b => (max (a : Nat) (b : Nat) : Nat)
  | .base _,   a, b => (max (a : Nat) (b : Nat) : Nat)
  | .unit,     _, _ => ()
  | .arr _ τ,  f, g => fun x => maxT τ (f x) (g x)
  | .prod ρ τ, p, q => (maxT ρ p.1 q.1, maxT τ p.2 q.2)

/-- `maxT` is a congruence for `hatMaj`. -/
theorem maxT_hatMaj : ∀ (ρ : Ty ι) (a b c d : Ty.interpret X ρ.hat),
    hatMaj ρ a b → hatMaj ρ c d → hatMaj ρ (maxT ρ a c) (maxT ρ b d) := by
  intro ρ
  induction ρ with
  | nat => intro a b c d h₁ h₂; simp only [hatMaj, maxT] at *; omega
  | base _ => intro a b c d h₁ h₂; simp only [hatMaj, maxT] at *; omega
  | unit => intro _ _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c d h₁ h₂
    exact ⟨fun x_star x hx => ihτ _ _ _ _ (h₁.1 x_star x hx) (h₂.1 x_star x hx),
           fun x_star x hx => ihτ _ _ _ _ (h₁.2 x_star x hx) (h₂.2 x_star x hx)⟩
  | prod ρ τ ihρ ihτ =>
    intro a b c d h₁ h₂
    exact ⟨ihρ _ _ _ _ h₁.1 h₂.1, ihτ _ _ _ _ h₁.2 h₂.2⟩

/-- `maxT ρ a b` majorizes whatever `a` majorizes, provided `b` majorizes itself. -/
theorem maxT_hatMaj_left : ∀ (ρ : Ty ι) (a b c : Ty.interpret X ρ.hat),
    hatMaj ρ a c → hatMaj ρ b b → hatMaj ρ (maxT ρ a b) c := by
  intro ρ
  induction ρ with
  | nat => intro a b c h _; simp only [hatMaj, maxT] at *; omega
  | base _ => intro a b c h _; simp only [hatMaj, maxT] at *; omega
  | unit => intro _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c h₁ h₂
    refine ⟨fun x_star x hx => ihτ _ _ _ (h₁.1 x_star x hx)
              (h₂.1 x_star x_star (hatMaj_self ρ _ _ hx)), ?_⟩
    exact (maxT_hatMaj (ρ →ₜ τ) a a b b (hatMaj_self _ _ _ h₁) h₂).2
  | prod ρ τ ihρ ihτ =>
    intro a b c h₁ h₂
    exact ⟨ihρ _ _ _ h₁.1 h₂.1, ihτ _ _ _ h₁.2 h₂.2⟩

/-- `maxT ρ a b` majorizes whatever `b` majorizes, provided `a` majorizes itself. -/
theorem maxT_hatMaj_right : ∀ (ρ : Ty ι) (a b c : Ty.interpret X ρ.hat),
    hatMaj ρ b c → hatMaj ρ a a → hatMaj ρ (maxT ρ a b) c := by
  intro ρ
  induction ρ with
  | nat => intro a b c h _; simp only [hatMaj, maxT] at *; omega
  | base _ => intro a b c h _; simp only [hatMaj, maxT] at *; omega
  | unit => intro _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c h₁ h₂
    refine ⟨fun x_star x hx => ihτ _ _ _ (h₁.1 x_star x hx)
              (h₂.1 x_star x_star (hatMaj_self ρ _ _ hx)), ?_⟩
    exact (maxT_hatMaj (ρ →ₜ τ) a a b b h₂ (hatMaj_self _ _ _ h₁)).2
  | prod ρ τ ihρ ihτ =>
    intro a b c h₁ h₂
    exact ⟨ihρ _ _ _ h₁.1 h₂.1, ihτ _ _ _ h₁.2 h₂.2⟩

/-- The mixed version: `maxT ρ a b` still majorizes what `a` majorizes. -/
theorem maxT_bezemMaj_left {base : (i : ι) → Nat → X i → Prop} (hbase : BaseMono base) :
    ∀ (ρ : Ty ι) (a b : Ty.interpret X ρ.hat) (c : Ty.interpret X ρ),
      bezemMaj base ρ a c → hatMaj ρ b b → bezemMaj base ρ (maxT ρ a b) c := by
  intro ρ
  induction ρ with
  | nat => intro a b c h _; simp only [bezemMaj, maxT] at *; omega
  | base i =>
    intro a b c h _
    refine hbase i _ _ _ ?_ h
    simp only [maxT]
    omega
  | unit => intro _ _ _ _ _; trivial
  | arr ρ τ _ ihτ =>
    intro a b c h₁ h₂
    refine ⟨fun x_star x hx => ihτ _ _ _ (h₁.1 x_star x hx)
              (h₂.1 x_star x_star (hatMaj_of_bezemMaj ρ _ _ hx)), ?_⟩
    exact (maxT_hatMaj (ρ →ₜ τ) a a b b (hatMaj_of_bezemMaj _ _ _ h₁) h₂).2
  | prod ρ τ ihρ ihτ =>
    intro a b c h₁ h₂
    exact ⟨ihρ _ _ _ h₁.1 h₂.1, ihτ _ _ _ h₁.2 h₂.2⟩

end MaxT

/-- For pure `WE-HA^ω` (`ι = Empty`) there are no base types, so the relation is
determined outright. -/
def bezemRelEmpty {X : Empty → Type} {F : Empty → Ty Empty} (si : SpaceInterp X F) :
    MajorizabilityRel si :=
  bezemRel si (fun i => i.elim)

end Metatheorems
