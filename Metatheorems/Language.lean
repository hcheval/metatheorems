/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Subst

/-!
# Formulas of WE-HA^{ω,X}

Following Chapter 2 (Definition 2.1.5) of the reference document, we define
the formulas of WE-HA^{ω,X}: a typed first-order language with equality at
type 0, propositional connectives, and quantifiers over all types.

## Main Definitions

* `Formula F Γ` — Formulas with free term-variables in context Γ.
* `eqAtType` — Higher-type equality (Def. 2.2.3).
* `Formula.isQF` — Quantifier-free predicate.
* `Formula.subst0` — Substitute a term for the outermost bound variable.
-/

-- ============================================================================
-- Formulas
-- ============================================================================

/-- Formulas of WE-HA^{ω,X} (Definition 2.1.5). -/
inductive Formula {ι : Type} (F : ι → Ty ι) : Ctx ι → Type where
  /-- Falsity ⊥. -/
  | bot    : Formula F Γ
  /-- Equality at type 0: s =₀ t. -/
  | eq0    : Term F Γ Ty.nat → Term F Γ Ty.nat → Formula F Γ
  /-- Conjunction: A ∧ B. -/
  | and    : Formula F Γ → Formula F Γ → Formula F Γ
  /-- Disjunction: A ∨ B. -/
  | or     : Formula F Γ → Formula F Γ → Formula F Γ
  /-- Implication: A → B. -/
  | imp    : Formula F Γ → Formula F Γ → Formula F Γ
  /-- Universal quantification: ∀x^ρ. A. -/
  | all    : (ρ : Ty ι) → Formula F (ρ :: Γ) → Formula F Γ
  /-- Existential quantification: ∃x^ρ. A. -/
  | ex     : (ρ : Ty ι) → Formula F (ρ :: Γ) → Formula F Γ

namespace Formula

variable {ι : Type} {F : ι → Ty ι}

-- ============================================================================
-- Notation
-- ============================================================================

scoped notation "⊥ᶠ" => Formula.bot
scoped infixl:35 " ∧ᶠ " => Formula.and
scoped infixl:30 " ∨ᶠ " => Formula.or
scoped infixr:25 " →ᶠ " => Formula.imp

/-- Negation: ¬A := A → ⊥ (Definition 2.1.12). -/
def neg (A : Formula F Γ) : Formula F Γ := A →ᶠ ⊥ᶠ

scoped prefix:40 "¬ᶠ" => Formula.neg

/-- Logical equivalence (Definition 2.1.13). -/
def iff' (A B : Formula F Γ) : Formula F Γ := (A →ᶠ B) ∧ᶠ (B →ᶠ A)

scoped infix:20 " ↔ᶠ " => Formula.iff'

-- ============================================================================
-- Quantifier-free predicate
-- ============================================================================

/-- A formula is quantifier-free if it contains no ∀ or ∃. -/
def isQF : Formula F Γ → Bool
  | .bot     => true
  | .eq0 _ _ => true
  | .and A B => A.isQF && B.isQF
  | .or  A B => A.isQF && B.isQF
  | .imp A B => A.isQF && B.isQF
  | .all _ _ => false
  | .ex  _ _ => false

/-- A formula is purely universal: a nesting of ∀ around a QF core.
    Needed for lem:negative-forall-equiv: purely universal formulas are
    equivalent to their negative translations in the base theory. -/
def isPurelyUniversal : Formula F Γ → Bool
  | .all _ A => A.isPurelyUniversal
  | A        => A.isQF

-- ============================================================================
-- ∨-free predicate (needed for Markov and IP Dialectica proofs)
-- ============================================================================

/-- A formula is ∨-free if it contains no disjunctions. -/
def isVFree : Formula F Γ → Bool
  | .bot     => true
  | .eq0 _ _ => true
  | .and A B => A.isVFree && B.isVFree
  | .or  _ _ => false
  | .imp A B => A.isVFree && B.isVFree
  | .all _ A => A.isVFree
  | .ex  _ A => A.isVFree

/-- A formula is quantifier-free and ∨-free (needed for Dialectica proofs
    of Markov's principle and Independence of Premise). -/
def isQFVFree : Formula F Γ → Bool := fun A => A.isQF && A.isVFree

-- ============================================================================
-- Renaming on Formulas
-- ============================================================================

/-- Apply a variable renaming to a formula. -/
def renameF (r : Renaming Γ Δ) : Formula F Γ → Formula F Δ
  | .bot     => .bot
  | .eq0 s t => .eq0 (s.rename r) (t.rename r)
  | .and A B => .and (renameF r A) (renameF r B)
  | .or  A B => .or  (renameF r A) (renameF r B)
  | .imp A B => .imp (renameF r A) (renameF r B)
  | .all ρ A => .all ρ (renameF (Renaming.ext r) A)
  | .ex  ρ A => .ex  ρ (renameF (Renaming.ext r) A)

-- ============================================================================
-- Substitution on Formulas
-- ============================================================================

/-- Apply a substitution to a formula. -/
def substF (s : Term.Subst F Γ Δ) : Formula F Γ → Formula F Δ
  | .bot     => .bot
  | .eq0 a b => .eq0 (a.subst s) (b.subst s)
  | .and A B => .and (substF s A) (substF s B)
  | .or  A B => .or  (substF s A) (substF s B)
  | .imp A B => .imp (substF s A) (substF s B)
  | .all ρ A => .all ρ (substF (Term.Subst.ext s) A)
  | .ex  ρ A => .ex  ρ (substF (Term.Subst.ext s) A)

/-- Substitute a term for the outermost bound variable in a formula. -/
def subst0 (A : Formula F (ρ :: Γ)) (s : Term F Γ ρ) : Formula F Γ :=
  substF (Term.subst0_map s) A

/-- Applying a substitution after a renaming with an identity composition leaves formulas
    unchanged.  The binder cases use the fact that extension preserves the identity property. -/
theorem substF_renameF_id {Γ Γ' : Ctx ι}
    (r : Renaming Γ Γ') (s : Term.Subst F Γ' Γ)
    (h : ∀ {τ} (v : Var Γ τ), s (r v) = Term.var v)
    (A : Formula F Γ) :
    (A.renameF r).substF s = A := by
  induction A generalizing Γ' with
  | bot => rfl
  | eq0 s' t' =>
    simp [Formula.renameF, Formula.substF, Term.subst_rename_id r s h]
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [Formula.renameF, Formula.substF, ihA r s h, ihB r s h]
  | ex ρ B ihB | all ρ B ihB =>
    simp only [Formula.renameF, Formula.substF]
    congr 1
    apply ihB (Renaming.ext r) (Term.Subst.ext s)
    intro τ v
    cases v with
    | vz => simp [Renaming.ext, Term.Subst.ext]
    | vs w =>
      simp only [Renaming.ext, Term.Subst.ext]
      rw [h w]
      simp [Term.weaken, Var.weaken]

/-- Weaken a formula: embed from context Γ into (σ :: Γ). -/
def weaken : Formula F Γ → Formula F (σ :: Γ) :=
  renameF Renaming.shift

-- ============================================================================
-- In-place substitution of variable 0
-- ============================================================================

/-- Substitution map that replaces variable 0 with `t` and keeps others in place.
    Unlike `subst0_map`, the replacement term lives in the same context. -/
def Term.substVar0_map (t : Term F (ρ :: Γ) ρ) : Term.Subst F (ρ :: Γ) (ρ :: Γ) :=
  fun {τ} v => match τ, v with
  | _, .vz   => t
  | _, .vs w => .var (.vs w)

/-- Substitute a term for variable 0, keeping the same context.
    Maps var 0 to `t` and var (n+1) to var (n+1). Unlike `subst0`, this
    does not shrink the context — it's used e.g. in the induction step
    where we substitute A(x) into A(Sx) while staying under a ∀x binder. -/
def substVar0 (A : Formula F (ρ :: Γ)) (t : Term F (ρ :: Γ) ρ) : Formula F (ρ :: Γ) :=
  substF (Term.substVar0_map t) A

-- ============================================================================
-- AC substitution (for the axiom of choice axiom schema)
-- ============================================================================

/-- Substitution used in the AC conclusion `∃Y^{ρ→τ}. ∀x^ρ. A(x, Yx)`.
    Maps context `τ :: ρ :: Γ` to `ρ :: (ρ →ₜ τ) :: Γ`:
    - index 0 (y : τ)   ↦  `Y x`  where Y = var(1), x = var(0)
    - index 1 (x : ρ)   ↦  `x`    (var 0 in the new context)
    - index k+2 from Γ  ↦  var(k+2) unchanged -/
def acSubst {ρ τ : Ty ι} : Term.Subst F (τ :: ρ :: Γ) (ρ :: (ρ →ₜ τ) :: Γ) :=
  fun {_} v => match v with
  | .vz         => Term.app (.var (.vs .vz)) (.var .vz)
  | .vs .vz     => .var .vz
  | .vs (.vs w) => .var (.vs (.vs w))

-- ============================================================================
-- Iterated quantifiers (for Dialectica)
-- ============================================================================

/-- Wrap a formula in iterated ∀ over a list of types. -/
def wrapAll : (ρs : List (Ty ι)) → Formula F (ρs ++ Γ) → Formula F Γ
  | [],      A => A
  | ρ :: ρs, A => wrapAll ρs (.all ρ A)

/-- Wrap a formula in iterated ∃ over a list of types. -/
def wrapEx : (ρs : List (Ty ι)) → Formula F (ρs ++ Γ) → Formula F Γ
  | [],      A => A
  | ρ :: ρs, A => wrapEx ρs (.ex ρ A)

end Formula

-- ============================================================================
-- Higher-type equality (Definition 2.2.3 / 2.3.3)
-- ============================================================================

/-- Higher-type equality at type ρ (Definition 2.2.3 / Definition 2.3.3).

For terms s, t of type ρ = ρ₁ → ... → ρₖ → ρ₀ (where ρ₀ is ground):
  s =_ρ t  :≡  ∀x₁^ρ₁. ... ∀xₖ^ρₖ. (s x₁ ... xₖ =_{ρ₀} t x₁ ... xₖ)

At ground type 0, this is s =₀ t.
At base type X_i, this uses the supplied predicate `EqX i s t`.
The document requires `EqX i` to be a purely universal formula (so that
it is trivially Dialectica-realized); the predicate itself is a parameter
of the proof system, not an axiom. -/
def eqAtType {ι : Type} {F : ι → Ty ι}
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ)
    {Γ : Ctx ι} :
    (ρ : Ty ι) → Term F Γ ρ → Term F Γ ρ → Formula F Γ
  | Ty.nat,      s, t => Formula.eq0 s t
  | Ty.base i,   s, t => EqX i s t
  | Ty.arr ρ τ,  s, t =>
      -- ∀x^ρ. (s x =_τ t x)
      Formula.all ρ (eqAtType EqX τ
        (Term.app s.weaken (.var .vz))
        (Term.app t.weaken (.var .vz)))
