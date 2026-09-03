/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Subst


namespace Metatheorems

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
inductive Formula {ι κ : Type} (F : κ → Ty ι) : Ctx ι → Type where
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

variable {ι κ : Type} {F : κ → Ty ι}

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
  -- closed under ∧ as well: `eqAtType` at a product type is a conjunction of two
  -- ∀-formulas, which is still ∃-free and ∨-free, hence still trivially realized.
  | .and A B => A.isPurelyUniversal && B.isPurelyUniversal
  | A        => A.isQF

/-- A formula is purely existential: a nesting of ∃ around a QF core — Kohlenbach's
"∃-formula" (`C∃` in Theorem 17.52). The mirror image of `isPurelyUniversal`, closed under
`∧` for the same reason (the Dialectica witness of `∃c C₀ ∧ ∃c' C₀'` is still just the pair
of witnesses, with nothing to challenge).

Added 2026-09-04 for the general-matrix metatheorem, `syntactic_general_metatheorem_gen`,
which takes a purely universal premise matrix and a purely existential conclusion matrix,
as 17.52 does. -/
def isPurelyExistential : Formula F Γ → Bool
  | .ex _ A  => A.isPurelyExistential
  | .and A B => A.isPurelyExistential && B.isPurelyExistential
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
def renameF (r : Term.Renaming Γ Δ) : Formula F Γ → Formula F Δ
  | .bot     => .bot
  | .eq0 s t => .eq0 (s.rename r) (t.rename r)
  | .and A B => .and (renameF r A) (renameF r B)
  | .or  A B => .or  (renameF r A) (renameF r B)
  | .imp A B => .imp (renameF r A) (renameF r B)
  | .all ρ A => .all ρ (renameF (Term.Renaming.ext r) A)
  | .ex  ρ A => .ex  ρ (renameF (Term.Renaming.ext r) A)

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
    (r : Term.Renaming Γ Γ') (s : Term.Subst F Γ' Γ)
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
    apply ihB (Term.Renaming.ext r) (Term.Subst.ext s)
    intro τ v
    cases v with
    | vz => simp [Term.Renaming.ext, Term.Subst.ext]
    | vs w =>
      simp only [Term.Renaming.ext, Term.Subst.ext]
      rw [h w]
      simp [Term.weaken, Term.rename, Term.Renaming.shift]

/-- Renaming then substituting = substituting with the composed map. The formula-level
counterpart of `Term.rename_subst`. -/
theorem renameF_substF {Γ Γ' Γ'' : Ctx ι}
    (r : Term.Renaming Γ Γ') (s : Term.Subst F Γ' Γ'') (A : Formula F Γ) :
    (A.renameF r).substF s = A.substF (fun {_τ} v => s (r v)) := by
  induction A generalizing Γ' Γ'' with
  | bot => rfl
  | eq0 a b => simp [renameF, substF, Term.rename_subst]
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [renameF, substF, ihA r s, ihB r s]
  | ex ρ B ihB | all ρ B ihB =>
    simp only [renameF, substF]
    congr 1
    rw [ihB (Term.Renaming.ext r) (Term.Subst.ext s)]
    congr 1; funext _τ v; cases v with
    | vz => rfl
    | vs w => rfl

/-- Renaming equals substituting with the variable injection. The formula-level counterpart
of `Term.rename_eq_subst`. -/
theorem renameF_eq_substF {Γ Γ' : Ctx ι}
    (r : Term.Renaming Γ Γ') (A : Formula F Γ) :
    A.renameF r = A.substF (fun {_τ} v => .var (r v)) := by
  induction A generalizing Γ' with
  | bot => rfl
  | eq0 a b => simp [renameF, substF, Term.rename_eq_subst]
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [renameF, substF, ihA r, ihB r]
  | ex ρ B ihB | all ρ B ihB =>
    simp only [renameF, substF]
    congr 1
    rw [ihB (Term.Renaming.ext r)]
    congr 1; funext _τ v; cases v with
    | vz => rfl
    | vs w => rfl

-- ============================================================================
-- Substitute-after-rename, in normal form
-- ============================================================================

/-!
The formula-level counterparts of `Term.subst_subst0_map_rename_ext` and
`Term.subst_cons_rename_ext`. Together they say: instantiating a formula that has been
weakened any number of times is a single `substF (Term.Subst.cons t r)`, with all the
weakenings collected into one `Term.Renaming.comp` tower.

`substF` then pushes down through the connectives as usual; under a binder the substitution
becomes `Term.Subst.ext (Term.Subst.cons t r)`, where the existing `Term.weaken_subst_ext`
takes over. At the leaves, `Term.subst_cons_weaken` fires even on opaque terms.
-/

/-- Substituting for variable 0 after a renaming under the binder is a single `cons`. This is
the shape left behind by instantiating a weakened `∀`-hypothesis. -/
theorem substF_subst0_map_renameF_ext {Γ Δ : Ctx ι} {σ : Ty ι}
    (r : Term.Renaming Γ Δ) (t : Term F Δ σ) (A : Formula F (σ :: Γ)) :
    (A.renameF (Term.Renaming.ext r)).substF (Term.subst0_map t)
      = A.substF (Term.Subst.cons t r) := by
  rw [renameF_substF]; congr 1; funext _τ v; cases v <;> rfl

/-- `subst0`-phrased form of `substF_subst0_map_renameF_ext`, for goals where the abbreviation
is still folded. -/
theorem subst0_renameF_ext {Γ Δ : Ctx ι} {σ : Ty ι}
    (r : Term.Renaming Γ Δ) (t : Term F Δ σ) (A : Formula F (σ :: Γ)) :
    (A.renameF (Term.Renaming.ext r)).subst0 t = A.substF (Term.Subst.cons t r) :=
  substF_subst0_map_renameF_ext r t A

/-- A renaming under a binder is a `cons` as well. This is the shape `∀`-elimination at the
bound variable leaves behind, and it joins the same normal form. -/
theorem renameF_ext_eq_substF_cons {Γ Δ : Ctx ι} {σ : Ty ι}
    (r : Term.Renaming Γ Δ) (A : Formula F (σ :: Γ)) :
    A.renameF (Term.Renaming.ext r)
      = A.substF (Term.Subst.cons (.var .vz)
          (Term.Renaming.comp Term.Renaming.shift r)) := by
  rw [renameF_eq_substF]; congr 1; funext _τ v; cases v <;> rfl

/-- `cons` absorbs a further renaming under the binder; iterating collapses a tower of
weakenings into one `Term.Renaming.comp`. -/
theorem substF_cons_renameF_ext {Γ Δ Δ' : Ctx ι} {σ : Ty ι}
    (r : Term.Renaming Δ Δ') (r' : Term.Renaming Γ Δ) (t : Term F Δ' σ)
    (A : Formula F (σ :: Γ)) :
    (A.renameF (Term.Renaming.ext r')).substF (Term.Subst.cons t r)
      = A.substF (Term.Subst.cons t (Term.Renaming.comp r r')) := by
  rw [renameF_substF]; congr 1; funext _τ v; cases v <;> rfl

/-- Weaken a formula: embed from context Γ into (σ :: Γ). -/
def weaken : Formula F Γ → Formula F (σ :: Γ) :=
  renameF Term.Renaming.shift

-- ============================================================================
-- In-place substitution of variable 0
-- ============================================================================

/-- Substitution map that replaces variable 0 with `t` and keeps others in place.
    Unlike `subst0_map`, the replacement term lives in the same context. -/
def Term.substVar0_map (t : Term F (ρ :: Γ) ρ) : Term.Subst F (ρ :: Γ) (ρ :: Γ) :=
  fun {τ} v => match τ, v with
  | _, .vz   => t
  | _, .vs w => .var (.vs w)

/-- `substVar0_map` at the two variable shapes, for the same reason as `Term.subst0_map_vz`:
`simp` cannot step through the bare definition. -/
@[simp] theorem Term.substVar0_map_vz {Γ : Ctx ι} {ρ : Ty ι} (t : Term F (ρ :: Γ) ρ) :
    Term.substVar0_map t (τ := ρ) .vz = t := rfl

@[simp] theorem Term.substVar0_map_vs {Γ : Ctx ι} {ρ τ : Ty ι} (t : Term F (ρ :: Γ) ρ)
    (w : Var Γ τ) : Term.substVar0_map t (.vs w) = .var (.vs w) := rfl

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

-- `eqAtType` moved to `Metatheorems/EqAtType.lean`. Base-type equality is now *defined* as
-- `d_i(s,t) =ℝ 0ℝ`, so it depends on the ℚ/ℝ term layer, which depends on `Formula` — this
-- file. It was the last declaration here and had no dependants inside it, so the split is
-- clean. See ARCHITECTURE.md.

end Metatheorems
