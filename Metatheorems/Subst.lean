/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Term


namespace Metatheorems

/-!
# Substitution and Renaming for Terms

We define substitution, renaming, and related operations on well-typed terms.

## Main Definitions

* `Term.rename` — Apply a variable renaming to a term.
* `Term.subst0` — Substitute a term for the outermost bound variable (index 0).
-/

namespace Term

/-- The identity renaming. -/
def Renaming.id : Renaming Γ Γ := fun v => v

variable {ι κ : Type} {F : κ → Ty ι}

/-- A substitution from context Γ to context Δ: maps each variable in Γ to
    a term of the same type in Δ. -/
def Subst (F : κ → Ty ι) (Γ Δ : Ctx ι) : Type :=
  ∀ {τ : Ty ι}, Var Γ τ → Term F Δ τ

/-- The identity substitution. -/
def Subst.id : Subst F Γ Γ := fun v => .var v

/-- Extend a substitution under a binder. -/
def Subst.ext (s : Subst F Γ Δ) : Subst F (σ :: Γ) (σ :: Δ) :=
  fun v => match v with
  | .vz   => .var .vz
  | .vs w => (s w).weaken

/-- Apply a substitution to a term. -/
def subst (s : Subst F Γ Δ) : Term F Γ τ → Term F Δ τ
  | .var v         => s v
  | .app f a       => .app (subst s f) (subst s a)
  | .lam body      => .lam (subst (Subst.ext s) body)
  | .zero          => .zero
  | .succ          => .succ
  | .prec ρ'       => .prec ρ'
  | .func ff       => .func ff
  | .zeroX i       => .zeroX i
  | .dist i        => .dist i
  | .unitI         => .unitI
  | .mkPair a b    => .mkPair (subst s a) (subst s b)
  | .fst pr        => .fst (subst s pr)
  | .snd pr        => .snd (subst s pr)

/-- The single-variable substitution: replace variable 0 with `s`,
    and shift all other variables down by one. -/
def subst0_map (s : Term F Γ ρ) : Subst F (ρ :: Γ) Γ :=
  fun v => match v with
  | .vz   => s
  | .vs w => .var w

/-- Substitute a term for the outermost bound variable (de Bruijn index 0). -/
def subst0 (t : Term F (ρ :: Γ) τ) (s : Term F Γ ρ) : Term F Γ τ :=
  subst (subst0_map s) t

/-! ### Substitution/renaming commutation lemmas -/

/-- Composing two renamings. -/
theorem rename_rename {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r₁ : Renaming Γ Δ) (r₂ : Renaming Δ Δ') (t : Term F Γ τ) :
    (t.rename r₁).rename r₂ = t.rename (fun v => r₂ (r₁ v)) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename]; exact congr (congrArg app (ihf r₁ r₂)) (iha r₁ r₂)
  | lam body ih =>
    simp only [rename]; congr 1
    rw [ih (Renaming.ext r₁) (Renaming.ext r₂)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX | dist | unitI => rfl
  | mkPair _ _ ih₁ ih₂ => simp only [rename]; rw [ih₁ r₁ r₂, ih₂ r₁ r₂]
  | fst _ ih => simp only [rename]; rw [ih r₁ r₂]
  | snd _ ih => simp only [rename]; rw [ih r₁ r₂]

/-- Renaming then substituting = substituting with composed map. -/
theorem rename_subst {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r : Renaming Γ Δ) (s : Subst F Δ Δ') (t : Term F Γ τ) :
    (t.rename r).subst s = t.subst (fun v => s (r v)) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename, subst]; exact congr (congrArg app (ihf r s)) (iha r s)
  | lam body ih =>
    simp only [rename, subst]; congr 1
    rw [ih (Renaming.ext r) (Subst.ext s)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX | dist | unitI => rfl
  | mkPair _ _ ih₁ ih₂ => simp only [rename, subst]; rw [ih₁ r s, ih₂ r s]
  | fst _ ih => simp only [rename, subst]; rw [ih r s]
  | snd _ ih => simp only [rename, subst]; rw [ih r s]

/-- Substituting then renaming = substituting with renamed map. -/
theorem subst_rename {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (s : Subst F Γ Δ) (r : Renaming Δ Δ') (t : Term F Γ τ) :
    (t.subst s).rename r = t.subst (fun v => (s v).rename r) := by
  induction t generalizing Δ Δ' with
  | var v => rfl
  | app _ _ ihf iha => simp only [subst, rename]; exact congr (congrArg app (ihf s r)) (iha s r)
  | lam body ih =>
    simp only [subst, rename]; congr 1
    rw [ih (Subst.ext s) (Renaming.ext r)]
    congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w =>
      show rename (Renaming.ext r) ((s w).weaken) = ((s w).rename r).weaken
      simp only [weaken]; rw [rename_rename, rename_rename]; rfl
  | zero | succ | prec | func | zeroX | dist | unitI => rfl
  | mkPair _ _ ih₁ ih₂ => simp only [subst, rename]; rw [ih₁ s r, ih₂ s r]
  | fst _ ih => simp only [subst, rename]; rw [ih s r]
  | snd _ ih => simp only [subst, rename]; rw [ih s r]

/-- `Subst.ext` of the identity substitution is the identity. -/
theorem Subst.ext_id {Γ : Ctx ι} {σ : Ty ι} :
    @Subst.ext ι κ F Γ Γ σ Subst.id = @Subst.id ι κ F (σ :: Γ) := by
  funext τ v; cases v with
  | vz => rfl
  | vs w => rfl

/-- Identity substitution leaves terms unchanged. -/
theorem subst_id (t : Term F Γ τ) : t.subst Subst.id = t := by
  induction t with
  | var v => rfl
  | app _ _ ihf iha => simp only [subst]; exact congr (congrArg app ihf) iha
  | lam body ih => simp only [subst]; congr 1; rw [Subst.ext_id]; exact ih
  | zero | succ | prec | func | zeroX | dist | unitI => rfl
  | mkPair _ _ ih₁ ih₂ => simp only [subst]; rw [ih₁, ih₂]
  | fst _ ih => simp only [subst]; rw [ih]
  | snd _ ih => simp only [subst]; rw [ih]

/-- Renaming equals substitution with variable injection. -/
theorem rename_eq_subst (r : Renaming Γ Δ) (t : Term F Γ τ) :
    t.rename r = t.subst (fun v => .var (r v)) := by
  induction t generalizing Δ with
  | var v => rfl
  | app _ _ ihf iha => simp only [rename, subst]; exact congr (congrArg app (ihf r)) (iha r)
  | lam body ih =>
    simp only [rename, subst]; congr 1
    rw [ih (Renaming.ext r)]; congr 1; funext τ v; cases v with
    | vz => rfl
    | vs w => rfl
  | zero | succ | prec | func | zeroX | dist | unitI => rfl
  | mkPair _ _ ih₁ ih₂ => simp only [rename, subst]; rw [ih₁ r, ih₂ r]
  | fst _ ih => simp only [rename, subst]; rw [ih r]
  | snd _ ih => simp only [rename, subst]; rw [ih r]

/-- Applying a substitution after a renaming with an identity composition leaves terms
    unchanged.  Corollary of `rename_subst`. -/
theorem subst_rename_id {Γ Γ' : Ctx ι}
    (r : Renaming Γ Γ') (s : Subst F Γ' Γ)
    (h : ∀ {τ} (v : Var Γ τ), s (r v) = Term.var v)
    {τ : Ty ι} (t : Term F Γ τ) :
    (t.rename r).subst s = t := by
  rw [rename_subst]
  have : (fun {τ} (v : Var Γ τ) => s (r v)) = @Subst.id ι κ F Γ :=
    funext fun τ => funext fun v => h v
  rw [this]; exact subst_id t

/-- Weakening commutes with extended substitution:
    `t.weaken.subst (Subst.ext σ) = (t.subst σ).weaken`.
    Standard de Bruijn naturality lemma. -/
theorem weaken_subst_ext {Γ Δ : Ctx ι} {σ_ty : Ty ι}
    (t : Term F Γ τ) (σ : Subst F Γ Δ) :
    (t.weaken (σ := σ_ty)).subst (Subst.ext σ) = (t.subst σ).weaken := by
  simp only [weaken]
  rw [rename_subst, subst_rename]; rfl

/-- Weakening then substituting for variable 0 cancels out:
    `t.weaken.subst0 s = t`. -/
theorem weaken_subst0 (t : Term F Γ τ) (s : Term F Γ ρ) :
    t.weaken.subst0 s = t := by
  simp only [subst0, weaken]
  rw [rename_subst]
  exact subst_id t

/-- `Subst.ext` at the two variable shapes, and weakening of a variable, so that `simp` can
step through an iterated `Subst.ext` under nested binders. -/
@[simp] theorem Subst.ext_vz {σ : Ty ι} (s : Subst F Γ Δ) :
    Subst.ext s (σ := σ) (τ := σ) .vz = .var .vz := rfl

@[simp] theorem Subst.ext_vs {σ τ : Ty ι} (s : Subst F Γ Δ) (w : Var Γ τ) :
    Subst.ext s (σ := σ) (.vs w) = (s w).weaken := rfl

@[simp] theorem weaken_var {σ τ : Ty ι} (v : Var Γ τ) :
    (Term.var v : Term F Γ τ).weaken (σ := σ) = .var (.vs v) := rfl

/-- `subst0_map` at the two variable shapes, so that `simp` can step through them. -/
@[simp] theorem subst0_map_vz (s : Term F Γ ρ) : subst0_map s (τ := ρ) .vz = s := rfl

@[simp] theorem subst0_map_vs (s : Term F Γ ρ) {τ : Ty ι} (w : Var Γ τ) :
    subst0_map s (.vs w) = .var w := rfl

/-- `weaken_subst0` with `subst0` unfolded — the form that matches a goal left by
`induction`, where `Formula.subst0` has been pushed down to bare `Term.subst`. -/
theorem subst_subst0_map_weaken (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (Term.subst0_map s) (Term.weaken t) = t :=
  weaken_subst0 t s

/-!
### A normal form for substitute-after-rename

`Subst.cons t r` — put `t` at variable 0, rename the rest by `r` — is the normal form for
every substitution-after-renaming composite that arises here.
-/

/-- Composition of renamings, as a named combinator rather than a lambda. -/
def Renaming.comp (r₂ : Renaming Δ Δ') (r₁ : Renaming Γ Δ) : Renaming Γ Δ' :=
  fun v => r₂ (r₁ v)

@[simp] theorem Renaming.comp_apply {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r₂ : Renaming Δ Δ') (r₁ : Renaming Γ Δ) (v : Var Γ τ) :
    Renaming.comp r₂ r₁ v = r₂ (r₁ v) := rfl

/-- `rename` of a composed renaming, in the direction that takes a composite apart. With
`Renaming.shift` at the leaves this turns an iterated composite into iterated `weaken`. -/
theorem rename_comp {Γ Δ Δ' : Ctx ι} {τ : Ty ι}
    (r₂ : Renaming Δ Δ') (r₁ : Renaming Γ Δ) (t : Term F Γ τ) :
    t.rename (Renaming.comp r₂ r₁) = (t.rename r₁).rename r₂ :=
  (rename_rename r₁ r₂ t).symm

/-- `Term.weaken` is `rename Renaming.shift`; state it so that `simp` folds a bare `shift`
rename back into the notation the user sees. -/
theorem rename_shift {σ : Ty ι} (t : Term F Γ τ) :
    t.rename (Renaming.shift (σ := σ)) = t.weaken := rfl

/-- Substituting the shift renaming *viewed as a substitution* is weakening — the
right-to-left direction of `rename_eq_subst` at `Renaming.shift`. -/
theorem subst_shift_eq_weaken {σ : Ty ι} (t : Term F Γ τ) :
    t.subst (fun {_} v => Term.var (Renaming.shift (σ := σ) v)) = t.weaken := by
  rw [← rename_eq_subst]; rfl

/-- Substitute `t` for variable 0 and rename every other variable by `r`.

This is the normal form for a substitution composed with a renaming. -/
def Subst.cons (t : Term F Δ σ) (r : Renaming Γ Δ) : Subst F (σ :: Γ) Δ :=
  fun v => match v with
  | .vz   => t
  | .vs w => .var (r w)

@[simp] theorem Subst.cons_vz {σ : Ty ι} (t : Term F Δ σ) (r : Renaming Γ Δ) :
    Subst.cons t r (τ := σ) .vz = t := rfl

@[simp] theorem Subst.cons_vs {σ τ : Ty ι} (t : Term F Δ σ) (r : Renaming Γ Δ) (w : Var Γ τ) :
    Subst.cons t r (.vs w) = .var (r w) := rfl

/-- The leaf rule for `Subst.cons`: being a named constructor, it fires on an opaque term. -/
@[simp] theorem subst_cons_weaken {σ : Ty ι} (t : Term F Δ σ) (r : Renaming Γ Δ)
    (u : Term F Γ τ) :
    (u.weaken (σ := σ)).subst (Subst.cons t r) = u.rename r := by
  simp only [weaken]
  rw [rename_subst, rename_eq_subst]
  rfl

/-- Substituting for variable 0 *after* a renaming under the binder is a `cons`. This is the
shape produced by instantiating a weakened `∀`. -/
theorem subst_subst0_map_rename_ext {Γ Δ : Ctx ι} {σ τ : Ty ι}
    (r : Renaming Γ Δ) (t : Term F Δ σ) (u : Term F (σ :: Γ) τ) :
    (u.rename (Renaming.ext r)).subst (subst0_map t) = u.subst (Subst.cons t r) := by
  rw [rename_subst]; congr 1; funext _τ v; cases v <;> rfl

/-- A renaming under a binder is a `cons` too: it keeps variable 0 and renames the rest. -/
theorem rename_ext_eq_subst_cons {Γ Δ : Ctx ι} {σ τ : Ty ι}
    (r : Renaming Γ Δ) (u : Term F (σ :: Γ) τ) :
    u.rename (Renaming.ext r)
      = u.subst (Subst.cons (.var .vz) (Renaming.comp Renaming.shift r)) := by
  rw [rename_eq_subst]; congr 1; funext _τ v; cases v <;> rfl

/-- `cons` absorbs a further renaming under the binder. Iterating this collapses any tower of
weakenings into a single `Subst.cons _ (Renaming.comp …)`. -/
theorem subst_cons_rename_ext {Γ Δ Δ' : Ctx ι} {σ τ : Ty ι}
    (r : Renaming Δ Δ') (r' : Renaming Γ Δ) (t : Term F Δ' σ) (u : Term F (σ :: Γ) τ) :
    (u.rename (Renaming.ext r')).subst (Subst.cons t r)
      = u.subst (Subst.cons t (Renaming.comp r r')) := by
  rw [rename_subst]; congr 1; funext _τ v; cases v <;> rfl

end Term

/-- `Term.Renaming` re-exported at the `Metatheorems` level. -/
abbrev Renaming {ι : Type} (Γ Δ : Ctx ι) := Term.Renaming Γ Δ

namespace Renaming
abbrev ext {ι : Type} {Γ Δ : Ctx ι} {σ : Ty ι} (r : Renaming Γ Δ) :
    Renaming (σ :: Γ) (σ :: Δ) := Term.Renaming.ext r
abbrev shift {ι : Type} {Γ : Ctx ι} {σ : Ty ι} : Renaming Γ (σ :: Γ) :=
    Term.Renaming.shift
abbrev id {ι : Type} {Γ : Ctx ι} : Renaming Γ Γ := Term.Renaming.id
end Renaming

end Metatheorems
