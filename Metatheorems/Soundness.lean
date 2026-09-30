/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetatheoremPrereqs

namespace Metatheorems

/-!
# Semantic soundness

`Derivable F allowed Premises A → ∀ env, Formula.interpret si A env`.

The theorem is **conditional**, and deliberately so: the proof system has constructors whose
truth is a property of the model, not of the syntax.  Those properties are taken as explicit
hypotheses (section `variable`s, so that the recursion re-applies them automatically):

* `hprem`       — every premise is true in the model.  Forced by `Derivable.premise`.
* `hdist_self`  — `d_i(x,x) =ℝ 0ℝ`.  Forced by `Derivable.dist_self`, and *also* by
                  `beta_eq`, `pair_fst`/`pair_snd`/`pair_eta`, `rec_zero`, `rec_succ` and
                  `qfer`, all of which assert an
                  `eqAtType` between two terms with equal interpretations; at a base type
                  `eqAtType` is `d_i(·,·) =ℝ 0ℝ`, so reflexivity of `=_X` is exactly this
                  model fact.
* `hdist_comm`  — `d_i(x,y) =ℝ d_i(y,x)`.  Forced by `Derivable.dist_comm`.
* `hdist_tri`   — `d_i(x,z) ≤ℝ d_i(x,y) +ℝ d_i(y,z)`.  Forced by `Derivable.dist_tri`.
* `hsep`        — **separation**: `d_i(s,t) =ℝ 0ℝ` implies `‖s‖ = ‖t‖` in the model.
                  Forced by `Derivable.qfer` only.  See `eq_of_interp_eqAtType` below.

Nothing else is assumed.  The `Allowed`-guarded principles (`lem`, `markov`, `ip`, `ac`,
`qfac`) are all true in the full set-theoretic type structure, classically, so their guards
are simply ignored.
-/

section

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}

-- Semantics of formula substitution / weakening


theorem Formula.interpret_substVar0 (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (A : Formula F (ρ :: Γ)) (u : Term F (ρ :: Γ) ρ)
    (v : Ty.interpret X ρ) (env : Ctx.interpret X Γ) :
    Formula.interpret si (A.substVar0 u) (v, env)
      = Formula.interpret si A (Term.interpret si u (v, env), env) := by
  simp only [Formula.substVar0, Formula.interpret_substF,
    Ctx.interpretSubst_substVar0_map]

/-- Interpreting a weakened formula in an extended environment. -/
theorem Formula.interpret_weakenF (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι}
    (B : Formula F Γ) (x : Ty.interpret X ρ) (env : Ctx.interpret X Γ) :
    Formula.interpret si (Formula.weakenBy ρ B) (x, env) = Formula.interpret si B env := by
  unfold Formula.weakenBy Formula.weaken
  exact Formula.interpret_renameF_gen si Term.Renaming.shift B (x, env) env (fun _ => rfl)

/-- The environment produced by the AC substitution. -/
theorem Ctx.interpretSubst_acSubst (si : SpaceInterp X F) {Γ : Ctx ι} {ρ τ : Ty ι}
    (x : Ty.interpret X ρ) (Y : Ty.interpret X ρ → Ty.interpret X τ)
    (env : Ctx.interpret X Γ) :
    Ctx.interpretSubst si (Formula.acSubst (F := F) (Γ := Γ) (ρ := ρ) (τ := τ))
        (x, (Y, env))
      = (Y x, (x, env)) := by
  simp only [Ctx.interpretSubst, Formula.acSubst, Term.interpret, Ctx.lookup]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  have h : (fun {t : Ty ι} (w : Var Γ t) =>
              (Term.var (Var.vs (Var.vs w)) : Term F (ρ :: (ρ →ₜ τ) :: Γ) t)) =
           (fun {t : Ty ι} (w : Var Γ t) =>
              (((Term.var w : Term F Γ t).weaken : Term F ((ρ →ₜ τ) :: Γ) t).weaken :
                Term F (ρ :: (ρ →ₜ τ) :: Γ) t)) := by funext; rfl
  rw [h, Ctx.interpretSubst_weaken_eq, Ctx.interpretSubst_weaken_eq,
    Ctx.interpretSubst_id]

-- `eq_R` / `le_R_pu` interpretation congruences

/-- `eq_R f g` mentions `f`, `g` only as `f.weaken`, `g.weaken` under a single `∀n`, so its
interpretation factors through the interpreted values. -/
theorem eq_R_interp_congr (si : SpaceInterp X F) {Γ : Ctx ι}
    (f f' g g' : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hf : Term.interpret si f env = Term.interpret si f' env)
    (hg : Term.interpret si g env = Term.interpret si g' env) :
    Formula.interpret si (eq_R f g) env ↔ Formula.interpret si (eq_R f' g') env := by
  have hfw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si f.weaken (n, env) = Term.interpret si f'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hf
  have hgw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si g.weaken (n, env) = Term.interpret si g'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hg
  simp only [eq_R, Formula.interpret, Term.app2, Term.interpret, hfw, hgw]

/-- Same for the purely-universal `≤ℝ`, which `dist_tri` is stated with. -/
theorem le_R_pu_interp_congr (si : SpaceInterp X F) {Γ : Ctx ι}
    (f f' g g' : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hf : Term.interpret si f env = Term.interpret si f' env)
    (hg : Term.interpret si g env = Term.interpret si g' env) :
    Formula.interpret si (le_R_pu f g) env ↔ Formula.interpret si (le_R_pu f' g') env := by
  have hfw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si f.weaken (n, env) = Term.interpret si f'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hf
  have hgw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si g.weaken (n, env) = Term.interpret si g'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hg
  simp only [le_R_pu, Formula.interpret, Term.app2, Term.interpret, hfw, hgw]

-- Every type is inhabited in the model (needed for the `ip` case)

/-- A canonical element of every interpreted type.  It exists because `SpaceInterp` carries
a `zeroInterp` for each base type; without it `Ty.interpret X (.base i)` could be empty and
the `ip` case would genuinely fail. -/
def Ty.someElem (si : SpaceInterp X F) : (ρ : Ty ι) → Ty.interpret X ρ
  | .nat      => 0
  | .base i   => si.zeroInterp i
  | .arr _ τ  => fun _ => Ty.someElem si τ
  | .unit     => ()
  | .prod ρ τ => (Ty.someElem si ρ, Ty.someElem si τ)

-- `eqAtType` and semantic equality

/-- **Soundness of `eqAtType`**: terms with equal interpretations satisfy `=_ρ`.

At a base type this *is* reflexivity of `d_i(·,·) =ℝ 0ℝ`, i.e. the `dist_self` model fact —
which is why `beta_eq`, `rec_zero`, `rec_succ` and `qfer` all need it. -/
theorem interp_eqAtType_of_interp_eq (si : SpaceInterp X F)
    (hself : ∀ (i : ι) {Γ' : Ctx ι} (u : Term F Γ' (Ty.base i))
      (e : Ctx.interpret X Γ'),
      Formula.interpret si (eq_R (Term.app2 (Term.dist i) u u) Term.zero_R) e) :
    ∀ (ρ : Ty ι) (Γ : Ctx ι) (s t : Term F Γ ρ) (env : Ctx.interpret X Γ),
      Term.interpret si s env = Term.interpret si t env →
      Formula.interpret si (eqAtType ρ s t) env := by
  intro ρ
  induction ρ with
  | nat =>
    intro _ _ _ _ h; exact h
  | base i =>
    intro Γ s t env h
    refine (eq_R_interp_congr si _ _ _ _ env ?_ rfl).mp (hself i s env)
    simp only [Term.app2, Term.interpret, h]
  | arr ρ τ _ ihτ =>
    intro Γ s t env h
    simp only [eqAtType, Formula.interpret]
    intro x
    refine ihτ (ρ :: Γ) _ _ (x, env) ?_
    simp only [Term.interpret, Term.interpret_weaken, Ctx.lookup]
    exact congrFun h x
  | unit =>
    intro _ _ _ _ _; rfl
  | prod ρ τ ihρ ihτ =>
    intro Γ s t env h
    refine ⟨ihρ Γ _ _ env ?_, ihτ Γ _ _ env ?_⟩ <;>
      simp only [Term.interpret, h]

/-- **Extraction from `eqAtType`**: `=_ρ` implies equality of interpretations.

At a base type this is *separation* — `d_i(s,t) =ℝ 0ℝ → ‖s‖ = ‖t‖` — which a proper
pseudometric does not satisfy.  It is used by exactly one constructor, `qfer`, and it is
what the quantifier-free extensionality rule needs: `qfer` concludes
`r[s] =_σ r[t]` from `s =_ρ t`, and in the full set-theoretic type structure `r` is an
arbitrary function, which respects `=_ρ` only when `=_ρ` is real equality. -/
theorem eq_of_interp_eqAtType (si : SpaceInterp X F)
    (hsep : ∀ (i : ι) {Γ' : Ctx ι} (u v : Term F Γ' (Ty.base i))
      (e : Ctx.interpret X Γ'),
      Formula.interpret si (eq_R (Term.app2 (Term.dist i) u v) Term.zero_R) e →
      Term.interpret si u e = Term.interpret si v e) :
    ∀ (ρ : Ty ι) (Γ : Ctx ι) (s t : Term F Γ ρ) (env : Ctx.interpret X Γ),
      Formula.interpret si (eqAtType ρ s t) env →
      Term.interpret si s env = Term.interpret si t env := by
  intro ρ
  induction ρ with
  | nat =>
    intro _ _ _ _ h; exact h
  | base i =>
    intro Γ s t env h; exact hsep i s t env h
  | arr ρ τ _ ihτ =>
    intro Γ s t env h
    simp only [eqAtType, Formula.interpret] at h
    funext x
    have := ihτ (ρ :: Γ) _ _ (x, env) (h x)
    simpa only [Term.interpret, Term.interpret_weaken, Ctx.lookup] using this
  | unit =>
    intro _ _ _ _ _
    exact Subsingleton.elim _ _
  | prod ρ τ ihρ ihτ =>
    intro Γ s t env h
    obtain ⟨h₁, h₂⟩ := h
    have e₁ := ihρ Γ _ _ env h₁
    have e₂ := ihτ Γ _ _ env h₂
    simp only [Term.interpret] at e₁ e₂
    exact Prod.ext e₁ e₂

end

/-- The semantic content of independence of premise, over an inhabited domain. -/
private theorem ip_semantic {α : Type} (P : Prop) (Q : α → Prop) (d : α)
    (h : P → ∃ x, Q x) : ∃ x, P → Q x := by
  by_cases hp : P
  · obtain ⟨x, hx⟩ := h hp
    exact ⟨x, fun _ => hx⟩
  · exact ⟨d, fun hc => absurd hc hp⟩

-- The soundness theorem

section Soundness

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
variable (si : SpaceInterp X F) {Premises : PremiseSet F} {allowed : Allowed}

-- Every premise is true in the model.
variable (hprem : ∀ {Γ : Ctx ι} (A : Formula F Γ), Premises ⟨Γ, A⟩ →
  ∀ env : Ctx.interpret X Γ, Formula.interpret si A env)

-- `d_i(x,x) =ℝ 0ℝ` holds in the model.
variable (hdist_self : ∀ (i : ι) {Γ : Ctx ι} (x : Term F Γ (Ty.base i))
  (env : Ctx.interpret X Γ),
  Formula.interpret si (eq_R (Term.app2 (Term.dist i) x x) Term.zero_R) env)

-- `d_i(x,y) =ℝ d_i(y,x)` holds in the model.
variable (hdist_comm : ∀ (i : ι) {Γ : Ctx ι} (x y : Term F Γ (Ty.base i))
  (env : Ctx.interpret X Γ),
  Formula.interpret si
    (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env)

-- The triangle inequality holds in the model.
variable (hdist_tri : ∀ (i : ι) {Γ : Ctx ι} (x y z : Term F Γ (Ty.base i))
  (env : Ctx.interpret X Γ),
  Formula.interpret si
    (le_R_pu (Term.app2 (Term.dist i) x z)
      (Term.app2 Term.add_R
        (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))) env)

-- Separation: `d_i` is a genuine metric, not merely a pseudometric.  Used by `qfer` only.
variable (hsep : ∀ (i : ι) {Γ : Ctx ι} (x y : Term F Γ (Ty.base i))
  (env : Ctx.interpret X Γ),
  Formula.interpret si (eq_R (Term.app2 (Term.dist i) x y) Term.zero_R) env →
  Term.interpret si x env = Term.interpret si y env)

include si hprem hdist_self hdist_comm hdist_tri hsep

/-- **Semantic soundness.**  Every derivable formula is true in the model, given the model
facts listed at the top of this file. -/
theorem soundness {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F allowed Premises A) :
    ∀ env : Ctx.interpret X Γ, Formula.interpret si A env := by
  induction h with
  | premise hp => exact hprem _ hp
  | or_contract => exact fun _ h => h.elim id id
  | and_contract => exact fun _ h => ⟨h, h⟩
  | or_weak => exact fun _ h => Or.inl h
  | and_weak => exact fun _ h => h.1
  | or_perm => exact fun _ h => h.symm
  | and_perm => exact fun _ h => h.symm
  | exfalso => exact fun _ h => h.elim
  | forall_ax t =>
    intro env h
    rw [Formula.interpret_subst0]
    exact h _
  | exist_ax t A =>
    intro env h
    rw [Formula.interpret_subst0] at h
    exact ⟨_, h⟩
  | mp _ _ ih1 ih2 => exact fun env => ih2 env (ih1 env)
  | syllogism _ _ ih1 ih2 => exact fun env h => ih2 env (ih1 env h)
  | exportation _ ih => exact fun env a b => ih env ⟨a, b⟩
  | importation _ ih => exact fun env h => ih env h.1 h.2
  | expansion _ ih => exact fun env h => h.imp id (ih env)
  | forall_rule _ ih =>
    intro env hB x
    refine ih (x, env) ?_
    rw [Formula.interpret_weakenF]
    exact hB
  | exist_rule _ ih =>
    intro env h
    obtain ⟨x, hx⟩ := h
    have := ih (x, env) hx
    rwa [Formula.interpret_weakenF] at this
  | univ_gen _ ih =>
    intro env x
    rw [Formula.interpret_weakenF]
    exact ih env
  | succ_ne_zero => exact fun _ n hn => Nat.succ_ne_zero n hn
  | succ_inj => exact fun _ _ _ h => Nat.succ.inj h
  | beta_eq body u =>
    intro env
    refine interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env ?_
    simp only [Term.interpret, Term.interpret_subst0]
  -- product β/η: the two sides' interpretations are definitionally equal
  -- (`(a,b).1 ≡ a`, and `Prod` η is definitional for structures)
  | pair_fst a b =>
    intro env
    exact interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env rfl
  | pair_snd a b =>
    intro env
    exact interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env rfl
  | pair_eta p =>
    intro env
    exact interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env rfl
  | rec_zero =>
    intro env
    refine interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env ?_
    simp only [Term.app3, Term.interpret]
    rfl
  | rec_succ =>
    intro env
    refine interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env ?_
    simp only [Term.app3, Term.app2, Term.interpret]
  | dist_self i x => exact fun env => hdist_self i x env
  | dist_comm i x y => exact fun env => hdist_comm i x y env
  | dist_tri i x y z => exact fun env => hdist_tri i x y z env
  | refl0 => exact fun _ => rfl
  | sym0 => exact fun _ h => h.symm
  | trans0 => exact fun _ h => h.1.trans h.2
  | qfer _ _ _ ih =>
    intro env ha
    have hst := eq_of_interp_eqAtType si hsep _ _ _ _ env (ih env ha)
    refine interp_eqAtType_of_interp_eq si hdist_self _ _ _ _ env ?_
    rw [Term.interpret_subst0, Term.interpret_subst0, hst]
  | induction _ _ ih0 ihs =>
    intro env n
    induction n with
    | zero =>
      have := ih0 env
      rwa [Formula.interpret_subst0] at this
    | succ m ihm =>
      have hstep := ihs env m ihm
      rwa [Formula.interpret_substVar0] at hstep
  | lem => exact fun _ => Classical.em _
  | markov _ _ _ =>
    intro env h
    exact Classical.byContradiction h
  | ip _ _ _ =>
    intro env h
    simp only [Formula.interpret] at h ⊢
    obtain ⟨x, hx⟩ := ip_semantic _ _ (Ty.someElem si _) h
    refine ⟨x, fun hc => hx ?_⟩
    rw [Formula.interpret_weakenF] at hc
    exact hc
  | ac _ =>
    intro env h
    choose Y hY using h
    refine ⟨Y, fun x => ?_⟩
    rw [Formula.interpret_substF, Ctx.interpretSubst_acSubst]
    exact hY x
  | qfac _ _ _ =>
    intro env h
    choose Y hY using h
    refine ⟨Y, fun x => ?_⟩
    rw [Formula.interpret_substF, Ctx.interpretSubst_acSubst]
    exact hY x

end Soundness

#print axioms soundness
#print axioms interp_eqAtType_of_interp_eq
#print axioms eq_of_interp_eqAtType

end Metatheorems
