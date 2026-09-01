/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.StrongMajorizability


namespace Metatheorems

/-!
# Abstract Majorizability (Definition 6.0.1)

Defines abstract majorizability for the general logical metatheorems (Chapter 6).

A family of relations `{≥*_ρ}_{ρ ∈ Types}` on `Ty.interpret X ρ̂ × Ty.interpret X ρ`
is an abstract majorizability if:
1. It respects the natural number order: `x* ≥*₀ x → x* ≥ x`
2. It respects application: `f* ≥*_{ρ→τ} f ∧ x* ≥*_ρ x → f* x* ≥*_τ f x`
3. All constants are majorizable (with a uniform threshold N).
-/

-- ============================================================================
-- Abstract Majorizability
-- ============================================================================

/-- Abstract majorizability (Definition 6.0.1).

Given a type structure `(X, F)` with interpretation `si`, an abstract
majorizability provides a family of relations indexed by types, relating
elements of ρ̂ to elements of ρ, satisfying compatibility conditions. -/
structure AbstractMajorizability {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) where
  /-- The majorizability relation at type ρ: `maj ρ x_star x` means x* ≥*_ρ x. -/
  maj : (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ → Prop
  /-- Property 1: respects the natural number order. -/
  nat_order : ∀ n m : Nat, maj .nat n m → n ≥ m
  /-- Property 2: respects term application. -/
  app_compat : ∀ {ρ τ : Ty ι}
    (f_star : Ty.interpret X (ρ →ₜ τ).hat) (f : Ty.interpret X (ρ →ₜ τ))
    (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
    maj (ρ →ₜ τ) f_star f → maj ρ x_star x → maj τ (f_star x_star) (f x)
  /-- Property 2': arrow introduction (converse of app_compat).
      Needed for primitive lambda abstractions. -/
  arrow_intro : ∀ {ρ τ : Ty ι}
    (f_star : Ty.interpret X (ρ →ₜ τ).hat) (f : Ty.interpret X (ρ →ₜ τ)),
    (∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
      maj ρ x_star x → maj τ (f_star x_star) (f x)) →
    maj (ρ →ₜ τ) f_star f
  /-- Product introduction: majorize componentwise. -/
  prod_intro : ∀ {ρ τ : Ty ι}
    (p_star : Ty.interpret X (ρ ×ₜ τ).hat) (p : Ty.interpret X (ρ ×ₜ τ)),
    maj ρ p_star.1 p.1 → maj τ p_star.2 p.2 → maj (ρ ×ₜ τ) p_star p
  /-- Product elimination, first component. -/
  prod_fst : ∀ {ρ τ : Ty ι}
    (p_star : Ty.interpret X (ρ ×ₜ τ).hat) (p : Ty.interpret X (ρ ×ₜ τ)),
    maj (ρ ×ₜ τ) p_star p → maj ρ p_star.1 p.1
  /-- Product elimination, second component. -/
  prod_snd : ∀ {ρ τ : Ty ι}
    (p_star : Ty.interpret X (ρ ×ₜ τ).hat) (p : Ty.interpret X (ρ ×ₜ τ)),
    maj (ρ ×ₜ τ) p_star p → maj τ p_star.2 p.2
  /-- The unit type is a singleton, so it is majorized outright. -/
  unit_maj : maj .unit () ()
  /-- The uniform threshold N for constant majorizability. -/
  N : ℕ
  /-- Majorant for zero (0 : nat). -/
  zero_maj : ∃ z_star : ℕ → Nat,
    ∀ n ≥ N, maj .nat (z_star n) (0 : Nat)
  /-- Majorant for successor (S : nat → nat). -/
  succ_maj : ∃ s_star : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat,
    ∀ n ≥ N, maj (.nat →ₜ .nat) (s_star n) (Nat.succ : Nat → Nat)
  /-- Majorant for the recursor (R_ρ). -/
  prec_maj : ∀ (ρ : Ty ι), ∃ r_star : ℕ → Ty.interpret X (recTy ρ).hat,
    ∀ n ≥ N, maj (recTy ρ) (r_star n)
      (fun (y : Ty.interpret X ρ) (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
           (n : Nat) => Nat.rec y (fun n ih => z ih n) n)
  /-- Majorant for function constants (f_χ). -/
  func_maj : ∀ (f : ι), ∃ f_star : ℕ → Ty.interpret X (F f).hat,
    ∀ n ≥ N, maj (F f) (f_star n) (si.funcInterp f)
  /-- Majorant for zero elements (0_{X_i}). -/
  zeroX_maj : ∀ (i : ι), ∃ z_star : ℕ → Nat,
    ∀ n ≥ N, maj (.base i) (z_star n) (si.zeroInterp i)

-- ============================================================================
-- Hat-context lookup and majorizable environments
-- ============================================================================

/-- Look up a variable in an interpreted hat-context. -/
def Ctx.lookupHat {ι : Type} {X : ι → Type} :
    {Γ : Ctx ι} → {τ : Ty ι} → Var Γ τ →
    Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X τ.hat
  | _ :: _, _, .vz,   (v, _)   => v
  | _ :: _, _, .vs x, (_, env) => Ctx.lookupHat x env

/-- An environment pair `(env_star, env)` is majorizable if each component
    of `env_star` majorizes the corresponding component of `env`. -/
def MajEnv {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) :
    (Γ : Ctx ι) → Ctx.interpret X (Γ.map Ty.hat) → Ctx.interpret X Γ → Prop
  | [],     (),              ()           => True
  | _ :: Γ, (v_star, e_star), (v, env)    => am.maj _ v_star v ∧ MajEnv am Γ e_star env

/-- Looking up a variable in a majorizable environment preserves majorizability. -/
lemma MajEnv.lookup {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si}
    {Γ : Ctx ι} {τ : Ty ι} (v : Var Γ τ)
    {env_star : Ctx.interpret X (Γ.map Ty.hat)} {env : Ctx.interpret X Γ}
    (h : MajEnv am Γ env_star env) :
    am.maj τ (Ctx.lookupHat v env_star) (Ctx.lookup v env) := by
  induction v with
  | vz => exact h.1
  | vs w ih => exact ih h.2

-- ============================================================================
-- All terms are majorizable (generalized Lemma 6.0.2)
-- ============================================================================

/-- A closed term `t : Term F [] ρ` is majorizable if there exists
    `t* : ℕ → Ty.interpret X ρ̂` such that `t*(n) ≥*_ρ t` for all `n ≥ N`. -/
def IsMajorizable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : Prop :=
  ∃ t_star : ℕ → Ty.interpret X ρ.hat,
    ∀ n ≥ am.N, am.maj ρ (t_star n) (Term.interpret si t ())

/-- **Lemma 6.0.2 (generalized)**: All terms are majorizable in majorizable
    environments.

    By induction on the term:
    - Variables: use `MajEnv.lookup`
    - Application: combine majorants via `app_compat`
    - Lambda: use IH on body + `arrow_intro`
    - Constants: use the corresponding field of `AbstractMajorizability` -/
theorem all_terms_majorizable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {Γ : Ctx ι} {ρ : Ty ι} (t : Term F Γ ρ) :
    ∃ t_star : ℕ → Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X ρ.hat,
      ∀ n ≥ am.N,
        ∀ (env_star : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
          MajEnv am Γ env_star env →
          am.maj ρ (t_star n env_star) (Term.interpret si t env) := by
  induction t with
  | var v =>
    exact ⟨fun _ env_star => Ctx.lookupHat v env_star, fun _ _ _ _ h => MajEnv.lookup v h⟩
  | app f a ihf iha =>
    obtain ⟨f_star, hf⟩ := ihf
    obtain ⟨a_star, ha⟩ := iha
    exact ⟨fun n env_star => f_star n env_star (a_star n env_star),
      fun n hn env_star env henv =>
        am.app_compat _ _ _ _ (hf n hn env_star env henv) (ha n hn env_star env henv)⟩
  | lam body ih =>
    obtain ⟨body_star, hbody⟩ := ih
    exact ⟨fun n env_star x_star => body_star n (x_star, env_star),
      fun n hn env_star env henv =>
        am.arrow_intro _ _ (fun x_star x hx =>
          hbody n hn (x_star, env_star) (x, env) ⟨hx, henv⟩)⟩
  | zero =>
    obtain ⟨z_star, hz⟩ := am.zero_maj
    exact ⟨fun n _ => z_star n, fun n hn _ _ _ => hz n hn⟩
  | succ =>
    obtain ⟨s_star, hs⟩ := am.succ_maj
    exact ⟨fun n _ => s_star n, fun n hn _ _ _ => hs n hn⟩
  | prec ρ =>
    obtain ⟨r_star, hr⟩ := am.prec_maj ρ
    exact ⟨fun n _ => r_star n, fun n hn _ _ _ => hr n hn⟩
  | func f =>
    obtain ⟨f_star, hf⟩ := am.func_maj f
    exact ⟨fun n _ => f_star n, fun n hn _ _ _ => hf n hn⟩
  | zeroX i =>
    obtain ⟨z_star, hz⟩ := am.zeroX_maj i
    exact ⟨fun n _ => z_star n, fun n hn _ _ _ => hz n hn⟩
  | unitI => exact ⟨fun _ _ => (), fun _ _ _ _ _ => am.unit_maj⟩
  | mkPair a b iha ihb =>
    obtain ⟨a_star, ha⟩ := iha
    obtain ⟨b_star, hb⟩ := ihb
    exact ⟨fun n env_star => (a_star n env_star, b_star n env_star),
      fun n hn env_star env henv =>
        am.prod_intro _ _ (ha n hn env_star env henv) (hb n hn env_star env henv)⟩
  | fst p ih =>
    obtain ⟨p_star, hp⟩ := ih
    exact ⟨fun n env_star => (p_star n env_star).1,
      fun n hn env_star env henv => am.prod_fst _ _ (hp n hn env_star env henv)⟩
  | snd p ih =>
    obtain ⟨p_star, hp⟩ := ih
    exact ⟨fun n env_star => (p_star n env_star).2,
      fun n hn env_star env henv => am.prod_snd _ _ (hp n hn env_star env henv)⟩

/-- **Corollary**: All closed terms are majorizable. -/
theorem all_closed_terms_majorizable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : IsMajorizable am t := by
  obtain ⟨t_star, ht⟩ := all_terms_majorizable am t
  exact ⟨fun n => t_star n (), fun n hn => ht n hn () () True.intro⟩

-- ============================================================================
-- Bridge to `MajorizabilityRel` (what the metatheorem consumes)
-- ============================================================================

/-- `AbstractMajorizability` contains `MajorizabilityRel`: same `maj`, and `nat_order` /
`app_compat` are `maj_le` / `maj_app` with explicit arguments. -/
def AbstractMajorizability.toRel {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) : MajorizabilityRel si where
  maj := am.maj
  maj_le h := am.nat_order _ _ h
  maj_app hf hx := am.app_compat _ _ _ _ hf hx

/-- **The point of the syntactic route.** A closed term's interpretation has a majorant,
outright — instantiate `all_closed_terms_majorizable` at the threshold `N`. This is exactly
the `U_star` / `V_star` that `metatheorem_core_of_majorants` asks for. -/
theorem majorant_of_closed_term {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) :
    ∃ x_star : Ty.interpret X ρ.hat,
      am.toRel.maj ρ x_star (Term.interpret si t ()) := by
  obtain ⟨t_star, ht⟩ := all_closed_terms_majorizable am t
  exact ⟨t_star am.N, ht am.N (Nat.le_refl _)⟩

-- ============================================================================
-- Building an `AbstractMajorizability` from a base-type relation
-- ============================================================================

/-! The document's route (`particular-cases-metric-spaces.tex`, and Kohlenbach's Proposition
in §17) fixes the relation only at the base types and then discharges *two structural
conditions* plus *one obligation per constant*. `bezemMaj` is exactly that extension of a
base relation, and every structural field of `AbstractMajorizability` holds for it by
definitional unfolding — `arrow_intro` in particular is `fun _ _ h => h`, because
`bezemMaj base (ρ →ₜ τ)` *is* the ∀-statement the field demands.

So instantiating for a concrete space means supplying only the five constant majorants.
That is `bezemAbstract`. -/

section BezemAbstract

variable {ι : Type} {X : ι → Type} {F : ι → Ty ι}

/-- The structural half of `AbstractMajorizability` for `bezemMaj base`, packaged so that a
concrete space supplies only the per-constant obligations.

`N` is the uniform threshold; the five majorant arguments are the document's per-constant
conditions, stated against `bezemMaj base`. -/
def bezemAbstract (si : SpaceInterp X F) (base : (i : ι) → Nat → X i → Prop)
    (N : ℕ)
    (zero_maj : ∃ z_star : ℕ → Nat, ∀ n ≥ N, bezemMaj base .nat (z_star n) (0 : Nat))
    (succ_maj : ∃ s_star : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat,
      ∀ n ≥ N, bezemMaj base (.nat →ₜ .nat) (s_star n) (Nat.succ : Nat → Nat))
    (prec_maj : ∀ (ρ : Ty ι), ∃ r_star : ℕ → Ty.interpret X (recTy ρ).hat,
      ∀ n ≥ N, bezemMaj base (recTy ρ) (r_star n)
        (fun (y : Ty.interpret X ρ)
             (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
             (n : Nat) => Nat.rec y (fun n ih => z ih n) n))
    (func_maj : ∀ (f : ι), ∃ f_star : ℕ → Ty.interpret X (F f).hat,
      ∀ n ≥ N, bezemMaj base (F f) (f_star n) (si.funcInterp f))
    (zeroX_maj : ∀ (i : ι), ∃ z_star : ℕ → Nat,
      ∀ n ≥ N, bezemMaj base (.base i) (z_star n) (si.zeroInterp i)) :
    AbstractMajorizability si where
  maj := bezemMaj base
  nat_order _ _ h := h
  app_compat _ _ _ _ hf hx := hf _ _ hx
  arrow_intro _ _ h := h
  prod_intro _ _ h₁ h₂ := ⟨h₁, h₂⟩
  prod_fst _ _ h := h.1
  prod_snd _ _ h := h.2
  unit_maj := trivial
  N := N
  zero_maj := zero_maj
  succ_maj := succ_maj
  prec_maj := prec_maj
  func_maj := func_maj
  zeroX_maj := zeroX_maj

/-! ### The two ℕ constants are majorizable for *any* base relation

`0` and `S` say nothing about the space, so they are discharged once here rather than in each
instance. `R` is not of this kind — see `prec_maj` in the document's Proposition, which needs
an induction and a `max`-variant majorant. -/

/-- `0` majorizes itself, for any base relation. -/
theorem bezem_zero_maj (base : (i : ι) → Nat → X i → Prop) (N : ℕ) :
    ∃ z_star : ℕ → Nat, ∀ n ≥ N, bezemMaj (X := X) base .nat (z_star n) (0 : Nat) :=
  ⟨fun _ => 0, fun _ _ => Nat.le_refl 0⟩

/-- `S` majorizes itself, for any base relation. -/
theorem bezem_succ_maj (base : (i : ι) → Nat → X i → Prop) (N : ℕ) :
    ∃ s_star : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat,
      ∀ n ≥ N, bezemMaj base (.nat →ₜ .nat) (s_star n) (Nat.succ : Nat → Nat) :=
  ⟨fun _ => Nat.succ, fun _ _ _ _ h => Nat.succ_le_succ h⟩

/-- `bezemAbstract` and `bezemRel` agree, so a space built the per-constant way still feeds
anything stated against `MajorizabilityRel`. -/
theorem bezemAbstract_toRel_maj (si : SpaceInterp X F) (base : (i : ι) → Nat → X i → Prop)
    {N hz hs hp hf hx} :
    (bezemAbstract si base N hz hs hp hf hx).toRel.maj = (bezemRel si base).maj := rfl

end BezemAbstract

end Metatheorems
