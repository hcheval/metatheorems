/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics


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
  /-- The uniform threshold N for constant majorizability. -/
  N : ℕ
  /-- Majorant for zero (0 : nat). -/
  zero_maj : ∃ z_star : ℕ → Nat,
    ∀ n ≥ N, maj .nat (z_star n) (0 : Nat)
  /-- Majorant for successor (S : nat → nat). -/
  succ_maj : ∃ s_star : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat,
    ∀ n ≥ N, maj (.nat →ₜ .nat) (s_star n) (Nat.succ : Nat → Nat)
  /-- Majorant for projection (Π_{ρ,τ}). -/
  proj_maj : ∀ (ρ τ : Ty ι), ∃ p_star : ℕ → Ty.interpret X (ρ →ₜ τ →ₜ ρ).hat,
    ∀ n ≥ N, maj (ρ →ₜ τ →ₜ ρ) (p_star n) (fun x _ => x)
  /-- Majorant for the combinator (Σ_{δ,ρ,τ}). -/
  comb_maj : ∀ (δ ρ τ : Ty ι),
    ∃ c_star : ℕ → Ty.interpret X ((δ →ₜ ρ →ₜ τ) →ₜ (δ →ₜ ρ) →ₜ δ →ₜ τ).hat,
    ∀ n ≥ N, maj ((δ →ₜ ρ →ₜ τ) →ₜ (δ →ₜ ρ) →ₜ δ →ₜ τ)
      (c_star n) (fun x y z => x z (y z))
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
-- All closed terms are majorizable (Lemma 6.0.2)
-- ============================================================================

/-- A closed term `t : Term F [] ρ` is majorizable if there exists
    `t* : ℕ → Ty.interpret X ρ̂` such that `t*(n) ≥*_ρ t` for all `n ≥ N`. -/
def IsMajorizable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : Prop :=
  ∃ t_star : ℕ → Ty.interpret X ρ.hat,
    ∀ n ≥ am.N, am.maj ρ (t_star n) (Term.interpret si t ())

/-- **Lemma 6.0.2**: All closed terms are majorizable.

    By induction on the term:
    - Constants: use the corresponding field of `AbstractMajorizability`
    - Application `t u`: combine majorants via `app_compat` -/
theorem all_closed_terms_majorizable {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : IsMajorizable am t := by
  induction t with
  | var v => nomatch v
  | app f a ihf iha =>
    obtain ⟨f_star, hf⟩ := ihf
    obtain ⟨a_star, ha⟩ := iha
    refine ⟨fun n => f_star n (a_star n), fun n hn => ?_⟩
    simp only [Term.interpret] at hf ⊢
    exact am.app_compat (f_star n) _ (a_star n) _ (hf n hn) (ha n hn)
  | zero =>
    obtain ⟨z_star, hz⟩ := am.zero_maj
    exact ⟨z_star, fun n hn => by simp only [Term.interpret]; exact hz n hn⟩
  | succ =>
    obtain ⟨s_star, hs⟩ := am.succ_maj
    exact ⟨s_star, fun n hn => by simp only [Term.interpret]; exact hs n hn⟩
  | proj ρ τ =>
    obtain ⟨p_star, hp⟩ := am.proj_maj ρ τ
    exact ⟨p_star, fun n hn => by simp only [Term.interpret]; exact hp n hn⟩
  | comb δ ρ τ =>
    obtain ⟨c_star, hc⟩ := am.comb_maj δ ρ τ
    exact ⟨c_star, fun n hn => by simp only [Term.interpret]; exact hc n hn⟩
  | prec ρ =>
    obtain ⟨r_star, hr⟩ := am.prec_maj ρ
    exact ⟨r_star, fun n hn => by simp only [Term.interpret]; exact hr n hn⟩
  | func f =>
    obtain ⟨f_star, hf⟩ := am.func_maj f
    exact ⟨f_star, fun n hn => by simp only [Term.interpret]; exact hf n hn⟩
  | zeroX i =>
    obtain ⟨z_star, hz⟩ := am.zeroX_maj i
    exact ⟨z_star, fun n hn => by simp only [Term.interpret]; exact hz n hn⟩

end Metatheorems
