/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.MajorizabilityRel


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

-- Abstract Majorizability

/-- Abstract majorizability (Definition 6.0.1).

Given a type structure `(X, F)` with interpretation `si`, an abstract
majorizability provides a family of relations indexed by types, relating
elements of ρ̂ to elements of ρ, satisfying compatibility conditions. -/
structure AbstractMajorizability {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
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
  /-- **Self-majorization** (`≽ᵃ_ρ̂`), the second conjunct of Bezem's definition. Both
      arguments are at the hat type; `bezemMaj`'s instance of this is `hatMaj`. A field rather
      than `maj ρ.hat`, because `ρ.hat.hat = ρ.hat` holds only propositionally. -/
  selfMaj : (ρ : Ty ι) → Ty.interpret X ρ.hat → Ty.interpret X ρ.hat → Prop
  /-- A majorant majorizes itself. -/
  maj_selfMaj : ∀ {ρ : Ty ι} {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ},
    maj ρ x_star x → selfMaj ρ x_star x_star
  /-- `selfMaj` entails self-majorization on the left. -/
  selfMaj_self : ∀ {ρ : Ty ι} {a b : Ty.interpret X ρ.hat}, selfMaj ρ a b → selfMaj ρ a a
  /-- `selfMaj` respects application. -/
  selfMaj_app : ∀ {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    {x y : Ty.interpret X ρ.hat},
    selfMaj (ρ →ₜ τ) f g → selfMaj ρ x y → selfMaj τ (f x) (g y)
  /-- Property 2': arrow introduction (converse of app_compat).
      Needed for primitive lambda abstractions. The second hypothesis is the
      self-majorization obligation. -/
  arrow_intro : ∀ {ρ τ : Ty ι}
    (f_star : Ty.interpret X (ρ →ₜ τ).hat) (f : Ty.interpret X (ρ →ₜ τ)),
    (∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
      maj ρ x_star x → maj τ (f_star x_star) (f x)) →
    (∀ (x_star x : Ty.interpret X ρ.hat),
      selfMaj ρ x_star x → selfMaj τ (f_star x_star) (f_star x)) →
    maj (ρ →ₜ τ) f_star f
  /-- Arrow introduction for `selfMaj`. -/
  selfMaj_arrow_intro : ∀ {ρ τ : Ty ι} (f g : Ty.interpret X (ρ →ₜ τ).hat),
    (∀ (x y : Ty.interpret X ρ.hat), selfMaj ρ x y → selfMaj τ (f x) (g y)) →
    (∀ (x y : Ty.interpret X ρ.hat), selfMaj ρ x y → selfMaj τ (f x) (f y)) →
    selfMaj (ρ →ₜ τ) f g
  /-- Product introduction for `selfMaj`. -/
  selfMaj_prod_intro : ∀ {ρ τ : Ty ι} (p q : Ty.interpret X (ρ ×ₜ τ).hat),
    selfMaj ρ p.1 q.1 → selfMaj τ p.2 q.2 → selfMaj (ρ ×ₜ τ) p q
  /-- Product elimination for `selfMaj`, first component. -/
  selfMaj_prod_fst : ∀ {ρ τ : Ty ι} (p q : Ty.interpret X (ρ ×ₜ τ).hat),
    selfMaj (ρ ×ₜ τ) p q → selfMaj ρ p.1 q.1
  /-- Product elimination for `selfMaj`, second component. -/
  selfMaj_prod_snd : ∀ {ρ τ : Ty ι} (p q : Ty.interpret X (ρ ×ₜ τ).hat),
    selfMaj (ρ ×ₜ τ) p q → selfMaj τ p.2 q.2
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
  /-- **`maxT` compatibility, left** — a pointwise maximum majorizes whatever its left
      argument majorizes, provided the right argument majorizes itself. Needed by
      `and_contract`'s monotone majorant; true of every `bezem*` instance
      (`maxT_bezemMaj_left`). -/
  maxT_maj_left : ∀ {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} {c : Ty.interpret X ρ},
    maj ρ a c → selfMaj ρ b b → maj ρ (maxT ρ a b) c
  /-- **`maxT` compatibility, right** — the mirror image of `maxT_maj_left`. -/
  maxT_maj_right : ∀ {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} {c : Ty.interpret X ρ},
    maj ρ b c → selfMaj ρ a a → maj ρ (maxT ρ a b) c
  /-- **`maxT` is a `selfMaj`-congruence.** The third `max` fact `and_contract` needs: the
      `max`-majorant must itself be self-majorizing (hat-monotone), which is what
      `arrow_intro`'s second clause asks of it. -/
  maxT_selfMaj : ∀ {ρ : Ty ι} {a b c d : Ty.interpret X ρ.hat},
    selfMaj ρ a b → selfMaj ρ c d → selfMaj ρ (maxT ρ a c) (maxT ρ b d)
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
  func_maj : ∀ (f : κ), ∃ f_star : ℕ → Ty.interpret X (F f).hat,
    ∀ n ≥ N, maj (F f) (f_star n) (si.funcInterp f)
  /-- Majorant for zero elements (0_{X_i}). -/
  zeroX_maj : ∀ (i : ι), ∃ z_star : ℕ → Nat,
    ∀ n ≥ N, maj (.base i) (z_star n) (si.zeroInterp i)
  /-- Majorant for the distance `d_{X_i}` carried by every base type.

      For a metric space with reference point `a` and `base i n x := d(a,x) ≤ n`, this is the
      usual `λn₁ n₂. (n₁ + n₂)◦` — a bound on `d(x,y)` given bounds on `d(a,x)`, `d(a,y)`,
      by the triangle inequality. -/
  dist_maj : ∀ (i : ι),
    ∃ d_star : ℕ → Ty.interpret X (Ty.base i →ₜ Ty.base i →ₜ realTy ι).hat,
    ∀ n ≥ N, maj (Ty.base i →ₜ Ty.base i →ₜ realTy ι) (d_star n) (si.distInterp i)

-- Hat-context lookup and majorizable environments

/-- Look up a variable in an interpreted hat-context. -/
def Ctx.lookupHat {ι : Type} {X : ι → Type} :
    {Γ : Ctx ι} → {τ : Ty ι} → Var Γ τ →
    Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X τ.hat
  | _ :: _, _, .vz,   (v, _)   => v
  | _ :: _, _, .vs x, (_, env) => Ctx.lookupHat x env

/-- An environment pair `(env_star, env)` is majorizable if each component
    of `env_star` majorizes the corresponding component of `env`. -/
def MajEnv {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) :
    (Γ : Ctx ι) → Ctx.interpret X (Γ.map Ty.hat) → Ctx.interpret X Γ → Prop
  | [],     (),              ()           => True
  | _ :: Γ, (v_star, e_star), (v, env)    => am.maj _ v_star v ∧ MajEnv am Γ e_star env

/-- Looking up a variable in a majorizable environment preserves majorizability. -/
lemma MajEnv.lookup {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si}
    {Γ : Ctx ι} {τ : Ty ι} (v : Var Γ τ)
    {env_star : Ctx.interpret X (Γ.map Ty.hat)} {env : Ctx.interpret X Γ}
    (h : MajEnv am Γ env_star env) :
    am.maj τ (Ctx.lookupHat v env_star) (Ctx.lookup v env) := by
  induction v with
  | vz => exact h.1
  | vs w ih => exact ih h.2

/-- Two hat-environments are `selfMaj`-related componentwise. The `lam` case of
`all_terms_majorizable` needs this: `arrow_intro`'s self-majorization obligation is a
statement about the *majorant* alone, so the induction has to carry hat-level monotonicity of
the majorant in its environment. -/
def SelfMajEnv {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) :
    (Γ : Ctx ι) → Ctx.interpret X (Γ.map Ty.hat) → Ctx.interpret X (Γ.map Ty.hat) → Prop
  | [],     (),          ()          => True
  | _ :: Γ, (v₁, e₁), (v₂, e₂) => am.selfMaj _ v₁ v₂ ∧ SelfMajEnv am Γ e₁ e₂

lemma SelfMajEnv.lookup {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si}
    {Γ : Ctx ι} {τ : Ty ι} (v : Var Γ τ)
    {e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)} (h : SelfMajEnv am Γ e₁ e₂) :
    am.selfMaj τ (Ctx.lookupHat v e₁) (Ctx.lookupHat v e₂) := by
  induction v with
  | vz => exact h.1
  | vs w ih => exact ih h.2

lemma SelfMajEnv.self {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} :
    ∀ (Γ : Ctx ι) {e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)},
      SelfMajEnv am Γ e₁ e₂ → SelfMajEnv am Γ e₁ e₁
  | [],     _, _, _ => trivial
  | _ :: Γ, _, _, h => ⟨am.selfMaj_self h.1, SelfMajEnv.self Γ h.2⟩

lemma MajEnv.toSelfMajEnv {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} :
    ∀ (Γ : Ctx ι) {env_star : Ctx.interpret X (Γ.map Ty.hat)} {env : Ctx.interpret X Γ},
      MajEnv am Γ env_star env → SelfMajEnv am Γ env_star env_star
  | [],     _, _, _ => trivial
  | _ :: Γ, _, _, h => ⟨am.maj_selfMaj h.1, MajEnv.toSelfMajEnv Γ h.2⟩

-- All terms are majorizable (generalized Lemma 6.0.2)

/-- A closed term `t : Term F [] ρ` is majorizable if there exists
    `t* : ℕ → Ty.interpret X ρ̂` such that `t*(n) ≥*_ρ t` for all `n ≥ N`. -/
def IsMajorizable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
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
theorem all_terms_majorizable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {Γ : Ctx ι} {ρ : Ty ι} (t : Term F Γ ρ) :
    ∃ t_star : ℕ → Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X ρ.hat,
      ∀ n ≥ am.N,
        (∀ (env_star : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
            MajEnv am Γ env_star env →
            am.maj ρ (t_star n env_star) (Term.interpret si t env))
        ∧ (∀ (e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)),
            SelfMajEnv am Γ e₁ e₂ → am.selfMaj ρ (t_star n e₁) (t_star n e₂)) := by
  induction t with
  | var v =>
    exact ⟨fun _ env_star => Ctx.lookupHat v env_star,
      fun _ _ => ⟨fun _ _ h => MajEnv.lookup v h, fun _ _ h => SelfMajEnv.lookup v h⟩⟩
  | app f a ihf iha =>
    obtain ⟨f_star, hf⟩ := ihf
    obtain ⟨a_star, ha⟩ := iha
    exact ⟨fun n env_star => f_star n env_star (a_star n env_star),
      fun n hn =>
        ⟨fun env_star env henv =>
            am.app_compat _ _ _ _ ((hf n hn).1 env_star env henv) ((ha n hn).1 env_star env henv),
         fun e₁ e₂ he =>
            am.selfMaj_app ((hf n hn).2 e₁ e₂ he) ((ha n hn).2 e₁ e₂ he)⟩⟩
  | lam body ih =>
    obtain ⟨body_star, hbody⟩ := ih
    refine ⟨fun n env_star x_star => body_star n (x_star, env_star), fun n hn => ⟨?_, ?_⟩⟩
    · exact fun env_star env henv =>
        am.arrow_intro _ _
          (fun x_star x hx => (hbody n hn).1 (x_star, env_star) (x, env) ⟨hx, henv⟩)
          (fun x_star x hx =>
            (hbody n hn).2 (x_star, env_star) (x, env_star)
              ⟨hx, MajEnv.toSelfMajEnv _ henv⟩)
    · exact fun e₁ e₂ he =>
        am.selfMaj_arrow_intro _ _
          (fun x y hx => (hbody n hn).2 (x, e₁) (y, e₂) ⟨hx, he⟩)
          (fun x y hx => (hbody n hn).2 (x, e₁) (y, e₁) ⟨hx, SelfMajEnv.self _ he⟩)
  | zero =>
    obtain ⟨z_star, hz⟩ := am.zero_maj
    exact ⟨fun n _ => z_star n,
      fun n hn => ⟨fun _ _ _ => hz n hn, fun _ _ _ => am.maj_selfMaj (hz n hn)⟩⟩
  | succ =>
    obtain ⟨s_star, hs⟩ := am.succ_maj
    exact ⟨fun n _ => s_star n,
      fun n hn => ⟨fun _ _ _ => hs n hn, fun _ _ _ => am.maj_selfMaj (hs n hn)⟩⟩
  | prec ρ =>
    obtain ⟨r_star, hr⟩ := am.prec_maj ρ
    exact ⟨fun n _ => r_star n,
      fun n hn => ⟨fun _ _ _ => hr n hn, fun _ _ _ => am.maj_selfMaj (hr n hn)⟩⟩
  | func f =>
    obtain ⟨f_star, hf⟩ := am.func_maj f
    exact ⟨fun n _ => f_star n,
      fun n hn => ⟨fun _ _ _ => hf n hn, fun _ _ _ => am.maj_selfMaj (hf n hn)⟩⟩
  | zeroX i =>
    obtain ⟨z_star, hz⟩ := am.zeroX_maj i
    exact ⟨fun n _ => z_star n,
      fun n hn => ⟨fun _ _ _ => hz n hn, fun _ _ _ => am.maj_selfMaj (hz n hn)⟩⟩
  | dist i =>
    obtain ⟨d_star, hd⟩ := am.dist_maj i
    exact ⟨fun n _ => d_star n,
      fun n hn => ⟨fun _ _ _ => hd n hn, fun _ _ _ => am.maj_selfMaj (hd n hn)⟩⟩
  | unitI =>
    exact ⟨fun _ _ => (),
      fun _ _ => ⟨fun _ _ _ => am.unit_maj, fun _ _ _ => am.maj_selfMaj am.unit_maj⟩⟩
  | mkPair a b iha ihb =>
    obtain ⟨a_star, ha⟩ := iha
    obtain ⟨b_star, hb⟩ := ihb
    exact ⟨fun n env_star => (a_star n env_star, b_star n env_star),
      fun n hn =>
        ⟨fun env_star env henv =>
            am.prod_intro _ _ ((ha n hn).1 env_star env henv) ((hb n hn).1 env_star env henv),
         fun e₁ e₂ he =>
            am.selfMaj_prod_intro _ _ ((ha n hn).2 e₁ e₂ he) ((hb n hn).2 e₁ e₂ he)⟩⟩
  | fst p ih =>
    obtain ⟨p_star, hp⟩ := ih
    exact ⟨fun n env_star => (p_star n env_star).1,
      fun n hn =>
        ⟨fun env_star env henv => am.prod_fst _ _ ((hp n hn).1 env_star env henv),
         fun e₁ e₂ he => am.selfMaj_prod_fst _ _ ((hp n hn).2 e₁ e₂ he)⟩⟩
  | snd p ih =>
    obtain ⟨p_star, hp⟩ := ih
    exact ⟨fun n env_star => (p_star n env_star).2,
      fun n hn =>
        ⟨fun env_star env henv => am.prod_snd _ _ ((hp n hn).1 env_star env henv),
         fun e₁ e₂ he => am.selfMaj_prod_snd _ _ ((hp n hn).2 e₁ e₂ he)⟩⟩

/-- **Corollary**: All closed terms are majorizable. -/
theorem all_closed_terms_majorizable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : IsMajorizable am t := by
  obtain ⟨t_star, ht⟩ := all_terms_majorizable am t
  exact ⟨fun n => t_star n (), fun n hn => (ht n hn).1 () () True.intro⟩

-- The majorant as DATA: `ConstMajorants` and `termMajorizer`

/-! `IsMajorizable` is a `Prop`, so `all_closed_terms_majorizable` proves that a majorant exists.
`ConstMajorants` is `AbstractMajorizability`'s six per-constant majorant fields as **data**, and
`termMajorizer` is `all_terms_majorizable`'s recursion written as a function — for callers who
need the number rather than its existence. -/

/-- The six per-constant majorants of an `AbstractMajorizability`, as data rather than as
existential statements. Everything else in the structure is already `Prop`-valued and stays
there; these are the only fields carrying computational content. -/
structure ConstMajorants {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) : Type where
  /-- Majorant for `0`. -/
  zeroM : ℕ → Nat
  zeroM_maj : ∀ n ≥ am.N, am.maj .nat (zeroM n) (0 : Nat)
  /-- Majorant for `S`. -/
  succM : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat
  succM_maj : ∀ n ≥ am.N, am.maj (.nat →ₜ .nat) (succM n) (Nat.succ : Nat → Nat)
  /-- Majorant for the recursor at each type. -/
  precM : (ρ : Ty ι) → ℕ → Ty.interpret X (recTy ρ).hat
  precM_maj : ∀ (ρ : Ty ι), ∀ n ≥ am.N, am.maj (recTy ρ) (precM ρ n)
    (fun (y : Ty.interpret X ρ)
         (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
         (n : Nat) => Nat.rec y (fun n ih => z ih n) n)
  /-- Majorant for each function constant. -/
  funcM : (f : κ) → ℕ → Ty.interpret X (F f).hat
  funcM_maj : ∀ (f : κ), ∀ n ≥ am.N, am.maj (F f) (funcM f n) (si.funcInterp f)
  /-- Majorant for each base-type zero element. -/
  zeroXM : (i : ι) → ℕ → Nat
  zeroXM_maj : ∀ (i : ι), ∀ n ≥ am.N, am.maj (.base i) (zeroXM i n) (si.zeroInterp i)
  /-- Majorant for each base type's distance. -/
  distM : (i : ι) → ℕ → Ty.interpret X (Ty.base i →ₜ Ty.base i →ₜ realTy ι).hat
  distM_maj : ∀ (i : ι), ∀ n ≥ am.N,
    am.maj (Ty.base i →ₜ Ty.base i →ₜ realTy ι) (distM i n) (si.distInterp i)

/-- **The majorant of a term, as a function.** This is `all_terms_majorizable`'s witness,
written out: the same structural recursion, but computing rather than asserting. Compare the
proof of `all_terms_majorizable` case by case — they agree constructor for constructor. -/
def termMajorizer {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} (cm : ConstMajorants am) :
    {Γ : Ctx ι} → {ρ : Ty ι} → Term F Γ ρ → ℕ →
      Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X ρ.hat
  | _, _, .var v,      _, env_star => Ctx.lookupHat v env_star
  | _, _, .app f a,    n, env_star =>
      termMajorizer cm f n env_star (termMajorizer cm a n env_star)
  | _, _, .lam body,   n, env_star => fun x_star => termMajorizer cm body n (x_star, env_star)
  | _, _, .zero,       n, _        => cm.zeroM n
  | _, _, .succ,       n, _        => cm.succM n
  | _, _, .prec ρ,     n, _        => cm.precM ρ n
  | _, _, .func f,     n, _        => cm.funcM f n
  | _, _, .zeroX i,    n, _        => cm.zeroXM i n
  | _, _, .dist i,     n, _        => cm.distM i n
  | _, _, .unitI,      _, _        => ()
  | _, _, .mkPair a b, n, env_star =>
      (termMajorizer cm a n env_star, termMajorizer cm b n env_star)
  | _, _, .fst p,      n, env_star => (termMajorizer cm p n env_star).1
  | _, _, .snd p,      n, env_star => (termMajorizer cm p n env_star).2

/-- **`termMajorizer` is correct.** Identical in content to `all_terms_majorizable`; the
difference is only that the witness is now named in the statement instead of bound by `∃`. -/
theorem termMajorizer_maj {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} (cm : ConstMajorants am)
    {Γ : Ctx ι} {ρ : Ty ι} (t : Term F Γ ρ) :
    ∀ n ≥ am.N,
      (∀ (env_star : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
          MajEnv am Γ env_star env →
          am.maj ρ (termMajorizer cm t n env_star) (Term.interpret si t env))
      ∧ (∀ (e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)),
          SelfMajEnv am Γ e₁ e₂ →
          am.selfMaj ρ (termMajorizer cm t n e₁) (termMajorizer cm t n e₂)) := by
  induction t with
  | var v =>
    exact fun _ _ => ⟨fun _ _ h => MajEnv.lookup v h, fun _ _ h => SelfMajEnv.lookup v h⟩
  | app f a ihf iha =>
    exact fun n hn =>
      ⟨fun env_star env henv =>
          am.app_compat _ _ _ _ ((ihf n hn).1 env_star env henv) ((iha n hn).1 env_star env henv),
       fun e₁ e₂ he => am.selfMaj_app ((ihf n hn).2 e₁ e₂ he) ((iha n hn).2 e₁ e₂ he)⟩
  | lam body ih =>
    refine fun n hn => ⟨?_, ?_⟩
    · exact fun env_star env henv =>
        am.arrow_intro _ _
          (fun x_star x hx => (ih n hn).1 (x_star, env_star) (x, env) ⟨hx, henv⟩)
          (fun x_star x hx =>
            (ih n hn).2 (x_star, env_star) (x, env_star) ⟨hx, MajEnv.toSelfMajEnv _ henv⟩)
    · exact fun e₁ e₂ he =>
        am.selfMaj_arrow_intro _ _
          (fun x y hx => (ih n hn).2 (x, e₁) (y, e₂) ⟨hx, he⟩)
          (fun x y hx => (ih n hn).2 (x, e₁) (y, e₁) ⟨hx, SelfMajEnv.self _ he⟩)
  | zero =>
    exact fun n hn => ⟨fun _ _ _ => cm.zeroM_maj n hn,
      fun _ _ _ => am.maj_selfMaj (cm.zeroM_maj n hn)⟩
  | succ =>
    exact fun n hn => ⟨fun _ _ _ => cm.succM_maj n hn,
      fun _ _ _ => am.maj_selfMaj (cm.succM_maj n hn)⟩
  | prec ρ =>
    exact fun n hn => ⟨fun _ _ _ => cm.precM_maj ρ n hn,
      fun _ _ _ => am.maj_selfMaj (cm.precM_maj ρ n hn)⟩
  | func f =>
    exact fun n hn => ⟨fun _ _ _ => cm.funcM_maj f n hn,
      fun _ _ _ => am.maj_selfMaj (cm.funcM_maj f n hn)⟩
  | zeroX i =>
    exact fun n hn => ⟨fun _ _ _ => cm.zeroXM_maj i n hn,
      fun _ _ _ => am.maj_selfMaj (cm.zeroXM_maj i n hn)⟩
  | dist i =>
    exact fun n hn => ⟨fun _ _ _ => cm.distM_maj i n hn,
      fun _ _ _ => am.maj_selfMaj (cm.distM_maj i n hn)⟩
  | unitI =>
    exact fun _ _ => ⟨fun _ _ _ => am.unit_maj, fun _ _ _ => am.maj_selfMaj am.unit_maj⟩
  | mkPair a b iha ihb =>
    exact fun n hn =>
      ⟨fun env_star env henv =>
          am.prod_intro _ _ ((iha n hn).1 env_star env henv) ((ihb n hn).1 env_star env henv),
       fun e₁ e₂ he =>
          am.selfMaj_prod_intro _ _ ((iha n hn).2 e₁ e₂ he) ((ihb n hn).2 e₁ e₂ he)⟩
  | fst p ih =>
    exact fun n hn =>
      ⟨fun env_star env henv => am.prod_fst _ _ ((ih n hn).1 env_star env henv),
       fun e₁ e₂ he => am.selfMaj_prod_fst _ _ ((ih n hn).2 e₁ e₂ he)⟩
  | snd p ih =>
    exact fun n hn =>
      ⟨fun env_star env henv => am.prod_snd _ _ ((ih n hn).1 env_star env henv),
       fun e₁ e₂ he => am.selfMaj_prod_snd _ _ ((ih n hn).2 e₁ e₂ he)⟩

/-- **The majorant of a closed term, computed.** The `Type`-valued counterpart of
`majorant_of_closed_term`: same value, but available rather than erased. -/
def closedMajorizer {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} (cm : ConstMajorants am)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) : Ty.interpret X ρ.hat :=
  termMajorizer cm t am.N ()

theorem closedMajorizer_maj {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} {am : AbstractMajorizability si} (cm : ConstMajorants am)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) :
    am.maj ρ (closedMajorizer cm t) (Term.interpret si t ()) :=
  (termMajorizer_maj cm t am.N (Nat.le_refl _)).1 () () trivial

-- `termMajorizer` commutes with renaming, weakening, casting and substitution

/-! These mirror `Term.interpret_rename_gen` / `interpret_weaken` / `interpret_subst0` in
`Semantics.lean`. With them `simp` pushes `termMajorizer` through the `Term.weaken` /
`Term.castTy` wrapping of a sub-realizer to its own majorant, without forcing the wrapped term
to whnf. -/

section Structural

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

/-- General form, mirroring `Term.interpret_rename_gen`: `termMajorizer` commutes with any
renaming whose `env_star`s agree on `Ctx.lookupHat`. -/
theorem termMajorizer_rename_gen (cm : ConstMajorants am) :
    ∀ {Γ Δ : Ctx ι} {ρ : Ty ι} (r : Term.Renaming Γ Δ) (t : Term F Γ ρ) (n : ℕ)
    (env_starΔ : Ctx.interpret X (Δ.map Ty.hat)) (env_starΓ : Ctx.interpret X (Γ.map Ty.hat)),
    (∀ {σ} (v : Var Γ σ), Ctx.lookupHat (r v) env_starΔ = Ctx.lookupHat v env_starΓ) →
    termMajorizer cm (t.rename r) n env_starΔ = termMajorizer cm t n env_starΓ := by
  intro Γ Δ ρ r t
  induction t generalizing Δ with
  | var v => intro n env_starΔ env_starΓ h; exact h v
  | app f a ihf iha =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ihf r n env_starΔ env_starΓ h,
      iha r n env_starΔ env_starΓ h]
  | lam body ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer]
    funext x
    exact ih (Term.Renaming.ext r) n (x, env_starΔ) (x, env_starΓ) (fun v => by
      cases v with
      | vz => rfl
      | vs w => exact h w)
  | zero | succ | prec | func | zeroX | dist | unitI => intros; rfl
  | mkPair a b iha ihb =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, iha r n env_starΔ env_starΓ h,
      ihb r n env_starΔ env_starΓ h]
  | fst p ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ih r n env_starΔ env_starΓ h]
  | snd p ih =>
    intro n env_starΔ env_starΓ h
    simp only [Term.rename, termMajorizer, ih r n env_starΔ env_starΓ h]

/-- **The enabling lemma.** `termMajorizer` commutes with `Term.weaken`. -/
@[simp] theorem termMajorizer_weaken (cm : ConstMajorants am) {Γ : Ctx ι} {ρ σ : Ty ι}
    (t : Term F Γ ρ) (n : ℕ) (x_star : Ty.interpret X σ.hat)
    (env_star : Ctx.interpret X (Γ.map Ty.hat)) :
    termMajorizer cm (Term.weaken t (σ := σ)) n (x_star, env_star)
      = termMajorizer cm t n env_star :=
  termMajorizer_rename_gen cm Term.Renaming.shift t n (x_star, env_star) env_star (fun _ => rfl)

/-- The substitution analogue of `termMajorizer_rename_gen`. -/
theorem termMajorizer_subst_gen (cm : ConstMajorants am) :
    ∀ {Γ Δ : Ctx ι} {ρ : Ty ι} (σ : Term.Subst F Γ Δ) (t : Term F Γ ρ) (n : ℕ)
    (eΔ : Ctx.interpret X (Δ.map Ty.hat)) (eΓ : Ctx.interpret X (Γ.map Ty.hat)),
    (∀ {τ} (v : Var Γ τ), termMajorizer cm (σ v) n eΔ = Ctx.lookupHat v eΓ) →
    termMajorizer cm (t.subst σ) n eΔ = termMajorizer cm t n eΓ := by
  intro Γ Δ ρ σ t
  induction t generalizing Δ with
  | var v => intro n eΔ eΓ h; exact h v
  | app f a ihf iha =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ihf σ n eΔ eΓ h, iha σ n eΔ eΓ h]
  | lam body ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer]
    funext x
    exact ih (Term.Subst.ext σ) n (x, eΔ) (x, eΓ) (fun v => by
      cases v with
      | vz => rfl
      | vs w =>
        change termMajorizer cm (Term.weaken (σ w)) n (x, eΔ) = _
        rw [termMajorizer_weaken]; exact h w)
  | zero | succ | prec | func | zeroX | dist | unitI => intros; rfl
  | mkPair a b iha ihb =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, iha σ n eΔ eΓ h, ihb σ n eΔ eΓ h]
  | fst p ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ih σ n eΔ eΓ h]
  | snd p ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ih σ n eΔ eΓ h]

/-- The `Term.interpret_subst0` analogue: substitution is environment extension. -/
@[simp] theorem termMajorizer_subst0 (cm : ConstMajorants am) {Γ : Ctx ι} {ρ σ : Ty ι}
    (t : Term F (σ :: Γ) ρ) (s : Term F Γ σ) (n : ℕ)
    (e : Ctx.interpret X (Γ.map Ty.hat)) :
    termMajorizer cm (t.subst0 s) n e = termMajorizer cm t n (termMajorizer cm s n e, e) :=
  termMajorizer_subst_gen cm (Term.subst0_map s) t n e (termMajorizer cm s n e, e)
    (fun v => by cases v with | vz => rfl | vs w => rfl)

end Structural

-- Bridge to `MajorizabilityRel` (what the metatheorem consumes)

/-- `AbstractMajorizability` contains `MajorizabilityRel`: same `maj`, and `nat_order` /
`app_compat` are `maj_le` / `maj_app` with explicit arguments. -/
def AbstractMajorizability.toRel {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si) : MajorizabilityRel si where
  maj := am.maj
  maj_le h := am.nat_order _ _ h
  maj_app hf hx := am.app_compat _ _ _ _ hf hx

/-- **The point of the syntactic route.** A closed term's interpretation has a majorant,
outright — instantiate `all_closed_terms_majorizable` at the threshold `N`. This is exactly
the `U_star` / `V_star` that `metatheorem_core_of_majorants` asks for. -/
theorem majorant_of_closed_term {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    {si : SpaceInterp X F} (am : AbstractMajorizability si)
    {ρ : Ty ι} (t : Term F ([] : Ctx ι) ρ) :
    ∃ x_star : Ty.interpret X ρ.hat,
      am.toRel.maj ρ x_star (Term.interpret si t ()) := by
  obtain ⟨t_star, ht⟩ := all_closed_terms_majorizable am t
  exact ⟨t_star am.N, ht am.N (Nat.le_refl _)⟩

-- Building an `AbstractMajorizability` from a base-type relation

/-! The document's route (`particular-cases-metric-spaces.tex`, and Kohlenbach's Proposition
in §17) fixes the relation only at the base types and then discharges *two structural
conditions* plus *one obligation per constant*. `bezemMaj` is exactly that extension of a
base relation, and every structural field of `AbstractMajorizability` holds for it by
definitional unfolding — `arrow_intro` in particular is `fun _ _ h => h`, because
`bezemMaj base (ρ →ₜ τ)` *is* the ∀-statement the field demands.

So instantiating for a concrete space means supplying only the five constant majorants.
That is `bezemAbstract`. -/

section BezemAbstract

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}

/-- The structural half of `AbstractMajorizability` for `bezemMaj base`, packaged so that a
concrete space supplies only the per-constant obligations.

`N` is the uniform threshold; the five majorant arguments are the document's per-constant
conditions, stated against `bezemMaj base`. `hbase : BaseMono base` is what the three
`maxT_*` fields need at a base type. -/
def bezemAbstract (si : SpaceInterp X F) (base : (i : ι) → Nat → X i → Prop)
    (hbase : BaseMono base) (N : ℕ)
    (zero_maj : ∃ z_star : ℕ → Nat, ∀ n ≥ N, bezemMaj base .nat (z_star n) (0 : Nat))
    (succ_maj : ∃ s_star : ℕ → Ty.interpret X (Ty.nat →ₜ Ty.nat).hat,
      ∀ n ≥ N, bezemMaj base (.nat →ₜ .nat) (s_star n) (Nat.succ : Nat → Nat))
    (prec_maj : ∀ (ρ : Ty ι), ∃ r_star : ℕ → Ty.interpret X (recTy ρ).hat,
      ∀ n ≥ N, bezemMaj base (recTy ρ) (r_star n)
        (fun (y : Ty.interpret X ρ)
             (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
             (n : Nat) => Nat.rec y (fun n ih => z ih n) n))
    (func_maj : ∀ (f : κ), ∃ f_star : ℕ → Ty.interpret X (F f).hat,
      ∀ n ≥ N, bezemMaj base (F f) (f_star n) (si.funcInterp f))
    (zeroX_maj : ∀ (i : ι), ∃ z_star : ℕ → Nat,
      ∀ n ≥ N, bezemMaj base (.base i) (z_star n) (si.zeroInterp i))
    (dist_maj : ∀ (i : ι),
      ∃ d_star : ℕ → Ty.interpret X (Ty.base i →ₜ Ty.base i →ₜ realTy ι).hat,
      ∀ n ≥ N, bezemMaj base (Ty.base i →ₜ Ty.base i →ₜ realTy ι) (d_star n)
        (si.distInterp i)) :
    AbstractMajorizability si where
  maj := bezemMaj base
  nat_order _ _ h := h
  app_compat _ _ _ _ hf hx := hf.1 _ _ hx
  selfMaj := hatMaj
  maj_selfMaj h := hatMaj_of_bezemMaj _ _ _ h
  selfMaj_self h := hatMaj_self _ _ _ h
  selfMaj_app hf hx := hf.1 _ _ hx
  arrow_intro _ _ h₁ h₂ := ⟨h₁, h₂⟩
  selfMaj_arrow_intro _ _ h₁ h₂ := ⟨h₁, h₂⟩
  selfMaj_prod_intro _ _ h₁ h₂ := ⟨h₁, h₂⟩
  selfMaj_prod_fst _ _ h := h.1
  selfMaj_prod_snd _ _ h := h.2
  prod_intro _ _ h₁ h₂ := ⟨h₁, h₂⟩
  prod_fst _ _ h := h.1
  prod_snd _ _ h := h.2
  unit_maj := trivial
  maxT_maj_left h₁ h₂ := maxT_bezemMaj_left hbase _ _ _ _ h₁ h₂
  maxT_maj_right h₁ h₂ := by
    rw [maxT_comm]
    exact maxT_bezemMaj_left hbase _ _ _ _ h₁ h₂
  maxT_selfMaj h₁ h₂ := maxT_hatMaj _ _ _ _ _ h₁ h₂
  N := N
  zero_maj := zero_maj
  succ_maj := succ_maj
  prec_maj := prec_maj
  func_maj := func_maj
  zeroX_maj := zeroX_maj
  dist_maj := dist_maj

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
  ⟨fun _ => Nat.succ,
    fun _ _ => ⟨fun _ _ h => Nat.succ_le_succ h, fun _ _ h => Nat.succ_le_succ h⟩⟩

/-! ### The recursor

The majorant is the recursion with a running `maxT`, so it is monotone by construction. The
obligation at `n* ≥ n` is closed by `recMaj_hatMaj` composed with `bezemMaj_of_hatMaj`. -/

/-- The recursor's semantic value, spelled as `Nat.rec` so it matches
`AbstractMajorizability.prec_maj`'s statement definitionally. -/
def recSem (ρ : Ty ι) (y : Ty.interpret X ρ)
    (z : Ty.interpret X ρ → Nat → Ty.interpret X ρ) (n : Nat) : Ty.interpret X ρ :=
  Nat.rec (motive := fun _ => Ty.interpret X ρ) y (fun k ih => z ih k) n

/-- The recursor's majorant: the same recursion with a running maximum. -/
def recMaj (ρ : Ty ι) (y_star : Ty.interpret X ρ.hat)
    (z_star : Ty.interpret X ρ.hat → Nat → Ty.interpret X ρ.hat) (n : Nat) :
    Ty.interpret X ρ.hat :=
  Nat.rec (motive := fun _ => Ty.interpret X ρ.hat) y_star
    (fun k ih => maxT ρ (z_star ih k) ih) n

theorem recSem_zero (ρ : Ty ι) (y : Ty.interpret X ρ) (z) : recSem ρ y z 0 = y := rfl

theorem recSem_succ (ρ : Ty ι) (y : Ty.interpret X ρ) (z) (k : Nat) :
    recSem ρ y z (k + 1) = z (recSem ρ y z k) k := rfl

theorem recMaj_zero (ρ : Ty ι) (y : Ty.interpret X ρ.hat) (z) : recMaj ρ y z 0 = y := rfl

theorem recMaj_succ (ρ : Ty ι) (y : Ty.interpret X ρ.hat) (z) (k : Nat) :
    recMaj ρ y z (k + 1) = maxT ρ (z (recMaj ρ y z k) k) (recMaj ρ y z k) := rfl

/-- The majorant is `hatMaj`-monotone in *all three* arguments, the numeric one included.
This is the statement the second conjunct exists to make provable. -/
theorem recMaj_hatMaj (ρ : Ty ι) {y₁ y₂ : Ty.interpret X ρ.hat}
    {z₁ z₂ : Ty.interpret X (ρ →ₜ Ty.nat →ₜ ρ).hat}
    (hy : hatMaj ρ y₁ y₂) (hz : hatMaj (ρ →ₜ Ty.nat →ₜ ρ) z₁ z₂) :
    ∀ n₁ n₂ : Nat, n₁ ≥ n₂ → hatMaj ρ (recMaj ρ y₁ z₁ n₁) (recMaj ρ y₂ z₂ n₂) := by
  intro n₁
  induction n₁ with
  | zero =>
    intro n₂ h
    have : n₂ = 0 := Nat.le_zero.mp h
    subst this
    exact hy
  | succ k ih =>
    intro n₂ h
    cases n₂ with
    | zero =>
      have hk := ih 0 (Nat.zero_le k)
      rw [recMaj_succ]
      refine maxT_hatMaj_right ρ _ _ _ hk ?_
      exact (hz.2 _ _ (hatMaj_self ρ _ _ hk)).1 k k (Nat.le_refl k)
    | succ m =>
      have hkm : k ≥ m := Nat.le_of_succ_le_succ h
      have hk := ih m hkm
      rw [recMaj_succ, recMaj_succ]
      exact maxT_hatMaj ρ _ _ _ _ ((hz.1 _ _ hk).1 k m hkm) hk

/-- The mixed statement, at `n* ≥ n` rather than at equal `n`. -/
theorem recMaj_bezemMaj {base : (i : ι) → Nat → X i → Prop} (hbase : BaseMono base)
    (ρ : Ty ι) {y_star : Ty.interpret X ρ.hat} {y : Ty.interpret X ρ}
    {z_star : Ty.interpret X (ρ →ₜ Ty.nat →ₜ ρ).hat}
    {z : Ty.interpret X (ρ →ₜ Ty.nat →ₜ ρ)}
    (hy : bezemMaj base ρ y_star y) (hz : bezemMaj base (ρ →ₜ Ty.nat →ₜ ρ) z_star z) :
    ∀ n_star n : Nat, n_star ≥ n →
      bezemMaj base ρ (recMaj ρ y_star z_star n_star) (recSem ρ y z n) := by
  intro n_star n
  induction n generalizing n_star with
  | zero =>
    intro h
    refine bezemMaj_of_hatMaj hbase ρ _ y_star _ ?_ hy
    exact recMaj_hatMaj ρ (hatMaj_of_bezemMaj ρ _ _ hy)
      (hatMaj_of_bezemMaj (ρ →ₜ Ty.nat →ₜ ρ) _ _ hz) n_star 0 (Nat.zero_le _)
  | succ m ih =>
    intro h
    cases n_star with
    | zero => exact absurd h (by omega)
    | succ k =>
      have hkm : k ≥ m := Nat.le_of_succ_le_succ h
      have hrec := ih k hkm
      rw [recMaj_succ, recSem_succ]
      exact maxT_bezemMaj_left hbase ρ _ _ _ ((hz.1 _ _ hrec).1 k m hkm)
        (hatMaj_of_bezemMaj ρ _ _ hrec)

/-- **`R` is majorizable**, for any base relation that is monotone in its numeric argument,
with the majorant `recMaj` **named** rather than existentially bound.

`bezem_prec_maj` below is the `∃` form; `ConstMajorants` needs this one, since it carries the
majorant as data. -/
theorem bezem_prec_maj_at {base : (i : ι) → Nat → X i → Prop} (hbase : BaseMono base) (N : ℕ)
    (ρ : Ty ι) :
    ∀ n ≥ N, bezemMaj base (recTy ρ)
        (fun y_star z_star n => recMaj ρ y_star z_star n)
        (fun (y : Ty.interpret X ρ)
             (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
             (n : Nat) => Nat.rec y (fun n ih => z ih n) n) := by
  refine fun _ _ => ⟨?_, ?_⟩
  · -- mixed clause
    intro y_star y hy
    refine ⟨?_, ?_⟩
    · intro z_star z hz
      exact ⟨fun n_star n hn => recMaj_bezemMaj hbase ρ hy hz n_star n hn,
             fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_of_bezemMaj ρ _ _ hy)
               (hatMaj_of_bezemMaj (ρ →ₜ Ty.nat →ₜ ρ) _ _ hz) n₁ n₂ hn⟩
    · intro z₁ z₂ hz
      exact ⟨fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_of_bezemMaj ρ _ _ hy) hz n₁ n₂ hn,
             fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_of_bezemMaj ρ _ _ hy)
               (hatMaj_self _ _ _ hz) n₁ n₂ hn⟩
  · -- self-majorization clause
    intro y₁ y₂ hy
    refine ⟨?_, ?_⟩
    · intro z₁ z₂ hz
      exact ⟨fun n₁ n₂ hn => recMaj_hatMaj ρ hy hz n₁ n₂ hn,
             fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_self _ _ _ hy)
               (hatMaj_self _ _ _ hz) n₁ n₂ hn⟩
    · intro z₁ z₂ hz
      exact ⟨fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_self _ _ _ hy) hz n₁ n₂ hn,
             fun n₁ n₂ hn => recMaj_hatMaj ρ (hatMaj_self _ _ _ hy)
               (hatMaj_self _ _ _ hz) n₁ n₂ hn⟩

/-- **`R` is majorizable**, existential form — `bezem_prec_maj_at` with the witness bound. -/
theorem bezem_prec_maj {base : (i : ι) → Nat → X i → Prop} (hbase : BaseMono base) (N : ℕ)
    (ρ : Ty ι) :
    ∃ r_star : ℕ → Ty.interpret X (recTy ρ).hat,
      ∀ n ≥ N, bezemMaj base (recTy ρ) (r_star n)
        (fun (y : Ty.interpret X ρ)
             (z : Ty.interpret X ρ → Ty.interpret X Ty.nat → Ty.interpret X ρ)
             (n : Nat) => Nat.rec y (fun n ih => z ih n) n) :=
  ⟨fun _ => fun y_star z_star n => recMaj ρ y_star z_star n, bezem_prec_maj_at hbase N ρ⟩

-- Pure WE-HA^ω (`ι = Empty`): the majorizability structure, with its data

/-! With no base types every space-dependent obligation is vacuous, so the structure is
determined outright — and, unlike the metric case, **everything here computes**: `Ty.interpret`
is built from `ℕ` alone, so `closedMajorizer` at `ι = Empty` produces an actual number. -/

/-- The majorizability structure for pure `WE-HA^ω`. -/
def bezemAbstractEmpty {X : Empty → Type} {F : Empty → Ty Empty} (si : SpaceInterp X F) :
    AbstractMajorizability si :=
  bezemAbstract si (fun i => i.elim) (fun i => i.elim) 0
    (bezem_zero_maj _ 0) (bezem_succ_maj _ 0)
    (fun ρ => bezem_prec_maj (fun i => i.elim) 0 ρ)
    (fun f => f.elim) (fun i => i.elim) (fun i => i.elim)

/-- Its constant majorants, as data. `0 ↦ 0`, `S ↦ S`, `R ↦ recMaj`; the three space-dependent
families are vacuous. This is what makes `termMajorizer` run. -/
def bezemConstMajorantsEmpty {X : Empty → Type} {F : Empty → Ty Empty}
    (si : SpaceInterp X F) : ConstMajorants (bezemAbstractEmpty si) where
  zeroM := fun _ => 0
  zeroM_maj := fun _ _ => Nat.le_refl 0
  succM := fun _ => Nat.succ
  succM_maj := fun _ _ =>
    ⟨fun _ _ h => Nat.succ_le_succ h, fun _ _ h => Nat.succ_le_succ h⟩
  precM := fun ρ _ => fun y_star z_star n => recMaj ρ y_star z_star n
  precM_maj := fun ρ => bezem_prec_maj_at (fun i => i.elim) 0 ρ
  funcM := fun f => f.elim
  funcM_maj := fun f => f.elim
  zeroXM := fun i => i.elim
  zeroXM_maj := fun i => i.elim
  distM := fun i => i.elim
  distM_maj := fun i => i.elim

/-! ### The majorant computes

Kernel-checked examples. Bare `rfl` gets stuck on the projection chain
`(bezemAbstractEmpty si).N → (bezemAbstract …).N`; `simp` naming the four definitions closes
them. -/

section ComputesDemo

/-- The carrier family for pure `WE-HA^ω`: no base types. -/
def XEmpty : Empty → Type := fun i => i.elim
/-- The function-constant signature for pure `WE-HA^ω`: none. -/
def FEmpty : Empty → Ty Empty := fun i => i.elim

/-- The numeral `3` majorizes itself: `S(S(S 0)) ↦ Nat.succ (Nat.succ (Nat.succ 0))`. The
interpretation `si` is a variable: the majorant does not depend on it. -/
example (si : SpaceInterp XEmpty FEmpty) : (3 : ℕ) =
    closedMajorizer (bezemConstMajorantsEmpty si)
      (Term.app Term.succ (Term.app Term.succ
        (Term.app (Term.succ (F := FEmpty) (Γ := [])) Term.zero))) := by
  simp [closedMajorizer, termMajorizer, bezemConstMajorantsEmpty, bezemAbstractEmpty,
    bezemAbstract]

/-- And the majorant of `S` is `Nat.succ`, so it majorizes every numeral pointwise. -/
example (si : SpaceInterp XEmpty FEmpty) : (8 : ℕ) =
    closedMajorizer (bezemConstMajorantsEmpty si)
      (Term.succ (F := FEmpty) (Γ := [])) ((7 : ℕ)) := by
  simp [closedMajorizer, termMajorizer, bezemConstMajorantsEmpty, bezemAbstractEmpty,
    bezemAbstract]

end ComputesDemo

/-- `bezemAbstract` and `bezemRel` agree, so a space built the per-constant way still feeds
anything stated against `MajorizabilityRel`. -/
theorem bezemAbstract_toRel_maj (si : SpaceInterp X F) (base : (i : ι) → Nat → X i → Prop)
    {hbase N hz hs hp hf hx hd} :
    (bezemAbstract si base hbase N hz hs hp hf hx hd).toRel.maj = (bezemRel si base).maj := rfl

end BezemAbstract

-- Axiom hygiene (CLAUDE.md note 5)

#print axioms all_terms_majorizable
#print axioms all_closed_terms_majorizable
#print axioms majorant_of_closed_term
#print axioms termMajorizer_maj
#print axioms closedMajorizer_maj
#print axioms bezem_prec_maj_at
#print axioms bezem_prec_maj
#print axioms bezemConstMajorantsEmpty

end Metatheorems
