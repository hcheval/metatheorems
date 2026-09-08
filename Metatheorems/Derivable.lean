/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.EqAtType


namespace Metatheorems

/-!
# Proof System for WE-HA^{ω,X}

Following Appendix 9 of the reference document, we define the Hilbert-style
proof system for WE-HA^{ω,X}_{=_X}.

The system is parametric in:
- `F : κ → Ty ι` — the abstract space function constants (`κ` indexes constants, `ι` base types)
- `allowed : Allowed` — which extension principles (LEM, AC, Markov, IP) are available

Equality at a base type is not a parameter: it is defined, as
`eqAtType (.base i) s t ≡ d_i(s,t) =ℝ 0ℝ`, and the three pseudometric axioms for
`Term.dist` are constructors below.
-/

open Formula

/-- Weaken a formula into context extended by ρ. Same as `Formula.weaken` but
    with the new type ρ given explicitly for unification. -/
def Formula.weakenBy {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι}
    (ρ : Ty ι) (A : Formula F Γ) : Formula F (ρ :: Γ) :=
  A.weaken

/-- `weakenBy` as a substitution, so that a substitution normaliser can push it inward. -/
theorem Formula.substF_shift_eq_weakenBy {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} {σ : Ty ι}
    (A : Formula F Γ) :
    A.substF (fun {_} v => Term.var (Term.Renaming.shift (σ := σ) v)) = A.weakenBy σ := by
  rw [Formula.weakenBy, Formula.weaken, Formula.renameF_eq_substF]

/-! ### Allowed principles -/

/-- Which extension principles are available in the proof system.
    The base theory WE-HA^{ω,X} has all fields `false`. -/
structure Allowed where
  lem    : Bool := false
  markov : Bool := false
  ip     : Bool := false
  ac     : Bool := false
  qfac   : Bool := false

namespace Allowed

/-- Base intuitionistic system WE-HA^{ω,X}. -/
def base : Allowed := {}

/-- Extended system T^ω[X,F] + AC + IP^ω_∀ + M^ω (Dialectica target).
    Includes qfac since full AC implies QF-AC. -/
def extended : Allowed := { markov := true, ip := true, ac := true, qfac := true }

/-- Classical system WE-HA^{ω,X}_c + LEM + QF-AC (negative translation source). -/
def classical : Allowed := { lem := true, qfac := true }

/-- NT target: T^ω + QF-AC + M^ω (negative translation output, Lemma lem:negative-eliminates-lem). -/
def nt_target : Allowed := { qfac := true, markov := true }

/-- Partial order: a₁ ≤ a₂ if every principle allowed in a₁ is also in a₂. -/
def le (a₁ a₂ : Allowed) : Prop :=
  (a₁.lem = true → a₂.lem = true) ∧
  (a₁.markov = true → a₂.markov = true) ∧
  (a₁.ip = true → a₂.ip = true) ∧
  (a₁.ac = true → a₂.ac = true) ∧
  (a₁.qfac = true → a₂.qfac = true)

/-- The base system permits nothing, so it is below every system. -/
theorem base_le (a : Allowed) : Allowed.le Allowed.base a :=
  ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
   fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

end Allowed

/-! ### The proof system -/

/-- Derivability in WE-HA^{ω,X}_{=_X} + allowed extensions.

Parametric in `F` (function constants) and `allowed` (which extension principles are
available).

When `allowed = Allowed.base`, this is pure WE-HA^{ω,X}.
When `allowed = Allowed.extended`, this adds AC + IP + Markov.
When `allowed = Allowed.classical`, this adds LEM + AC. -/
abbrev PremiseSet {ι κ : Type} (F : κ → Ty ι) := (Σ Γ : Ctx ι, Formula F Γ) → Prop

inductive Derivable {ι κ : Type} (F : κ → Ty ι)
    (allowed : Allowed)
    (Premises : PremiseSet F) :
    {Γ : Ctx ι} → Formula F Γ → Type where
  -- Premises (theory axioms). No shape condition on `A`: only `negTrans_sound` needs one,
  -- and it asks for it itself, as NT-stability.
  | premise      : Premises ⟨_, A⟩ → Derivable F allowed Premises A
  -- Propositional axioms (§9.1)
  | or_contract  : Derivable F allowed Premises (A ∨ᶠ A →ᶠ A)
  | and_contract : Derivable F allowed Premises (A →ᶠ A ∧ᶠ A)
  | or_weak      : Derivable F allowed Premises (A →ᶠ A ∨ᶠ B)
  | and_weak     : Derivable F allowed Premises (A ∧ᶠ B →ᶠ A)
  | or_perm      : Derivable F allowed Premises (A ∨ᶠ B →ᶠ B ∨ᶠ A)
  | and_perm     : Derivable F allowed Premises (A ∧ᶠ B →ᶠ B ∧ᶠ A)
  | exfalso      : Derivable F allowed Premises (⊥ᶠ →ᶠ A)
  | forall_ax    : (t : Term F Γ ρ) → Derivable F allowed Premises (Formula.all ρ A →ᶠ A.subst0 t)
  | exist_ax     : (t : Term F Γ ρ) → (A : Formula F (ρ :: Γ)) →
                   Derivable F allowed Premises (A.subst0 t →ᶠ Formula.ex ρ A)

  -- Rules (§9.2)
  | mp           : Derivable F allowed Premises A → Derivable F allowed Premises (A →ᶠ B) →
                   Derivable F allowed Premises B
  | syllogism    : Derivable F allowed Premises (A →ᶠ B) → Derivable F allowed Premises (B →ᶠ C) →
                   Derivable F allowed Premises (A →ᶠ C)
  | exportation  : Derivable F allowed Premises (A ∧ᶠ B →ᶠ C) →
                   Derivable F allowed Premises (A →ᶠ B →ᶠ C)
  | importation  : Derivable F allowed Premises (A →ᶠ B →ᶠ C) →
                   Derivable F allowed Premises (A ∧ᶠ B →ᶠ C)
  | expansion    : Derivable F allowed Premises (A →ᶠ B) →
                   Derivable F allowed Premises (C ∨ᶠ A →ᶠ C ∨ᶠ B)
  | forall_rule  : Derivable F allowed Premises (Formula.weakenBy ρ B →ᶠ A) →
                   Derivable F allowed Premises (B →ᶠ Formula.all ρ A)
  | exist_rule   : {B : Formula F Γ} → {A : Formula F (ρ :: Γ)} →
                   Derivable F allowed Premises (A →ᶠ Formula.weakenBy ρ B) →
                   Derivable F allowed Premises (Formula.ex ρ A →ᶠ B)

  -- Universal generalization (9.42)
  | univ_gen     : Derivable F allowed Premises A →
                   Derivable F allowed Premises (Formula.all ρ (Formula.weakenBy ρ A))

  -- Successor (§9.5)
  | succ_ne_zero : Derivable F allowed Premises
      (Formula.all Ty.nat
        (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ))
  | succ_inj     : Derivable F allowed Premises
      (Formula.all Ty.nat (Formula.all Ty.nat
        (Formula.eq0
          (Term.app Term.succ (.var (.vs .vz)))
          (Term.app Term.succ (.var .vz))
        →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))))

  -- Beta reduction (β-equality for primitive λ)
  | beta_eq      : (body : Term F (ρ :: Γ) τ) → (u : Term F Γ ρ) →
                   Derivable F allowed Premises
      (eqAtType τ (Term.app (Term.lam body) u) (Term.subst0 body u))

  -- Product β/η-equality, for the primitive `mkPair`/`fst`/`snd`
  | pair_fst     : (a : Term F Γ ρ) → (b : Term F Γ τ) →
                   Derivable F allowed Premises
      (eqAtType ρ (Term.fst (Term.mkPair a b)) a)
  | pair_snd     : (a : Term F Γ ρ) → (b : Term F Γ τ) →
                   Derivable F allowed Premises
      (eqAtType τ (Term.snd (Term.mkPair a b)) b)
  | pair_eta     : (p : Term F Γ (Ty.prod ρ τ)) →
                   Derivable F allowed Premises
      (eqAtType (Ty.prod ρ τ) (Term.mkPair (Term.fst p) (Term.snd p)) p)

  -- Recursor (§9.6, eq. 9.54)
  | rec_zero     : Derivable F allowed Premises
      (eqAtType ρ (Term.app3 (Term.prec ρ) y z Term.zero) y)
  | rec_succ     : Derivable F allowed Premises
      (eqAtType ρ
        (Term.app3 (Term.prec ρ) y z (Term.app Term.succ x))
        (Term.app2 z (Term.app3 (Term.prec ρ) y z x) x))

  -- Equality (§9.7). The pseudometric axioms for the structural `Term.dist` are what make
  -- equality at a base type an equivalence relation derivably; all three are Π⁰₁.
  | dist_self {Γ : Ctx ι} (i : ι) (x : Term F Γ (Ty.base i)) :
      Derivable F allowed Premises
        (eq_R (Term.app2 (Term.dist i) x x) Term.zero_R)
  | dist_comm {Γ : Ctx ι} (i : ι) (x y : Term F Γ (Ty.base i)) :
      Derivable F allowed Premises
        (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x))
  | dist_tri  {Γ : Ctx ι} (i : ι) (x y z : Term F Γ (Ty.base i)) :
      Derivable F allowed Premises
        (le_R_pu (Term.app2 (Term.dist i) x z)
          (Term.app2 Term.add_R
            (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z)))

  | refl0        : Derivable F allowed Premises (Formula.eq0 t t)
  | sym0         : Derivable F allowed Premises (Formula.eq0 s t →ᶠ Formula.eq0 t s)
  | trans0       : Derivable F allowed Premises
      (Formula.eq0 s t ∧ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u)

  -- QF-ER (§9.7, eq. 9.58). The ∨-freeness side condition is ours, not the document's:
  -- the Dialectica proof needs `Subsingleton` on the counter type.
  | qfer         : {A₀ : Formula F Γ} →
                   A₀.isQF = true → A₀.isVFree = true →
                   Derivable F allowed Premises (A₀ →ᶠ eqAtType ρ s t) →
                   Derivable F allowed Premises (A₀ →ᶠ eqAtType σ (Term.subst0 r s) (Term.subst0 r t))

  -- Induction (§9.8)
  | induction    : Derivable F allowed Premises (A.subst0 Term.zero) →
                   Derivable F allowed Premises (Formula.all Ty.nat
                     (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))) →
                   Derivable F allowed Premises (Formula.all Ty.nat A)

  -- Extension principles (guarded by `allowed` fields)

  -- Law of excluded middle
  | lem          : allowed.lem = true →
                   Derivable F allowed Premises (A ∨ᶠ ¬ᶠA)

  -- Markov's principle M^ω (QF ∨-free)
  | markov       : allowed.markov = true →
                   {A₀ : Formula F (ρ :: Γ)} → A₀.isQF = true → Formula.isVFree A₀ = true →
                   Derivable F allowed Premises (¬ᶠ(¬ᶠ(Formula.ex ρ A₀)) →ᶠ Formula.ex ρ A₀)

  -- Independence of premise IP^ω_∀ (QF ∨-free premise)
  | ip           : allowed.ip = true →
                   {A₀ : Formula F (σ :: Γ)} → A₀.isQF = true → Formula.isVFree A₀ = true →
                   Derivable F allowed Premises
                     ((Formula.all σ A₀ →ᶠ Formula.ex ρ B) →ᶠ
                      Formula.ex ρ ((Formula.all σ A₀).weakenBy ρ →ᶠ B))

  -- Axiom of choice AC (full, for arbitrary A)
  | ac           : allowed.ac = true →
                   {A : Formula F (τ :: ρ :: Γ)} →
                   Derivable F allowed Premises
                     ((Formula.all ρ (Formula.ex τ A)) →ᶠ
                      Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A)))

  -- QF-Axiom of choice (matrix must be QF ∨-free; ∨-freeness is ours, for the NT proof)
  | qfac         : allowed.qfac = true →
                   {A₀ : Formula F (τ :: ρ :: Γ)} → A₀.isQF = true →
                   Formula.isVFree A₀ = true →
                   Derivable F allowed Premises
                     ((Formula.all ρ (Formula.ex τ A₀)) →ᶠ
                      Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀)))

/-- If `a₁ ≤ a₂`, then any derivation in system `a₁` is also a derivation in `a₂`. -/
def Derivable.castAllowed {ι κ : Type} {F : κ → Ty ι}
    {a₁ a₂ : Allowed} (h_le : Allowed.le a₁ a₂)
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F a₁ Premises A) : Derivable F a₂ Premises A :=
  match h with
  | .premise hp => .premise hp
  | .or_contract  => .or_contract
  | .and_contract => .and_contract
  | .or_weak      => .or_weak
  | .and_weak     => .and_weak
  | .or_perm      => .or_perm
  | .and_perm     => .and_perm
  | .exfalso      => .exfalso
  | .forall_ax t  => .forall_ax t
  | .exist_ax t A => .exist_ax t A
  | .mp h1 h2     => .mp (h1.castAllowed h_le) (h2.castAllowed h_le)
  | .syllogism h1 h2 => .syllogism (h1.castAllowed h_le) (h2.castAllowed h_le)
  | .exportation h1   => .exportation (h1.castAllowed h_le)
  | .importation h1   => .importation (h1.castAllowed h_le)
  | .expansion h1     => .expansion (h1.castAllowed h_le)
  | .forall_rule h1   => .forall_rule (h1.castAllowed h_le)
  | .exist_rule h1    => .exist_rule (h1.castAllowed h_le)
  | .univ_gen h1      => .univ_gen (h1.castAllowed h_le)
  | .succ_ne_zero     => .succ_ne_zero
  | .succ_inj         => .succ_inj
  | .beta_eq b u      => .beta_eq b u
  | .pair_fst a b     => .pair_fst a b
  | .pair_snd a b     => .pair_snd a b
  | .pair_eta p       => .pair_eta p
  | .rec_zero         => .rec_zero
  | .rec_succ         => .rec_succ
  | .dist_self i x    => .dist_self i x
  | .dist_comm i x y  => .dist_comm i x y
  | .dist_tri i x y z => .dist_tri i x y z
  | .refl0            => .refl0
  | .sym0             => .sym0
  | .trans0           => .trans0
  | .qfer hqf hvf h1  => .qfer hqf hvf (h1.castAllowed h_le)
  | .induction h1 h2  => .induction (h1.castAllowed h_le) (h2.castAllowed h_le)
  | .lem h1           => .lem (h_le.1 h1)
  | .markov h1 hqf hvf => .markov (h_le.2.1 h1) hqf hvf
  | .ip h1 hqf hvf     => .ip (h_le.2.2.1 h1) hqf hvf
  | .ac h1             => .ac (h_le.2.2.2.1 h1)
  | .qfac h1 hqf hvf   => .qfac (h_le.2.2.2.2 h1) hqf hvf

end Metatheorems
