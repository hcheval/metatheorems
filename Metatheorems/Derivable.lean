/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Language


namespace Metatheorems

/-!
# Proof System for WE-HA^{ω,X}

Following Appendix 9 of the reference document, we define the Hilbert-style
proof system for WE-HA^{ω,X}_{=_X}.

The system is parametric in:
- `F : ι → Ty ι` — the abstract space function constants
- `EqX : (i : ι) → {Γ} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ`
  — the equality predicate at each base type X_i
- `allowed : Allowed` — which extension principles (LEM, AC, Markov, IP) are available

`EqX` is a purely syntactic parameter: no axioms about it appear here.
Concrete theories (e.g. metric spaces) extend this system by adding purely
universal axioms for their chosen `EqX`, which are trivially Dialectica-realized.
-/

open Formula

-- ============================================================================
-- Helper: weakening with explicit type annotation
-- ============================================================================

/-- Weaken a formula into context extended by ρ. Same as `Formula.weaken` but
    with the new type ρ given explicitly for unification. -/
def Formula.weakenBy {ι : Type} {F : ι → Ty ι} {Γ : Ctx ι}
    (ρ : Ty ι) (A : Formula F Γ) : Formula F (ρ :: Γ) :=
  A.weaken

-- ============================================================================
-- Allowed principles
-- ============================================================================

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

end Allowed

-- ============================================================================
-- The proof system
-- ============================================================================

/-- Derivability in WE-HA^{ω,X}_{=_X} + allowed extensions.

Parametric in `F` (function constants), `EqX` (base-type equality predicates),
and `allowed` (which extension principles are available).

When `allowed = Allowed.base`, this is pure WE-HA^{ω,X}.
When `allowed = Allowed.extended`, this adds AC + IP + Markov.
When `allowed = Allowed.classical`, this adds LEM + AC. -/
abbrev PremiseSet {ι : Type} (F : ι → Ty ι) := (Σ Γ : Ctx ι, Formula F Γ) → Prop

inductive Derivable {ι : Type} (F : ι → Ty ι)
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ)
    (allowed : Allowed)
    (Premises : PremiseSet F) :
    {Γ : Ctx ι} → Formula F Γ → Type where
  -- Premises (theory axioms)
  | premise       : A.isPurelyUniversal = true ∧ Premises ⟨_, A⟩ → Derivable F EqX allowed Premises A
  -- Propositional axioms (§9.1)
  | or_contract  : Derivable F EqX allowed Premises (A ∨ᶠ A →ᶠ A)
  | and_contract : Derivable F EqX allowed Premises (A →ᶠ A ∧ᶠ A)
  | or_weak      : Derivable F EqX allowed Premises (A →ᶠ A ∨ᶠ B)
  | and_weak     : Derivable F EqX allowed Premises (A ∧ᶠ B →ᶠ A)
  | or_perm      : Derivable F EqX allowed Premises (A ∨ᶠ B →ᶠ B ∨ᶠ A)
  | and_perm     : Derivable F EqX allowed Premises (A ∧ᶠ B →ᶠ B ∧ᶠ A)
  | exfalso      : Derivable F EqX allowed Premises (⊥ᶠ →ᶠ A)
  | forall_ax    : (t : Term F Γ ρ) → Derivable F EqX allowed Premises (Formula.all ρ A →ᶠ A.subst0 t)
  | exist_ax     : (t : Term F Γ ρ) → (A : Formula F (ρ :: Γ)) →
                   Derivable F EqX allowed Premises (A.subst0 t →ᶠ Formula.ex ρ A)

  -- Rules (§9.2)
  | mp           : Derivable F EqX allowed Premises A → Derivable F EqX allowed Premises (A →ᶠ B) →
                   Derivable F EqX allowed Premises B
  | syllogism    : Derivable F EqX allowed Premises (A →ᶠ B) → Derivable F EqX allowed Premises (B →ᶠ C) →
                   Derivable F EqX allowed Premises (A →ᶠ C)
  | exportation  : Derivable F EqX allowed Premises (A ∧ᶠ B →ᶠ C) →
                   Derivable F EqX allowed Premises (A →ᶠ B →ᶠ C)
  | importation  : Derivable F EqX allowed Premises (A →ᶠ B →ᶠ C) →
                   Derivable F EqX allowed Premises (A ∧ᶠ B →ᶠ C)
  | expansion    : Derivable F EqX allowed Premises (A →ᶠ B) →
                   Derivable F EqX allowed Premises (C ∨ᶠ A →ᶠ C ∨ᶠ B)
  | forall_rule  : Derivable F EqX allowed Premises (Formula.weakenBy ρ B →ᶠ A) →
                   Derivable F EqX allowed Premises (B →ᶠ Formula.all ρ A)
  | exist_rule   : {B : Formula F Γ} → {A : Formula F (ρ :: Γ)} →
                   Derivable F EqX allowed Premises (A →ᶠ Formula.weakenBy ρ B) →
                   Derivable F EqX allowed Premises (Formula.ex ρ A →ᶠ B)

  -- Universal generalization (9.42)
  | univ_gen     : Derivable F EqX allowed Premises A →
                   Derivable F EqX allowed Premises (Formula.all ρ (Formula.weakenBy ρ A))

  -- Successor (§9.5)
  | succ_ne_zero : Derivable F EqX allowed Premises
      (Formula.all Ty.nat
        (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ))
  | succ_inj     : Derivable F EqX allowed Premises
      (Formula.all Ty.nat (Formula.all Ty.nat
        (Formula.eq0
          (Term.app Term.succ (.var (.vs .vz)))
          (Term.app Term.succ (.var .vz))
        →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))))

  -- Combinators (§9.6)
  | proj_ax      : Derivable F EqX allowed Premises
      (eqAtType EqX ρ (Term.app2 (Term.proj ρ τ) s t) s)
  | comb_ax      : Derivable F EqX allowed Premises
      (eqAtType EqX τ
        (Term.app3 (Term.comb δ ρ τ) f g x)
        (Term.app (Term.app f x) (Term.app g x)))

  -- Recursor (§9.6, eq. 9.54)
  | rec_zero     : Derivable F EqX allowed Premises
      (eqAtType EqX ρ (Term.app3 (Term.prec ρ) y z Term.zero) y)
  | rec_succ     : Derivable F EqX allowed Premises
      (eqAtType EqX ρ
        (Term.app3 (Term.prec ρ) y z (Term.app Term.succ x))
        (Term.app2 z (Term.app3 (Term.prec ρ) y z x) x))

  -- Equality (§9.7)
  | refl0        : Derivable F EqX allowed Premises (Formula.eq0 t t)
  | sym0         : Derivable F EqX allowed Premises (Formula.eq0 s t →ᶠ Formula.eq0 t s)
  | trans0       : Derivable F EqX allowed Premises
      (Formula.eq0 s t ∧ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u)

  -- QF-ER (§9.7, eq. 9.58)
  -- NOTE: The document's QF-ER only requires QF, not ∨-free. We add isVFree here
  -- because our Dialectica proof (dialectica_qfer) needs Subsingleton on the counter
  -- type, which requires ∨-free. To remove hvf, the Dialectica proof would need to
  -- first encode A₀ as `qf_term A₀ =₀ 0` (which IS ∨-free) via qf_term_correct.
  | qfer         : {A₀ : Formula F Γ} →
                   A₀.isQF = true → A₀.isVFree = true →
                   Derivable F EqX allowed Premises (A₀ →ᶠ eqAtType EqX ρ s t) →
                   Derivable F EqX allowed Premises (A₀ →ᶠ eqAtType EqX σ (Term.subst0 r s) (Term.subst0 r t))

  -- Induction (§9.8)
  | induction    : Derivable F EqX allowed Premises (A.subst0 Term.zero) →
                   Derivable F EqX allowed Premises (Formula.all Ty.nat
                     (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))) →
                   Derivable F EqX allowed Premises (Formula.all Ty.nat A)

  -- ══════════════════════════════════════════════════════════════════════════
  -- Extension principles (guarded by `allowed` fields)
  -- ══════════════════════════════════════════════════════════════════════════

  -- Law of excluded middle
  | lem          : allowed.lem = true →
                   Derivable F EqX allowed Premises (A ∨ᶠ ¬ᶠA)

  -- Markov's principle M^ω (QF ∨-free)
  | markov       : allowed.markov = true →
                   {A₀ : Formula F (ρ :: Γ)} → A₀.isQF = true → Formula.isVFree A₀ = true →
                   Derivable F EqX allowed Premises (¬ᶠ(¬ᶠ(Formula.ex ρ A₀)) →ᶠ Formula.ex ρ A₀)

  -- Independence of premise IP^ω_∀ (QF ∨-free premise)
  | ip           : allowed.ip = true →
                   {A₀ : Formula F (σ :: Γ)} → A₀.isQF = true → Formula.isVFree A₀ = true →
                   Derivable F EqX allowed Premises
                     ((Formula.all σ A₀ →ᶠ Formula.ex ρ B) →ᶠ
                      Formula.ex ρ ((Formula.all σ A₀).weakenBy ρ →ᶠ B))

  -- Axiom of choice AC (full, for arbitrary A)
  | ac           : allowed.ac = true →
                   {A : Formula F (τ :: ρ :: Γ)} →
                   Derivable F EqX allowed Premises
                     ((Formula.all ρ (Formula.ex τ A)) →ᶠ
                      Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A)))

  -- QF-Axiom of choice (matrix must be QF ∨-free)
  -- NOTE: The document's QF-AC only requires QF. We add isVFree because the NT
  -- proof uses Markov (which requires ∨-free). To remove hvf, one would derive
  -- a general Markov for QF via the decision function (qf_term_correct).
  | qfac         : allowed.qfac = true →
                   {A₀ : Formula F (τ :: ρ :: Γ)} → A₀.isQF = true →
                   Formula.isVFree A₀ = true →
                   Derivable F EqX allowed Premises
                     ((Formula.all ρ (Formula.ex τ A₀)) →ᶠ
                      Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀)))

-- ============================================================================
-- Weakening of allowed principles
-- ============================================================================

/-- If `a₁ ≤ a₂`, then any derivation in system `a₁` is also a derivation in `a₂`.
    Proved by structural recursion on the derivation. -/
def Derivable.castAllowed {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a₁ a₂ : Allowed} (h_le : Allowed.le a₁ a₂)
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : Derivable F EqX a₁ Premises A) : Derivable F EqX a₂ Premises A :=
  match h with
  | .premise ⟨hpu, hp⟩ => .premise ⟨hpu, hp⟩
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
  | .proj_ax          => .proj_ax
  | .comb_ax          => .comb_ax
  | .rec_zero         => .rec_zero
  | .rec_succ         => .rec_succ
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

-- ============================================================================
-- Admissibility conditions on EqX
-- ============================================================================

/-- Proof-system conditions on the base-type equality predicate EqX.
    These are needed for higher-type equality (eqAtType) to be reflexive,
    symmetric, transitive, and natural w.r.t. substitution.

    Fields are polymorphic in `allowed` because the proofs use only base
    constructors, which are available in every system.

    For `ι = Empty` (pure WE-HA^ω), this is trivially satisfiable.
    For concrete metric-space EqX (e.g. `d(x,y) =_ℝ 0`), all conditions hold. -/
structure AdmissibleEqX {ι : Type} {F : ι → Ty ι}
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) →
           Term F Γ (Ty.base i) → Formula F Γ) where
  /-- EqX commutes with substitution (naturality). -/
  substF_nat : ∀ {Γ Δ : Ctx ι} {i : ι} (u v : Term F Γ (Ty.base i))
      (σ : Term.Subst F Γ Δ),
      (EqX i u v).substF σ = EqX i (u.subst σ) (v.subst σ)
  /-- Reflexivity: ⊢ EqX i t t. -/
  eqx_refl : ∀ {a : Allowed} {Premises : PremiseSet F}
      {Γ : Ctx ι} {i : ι} (t : Term F Γ (Ty.base i)),
      Derivable F EqX a Premises (EqX i t t)
  /-- Symmetry: ⊢ EqX i s t → EqX i t s. -/
  eqx_sym : ∀ {a : Allowed} {Premises : PremiseSet F}
      {Γ : Ctx ι} {i : ι} {s t : Term F Γ (Ty.base i)},
      Derivable F EqX a Premises (EqX i s t →ᶠ EqX i t s)
  /-- Transitivity: ⊢ EqX i s t ∧ EqX i t u → EqX i s u. -/
  eqx_trans : ∀ {a : Allowed} {Premises : PremiseSet F}
      {Γ : Ctx ι} {i : ι} {s t u : Term F Γ (Ty.base i)},
      Derivable F EqX a Premises (EqX i s t ∧ᶠ EqX i t u →ᶠ EqX i s u)
  /-- EqX at base types is purely universal (∀-nesting around QF core).
      Ensures eqAtType is provably equivalent to its kurodaInner image,
      needed by the negative translation (lem:negative-forall-equiv). -/
  eqx_pu : ∀ (i : ι) {Γ : Ctx ι} (s t : Term F Γ (Ty.base i)),
      (EqX i s t).isPurelyUniversal = true

end Metatheorems
