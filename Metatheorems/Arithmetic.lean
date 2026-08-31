/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Derivable
import Metatheorems.PropositionalLemmas
import Metatheorems.PureFOLLemmas
import Metatheorems.SimpSets


namespace Metatheorems

/-!
# Arithmetic in WE-HA^{ω,X}

Following arithmetic.tex, lambda.tex, and wehax.tex (§2.3) of the reference document.

## Main contents

**Term definitions** (arithmetic.tex §Def 2.3.?):
- `Term.sg_bar` — sḡ(0) = 1, sḡ(Sn) = 0  (co-sign function)
- `Term.pd`     — pd(0) = 0, pd(Sn) = n    (predecessor)
- `Term.add`    — x + 0 = x, x + Sn = S(x + n)
- `Term.mul`    — x · 0 = 0, x · Sn = (x · n) + x
- `Term.monus`  — x ∸ 0 = x, x ∸ Sn = pd(x ∸ n)
- `Term.abs_diff` — |x − y| = (x ∸ y) + (y ∸ x)

**Lambda correctness** (lambda.tex Prop 2.3.?):
- `Term.lam_correct` — (λx.t) s =_τ t[s/x]

**Arithmetic correctness**:
- Unfolding lemmas for each arithmetic operation

**QF formula encoding** (wehax.tex Prop prop:qf-equiv-term):
- `qf_term`         — decision term for a QF formula
- `qf_term_correct` — ⊢ ∀x̄. (qf_term A₀ x̄ =₀ 0 ↔ A₀(x̄))

**Decidability of QF formulas** (wehax.tex Prop prop:qf-lem, Cor cor:qf-double-neg-elim):
- `qf_lem`              — ⊢ A₀ ∨ ¬A₀ for QF A₀
- `qf_double_neg_elim`  — ⊢ ¬¬A₀ → A₀ for QF A₀
-/

open Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {al : Allowed} {Premises : PremiseSet F} (adm : AdmissibleEqX EqX)

-- Private combinators used throughout (same as NegTrans.lean private defs)
private def self_imp_h {Γ : Ctx ι} {A : Formula F Γ} :
    Derivable F EqX al Premises (A →ᶠ A) :=
  .syllogism .and_contract .and_weak

def weaken_intro_h {Γ : Ctx ι} {A B : Formula F Γ}
    (h : Derivable F EqX al Premises A) : Derivable F EqX al Premises (B →ᶠ A) :=
  .mp h (.exportation .and_weak)

/-- (∀x:ρ. P).weakenBy ρ →ᶠ P  in context ρ :: Γ. -/
def forall_ax_inst {Γ : Ctx ι} {ρ : Ty ι} (P : Formula F (ρ :: Γ)) :
    Derivable F EqX al Premises ((Formula.all ρ P).weakenBy ρ →ᶠ P) :=
  let hbody : ∀ {τ : Ty ι} (v : Var (ρ :: Γ) τ),
      Term.subst0_map (.var .vz) (Renaming.ext Renaming.shift v) = Term.var v :=
    fun {_} v => match v with
    | .vz   => rfl
    | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]
  let heq : (Formula.renameF (Renaming.ext Renaming.shift) P).subst0 (.var .vz) = P :=
    Formula.substF_renameF_id (Renaming.ext Renaming.shift)
      (Term.subst0_map (.var .vz)) hbody P
  have h := @Derivable.forall_ax ι F EqX al Premises (ρ :: Γ) ρ
              (Formula.renameF (Renaming.ext Renaming.shift) P) (.var .vz)
  -- h : ⊢ all ρ (renameF (ext shift) P) →ᶠ X  where X = (renameF (ext shift) P).subst0 (var vz)
  -- heq : X = P.  Use Eq.mp to convert only the consequent X → P.
  -- Antecedent (all ρ P).weakenBy ρ = all ρ (renameF (ext shift) P) definitionally.
  let ant := Formula.all ρ (Formula.renameF (Renaming.ext Renaming.shift) P)
  Eq.mp (congrArg (fun Y => Derivable F EqX al Premises (ant →ᶠ Y)) heq) h

-- ============================================================================
-- Section 1: Arithmetic Term Definitions
-- ============================================================================
-- All terms are polymorphic in the ambient context Γ, since they use only
-- closed constants (prec, succ, zero) and lam which exist in any context.

namespace Term

/-- Co-sign: sḡ(0) = 1, sḡ(Sn) = 0.
    sḡ = λx. R (S0) (λr k. 0) x
    Used to encode implication in the QF decision function. -/
def sg_bar {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      (.app .succ .zero)                      -- y = S0 = 1
      (Term.lam (Term.lam .zero))             -- z = λr k. 0
      (.var .vz))                             -- x

/-- Predecessor: pd(0) = 0, pd(Sn) = n.
    pd = λx. R 0 (λr k. k) x
    The step z(r, k) = k returns the current counter, not the recursive result. -/
def pd {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                   -- y = 0
      (Term.lam (Term.lam (.var .vz)))        -- z = λr k. k  (k = var vz, r = var (vs vz))
      (.var .vz))                             -- x

/-- Addition: x + 0 = x, x + Sn = S(x + n).
    add = λx. λn. R x (λr k. Sr) n -/
def add {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      (.var (.vs .vz))                        -- y = x  (position 1 in [n, x])
      (Term.lam (Term.lam                     -- z = λr k. Sr  (r = vs vz, k = vz)
        (.app .succ (.var (.vs .vz)))))
      (.var .vz)))                            -- n  (position 0 in [n, x])

/-- Multiplication: x · 0 = 0, x · Sn = (x · n) + x.
    mul = λx. λn. R 0 (λr k. add r x) n -/
def mul {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                   -- y = 0
      (Term.lam (Term.lam                     -- z = λr k. add r x
        (Term.app2 Term.add
          (.var (.vs .vz))                    --   r  (position 1 in [k, r, n, x])
          (.var (.vs (.vs (.vs .vz)))))))     --   x  (position 3 in [k, r, n, x])
      (.var .vz)))                            -- n  (position 0 in [n, x])

/-- Truncated subtraction (monus): x ∸ 0 = x, x ∸ Sn = pd(x ∸ n).
    monus = λx. λn. R x (λr k. pd r) n -/
def monus {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      (.var (.vs .vz))                        -- y = x  (position 1 in [n, x])
      (Term.lam (Term.lam                     -- z = λr k. pd r
        (.app Term.pd (.var (.vs .vz)))))     --   pd r  (r = var (vs vz) in [k, r, n, x])
      (.var .vz)))                            -- n

/-- Absolute difference: |x − y| = (x ∸ y) + (y ∸ x).
    abs_diff = λx. λy. add (monus x y) (monus y x) -/
def abs_diff {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.add
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))  -- monus x y  (x = vs vz, y = vz)
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))))) -- monus y x

end Term

-- ============================================================================
-- Section 2: Higher-type equality
-- ============================================================================
-- Reflexivity, symmetry, transitivity of eqAtType at all types.
-- These are needed for lambda correctness (Section 3) and arithmetic proofs.

section EqAtType

variable {Γ : Ctx ι}

/-- Reflexivity of higher-type equality (derived from refl0 + forall_rule).
    eqAtType ρ s s -/
def eqAtType_refl {Γ : Ctx ι} {ρ : Ty ι} (s : Term F Γ ρ) :
    Derivable F EqX al Premises (eqAtType EqX ρ s s) :=
  match ρ with
  | .nat    => .refl0
  | .base _ => adm.eqx_refl s
  | .arr ρ' σ' =>
    -- eqAtType (ρ'→σ') s s = ∀x:ρ'. eqAtType σ' (s.weaken x) (s.weaken x)
    -- IH in context ρ'::Γ; then weaken_intro + forall_rule + mp to close ∀
    let ih : Derivable F EqX al Premises (eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app s.weaken (.var .vz))) :=
      eqAtType_refl (Term.app s.weaken (.var .vz))
    -- weaken_intro: ⊢ B →ᶠ P where B = ⊥ᶠ →ᶠ ⊥ᶠ (= (⊥ᶠ →ᶠ ⊥ᶠ).weakenBy ρ' definitionally)
    let step1 : Derivable F EqX al Premises ((⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app s.weaken (.var .vz))) :=
      weaken_intro_h ih
    -- forall_rule: B = ⊥ᶠ →ᶠ ⊥ᶠ in Γ; (⊥ᶠ→ᶠ⊥ᶠ).weakenBy ρ' = ⊥ᶠ→ᶠ⊥ᶠ definitionally
    let step2 : Derivable F EqX al Premises ((⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ Formula.all ρ' (eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app s.weaken (.var .vz)))) :=
      .forall_rule step1
    -- self_imp at ⊥ᶠ gives ⊢ ⊥ᶠ →ᶠ ⊥ᶠ; then mp closes the goal
    let taut : Derivable F EqX al Premises (⊥ᶠ →ᶠ ⊥ᶠ) := self_imp_h
    .mp taut step2

/-- Symmetry of higher-type equality (from sym0 + forall_rule). -/
def eqAtType_sym {Γ : Ctx ι} {ρ : Ty ι} {s t : Term F Γ ρ} :
    Derivable F EqX al Premises (eqAtType EqX ρ s t →ᶠ eqAtType EqX ρ t s) :=
  match ρ with
  | .nat    => .sym0
  | .base _ => adm.eqx_sym
  | .arr ρ' σ' =>
    let P_st : Formula F (ρ' :: Γ) :=
      eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))
    let inst_st := forall_ax_inst P_st
    let ih : Derivable F EqX al Premises (P_st →ᶠ
        eqAtType EqX σ' (Term.app t.weaken (.var .vz)) (Term.app s.weaken (.var .vz))) :=
      eqAtType_sym
    .forall_rule (.syllogism inst_st ih)

/-- Transitivity of higher-type equality (from trans0 + forall_rule). -/
def eqAtType_trans {Γ : Ctx ι} {ρ : Ty ι} {s t u : Term F Γ ρ} :
    Derivable F EqX al Premises (eqAtType EqX ρ s t ∧ᶠ eqAtType EqX ρ t u →ᶠ eqAtType EqX ρ s u) :=
  match ρ with
  | .nat    => .trans0
  | .base _ => adm.eqx_trans
  | .arr ρ' σ' =>
    let P_st : Formula F (ρ' :: Γ) :=
      eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))
    let P_tu : Formula F (ρ' :: Γ) :=
      eqAtType EqX σ' (Term.app t.weaken (.var .vz)) (Term.app u.weaken (.var .vz))
    let inst_st := forall_ax_inst P_st
    let inst_tu := forall_ax_inst P_tu
    let ih : Derivable F EqX al Premises (P_st ∧ᶠ P_tu →ᶠ
        eqAtType EqX σ' (Term.app s.weaken (.var .vz)) (Term.app u.weaken (.var .vz))) :=
      eqAtType_trans
    let get_P_st : Derivable F EqX al Premises
        ((Formula.all ρ' P_st ∧ᶠ Formula.all ρ' P_tu).weakenBy ρ' →ᶠ P_st) :=
      .syllogism .and_weak inst_st
    let get_P_tu : Derivable F EqX al Premises
        ((Formula.all ρ' P_st ∧ᶠ Formula.all ρ' P_tu).weakenBy ρ' →ᶠ P_tu) :=
      .syllogism (.syllogism .and_perm .and_weak) inst_tu
    let get_pair : Derivable F EqX al Premises
        ((Formula.all ρ' P_st ∧ᶠ Formula.all ρ' P_tu).weakenBy ρ' →ᶠ P_st ∧ᶠ P_tu) :=
      pair_h get_P_st get_P_tu
    .forall_rule (.syllogism get_pair ih)

end EqAtType

-- ============================================================================
-- Section 2b: Infrastructure for lambda correctness
-- ============================================================================
-- eqAtType commutes with substitution, and qfer without QF premise.

private theorem weaken_subst_ext_h {Γ Δ : Ctx ι} {σ_ty : Ty ι} {τ : Ty ι}
    (t : Term F Γ τ) (σ : Term.Subst F Γ Δ) :
    (t.weaken (σ := σ_ty)).subst (Term.Subst.ext σ) = (t.subst σ).weaken :=
  Term.weaken_subst_ext t σ

private theorem weaken_subst0_h (t : Term F Γ τ) (s : Term F Γ ρ) :
    t.weaken.subst0 s = t :=
  Term.weaken_subst0 t s

/-- `(app t.weaken (var vz)).subst0 u = app t u` -/
private theorem app_weaken_vz_subst0 (t : Term F Γ (ρ →ₜ σ')) (u : Term F Γ ρ) :
    (Term.app t.weaken (.var .vz)).subst0 u = Term.app t u := by
  change Term.app (t.weaken.subst0 u) u = Term.app t u
  rw [weaken_subst0_h]

/-- eqAtType commutes with general substitution (naturality).
    At base types, this requires EqX to commute with substitution (sorry). -/
private theorem eqAtType_substF (adm : AdmissibleEqX EqX) {τ : Ty ι} {Γ Δ : Ctx ι}
    (u v : Term F Γ τ) (σ : Term.Subst F Γ Δ) :
    (eqAtType EqX τ u v).substF σ = eqAtType EqX τ (u.subst σ) (v.subst σ) := by
  induction τ generalizing Γ Δ σ with
  | nat => rfl
  | base i => exact adm.substF_nat u v σ
  | arr ρ' σ' _ ih =>
    simp only [eqAtType, Formula.substF]
    congr 1; rw [ih]
    simp only [Term.subst, Term.Subst.ext, weaken_subst_ext_h]

/-- eqAtType commutes with single-variable substitution. -/
private theorem eqAtType_subst0 (adm : AdmissibleEqX EqX) {τ : Ty ι} {ρ : Ty ι} {Γ : Ctx ι}
    (u v : Term F (ρ :: Γ) τ) (s : Term F Γ ρ) :
    (eqAtType EqX τ u v).subst0 s = eqAtType EqX τ (u.subst0 s) (v.subst0 s) :=
  eqAtType_substF adm u v (Term.subst0_map s)

/-- QF-ER without QF premise (prop:qfer-no-premise from wehax.tex):
    from ⊢ s =_ρ t, derive ⊢ r[s] =_σ r[t].
    Proof: pad with A₀ = (0 =₀ 0) which is trivially QF ∧ VFree. -/
def qfer_no_premise {ρ σ : Ty ι} {Γ : Ctx ι}
    {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (h : Derivable F EqX al Premises (eqAtType EqX ρ s t)) :
    Derivable F EqX al Premises (eqAtType EqX σ (r.subst0 s) (r.subst0 t)) :=
  .mp (.refl0 (t := Term.zero)) (.qfer (by rfl) (by rfl) (weaken_intro_h h))

/-- QF-ER at nat type with explicit normal forms for the subst0 results.
    Avoids deep defeq reduction in downstream proofs. -/
def qfer_nat_nf {Γ : Ctx ι} {A₀ : Formula F Γ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (A₀ →ᶠ Formula.eq0 s t))
    {r : Term F (Ty.nat :: Γ) Ty.nat} {rs rt : Term F Γ Ty.nat}
    (hs : r.subst0 s = rs) (ht : r.subst0 t = rt) :
    Derivable F EqX al Premises (A₀ →ᶠ Formula.eq0 rs rt) :=
  let h' : Derivable F EqX al Premises (A₀ →ᶠ eqAtType EqX Ty.nat s t) := h
  let q : Derivable F EqX al Premises (A₀ →ᶠ Formula.eq0 (r.subst0 s) (r.subst0 t)) :=
    .qfer (σ := Ty.nat) hqf hvf h'
  Eq.mp (congrArg (Derivable F EqX al Premises ·) (by rw [show r.subst0 s = rs from hs,
    show r.subst0 t = rt from ht])) q

/-- QF-ER without premise, at nat type, with explicit normal forms. -/
def qfer_no_premise_nat_nf {Γ : Ctx ι}
    {s t : Term F Γ Ty.nat} (h : Derivable F EqX al Premises (Formula.eq0 s t))
    {r : Term F (Ty.nat :: Γ) Ty.nat} {rs rt : Term F Γ Ty.nat}
    (hs : r.subst0 s = rs) (ht : r.subst0 t = rt) :
    Derivable F EqX al Premises (Formula.eq0 rs rt) :=
  let h' : Derivable F EqX al Premises (eqAtType EqX Ty.nat s t) := h
  let q : Derivable F EqX al Premises (Formula.eq0 (r.subst0 s) (r.subst0 t)) :=
    qfer_no_premise (σ := Ty.nat) h'
  Eq.mp (congrArg (Derivable F EqX al Premises ·) (by rw [show r.subst0 s = rs from hs,
    show r.subst0 t = rt from ht])) q

-- ============================================================================
-- Section 3: Lambda correctness
-- ============================================================================
-- With primitive λ, beta reduction is an axiom (beta_eq constructor of Derivable).

/-- Lambda correctness: applying (lam t) to s equals t with s substituted for x.
    (λx.t)(s) =_τ t[s/x]
    Now trivially the beta_eq axiom. -/
def Term.lam_correct {ρ τ : Ty ι} {Γ : Ctx ι}
    (t : Term F (ρ :: Γ) τ) (s : Term F Γ ρ) :
    Derivable F EqX al Premises (eqAtType EqX τ (Term.app (Term.lam t) s) (t.subst0 s)) :=
  .beta_eq t s

-- ============================================================================
-- Section 3b: Universal generalization and lam2_correct
-- ============================================================================

/-- Universal generalization: from ⊢ A in context ρ :: Γ, derive ⊢ ∀x:ρ. A in context Γ. -/
def univ_gen {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Derivable F EqX al Premises A) : Derivable F EqX al Premises (Formula.all ρ A) :=
  -- Use B = ⊥→⊥ which satisfies B.weakenBy ρ = B definitionally
  let h1 : Derivable F EqX al Premises ((⊥ᶠ →ᶠ ⊥ᶠ : Formula F (ρ :: Γ)) →ᶠ A) := weaken_intro_h h
  let h2 : Derivable F EqX al Premises ((⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ) →ᶠ Formula.all ρ A) := .forall_rule h1
  .mp self_imp_h h2

/-- Lambda correctness for two-argument application:
    app2 (lam (lam body)) s₁ s₂ =_τ (body.subst0 (s₂.weaken)).subst0 s₁

    Proof: First lam_correct gives arrow equality, instantiate at s₂.
    Second level: lam_correct body (s₂.weaken) in context ρ₂ :: Γ,
    then universalize over ρ₂ and instantiate at s₁. -/
def Term.lam2_correct {ρ₂ ρ₁ τ : Ty ι} {Γ : Ctx ι}
    (adm : AdmissibleEqX EqX)
    (body : Term F (ρ₁ :: ρ₂ :: Γ) τ) (s₁ : Term F Γ ρ₂) (s₂ : Term F Γ ρ₁) :
    Derivable F EqX al Premises (eqAtType EqX τ
      (Term.app2 (Term.lam (Term.lam body)) s₁ s₂)
      ((body.subst0 (s₂.weaken)).subst0 s₁)) :=
  -- Step A: first lam_correct gives arrow equality
  let step_a := Term.lam_correct (Term.lam body) s₁
  -- step_a : eqAtType (ρ₁→τ) (app (lam (lam body)) s₁) ((lam body).subst0 s₁)
  -- Instantiate at s₂ via forall_ax + transport
  let P := eqAtType EqX τ (Term.app (Term.app (Term.lam (Term.lam body)) s₁).weaken (.var .vz))
                            (Term.app ((Term.lam body).subst0 s₁).weaken (.var .vz))
  let step_a2_raw : Derivable F EqX al Premises (P.subst0 s₂) := .mp step_a (.forall_ax s₂)
  let heq_a : P.subst0 s₂ = eqAtType EqX τ
      (Term.app (Term.app (Term.lam (Term.lam body)) s₁) s₂)
      (Term.app ((Term.lam body).subst0 s₁) s₂) := by
    rw [eqAtType_subst0 adm, app_weaken_vz_subst0, app_weaken_vz_subst0]
  let step_a2 := Eq.mp (congrArg (Derivable F EqX al Premises) heq_a) step_a2_raw
  -- Step B: second lam_correct in extended context ρ₂ :: Γ
  -- lam_correct body (s₂.weaken) in context ρ₂ :: Γ
  let step_b : Derivable F EqX al Premises
      (eqAtType EqX τ (Term.app (Term.lam body) s₂.weaken) (body.subst0 s₂.weaken)) :=
    Term.lam_correct body s₂.weaken
  -- Universalize over ρ₂ variable, then instantiate at s₁
  let step_b_all := univ_gen step_b
  -- step_b_all : ∀x:ρ₂. eqAtType τ (app (lam body) (s₂.weaken)) (body.subst0 (s₂.weaken))
  let Q := eqAtType EqX τ (Term.app (Term.lam body) s₂.weaken) (body.subst0 s₂.weaken)
  let step_b2_raw : Derivable F EqX al Premises (Q.subst0 s₁) := .mp step_b_all (.forall_ax s₁)
  -- Transport Q.subst0 s₁:
  -- Q.subst0 s₁ = eqAtType τ (app ((lam body).subst0 s₁) (s₂.weaken.subst0 s₁))
  --                            ((body.subst0 s₂.weaken).subst0 s₁)
  --             = eqAtType τ (app ((lam body).subst0 s₁) s₂) ((body.subst0 s₂.weaken).subst0 s₁)
  let heq_b : Q.subst0 s₁ = eqAtType EqX τ
      (Term.app ((Term.lam body).subst0 s₁) s₂)
      ((body.subst0 s₂.weaken).subst0 s₁) := by
    rw [eqAtType_subst0 adm]
    congr 1
    · -- app (lam body) (s₂.weaken) with var vz → s₁
      show Term.app ((Term.lam body).subst0 s₁) (s₂.weaken.subst0 s₁) =
           Term.app ((Term.lam body).subst0 s₁) s₂
      rw [weaken_subst0_h]
  let step_b2 := Eq.mp (congrArg (Derivable F EqX al Premises) heq_b) step_b2_raw
  -- Chain step_a2 and step_b2 via eqAtType_trans
  .mp (.mp step_b2 (.mp step_a2 and_intro)) (eqAtType_trans adm)

/-- lam2_correct with explicit normal form: gives
    app2 (lam (lam body)) s₁ s₂ =_τ target
    when `(body.subst0 (s₂.weaken)).subst0 s₁ = target`. -/
def lam2_correct_nf (adm : AdmissibleEqX EqX) {ρ₂ ρ₁ τ : Ty ι} {Γ : Ctx ι}
    (body : Term F (ρ₁ :: ρ₂ :: Γ) τ) (s₁ : Term F Γ ρ₂) (s₂ : Term F Γ ρ₁)
    {target : Term F Γ τ} (hnf : (body.subst0 (s₂.weaken)).subst0 s₁ = target) :
    Derivable F EqX al Premises (eqAtType EqX τ (Term.app2 (Term.lam (Term.lam body)) s₁ s₂) target) :=
  Eq.mp (congrArg (Derivable F EqX al Premises ·)
    (congrArg (eqAtType EqX τ (Term.app2 (Term.lam (Term.lam body)) s₁ s₂)) hnf))
    (Term.lam2_correct adm body s₁ s₂)

/-- Beta-reduction for 3-argument lambda application.
    `(lam (lam (lam body))) s₁ s₂ s₃ =_τ NF`
    where NF = `((body.subst0 (s₃.weaken.weaken)).subst0 (s₂.weaken)).subst0 s₁`. -/
def Term.lam3_correct {ρ₃ ρ₂ ρ₁ τ : Ty ι} {Γ : Ctx ι}
    (adm : AdmissibleEqX EqX)
    (body : Term F (ρ₁ :: ρ₂ :: ρ₃ :: Γ) τ)
    (s₁ : Term F Γ ρ₃) (s₂ : Term F Γ ρ₂) (s₃ : Term F Γ ρ₁) :
    Derivable F EqX al Premises (eqAtType EqX τ
      (Term.app3 (Term.lam (Term.lam (Term.lam body))) s₁ s₂ s₃)
      (((body.subst0 (s₃.weaken.weaken)).subst0 (s₂.weaken)).subst0 s₁)) :=
  -- Step A: lam2_correct on outer two lambdas gives function-type equality
  let step_a := Term.lam2_correct adm (Term.lam body) s₁ s₂
  -- step_a : eqAtType (ρ₁ →ₜ τ) (app2 (lam₃ body) s₁ s₂) mid
  -- where mid = ((lam body).subst0 (s₂.weaken)).subst0 s₁
  -- Step B: instantiate at s₃ via forall_ax + transport
  let P := eqAtType EqX τ
    (Term.app (Term.app2 (Term.lam (Term.lam (Term.lam body))) s₁ s₂).weaken (.var .vz))
    (Term.app (((Term.lam body).subst0 (s₂.weaken)).subst0 s₁).weaken (.var .vz))
  let inst_raw : Derivable F EqX al Premises (P.subst0 s₃) := .mp step_a (.forall_ax s₃)
  let heq_inst : P.subst0 s₃ = eqAtType EqX τ
      (Term.app (Term.app2 (Term.lam (Term.lam (Term.lam body))) s₁ s₂) s₃)
      (Term.app (((Term.lam body).subst0 (s₂.weaken)).subst0 s₁) s₃) := by
    rw [eqAtType_subst0 adm, app_weaken_vz_subst0, app_weaken_vz_subst0]
  let step_b := Eq.mp (congrArg (Derivable F EqX al Premises) heq_inst) inst_raw
  -- Step C: lam_correct body (s₃.ww) in context ρ₂ :: ρ₃ :: Γ, then universalize twice
  let step_c0 : Derivable F EqX al Premises
      (eqAtType EqX τ (Term.app (Term.lam body) s₃.weaken.weaken)
        (body.subst0 s₃.weaken.weaken)) :=
    Term.lam_correct body s₃.weaken.weaken
  -- First universalize over ρ₂ (var 0), instantiate at s₂.weaken
  let step_c1 := univ_gen step_c0
  let Q1 := eqAtType EqX τ (Term.app (Term.lam body) s₃.weaken.weaken)
    (body.subst0 s₃.weaken.weaken)
  let step_c2_raw : Derivable F EqX al Premises (Q1.subst0 s₂.weaken) :=
    .mp step_c1 (.forall_ax s₂.weaken)
  let heq_c1 : Q1.subst0 s₂.weaken = eqAtType EqX τ
      (Term.app ((Term.lam body).subst0 s₂.weaken) s₃.weaken)
      ((body.subst0 s₃.weaken.weaken).subst0 s₂.weaken) := by
    rw [eqAtType_subst0 adm]
    congr 1
    · show Term.app ((Term.lam body).subst0 s₂.weaken) (s₃.weaken.weaken.subst0 s₂.weaken) =
           Term.app ((Term.lam body).subst0 s₂.weaken) s₃.weaken
      rw [weaken_subst0_h]
  let step_c2 := Eq.mp (congrArg (Derivable F EqX al Premises) heq_c1) step_c2_raw
  -- Second universalize over ρ₃ (var 0), instantiate at s₁
  let step_c3 := univ_gen step_c2
  let Q2 := eqAtType EqX τ
    (Term.app ((Term.lam body).subst0 s₂.weaken) s₃.weaken)
    ((body.subst0 s₃.weaken.weaken).subst0 s₂.weaken)
  let step_c4_raw : Derivable F EqX al Premises (Q2.subst0 s₁) :=
    .mp step_c3 (.forall_ax s₁)
  let heq_c2 : Q2.subst0 s₁ = eqAtType EqX τ
      (Term.app (((Term.lam body).subst0 s₂.weaken).subst0 s₁) s₃)
      (((body.subst0 s₃.weaken.weaken).subst0 s₂.weaken).subst0 s₁) := by
    rw [eqAtType_subst0 adm]
    congr 1
    · show Term.app (((Term.lam body).subst0 s₂.weaken).subst0 s₁) (s₃.weaken.subst0 s₁) =
           Term.app (((Term.lam body).subst0 s₂.weaken).subst0 s₁) s₃
      rw [weaken_subst0_h]
  let step_c4 := Eq.mp (congrArg (Derivable F EqX al Premises) heq_c2) step_c4_raw
  -- Chain step_b and step_c4 via eqAtType_trans
  .mp (.mp step_c4 (.mp step_b and_intro)) (eqAtType_trans adm)

/-- lam3_correct with explicit normal form. -/
def lam3_correct_nf (adm : AdmissibleEqX EqX) {ρ₃ ρ₂ ρ₁ τ : Ty ι} {Γ : Ctx ι}
    (body : Term F (ρ₁ :: ρ₂ :: ρ₃ :: Γ) τ)
    (s₁ : Term F Γ ρ₃) (s₂ : Term F Γ ρ₂) (s₃ : Term F Γ ρ₁)
    {target : Term F Γ τ}
    (hnf : ((body.subst0 (s₃.weaken.weaken)).subst0 (s₂.weaken)).subst0 s₁ = target) :
    Derivable F EqX al Premises (eqAtType EqX τ
      (Term.app3 (Term.lam (Term.lam (Term.lam body))) s₁ s₂ s₃) target) :=
  Eq.mp (congrArg (Derivable F EqX al Premises ·)
    (congrArg (eqAtType EqX τ (Term.app3 (Term.lam (Term.lam (Term.lam body))) s₁ s₂ s₃)) hnf))
    (Term.lam3_correct adm body s₁ s₂ s₃)

/-- lam_correct with explicit normal form. -/
def lam_correct_nf {ρ τ : Ty ι} {Γ : Ctx ι}
    (body : Term F (ρ :: Γ) τ) (s : Term F Γ ρ)
    {target : Term F Γ τ} (hnf : body.subst0 s = target) :
    Derivable F EqX al Premises (eqAtType EqX τ (Term.app (Term.lam body) s) target) :=
  Eq.mp (congrArg (Derivable F EqX al Premises ·)
    (congrArg (eqAtType EqX τ (Term.app (Term.lam body) s)) hnf))
    (Term.lam_correct body s)

-- ============================================================================
-- Section 4: Arithmetic term correctness
-- ============================================================================
-- Each arithmetic function unfolds correctly via rec_zero/rec_succ + lam_correct.
-- Substitution normal-form lemmas are isolated to avoid defeq abuse.

-- ── Substitution normal forms (isolating deep reductions) ─────────────────

-- Single-argument bodies: body.subst0 s = app3 (prec nat) y z s
private theorem sg_bar_body_nf (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat) (.app .succ .zero) (Term.lam (Term.lam .zero))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat) (.app .succ .zero) (Term.lam (Term.lam .zero)) s := by rfl

private theorem pd_body_nf (s : Term F Γ Ty.nat) :
    (Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.var .vz)))
      (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.var .vz))) s := by rfl

-- Two-argument bodies: (body.subst0 (s.weaken)).subst0 x = app3 (prec nat) y z s
private theorem add_body_nf (x s : Term F Γ Ty.nat) :
    ((Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app .succ (.var (.vs .vz)))))
      (.var .vz) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 (s.weaken)).subst0 x =
    Term.app3 (.prec Ty.nat) x (Term.lam (Term.lam (.app .succ (.var (.vs .vz))))) s := by
  simp [Term.subst0, Term.subst, Term.subst0_map, Term.app3]
  exact weaken_subst0_h s x

/-- `Term.pd` is closed. Public: proof scripts need it in the goal-normalising simp set. -/
theorem pd_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    Term.subst σ (Term.pd : Term F Γ _) = Term.pd := by rfl

private theorem monus_body_nf (x s : Term F Γ Ty.nat) :
    ((Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app Term.pd (.var (.vs .vz)))))
      (.var .vz) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 (s.weaken)).subst0 x =
    Term.app3 (.prec Ty.nat) x
      (Term.lam (Term.lam (.app Term.pd (.var (.vs .vz))))) s := by
  simp [Term.subst0, Term.subst, Term.subst0_map, Term.app3, pd_closed_subst]
  exact weaken_subst0_h s x

-- Step function reductions: (step.subst0 (n.weaken)).subst0 r = f(r, n)
private theorem step_succ_nf (r n : Term F Γ Ty.nat) :
    ((Term.app .succ (.var (.vs .vz)) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0
      (n.weaken)).subst0 r = Term.app .succ r := by rfl

private theorem step_id_nf (r n : Term F Γ Ty.nat) :
    ((Term.var .vz : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0
      (n.weaken)).subst0 r = n := by
  simp [Term.subst0, Term.subst, Term.subst0_map]
  exact weaken_subst0_h n r

private theorem step_pd_nf (r n : Term F Γ Ty.nat) :
    ((Term.app Term.pd (.var (.vs .vz)) : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0
      (n.weaken)).subst0 r = Term.app Term.pd r := by rfl

private theorem add_closed_subst' {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    Term.subst σ (Term.add : Term F Γ _) = Term.add := by rfl

/-- `mul` is closed under substitution (no free variables in compiled form). -/
private theorem mul_closed_subst' {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    Term.subst σ (Term.mul : Term F Γ _) = Term.mul := by rfl

/-- The compiled step function of mul: `λr.λk. add r x` where x is at position 1. -/
private def mul_step_lam {Γ : Ctx ι} : Term F (Ty.nat :: Ty.nat :: Γ) (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz)) (.var (.vs (.vs (.vs .vz))))))

/-- The step function of mul doesn't reference var vz (position 0 = n). -/
private theorem mul_step_subst0_irrel {Γ : Ctx ι}
    (s t : Term F (Ty.nat :: Γ) Ty.nat) :
    (mul_step_lam (Γ := Γ)).subst0 s = (mul_step_lam (Γ := Γ)).subst0 t := by
  rfl

/-- mul body with VARIABLE substitutions: round-trips step_lam back to itself. -/
private theorem mul_body_var_nf {Γ : Ctx ι}
    (s : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat) :
    ((Term.app3 (.prec Ty.nat) .zero (mul_step_lam (Γ := Ty.nat :: Ty.nat :: Γ)) (.var .vz)
      : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0
      s.weaken).subst0 (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _) =
    Term.app3 (.prec Ty.nat) Term.zero (mul_step_lam (Γ := Γ)) s := by
  simp only [Term.subst0, Term.subst, Term.subst0_map, Term.app3, Term.app2,
    mul_step_lam, add_closed_subst', Term.Subst.ext, Term.weaken, Term.rename,
    Term.Renaming.ext, Term.Renaming.shift]
  exact congrArg _ (weaken_subst0_h s (.var (.vs .vz)))

/-- mul step: (add (var (vs vz)) x.weaken.weaken).subst0 k.weaken).subst0 r = add r x -/
private theorem mul_step_nf (x r k : Term F Γ Ty.nat) :
    ((Term.app2 Term.add (.var (.vs .vz)) x.weaken.weaken
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 k.weaken).subst0 r =
    Term.app2 Term.add r x := by
  -- Reduce inner subst0 first, then outer
  have h_inner : (Term.app2 Term.add (.var (.vs .vz)) x.weaken.weaken
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 k.weaken =
      Term.app2 Term.add (.var .vz) x.weaken := by
    simp only [Term.app2, Term.subst0, Term.subst, add_closed_subst', Term.subst0_map]
    exact congrArg _ (weaken_subst0_h x.weaken k.weaken)
  rw [h_inner]
  simp only [Term.app2, Term.subst0, Term.subst, add_closed_subst', Term.subst0_map]
  exact congrArg _ (weaken_subst0_h x r)

section ArithCorr

variable {Γ : Ctx ι}

-- ── sg_bar ──────────────────────────────────────────────────────────────────

/-- sḡ(0) = 1  (= S0). -/
def sg_bar_zero {Γ : Ctx ι} :
    Derivable F EqX al Premises (Formula.eq0 (Term.app (Term.sg_bar (Γ := Γ)) Term.zero) (.app .succ .zero)) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.app .succ .zero) (Term.lam (Term.lam .zero)) (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- sḡ(Sn) = 0. -/
def sg_bar_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app Term.sg_bar (Term.app Term.succ n)) Term.zero) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.app .succ .zero) (Term.lam (Term.lam .zero)) (.var .vz)
  let z := Term.lam (Term.lam (.zero : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat))
  let h1 := lam_correct_nf body (.app .succ n) (sg_bar_body_nf _)
  let h2 := lam2_correct_nf adm (.zero : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat)
    (Term.app3 (.prec Ty.nat) (.app .succ .zero) z n) n (by rfl)
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)

-- ── pd ──────────────────────────────────────────────────────────────────────

/-- pd(0) = 0. -/
def pd_zero {Γ : Ctx ι} :
    Derivable F EqX al Premises (Formula.eq0 (Term.app (Term.pd (Γ := Γ)) Term.zero) Term.zero) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.var .vz))) (.var .vz)
  let h1 := Term.lam_correct body Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- pd(Sn) = n. -/
def pd_succ (n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app Term.pd (Term.app Term.succ n)) n) :=
  let body : Term F (Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero (Term.lam (Term.lam (.var .vz))) (.var .vz)
  let step : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .var .vz
  let z := Term.lam (Term.lam step)
  let h1 := lam_correct_nf body (.app .succ n) (pd_body_nf _)
  let h2 := lam2_correct_nf adm step
    (Term.app3 (.prec Ty.nat) .zero z n) n (step_id_nf _ _)
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)

-- ── add ─────────────────────────────────────────────────────────────────────

/-- x + 0 = x. -/
def add_zero_r (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add x Term.zero) x) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app .succ (.var (.vs .vz))))) (.var .vz)
  let h1 := Term.lam2_correct adm body x Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- x + Sn = S(x + n). -/
def add_succ (x n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add x (Term.app Term.succ n))
      (Term.app Term.succ (Term.app2 Term.add x n))) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app .succ (.var (.vs .vz))))) (.var .vz)
  let step : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .app .succ (.var (.vs .vz))
  let z := Term.lam (Term.lam step)
  let h1 := lam2_correct_nf adm body x (.app .succ n) (add_body_nf x _)
  let h2 := lam2_correct_nf adm step (Term.app3 (.prec Ty.nat) x z n) n
    (step_succ_nf _ _)
  let h3 := lam2_correct_nf adm body x n (add_body_nf x _)
  let h4 := @qfer_no_premise _ _ EqX al Premises _ _ _ _ _
    (.app .succ (.var .vz)) (Derivable.mp h3 (eqAtType_sym adm))
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h4 (.mp c2 and_intro)) (eqAtType_trans adm)

-- ── mul ─────────────────────────────────────────────────────────────────────

private theorem mul_add_subst0_l_nf (x t : Term F Γ Ty.nat) :
    (Term.app2 Term.add (.var .vz) x.weaken : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.add t x := by
  simp only [Term.subst0, Term.app2, Term.subst, add_closed_subst', Term.subst0_map]
  exact congrArg _ (weaken_subst0_h x t)

/-- x · 0 = 0. -/
def mul_zero (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul x Term.zero) Term.zero) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero
      (Term.lam (Term.lam (Term.app2 Term.add (.var (.vs .vz))
        (.var (.vs (.vs (.vs .vz))))))) (.var .vz)
  let h1 := Term.lam2_correct adm body x Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- mul_succ in variable context nat :: nat :: Γ (x = var (vs vz), n = var vz).
    Here step_lam round-trips under substitution because all subst0s are variable-based. -/
private def mul_succ_var {Γ : Ctx ι} :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _)
        (Term.app Term.succ (.var .vz)))
      (Term.app2 Term.add
        (Term.app2 Term.mul (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _) (.var .vz))
        (.var (.vs .vz)))) :=
  -- Body of mul (inside the two outer lams), in extended context
  let body : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) .zero (mul_step_lam (Γ := Ty.nat :: Ty.nat :: Γ)) (.var .vz)
  -- Raw step body (before step's lam lam compilation)
  let raw_step : Term F (Ty.nat :: Ty.nat :: Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add (.var (.vs .vz))
      (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _).weaken.weaken
  -- Compiled step = lam (lam raw_step) = mul_step_lam
  let z := mul_step_lam (Γ := Γ)
  -- h1: mul(x, Sn) =_nat app3 prec 0 z (Sn)
  let h1 := lam2_correct_nf adm body (.var (.vs .vz)) (.app .succ (.var .vz))
    (mul_body_var_nf (.app .succ (.var .vz)))
  -- h2: app2 z (app3 prec 0 z n) n =_nat add (app3 prec 0 z n) x
  let h2 := lam2_correct_nf adm raw_step
    (Term.app3 (.prec Ty.nat) Term.zero z (.var .vz)) (.var .vz)
    (mul_step_nf (.var (.vs .vz)) _ _)
  -- h3: mul(x, n) =_nat app3 prec 0 z n
  let h3 := lam2_correct_nf adm body (.var (.vs .vz)) (.var .vz)
    (mul_body_var_nf (.var .vz))
  -- h4: congruence — replace app3 prec 0 z n with mul(x, n) inside add
  let h4 := qfer_no_premise_nat_nf (.mp h3 (eqAtType_sym adm))
    (mul_add_subst0_l_nf (.var (.vs .vz)) (Term.app3 (.prec Ty.nat) Term.zero z (.var .vz)))
    (mul_add_subst0_l_nf (.var (.vs .vz))
      (Term.app2 Term.mul (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _) (.var .vz)))
  -- Chain: h1 → rec_succ → h2 → h4
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h4 (.mp c2 and_intro)) (eqAtType_trans adm)

/-- Formula normalization for transporting mul_succ from variable context to general. -/
private theorem mul_succ_formula_nf (x n : Term F Γ Ty.nat) :
    ((Formula.eq0
      (Term.app2 Term.mul (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _)
        (Term.app Term.succ (.var .vz)))
      (Term.app2 Term.add
        (Term.app2 Term.mul (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _) (.var .vz))
        (.var (.vs .vz)))).subst0 n.weaken).subst0 x =
    Formula.eq0 (Term.app2 Term.mul x (Term.app Term.succ n))
      (Term.app2 Term.add (Term.app2 Term.mul x n) x) := by
  simp only [Formula.subst0, Formula.substF, Term.app2, Term.subst,
    Term.subst0_map, mul_closed_subst', add_closed_subst']
  -- Remaining: n.weaken.subst (subst0_map x) needs to simplify to n
  have hw := weaken_subst0_h n x
  simp only [Term.subst0] at hw
  rw [hw]

/-- x · Sn = (x · n) + x. -/
def mul_succ (x n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul x (Term.app Term.succ n))
      (Term.app2 Term.add (Term.app2 Term.mul x n) x)) :=
  -- Prove in variable context nat :: nat :: Γ, then transport
  let h_var := @mul_succ_var _ _ _ _ Premises adm Γ
  let h_all_n := univ_gen h_var
  let h_at_n := .mp h_all_n (.forall_ax n.weaken)
  let h_all_x := univ_gen h_at_n
  let h_at_x := .mp h_all_x (.forall_ax x)
  Eq.mp (congrArg (Derivable F EqX al Premises) (mul_succ_formula_nf x n)) h_at_x

/-- 0 · y = 0 for all y (by induction on y). -/
def mul_zero_l (y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul Term.zero y) Term.zero) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul Term.zero (.var .vz)) Term.zero
  -- Base: A[0] = mul 0 0 = 0. By mul_zero.
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.mul Term.zero Term.zero) Term.zero := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst']
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    base_nf ▸ mul_zero adm Term.zero
  -- Step: A(y) → A(Sy). mul 0 (Sy) = add (mul 0 y) 0 = mul 0 y = 0.
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.mul Term.zero (.app .succ (.var .vz))) Term.zero := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      mul_closed_subst']
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    -- t1: mul 0 (Sy) = add (mul 0 y) 0
    let t1 := mul_succ (Premises := Premises) adm Term.zero (.var .vz : Term F (Ty.nat :: Γ) _)
    -- t2: add (mul 0 y) 0 = mul 0 y
    let t2 := add_zero_r adm (Term.app2 Term.mul Term.zero (.var .vz : Term F (Ty.nat :: Γ) _))
    -- t12: mul 0 (Sy) = mul 0 y (by trans)
    let t12 := .mp (.mp t2 (.mp t1 and_intro)) .trans0
    -- Chain: (mul 0 (Sy) = mul 0 y) ∧ (mul 0 y = 0) → mul 0 (Sy) = 0
    .syllogism (pair_h (weaken_intro_h t12) I_comb) .trans0
  -- Induction + instantiation
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.mul Term.zero y) Term.zero := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst']
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

-- ── monus ────────────────────────────────────────────────────────────────────

/-- x ∸ 0 = x. -/
def monus_zero (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus x Term.zero) x) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app Term.pd (.var (.vs .vz))))) (.var .vz)
  let h1 := Term.lam2_correct adm body x Term.zero
  .mp (.mp (.rec_zero (ρ := Ty.nat)) (.mp h1 and_intro)) .trans0

/-- x ∸ Sn = pd(x ∸ n). -/
def monus_succ (x n : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.monus x (Term.app Term.succ n))
      (Term.app Term.pd (Term.app2 Term.monus x n))) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app3 (.prec Ty.nat) (.var (.vs .vz))
      (Term.lam (Term.lam (.app Term.pd (.var (.vs .vz))))) (.var .vz)
  let step : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat := .app Term.pd (.var (.vs .vz))
  let z := Term.lam (Term.lam step)
  let h1 := lam2_correct_nf adm body x (.app .succ n) (monus_body_nf x _)
  let h2 := lam2_correct_nf adm step
    (Term.app3 (.prec Ty.nat) x z n) n (step_pd_nf _ _)
  let h3 := lam2_correct_nf adm body x n (monus_body_nf x _)
  let h4 := @qfer_no_premise _ _ EqX al Premises _ _ _ _ _
    (.app Term.pd (.var .vz)) (Derivable.mp h3 (eqAtType_sym adm))
  let c1 := .mp (.mp .rec_succ (.mp h1 and_intro)) (eqAtType_trans adm)
  let c2 := .mp (.mp h2 (.mp c1 and_intro)) (eqAtType_trans adm)
  .mp (.mp h4 (.mp c2 and_intro)) (eqAtType_trans adm)

end ArithCorr

-- ── Isolated nf lemmas for Term.add under subst0 (avoiding deep defeq) ───

/-- Weakened terms are invariant under substVar0.

Public: this is one of the rewrites a proof script needs to see through the goals that
`induction` leaves behind — see `ProofMode/Arith.lean`. -/
theorem weaken_substVar0 {ρ : Ty ι} (t : Term F Γ τ) (u : Term F (ρ :: Γ) ρ) :
    t.weaken.subst (Term.substVar0_map u) = t.weaken := by
  simp only [Term.weaken]
  rw [Term.rename_subst, Term.rename_eq_subst]; rfl

/-- The terms defined above are closed, so substitution leaves them alone. Public because a
proof script has to see through the substitutions that `induction` leaves in a goal — see
`ProofMode/Arith.lean`. -/
theorem mul_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    (Term.mul : Term F Γ _).subst σ = Term.mul := by rfl

theorem monus_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    (Term.monus : Term F Γ _).subst σ = Term.monus := by rfl

theorem abs_diff_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    (Term.abs_diff : Term F Γ _).subst σ = Term.abs_diff := by rfl

theorem sg_bar_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    (Term.sg_bar : Term F Γ _).subst σ = Term.sg_bar := by rfl

/-- `Term.add` is closed, so substitution leaves it alone. Public for the same reason. -/
theorem add_closed_subst {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    Term.subst σ (Term.add : Term F Γ _) = Term.add := add_closed_subst' σ

-- The arithmetic constants join the `closed_subst` set. The primed variants above are the
-- same statements — `add_closed_subst` is literally `add_closed_subst' σ` — and exist only
-- because they are needed earlier in the file, so only the canonical names are tagged.
attribute [closed_subst] pd_closed_subst mul_closed_subst monus_closed_subst
  abs_diff_closed_subst sg_bar_closed_subst add_closed_subst

/-- The eta-expanded form of `Term.weaken_subst0`. `simp` leaves the substitution as
`fun {τ} => …`, which the plain lemma does not match, so the normalising set needs this
spelling rather than the direct one. -/
theorem Term.weaken_subst0_eta {Γ : Ctx ι} {τ ρ : Ty ι} (t : Term F Γ τ) (s : Term F Γ ρ) :
    Term.subst (fun {_τ} => Term.subst0_map s) (Term.weaken t) = t :=
  Term.weaken_subst0 t s

-- `qnorm` is the substitution-normalising `simp only` that this development writes out by
-- hand roughly 300 times: push `subst`/`subst0` through the application spine, and leave the
-- closed constants alone. The explicit lists it replaces had to name every closed constant
-- appearing in the goal, and omitting one *fails* the call rather than weakening it.
--
-- `qnorm [h₁, h₂]` adds lemmas to the front — in practice the local `let` abbreviations a
-- goal is stated in terms of, which have to be zeta-unfolded in the same pass.
open Lean.Parser.Tactic in
syntax "qnorm" (" [" (simpErase <|> simpLemma),* "]")? : tactic

macro_rules
  | `(tactic| qnorm) => `(tactic| qnorm [])
  | `(tactic| qnorm [$ts,*]) =>
      `(tactic| simp only [$ts,*, Term.subst0, Term.subst, Term.subst0_map,
          Term.subst0_map_vz, Term.subst0_map_vs, Term.app2, Term.app3,
          Term.weaken_subst0, Term.weaken_subst0_eta, closed_subst])

private theorem add_qfer_l_nf {Γ : Ctx ι} (x y s : Term F Γ Ty.nat) :
    (Term.app2 Term.add (.var .vz) y.weaken : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app2 Term.add s y := by
  simp only [Term.subst0, Term.app2, Term.subst, add_closed_subst, Term.subst0_map]
  exact congrArg _ (weaken_subst0_h y s)

private theorem add_qfer_r_nf {Γ : Ctx ι} (x y s : Term F Γ Ty.nat) :
    (Term.app2 Term.add x.weaken (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 s =
    Term.app2 Term.add x s := by
  simp only [Term.subst0, Term.app2, Term.subst, add_closed_subst, Term.subst0_map]
  exact congrArg (fun z => Term.app (Term.app Term.add z) s) (weaken_subst0_h x s)

-- ============================================================================
-- Section 5a: eq0 decidability (needed by ArithProps)
-- ============================================================================

/-- For any natural number n, either n = 0 or n ≠ 0.
    Proved by induction: the step case follows directly from succ_ne_zero,
    without using the induction hypothesis. -/
def eq0_decidable' {Γ : Ctx ι} :
    Derivable F EqX al Premises (Formula.all Ty.nat
      (Formula.eq0 (Γ := Ty.nat :: Γ) (.var .vz) Term.zero ∨ᶠ
       ¬ᶠFormula.eq0 (.var .vz) Term.zero)) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (.var .vz) Term.zero ∨ᶠ ¬ᶠFormula.eq0 (.var .vz) Term.zero
  let base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    .mp (.refl0 (t := Term.zero)) .or_weak
  let succ_ne : Derivable F EqX al Premises
      (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ) :=
    .mp (@Derivable.succ_ne_zero ι F EqX al Premises (Ty.nat :: Γ)) (.forall_ax (.var .vz))
  let concl : Derivable F EqX al Premises (Formula.substVar0 A (Term.app Term.succ (.var .vz))) :=
    .mp succ_ne or_inr
  let step_body : Derivable F EqX al Premises
      ((⊥ᶠ →ᶠ ⊥ᶠ).weakenBy Ty.nat →ᶠ
       A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz))) :=
    weaken_intro_h (weaken_intro_h concl)
  let step : Derivable F EqX al Premises
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))) :=
    .mp self_imp_h (.forall_rule step_body)
  .induction base step

-- ── S-congruence helper ───────────────────────────────────────────────────
private def succ_congr {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (.app .succ s) (.app .succ t)) :=
  qfer_no_premise_nat_nf h (r := .app .succ (.var .vz)) rfl rfl

-- ── add_succ_l ────────────────────────────────────────────────────────────
/-- Sx + y = S(x + y). By induction on y. -/
def add_succ_l {Γ : Ctx ι} (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add (.app .succ x) y)
      (.app .succ (Term.app2 Term.add x y))) :=
  let xw := x.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.add (.app .succ xw) (.var .vz))
      (.app .succ (Term.app2 Term.add xw (.var .vz)))
  -- Base: add(Sx,0) = S(add(x,0)). Both sides = Sx via add_zero.
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x :=
    Term.weaken_subst0 x
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.add (.app .succ x) Term.zero)
        (.app .succ (Term.app2 Term.add x Term.zero)) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, xw_subst0]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    .mp (.mp (succ_congr (.mp (add_zero_r adm x) .sym0)) (.mp (add_zero_r adm (.app .succ x)) and_intro)) .trans0
  -- Step: A(y) → A(Sy). add_succ on both sides + S-congruence on IH.
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.add (.app .succ xw) (.app .succ (.var .vz)))
        (.app .succ (Term.app2 Term.add xw (.app .succ (.var .vz)))) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      add_closed_subst, weaken_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    -- as1: add(Sxw, Sy) = S(add(Sxw, y))
    let as1 := add_succ adm (.app .succ xw) (.var .vz : Term F (Ty.nat :: Γ) _)
    -- s_ih: IH → S(add(Sxw,y)) = S(S(add(xw,y)))  (S-congruence on IH)
    let s_ih := qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app .succ (.var .vz)) rfl rfl
    -- c1: IH → add(Sxw, Sy) = S(S(add(xw, y)))
    let c1 := .syllogism (pair_h (weaken_intro_h as1) s_ih) .trans0
    -- as2: add(xw, Sy) = S(add(xw, y))
    let as2 := add_succ adm xw (.var .vz : Term F (Ty.nat :: Γ) _)
    -- s_as2: S(S(add(xw,y))) = S(add(xw,Sy))  (S-congruence on sym(as2))
    let s_as2 := succ_congr (.mp as2 .sym0)
    .syllogism (pair_h c1 (weaken_intro_h s_as2)) .trans0
  -- Induction + instantiation
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.add (.app .succ x) y)
        (.app .succ (Term.app2 Term.add x y)) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

-- ============================================================================
-- Section 5b: Basic arithmetic properties
-- ============================================================================
-- From arithmetic.tex Prop prop:basic-arithmetic-properties.
-- These are the algebraic facts needed to prove qf_equiv_term.

section ArithProps

variable {Γ : Ctx ι}

/-- x ≠ 0 → x = S(pd x).  (prop:basic-arithmetic-properties.6) -/
def ne_zero_eq_succ_pd (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (¬ᶠFormula.eq0 x Term.zero →ᶠ
       Formula.eq0 x (Term.app Term.succ (Term.app Term.pd x))) :=
  let A : Formula F (Ty.nat :: Γ) :=
    ¬ᶠFormula.eq0 (.var .vz) Term.zero →ᶠ
      Formula.eq0 (.var .vz) (.app .succ (.app Term.pd (.var .vz)))
  let base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    .syllogism (eval_h I_comb (weaken_intro_h .refl0)) .exfalso
  let pd_sx := pd_succ adm (.var .vz : Term F (Ty.nat :: Γ) Ty.nat)
  let sx_eq : Derivable F EqX al Premises (Formula.eq0
      (.app .succ (.var .vz)) (.app .succ (.app Term.pd (.app .succ (.var .vz))))) :=
    Derivable.mp (@qfer_no_premise _ _ EqX al Premises _ _ _ _ _
      (.app .succ (.var .vz)) pd_sx) .sym0
  let step_body : Derivable F EqX al Premises
      (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    weaken_intro_h (weaken_intro_h sx_eq)
  Derivable.mp (Derivable.induction base (univ_gen step_body)) (.forall_ax x)

/-- x + y = 0 ↔ x = 0 ∧ y = 0.  (prop:basic-arithmetic-properties.1) -/
def add_eq_zero_iff (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      ((Formula.eq0 (Term.app2 Term.add x y) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 y Term.zero) ∧ᶠ
       (Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 y Term.zero →ᶠ
        Formula.eq0 (Term.app2 Term.add x y) Term.zero)) := by
  -- Backward: x=0 ∧ y=0 → add x y = 0. By qfer + add_zero.
  have qf_add_l : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.add x y) (Term.app2 Term.add Term.zero y)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb (add_qfer_l_nf x y x) (add_qfer_l_nf x y Term.zero)
  have qf_add_r : Derivable F EqX al Premises (Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.add Term.zero y) (Term.app2 Term.add Term.zero Term.zero)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb (add_qfer_r_nf Term.zero y y) (add_qfer_r_nf Term.zero y Term.zero)
  have add00 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add (Term.zero (F := F) (Γ := Γ)) Term.zero) Term.zero) :=
    add_zero_r adm (Term.zero (F := F) (Γ := Γ))
  have bwd : Derivable F EqX al Premises (Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.add x y) Term.zero) :=
    Derivable.syllogism
      (pair_h
        (Derivable.syllogism
          (pair_h (Derivable.syllogism .and_weak qf_add_l)
            (Derivable.syllogism and_proj2 qf_add_r)) .trans0)
        (weaken_intro_h add00)) .trans0
  -- Forward: add x y = 0 → x = 0 ∧ y = 0. By induction on y.
  -- A(y) = add(x', y) = 0 → x' = 0 ∧ y = 0, with x' = x.weaken in context nat :: Γ.
  let xw := x.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.add xw (.var .vz)) Term.zero →ᶠ
      Formula.eq0 xw Term.zero ∧ᶠ Formula.eq0 (.var .vz) Term.zero
  -- Base: A[0] = add(x,0) = 0 → x = 0 ∧ 0 = 0. By add_zero: add(x,0) = x. Then pair with refl.
  have base_nf : A.subst0 Term.zero =
      (Formula.eq0 (Term.app2 Term.add x Term.zero) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 Term.zero Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst0, Term.app2, Term.subst,
      add_closed_subst, Term.subst0_map]
    exact congrArg (fun z => (Formula.eq0 (Term.app (Term.app Term.add z) Term.zero) Term.zero →ᶠ
      Formula.eq0 z Term.zero ∧ᶠ Formula.eq0 Term.zero Term.zero)) (weaken_subst0_h x Term.zero)
  -- base proof: add(x,0)=0 → x=0 ∧ 0=0. From add_zero: add(x,0)=x. Sym+trans: x=0. Pair with refl.
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    Derivable.syllogism
      (pair_h (weaken_intro_h (Derivable.mp (add_zero_r adm x) .sym0)) I_comb)
      (Derivable.syllogism .trans0 (pair_h I_comb (weaken_intro_h .refl0)))
  -- Step nf: substVar0 A (S(var vz)) normalizes.
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      (Formula.eq0 (Term.app2 Term.add xw (.app .succ (.var .vz))) Term.zero →ᶠ
        Formula.eq0 xw Term.zero ∧ᶠ Formula.eq0 (.app .succ (.var .vz)) Term.zero) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.app2, Term.subst,
      add_closed_subst, Term.substVar0_map, weaken_substVar0]
  -- Instantiation nf: A.subst0 y normalizes.
  have inst_nf : A.subst0 y =
      (Formula.eq0 (Term.app2 Term.add x y) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 y Term.zero) := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst0, Term.app2, Term.subst,
      add_closed_subst, Term.subst0_map]
    exact congrArg (fun z => (Formula.eq0 (Term.app (Term.app Term.add z) y) Term.zero →ᶠ
      Formula.eq0 z Term.zero ∧ᶠ Formula.eq0 y Term.zero)) (weaken_subst0_h x y)
  -- Step: A(y) → A(Sy). Ignore IH. From add(x',Sy)=0: by add_succ, S(add(x',y))=0, contradiction.
  have add_succ_w : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add xw (.app .succ (.var .vz)))
        (.app .succ (Term.app2 Term.add xw (.var .vz)))) :=
    add_succ adm xw (.var .vz : Term F (Ty.nat :: Γ) Ty.nat)
  have step_to_bot : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.add xw (.app .succ (.var .vz))) Term.zero →ᶠ ⊥ᶠ) :=
    Derivable.syllogism (pair_h (weaken_intro_h (Derivable.mp add_succ_w .sym0)) I_comb)
      (Derivable.syllogism .trans0 (Derivable.mp .succ_ne_zero
        (.forall_ax (Term.app2 Term.add xw (.var .vz)))))
  have step_body : Derivable F EqX al Premises
      (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸ weaken_intro_h (Derivable.syllogism step_to_bot .exfalso)
  have fwd_all := Derivable.induction base (univ_gen step_body)
  have fwd : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add x y) Term.zero →ᶠ
      Formula.eq0 x Term.zero ∧ᶠ Formula.eq0 y Term.zero) :=
    inst_nf ▸ Derivable.mp fwd_all (.forall_ax y)
  exact .mp bwd (.mp fwd and_intro)

-- helpers for mul under subst0
private theorem mul_subst0_r_nf (x t : Term F Γ Ty.nat) :
    (Term.app2 Term.mul x.weaken (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.mul x t := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst']
  exact congrArg (Term.app · t) (congrArg (Term.app Term.mul) (Term.weaken_subst0 x t))

private theorem mul_subst0_l_nf (y t : Term F Γ Ty.nat) :
    (Term.app2 Term.mul (.var .vz) y.weaken : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.mul t y := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst']
  exact congrArg _ (Term.weaken_subst0 y t)

/-- x · y = 0 ↔ x = 0 ∨ y = 0.  (prop:basic-arithmetic-properties.2) -/
def mul_eq_zero_iff (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      ((Formula.eq0 (Term.app2 Term.mul x y) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∨ᶠ Formula.eq0 y Term.zero) ∧ᶠ
       (Formula.eq0 x Term.zero ∨ᶠ Formula.eq0 y Term.zero →ᶠ
        Formula.eq0 (Term.app2 Term.mul x y) Term.zero)) :=
  -- ── Backward: x=0 ∨ y=0 → mul x y = 0 ──
  -- Case y=0: by qfer (y=0 → mul x y = mul x 0) + mul_zero
  let qf_mul_y0 : Derivable F EqX al Premises (Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.mul x y) (Term.app2 Term.mul x Term.zero)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb (mul_subst0_r_nf x y) (mul_subst0_r_nf x Term.zero)
  let bwd_y0 : Derivable F EqX al Premises (Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.mul x y) Term.zero) :=
    .syllogism (pair_h qf_mul_y0 (weaken_intro_h (mul_zero adm x))) .trans0
  -- Case x=0: by qfer (x=0 → mul x y = mul 0 y) + mul_zero_l
  let qf_mul_x0 : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.mul x y) (Term.app2 Term.mul Term.zero y)) :=
    qfer_nat_nf (by rfl) (by rfl) I_comb (mul_subst0_l_nf y x) (mul_subst0_l_nf y Term.zero)
  let bwd_x0 : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.mul x y) Term.zero) :=
    .syllogism (pair_h qf_mul_x0 (weaken_intro_h (mul_zero_l adm y))) .trans0
  let bwd := or_elim_rule bwd_x0 bwd_y0
  -- ── Forward: mul x y = 0 → x=0 ∨ y=0 (by induction on y) ──
  let xw := x.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul xw (.var .vz)) Term.zero →ᶠ
      Formula.eq0 xw Term.zero ∨ᶠ Formula.eq0 (.var .vz) Term.zero
  -- Base: A[0] = mul(x,0)=0 → x=0 ∨ 0=0. Consequent holds unconditionally.
  have base_nf : A.subst0 Term.zero =
      (Formula.eq0 (Term.app2 Term.mul x Term.zero) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∨ᶠ Formula.eq0 Term.zero Term.zero) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst']
    exact congrArg (fun z => Formula.eq0 (Term.app (Term.app Term.mul z) Term.zero) Term.zero →ᶠ
      Formula.eq0 z Term.zero ∨ᶠ Formula.eq0 Term.zero Term.zero) (weaken_subst0_h x Term.zero)
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) :=
    base_nf ▸ weaken_intro_h (.mp .refl0 or_inr)
  -- Step: A(y) → A(Sy). mul(x',Sy)=0 → x'=0 ∨ Sy=0.
  -- From mul_succ: mul(x',Sy) = add(mul(x',y), x'). So add(...)=0. By add_eq_zero_iff: x'=0. Or_weak.
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      (Formula.eq0 (Term.app2 Term.mul xw (.app .succ (.var .vz))) Term.zero →ᶠ
        Formula.eq0 xw Term.zero ∨ᶠ Formula.eq0 (.app .succ (.var .vz)) Term.zero) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      mul_closed_subst', weaken_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸ weaken_intro_h (
    -- Goal: mul(x', Sy) = 0 → x' = 0 ∨ Sy = 0
    -- From mul_succ: mul(x', Sy) = add(mul(x', y), x')
    let ms := mul_succ (Premises := Premises) adm xw (.var .vz : Term F (Ty.nat :: Γ) _)
    -- ms_chain: mul(x',Sy)=0 → add(mul(x',y), x')=0
    let ms_chain : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul xw (.app .succ (.var .vz))) Term.zero →ᶠ
        Formula.eq0 (Term.app2 Term.add (Term.app2 Term.mul xw (.var .vz)) xw) Term.zero) :=
      .syllogism (pair_h (weaken_intro_h (.mp ms .sym0)) I_comb) .trans0
    -- add_fwd: add(a, b)=0 → a=0 ∧ b=0
    let add_fwd := (add_eq_zero_iff adm (Term.app2 Term.mul xw (.var .vz)) xw).mp .and_weak
    -- get x'=0
    let get_x0 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul xw (.app .succ (.var .vz))) Term.zero →ᶠ
        Formula.eq0 xw Term.zero) :=
      .syllogism (.syllogism ms_chain add_fwd) (.syllogism .and_perm .and_weak)
    .syllogism get_x0 .or_weak)
  -- Induction + instantiation
  have inst_nf : A.subst0 y =
      (Formula.eq0 (Term.app2 Term.mul x y) Term.zero →ᶠ
        Formula.eq0 x Term.zero ∨ᶠ Formula.eq0 y Term.zero) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst']
    exact congrArg (fun z => Formula.eq0 (Term.app (Term.app Term.mul z) y) Term.zero →ᶠ
      Formula.eq0 z Term.zero ∨ᶠ Formula.eq0 y Term.zero) (weaken_subst0_h x y)
  let fwd : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul x y) Term.zero →ᶠ
      Formula.eq0 x Term.zero ∨ᶠ Formula.eq0 y Term.zero) :=
    inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)
  .mp bwd (.mp fwd and_intro)

/-- sḡ(x) = 0 ↔ x ≠ 0.  (prop:basic-arithmetic-properties.3) -/
def sg_bar_eq_zero_iff (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      ((Formula.eq0 (Term.app Term.sg_bar x) Term.zero →ᶠ ¬ᶠFormula.eq0 x Term.zero) ∧ᶠ
       (¬ᶠFormula.eq0 x Term.zero →ᶠ Formula.eq0 (Term.app Term.sg_bar x) Term.zero)) := by
  -- Forward: sg_bar(x) = 0 → x ≠ 0.
  -- If x=0 then sg_bar(x)=sg_bar(0)=S0 by qfer+sg_bar_zero; with sg_bar(x)=0 get S0=0, contradiction.
  have qf_sgx : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app Term.sg_bar x) (Term.app Term.sg_bar Term.zero)) :=
    Derivable.qfer (r := .app Term.sg_bar (.var .vz)) (by rfl) (by rfl) I_comb
  have x0_to_sgS0 : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app Term.sg_bar x) (.app .succ .zero)) :=
    Derivable.syllogism (pair_h qf_sgx
      (weaken_intro_h (sg_bar_zero (Γ := Γ)))) .trans0
  have fwd : Derivable F EqX al Premises (Formula.eq0 (Term.app Term.sg_bar x) Term.zero →ᶠ
      ¬ᶠFormula.eq0 x Term.zero) :=
    .exportation (Derivable.syllogism
      (pair_h (Derivable.syllogism .and_weak .sym0)
        (Derivable.syllogism (Derivable.syllogism .and_perm .and_weak) x0_to_sgS0))
      (Derivable.syllogism .trans0
        (Derivable.syllogism .sym0 (Derivable.mp .succ_ne_zero (.forall_ax Term.zero)))))
  -- Backward: x ≠ 0 → sg_bar(x) = 0.
  -- By ne_zero_eq_succ_pd: x = S(pd x). Then qfer: sg_bar(x) = sg_bar(S(pd x)) = 0 by sg_bar_succ.
  have qf_sg : Derivable F EqX al Premises (¬ᶠFormula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app Term.sg_bar x) (Term.app Term.sg_bar (.app .succ (.app Term.pd x)))) :=
    Derivable.qfer (r := .app Term.sg_bar (.var .vz)) (by rfl) (by rfl) (ne_zero_eq_succ_pd adm x)
  have bwd : Derivable F EqX al Premises (¬ᶠFormula.eq0 x Term.zero →ᶠ
      Formula.eq0 (Term.app Term.sg_bar x) Term.zero) :=
    Derivable.syllogism (pair_h qf_sg
      (weaken_intro_h (sg_bar_succ adm (Term.app Term.pd x)))) .trans0
  exact .mp bwd (.mp fwd and_intro)

/-- sḡ(x) · y = 0 ↔ (x = 0 → y = 0).  (prop:basic-arithmetic-properties.4) -/
def sg_bar_mul_eq_zero_iff (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      ((Formula.eq0 (Term.app2 Term.mul (Term.app Term.sg_bar x) y) Term.zero →ᶠ
        Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) ∧ᶠ
       ((Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) →ᶠ
        Formula.eq0 (Term.app2 Term.mul (Term.app Term.sg_bar x) y) Term.zero)) :=
  let sx := Term.app Term.sg_bar x
  -- ── Forward: sḡ(x)·y=0 → (x=0 → y=0) ──
  let mul_fwd := .mp (mul_eq_zero_iff adm sx y) .and_weak
  let sgb_fwd := .mp (sg_bar_eq_zero_iff adm x) .and_weak
  -- lift: (x=0→⊥) → (x=0→y=0) via S(K exfalso)(id)
  let lift : Derivable F EqX al Premises (¬ᶠFormula.eq0 x Term.zero →ᶠ
      Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) :=
    .mp (.mp (.exfalso (A := Formula.eq0 y Term.zero)) K_comb) S_comb
  let case_sg := .syllogism sgb_fwd lift
  let case_y : Derivable F EqX al Premises (Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) := K_comb
  let fwd := .syllogism mul_fwd (or_elim_rule case_sg case_y)
  -- ── Backward: (x=0→y=0) → sḡ(x)·y=0 ──
  let mul_bwd := .mp (mul_eq_zero_iff adm sx y) (.syllogism .and_perm .and_weak)
  let sgb_bwd := .mp (sg_bar_eq_zero_iff adm x) (.syllogism .and_perm .and_weak)
  let dec_x := .mp eq0_decidable' (.forall_ax x)
  -- Case x=0: x=0 → (x=0→y=0) → sḡ(x)·y=0
  let bwd_from_y0 : Derivable F EqX al Premises (Formula.eq0 y Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.mul sx y) Term.zero) :=
    .syllogism (pair_h (qfer_nat_nf (by rfl) (by rfl) I_comb
      (mul_subst0_r_nf sx y) (mul_subst0_r_nf sx Term.zero))
      (weaken_intro_h (mul_zero adm sx))) .trans0
  let case_x0 : Derivable F EqX al Premises (Formula.eq0 x Term.zero →ᶠ
      (Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) →ᶠ
      Formula.eq0 (Term.app2 Term.mul sx y) Term.zero) :=
    .exportation (.syllogism (.syllogism .and_perm (.importation mp_form)) bwd_from_y0)
  -- Case x≠0: x≠0 → (x=0→y=0) → sḡ(x)·y=0 (premise unused)
  let case_xne0 : Derivable F EqX al Premises (¬ᶠFormula.eq0 x Term.zero →ᶠ
      (Formula.eq0 x Term.zero →ᶠ Formula.eq0 y Term.zero) →ᶠ
      Formula.eq0 (Term.app2 Term.mul sx y) Term.zero) :=
    .syllogism (.syllogism sgb_bwd (.syllogism .or_weak mul_bwd)) K_comb
  let bwd := .mp dec_x (or_elim_rule case_x0 case_xne0)
  .mp bwd (.mp fwd and_intro)

/-- |x − y| = 0 ↔ x = y.  (prop:basic-arithmetic-properties.5) -/
private theorem monus_closed_subst' {Γ Δ : Ctx ι} (σ : Term.Subst F Γ Δ) :
    Term.subst σ (Term.monus : Term F Γ _) = Term.monus := by rfl

private theorem add_closed_rename {Γ Δ : Ctx ι} (r : Renaming Γ Δ) :
    Term.rename r (Term.add : Term F Γ _) = Term.add := by rfl

private theorem monus_closed_rename {Γ Δ : Ctx ι} (r : Renaming Γ Δ) :
    Term.rename r (Term.monus : Term F Γ _) = Term.monus := by rfl

-- helper: (app2 monus (var vz) (var vz)).subst0 t = app2 monus t t
private theorem monus_self_subst0_nf (t : Term F Γ Ty.nat) :
    (Term.app2 Term.monus (.var .vz) (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.monus t t := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst']

-- helper: (monus x.weaken (var vz)).subst0 t = monus x t  (subst on RIGHT arg)
private theorem monus_subst0_rw_nf (x t : Term F Γ Ty.nat) :
    (Term.app2 Term.monus x.weaken (.var .vz) : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.monus x t := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst']
  exact congrArg (Term.app · t) (congrArg (Term.app Term.monus) (Term.weaken_subst0 x t))

-- helper: (monus (var vz) x.weaken).subst0 t = monus t x  (subst on LEFT arg)
private theorem monus_subst0_lw_nf (x t : Term F Γ Ty.nat) :
    (Term.app2 Term.monus (.var .vz) x.weaken : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.monus t x := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, monus_closed_subst']
  exact congrArg _ (Term.weaken_subst0 x t)

/-- 0 + x = x. By induction on x. -/
def add_zero_l (y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add Term.zero y) y) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.add Term.zero (.var .vz)) (.var .vz)
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.add Term.zero Term.zero) Term.zero := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸ add_zero_r adm Term.zero
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.add Term.zero (.app .succ (.var .vz))) (.app .succ (.var .vz)) := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      add_closed_subst]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let as := add_succ adm Term.zero (.var .vz : Term F (Ty.nat :: Γ) _)
    -- IH: add 0 y = y. as: add 0 (Sy) = S(add 0 y). S-congr IH: S(add 0 y) = Sy.
    -- Chain: add 0 (Sy) = S(add 0 y) = Sy.
    .syllogism (pair_h (weaken_intro_h as) (qfer_nat_nf (by rfl) (by rfl) I_comb
      (r := .app .succ (.var .vz)) rfl rfl)) .trans0
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.add Term.zero y) y := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- x + y = y + x. By induction on y. -/
def add_comm (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add x y) (Term.app2 Term.add y x)) :=
  let xw := x.weaken (σ := Ty.nat)
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x :=
    Term.weaken_subst0 x
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.add xw (.var .vz)) (Term.app2 Term.add (.var .vz) xw)
  -- Base: add(x, 0) = add(0, x). Chain: add(x,0) = x = add(0,x).
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.add x Term.zero) (Term.app2 Term.add Term.zero x) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, xw_subst0]
  have base := base_nf ▸
    .mp (.mp (.mp (add_zero_l adm x) .sym0) (.mp (add_zero_r adm x) and_intro)) .trans0
  -- Step: A(y) → A(Sy).
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.add xw (.app .succ (.var .vz)))
        (Term.app2 Term.add (.app .succ (.var .vz)) xw) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      add_closed_subst, weaken_substVar0]
  have step_body := step_nf ▸ (
    -- as: add(xw, Sy) = S(add(xw, y))
    let as := add_succ adm xw (.var .vz : Term F (Ty.nat :: Γ) _)
    -- S-congr on IH: add(xw, y) = add(y, xw) → S(add(xw, y)) = S(add(y, xw))
    let qf_succ := qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app .succ (.var .vz)) rfl rfl
    -- asl: S(y) + xw = S(y + xw)
    let asl := add_succ_l adm (.var .vz : Term F (Ty.nat :: Γ) _) xw
    -- Chain: IH → add(xw, Sy) = S(add(xw, y)) = S(add(y, xw)) = add(Sy, xw)
    let c1 := .syllogism (pair_h (weaken_intro_h as) qf_succ) .trans0
    .syllogism (pair_h c1 (weaken_intro_h (.mp asl .sym0))) .trans0)
  -- Induction + instantiation
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.add x y) (Term.app2 Term.add y x) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      add_closed_subst, xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

-- helper for add_congr_r under subst0 (used in add_assoc)
private theorem add_w_vz_subst0 (u s : Term F Γ Ty.nat) :
    (Term.app2 Term.add u.weaken (.var .vz) : Term F (Ty.nat :: Γ) _).subst0 s =
    Term.app2 Term.add u s := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst']
  have := Term.weaken_subst0 u s; simp only [Term.subst0] at this; rw [this]

/-- (x + y) + z = x + (y + z). By induction on z. -/
def add_assoc (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add (Term.app2 Term.add x y) z)
      (Term.app2 Term.add x (Term.app2 Term.add y z))) :=
  let xw := x.weaken (σ := Ty.nat)
  let yw := y.weaken (σ := Ty.nat)
  let xy := Term.app2 Term.add xw yw
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  have yw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) y.weaken = y := Term.weaken_subst0 y
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.add xy (.var .vz))
      (Term.app2 Term.add xw (Term.app2 Term.add yw (.var .vz)))
  -- Base: (x+y)+0 = x+(y+0). Both sides reduce to x+y.
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.add (Term.app2 Term.add x y) Term.zero)
        (Term.app2 Term.add x (Term.app2 Term.add y Term.zero)) := by
    simp only [A, xy, xw, yw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst, xw_subst0, yw_subst0]
  have base := base_nf ▸ (
    let az1 := add_zero_r adm (Term.app2 Term.add x y)
    let az2 := add_zero_r adm y
    let rhs := qfer_no_premise_nat_nf az2 (r := Term.app2 Term.add x.weaken (.var .vz))
      (add_w_vz_subst0 x (Term.app2 Term.add y Term.zero))
      (add_w_vz_subst0 x y)
    .mp (.mp (.mp rhs .sym0) (.mp az1 and_intro)) .trans0)
  -- Step: A(z) → A(Sz).
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.add xy (.app .succ (.var .vz)))
        (Term.app2 Term.add xw (Term.app2 Term.add yw (.app .succ (.var .vz)))) := by
    simp only [A, xy, xw, yw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, add_closed_subst, weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- (x+y)+Sz = S((x+y)+z) by add_succ
    let as1 := add_succ adm xy vz
    -- IH → S((x+y)+z) = S(x+(y+z)) by S-congr
    let s_ih := qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app .succ (.var .vz)) rfl rfl
    -- x+S(y+z) = S(x+(y+z)) by add_succ, reversed
    let as3 := .mp (add_succ adm xw (Term.app2 Term.add yw vz)) .sym0
    -- x+(y+Sz) = x+S(y+z) by congr_r on sym(y+Sz = S(y+z))
    let congr_as2 := qfer_no_premise_nat_nf (.mp (add_succ adm yw vz) .sym0)
      (add_w_vz_subst0 xw (Term.app .succ (Term.app2 Term.add yw vz)))
      (add_w_vz_subst0 xw (Term.app2 Term.add yw (.app .succ vz)))
    -- Chain: IH → (x+y)+Sz = S((x+y)+z) = S(x+(y+z)) = x+S(y+z) = x+(y+Sz)
    let c1 := .syllogism (pair_h (weaken_intro_h as1) s_ih) .trans0
    let c23 := .mp (.mp congr_as2 (.mp as3 and_intro)) .trans0
    .syllogism (pair_h c1 (weaken_intro_h c23)) .trans0)
  -- Induction + instantiation
  have inst_nf : A.subst0 z =
      Formula.eq0 (Term.app2 Term.add (Term.app2 Term.add x y) z)
        (Term.app2 Term.add x (Term.app2 Term.add y z)) := by
    simp only [A, xy, xw, yw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst, xw_subst0, yw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax z)

/-- Step inner: IH@Sk → monus(S(add(k,y)), Sy) = k.
    Chain: add_succ_l congruence + pd congruence + pd_succ + monus_succ + trans. -/
private def monus_cancel_step_inner {Γ : Ctx ι} :
    Derivable F EqX al Premises
      (Formula.eq0
        (Term.app2 Term.monus
          (Term.app2 Term.add (.app .succ (.var .vz)) (.var (.vs .vz) : Term F (Ty.nat :: Ty.nat :: Γ) _))
          (.var (.vs .vz)))
        (.app .succ (.var .vz)) →ᶠ
       Formula.eq0
        (Term.app2 Term.monus (.app .succ (Term.app2 Term.add (.var .vz) (.var (.vs .vz))))
          (.app .succ (.var (.vs .vz))))
        (.var .vz)) :=
  let kv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let aky := Term.app2 Term.add kv yv
  let sky := Term.app Term.succ aky
  let skv := Term.app Term.succ kv
  let IH_Sk := Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add skv yv) yv) skv
  let congr1 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add skv yv) yv)
      (Term.app2 Term.monus sky yv)) :=
    qfer_no_premise_nat_nf (add_succ_l adm kv yv)
      (monus_subst0_lw_nf yv (Term.app2 Term.add skv yv)) (monus_subst0_lw_nf yv sky)
  let stepA : Derivable F EqX al Premises (IH_Sk →ᶠ
      Formula.eq0 (Term.app2 Term.monus sky yv) skv) :=
    .syllogism (pair_h (weaken_intro_h (.mp congr1 .sym0)) I_comb) .trans0
  let stepB : Derivable F EqX al Premises (IH_Sk →ᶠ
      Formula.eq0 (.app Term.pd (Term.app2 Term.monus sky yv)) (.app Term.pd skv)) :=
    .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) stepA
  let stepD : Derivable F EqX al Premises (IH_Sk →ᶠ
      Formula.eq0 (.app Term.pd (Term.app2 Term.monus sky yv)) kv) :=
    .syllogism (pair_h stepB (weaken_intro_h (pd_succ adm kv))) .trans0
  .syllogism (pair_h (weaken_intro_h (monus_succ adm sky yv)) stepD) .trans0

/-- Step: B(y) → substVar0 B (Sy) using forall_inst_succ + forall_lift.
    Avoids direct forall_rule on formulas containing monus/add. -/
private def monus_cancel_step {Γ : Ctx ι} :
    let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus
        (Term.app2 Term.add (.var .vz) (.var (.vs .vz))) (.var (.vs .vz))) (.var .vz)
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
    Derivable F EqX al Premises (B →ᶠ Formula.substVar0 B (.app .succ (.var .vz))) := by
  intro C B
  let kv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let sky := Term.app Term.succ (Term.app2 Term.add kv yv)
  let syv := Term.app Term.succ yv
  let skv := Term.app Term.succ kv
  -- congr2: monus(add(k,Sy),Sy) = monus(sky,Sy) via add_succ
  let congr2 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add kv syv) syv)
      (Term.app2 Term.monus sky syv)) :=
    qfer_no_premise_nat_nf (add_succ adm kv yv)
      (monus_subst0_lw_nf syv (Term.app2 Term.add kv syv)) (monus_subst0_lw_nf syv sky)
  -- Cast monus_cancel_step_inner to use local let-bound names
  let inner : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add skv yv) yv) skv →ᶠ
       Formula.eq0 (Term.app2 Term.monus sky syv) kv) :=
    @monus_cancel_step_inner _ _ _ _ Premises adm Γ
  -- inner_chain: C(Sk,y) → C(k,Sy)  (= inner + congr2 + trans)
  let inner_chain : Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add skv yv) yv) skv →ᶠ
       Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add kv syv) syv) kv) :=
    .syllogism (pair_h (weaken_intro_h congr2) inner) .trans0
  -- Step 1: B → ∀k. C(Sk,y) via forall_inst_succ
  -- Step 2: (∀k. C(Sk,y)) → (∀k. C(k,Sy)) via forall_lift using inner_chain
  -- Compose: B → ∀k. C(k,Sy) = substVar0 B (Sy)
  -- step_nf: substVar0 B (Sy) = ∀k. C(k,Sy)
  have step_nf : Formula.substVar0 B (.app .succ (.var .vz)) =
      Formula.all Ty.nat (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add kv syv) syv) kv) := by
    simp only [B, C, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst', add_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]; rfl
  rw [step_nf]
  -- inst_succ_nf: C.substVar0(Sk) = inner_chain's input formula
  have inst_succ_nf : C.substVar0 (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add skv yv) yv) skv := by
    simp only [C, kv, yv, skv, Formula.substVar0, Formula.substF, Term.subst,
      Term.substVar0_map, Term.app2, monus_closed_subst', add_closed_subst]
  -- forall_inst_succ : B → ∀k. C.substVar0(Sk), cast to B → ∀k. inner_input
  let fis := Eq.mp (congrArg (Derivable F EqX al Premises <| B →ᶠ Formula.all Ty.nat ·) inst_succ_nf)
    forall_inst_succ
  -- forall_map inner_chain : ∀k. inner_input → ∀k. inner_output
  exact .syllogism fis (forall_map inner_chain)

/-- (x + y) ∸ y = x. By induction on y with ∀k bundled. -/
def monus_cancel (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add x y) y) x) :=
  let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus
      (Term.app2 Term.add (.var .vz) (.var (.vs .vz))) (.var (.vs .vz))) (.var .vz)
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
  have base_nf : B.subst0 Term.zero = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add (.var .vz) Term.zero) Term.zero)
        (.var .vz)) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst', add_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  have base : Derivable F EqX al Premises (B.subst0 Term.zero) := base_nf ▸
    let kv : Term F (Ty.nat :: Γ) _ := .var .vz
    univ_gen (.mp (.mp (add_zero_r adm kv)
      (.mp (monus_zero adm (Term.app2 Term.add kv Term.zero)) and_intro)) .trans0)
  let step := @monus_cancel_step _ _ _ _ Premises adm Γ
  -- Normalize B.subst0 y to an explicit ∀k formula
  have B_y_nf : B.subst0 y = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add (.var .vz) y.weaken) y.weaken)
        (.var .vz)) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.Subst.ext, Term.subst0_map,
      Term.app2, monus_closed_subst', add_closed_subst, Term.weaken]
  -- Normalize the inner formula after subst0 x
  have inner_x_nf :
      (Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add (.var .vz) y.weaken) y.weaken)
        (.var .vz)).subst0 x =
      Formula.eq0 (Term.app2 Term.monus (Term.app2 Term.add x y) y) x := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst', add_closed_subst]
    have hw := Term.weaken_subst0 y x; simp only [Term.subst0] at hw; rw [hw]
  let ind := Derivable.induction base (univ_gen step)
  let at_y_raw := .mp ind (.forall_ax y)
  -- Cast B.subst0 y to the explicit all-formula
  let at_y := Eq.mp (congrArg (Derivable F EqX al Premises) B_y_nf) at_y_raw
  -- Apply forall_ax x to the explicit all-formula
  let at_xy := .mp at_y (.forall_ax x)
  -- Cast inner formula to the target
  Eq.mp (congrArg (Derivable F EqX al Premises) inner_x_nf) at_xy

/-- x ∸ x = 0. From monus_cancel with x = 0 + add_zero_l. -/
def monus_self (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus x x) Term.zero) :=
  -- monus x x = monus (add 0 x) x [by add_zero_l]
  -- monus (add 0 x) x = 0 [by monus_cancel]
  let h1 := add_zero_l adm x  -- add 0 x = x
  -- h2 : monus x x = monus (add 0 x) x (congruence under monus(•, x))
  let h2 := qfer_no_premise_nat_nf (.mp h1 .sym0) (monus_subst0_lw_nf x x)
    (monus_subst0_lw_nf x (Term.app2 Term.add Term.zero x))
  .mp (.mp (monus_cancel (Premises := Premises) adm Term.zero x) (.mp h2 and_intro)) .trans0

/-- 0 ∸ y = 0. By induction on y. -/
def monus_zero_l (y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus Term.zero y) Term.zero) :=
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus Term.zero (.var .vz)) Term.zero
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus Term.zero Term.zero) Term.zero := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst']
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸ monus_zero adm Term.zero
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus Term.zero (.app .succ (.var .vz))) Term.zero := by
    simp only [A, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      monus_closed_subst']
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    -- monus 0 (Sy) = pd(monus 0 y) [monus_succ]. IH: monus 0 y = 0.
    -- pd(monus 0 y) = pd(0) [pd congruence on IH]. pd(0) = 0 [pd_zero].
    -- Chain: monus 0 (Sy) = pd(monus 0 y) = pd(0) = 0.
    let t1 := monus_succ adm Term.zero (.var .vz : Term F (Ty.nat :: Γ) _)
    let pd_ih : Derivable F EqX al Premises (A →ᶠ Formula.eq0 (.app Term.pd (Term.app2 Term.monus Term.zero (.var .vz)))
        (.app Term.pd Term.zero)) :=
      .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) I_comb
    let chain1 := .syllogism (pair_h pd_ih (weaken_intro_h (pd_zero (Γ := Ty.nat :: Γ)))) .trans0
    .syllogism (pair_h (weaken_intro_h t1) chain1) .trans0
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.monus Term.zero y) Term.zero := by
    simp only [A, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst']
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- Sx ∸ Sy = x ∸ y. By induction on y (x is a parameter). -/
def monus_succ_l (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.monus (.app .succ x) (.app .succ y))
      (Term.app2 Term.monus x y)) :=
  let xw := x.weaken (σ := Ty.nat)
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.app .succ xw) (.app .succ (.var .vz)))
      (Term.app2 Term.monus xw (.var .vz))
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  -- Base: monus(Sx,S0) = monus(x,0). Both = x by pd_succ + monus_zero.
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus (.app .succ x) (.app .succ .zero))
        (Term.app2 Term.monus x Term.zero) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst', xw_subst0]
  have base : Derivable F EqX al Premises (A.subst0 Term.zero) := base_nf ▸
    -- monus(Sx,S0) = pd(monus(Sx,0)) [monus_succ] = pd(Sx) [pd congr monus_zero] = x [pd_succ]
    -- monus(x,0) = x [monus_zero]. Chain both to x, then sym+trans.
    let ms := monus_succ adm (.app .succ x) Term.zero
    let pd_c := qfer_no_premise_nat_nf (monus_zero adm (.app .succ x))
      (r := .app Term.pd (.var .vz)) rfl rfl
    -- s12: monus(Sx,S0) = pd(Sx)
    let s12 := .mp (.mp pd_c (.mp ms and_intro)) .trans0
    -- s123: monus(Sx,S0) = x
    let s123 := .mp (.mp (pd_succ adm x) (.mp s12 and_intro)) .trans0
    -- result: monus(Sx,S0) = monus(x,0) via s123 + sym(monus_zero x)
    .mp (.mp (.mp (monus_zero adm x) .sym0) (.mp s123 and_intro)) .trans0
  -- Step: monus(Sx,Sy)=monus(x,y) → monus(Sx,SSy)=monus(x,Sy).
  -- monus(Sx,SSy) = pd(monus(Sx,Sy)). IH: monus(Sx,Sy) = monus(x,y).
  -- pd(monus(Sx,Sy)) = pd(monus(x,y)). monus(x,Sy) = pd(monus(x,y)). Equal!
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus (.app .succ xw) (.app .succ (.app .succ (.var .vz))))
        (Term.app2 Term.monus xw (.app .succ (.var .vz))) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      monus_closed_subst', weaken_substVar0]
  have step_body : Derivable F EqX al Premises (A →ᶠ Formula.substVar0 A (.app .succ (.var .vz))) :=
    step_nf ▸
    let ms1 := monus_succ adm (.app .succ xw) (.app .succ (.var .vz) : Term F (Ty.nat :: Γ) _)
    let ms2 := monus_succ adm xw (.var .vz : Term F (Ty.nat :: Γ) _)
    -- IH: monus(Sx,Sy)=monus(x,y). pd_congr: pd(monus(Sx,Sy))=pd(monus(x,y)).
    -- ms1: monus(Sx,SSy) = pd(monus(Sx,Sy)). ms2: monus(x,Sy) = pd(monus(x,y)).
    -- Chain: monus(Sx,SSy) = pd(monus(Sx,Sy)) = pd(monus(x,y)) = monus(x,Sy).
    let pd_ih := .qfer (σ := Ty.nat) (r := .app Term.pd (.var .vz)) (by rfl) (by rfl) I_comb
    .syllogism (pair_h (weaken_intro_h ms1) (.syllogism (pair_h pd_ih
      (weaken_intro_h (.mp ms2 .sym0))) .trans0)) .trans0
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.monus (.app .succ x) (.app .succ y))
        (Term.app2 Term.monus x y) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      monus_closed_subst', xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- Case y=0 for monus_antisym: y=0 → monus(Sx,y)=0 ∧ monus(y,Sx)=0 → Sx=y.
    Proof: monus(Sx,0)=Sx=0 → contradiction by succ_ne_zero → exfalso. -/
private def monus_antisym_case_y0 {Γ : Ctx ι} :
    let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
    let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
    let sxv := Term.app Term.succ xv
    Derivable F EqX al Premises (Formula.eq0 yv Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.monus sxv yv) Term.zero ∧ᶠ
      Formula.eq0 (Term.app2 Term.monus yv sxv) Term.zero →ᶠ Formula.eq0 sxv yv) :=
  let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let sxv := Term.app Term.succ xv
  let succ_ne : Derivable F EqX al Premises (Formula.eq0 sxv Term.zero →ᶠ ⊥ᶠ) :=
    .mp (@Derivable.succ_ne_zero _ _ EqX al Premises (Ty.nat :: Ty.nat :: Γ)) (.forall_ax xv)
  -- qf_mz: y=0 → monus(Sx,y) = monus(Sx,0)
  let qf_mz := qfer_nat_nf (by rfl) (by rfl) (I_comb (EqX := EqX))
    (monus_subst0_rw_nf sxv yv) (monus_subst0_rw_nf sxv Term.zero)
  let mz_sx := monus_zero adm sxv  -- monus(Sx,0) = Sx
  -- reduce_mz: y=0 → monus(Sx,y) = Sx
  let reduce_mz := .syllogism (pair_h qf_mz (weaken_intro_h mz_sx)) .trans0
  -- get_y0: y=0 ∧ (P ∧ Q) → y=0
  -- get_mx0: y=0 ∧ (P ∧ Q) → monus(Sx,y)=0 (= P)
  -- Build: conj → Sx=monus(Sx,y) ∧ monus(Sx,y)=0 → Sx=0 → ⊥ → Sx=y
  .exportation
    (.syllogism
      (pair_h (.syllogism .and_weak (.syllogism reduce_mz .sym0))
        (.syllogism .and_perm (.syllogism .and_weak .and_weak)))
      (.syllogism .trans0 (.syllogism succ_ne .exfalso)))

/-- Case y≠0 for monus_antisym: IH at pd(y) as OBJECT-LEVEL premise →
    y≠0 → monus(Sx,y)=0 ∧ monus(y,Sx)=0 → Sx=y.
    y≠0 → y=S(pd y). monus_succ_l reduces. IH gives x=pd(y). succ_congr: Sx=y. -/
private def monus_antisym_case_yne0 {Γ : Ctx ι} :
    let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
    let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
    let pdy := Term.app Term.pd yv
    let sxv := Term.app Term.succ xv
    let IH_pdy := Formula.eq0 (Term.app2 Term.monus xv pdy) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus pdy xv) Term.zero →ᶠ Formula.eq0 xv pdy
    Derivable F EqX al Premises (IH_pdy →ᶠ ¬ᶠFormula.eq0 yv Term.zero →ᶠ
      Formula.eq0 (Term.app2 Term.monus sxv yv) Term.zero ∧ᶠ
      Formula.eq0 (Term.app2 Term.monus yv sxv) Term.zero →ᶠ Formula.eq0 sxv yv) :=
  -- Triple importation: IH ∧ y≠0 ∧ (P∧Q) → Sx=y. Then triple exportation.
  let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let sxv := Term.app Term.succ xv
  let pdy := Term.app Term.pd yv
  let spdy := Term.app Term.succ pdy
  let ne_succ := ne_zero_eq_succ_pd adm yv
  let msl1' : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus sxv spdy) (Term.app2 Term.monus xv pdy)) :=
    monus_succ_l adm xv pdy
  let msl2' : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus spdy sxv) (Term.app2 Term.monus pdy xv)) :=
    monus_succ_l adm pdy xv
  let qf1 := qfer_nat_nf (by rfl) (by rfl) ne_succ
    (monus_subst0_rw_nf sxv yv) (monus_subst0_rw_nf sxv spdy)
  let qf2 := qfer_nat_nf (by rfl) (by rfl) ne_succ
    (monus_subst0_lw_nf sxv yv) (monus_subst0_lw_nf sxv spdy)
  let reduce1 := .syllogism (pair_h qf1 (weaken_intro_h msl1')) .trans0
  let reduce2 := .syllogism (pair_h qf2 (weaken_intro_h msl2')) .trans0
  let succ_imp : Derivable F EqX al Premises (Formula.eq0 xv pdy →ᶠ Formula.eq0 sxv spdy) :=
    .qfer (σ := Ty.nat) (r := .app .succ (.var .vz)) (by rfl) (by rfl) I_comb
  -- Projections from IH ∧ (NE ∧ (P ∧ Q))
  let get_IH := @Derivable.and_weak _ _ EqX al _ _ _  -- → IH
  let get_NE := .syllogism (.syllogism .and_perm .and_weak) .and_weak  -- → NE
  let get_PQ := .syllogism (.syllogism .and_perm .and_weak) (.syllogism .and_perm .and_weak)  -- → P∧Q
  let get_P := .syllogism get_PQ .and_weak  -- → P
  let get_Q := .syllogism get_PQ (.syllogism .and_perm .and_weak)  -- → Q
  -- reduced_P: triple → monus(x,pdy)=0 via sym(reduce1) + P + trans
  let reduced_P := .syllogism (pair_h (.syllogism get_NE (.syllogism reduce1 .sym0)) get_P) .trans0
  -- reduced_Q: triple → monus(pdy,x)=0 via sym(reduce2) + Q + trans
  let reduced_Q := .syllogism (pair_h (.syllogism get_NE (.syllogism reduce2 .sym0)) get_Q) .trans0
  -- apply IH: triple → x=pdy (via mp_form on IH and reduced pair)
  let apply_IH := .syllogism (pair_h get_IH (pair_h reduced_P reduced_Q)) (.importation mp_form)
  -- ne_sym: triple → S(pdy)=y
  let ne_sym := .syllogism get_NE (.syllogism ne_succ .sym0)
  -- final: IH ∧ (NE ∧ PQ) → Sx=y
  let final := .syllogism (pair_h (.syllogism apply_IH succ_imp) ne_sym) .trans0
  -- Re-associate: (IH ∧ NE) ∧ PQ → IH ∧ (NE ∧ PQ)
  let reassoc : Derivable F EqX al Premises (_ ∧ᶠ _ →ᶠ _) :=
    pair_h (.syllogism .and_weak .and_weak)
      (pair_h (.syllogism .and_weak (.syllogism .and_perm .and_weak)) (.syllogism .and_perm .and_weak))
  -- (IH ∧ NE) ∧ PQ → Sx=y
  let final_la := .syllogism reassoc final
  -- IH → NE → PQ → Sx=y via double exportation
  .exportation (.exportation final_la)

/-- Step body for monus_eq_zero_antisym. -/
-- Step body: B_w →ᶠ C_step(Sx,y). Built in term mode to avoid tactic resolution issues.
private def monus_antisym_step_body {Γ : Ctx ι} :
    let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) Term.zero ∧ᶠ
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
      Formula.eq0 (.var (.vs .vz)) (.var .vz)
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
    let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
    let pdy := Term.app Term.pd yv
    let C_step := Formula.eq0 (Term.app2 Term.monus (.app .succ (.var (.vs .vz))) (.var .vz)) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) (.app .succ (.var (.vs .vz)))) Term.zero →ᶠ
       Formula.eq0 (.app .succ (.var (.vs .vz))) (.var .vz)
    Derivable F EqX al Premises (B.weakenBy Ty.nat →ᶠ C_step) :=
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let pdy := Term.app Term.pd yv
  let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) Term.zero ∧ᶠ
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
    Formula.eq0 (.var (.vs .vz)) (.var .vz)
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
  have ih_nf : (C.renameF (Renaming.ext Renaming.shift)).subst0 pdy =
      (Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) pdy) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus pdy (.var (.vs .vz))) Term.zero →ᶠ
       Formula.eq0 (.var (.vs .vz)) pdy) := by
    simp only [C, Formula.renameF, Formula.subst0, Formula.substF, Term.rename, Term.subst,
      Term.Renaming.ext, Term.Renaming.shift, Term.subst0_map, Term.Subst.ext,
      Term.app2, monus_closed_rename, monus_closed_subst', add_closed_rename, add_closed_subst',
      pd_closed_subst, Term.weaken, Term.pd]
  let ih_inst := Eq.mp (congrArg (fun f => Derivable F EqX al Premises (B.weakenBy Ty.nat →ᶠ f)) ih_nf)
    (Derivable.forall_ax pdy)
  let case_yne0 := @monus_antisym_case_yne0 _ _ _ _ Premises adm Γ
  let case_y0 := @monus_antisym_case_y0 _ _ _ _ Premises adm Γ
  let dec_y := .mp eq0_decidable' (.forall_ax yv)
  -- f: y=0 → (B_w∧PQ → Sx=y)
  let f := .exportation (.syllogism
    (pair_h .and_weak (.syllogism .and_perm (.syllogism .and_weak (.syllogism .and_perm .and_weak))))
    (.importation case_y0))
  -- g: y≠0 → (B_w∧PQ → Sx=y)
  let get_bw := .syllogism (.syllogism .and_perm .and_weak) .and_weak
  let get_ne : Derivable F EqX al Premises (_ →ᶠ _) := .and_weak
  let get_pq := .syllogism (.syllogism .and_perm .and_weak) (.syllogism .and_perm .and_weak)
  -- g: y≠0 → (B_w∧PQ → Sx=y)
  -- From y≠0 ∧ (B_w ∧ PQ):
  --   step1: pair (y≠0→PQ→Sx=y, y≠0) → mp_form → PQ→Sx=y
  --   step2: PQ
  --   pair + mp_form → Sx=y
  let g := .exportation (.syllogism
    (pair_h
      (.syllogism (pair_h (.syllogism get_bw (.syllogism ih_inst case_yne0)) get_ne)
        (.importation mp_form))
      get_pq)
    (.importation mp_form))
  .exportation (.mp dec_y (or_elim_rule f g))

private def monus_antisym_step {Γ : Ctx ι} :
    let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) Term.zero ∧ᶠ
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
      Formula.eq0 (.var (.vs .vz)) (.var .vz)
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
    Derivable F EqX al Premises (B →ᶠ Formula.substVar0 B (.app .succ (.var .vz))) := by
  intro C B
  have step_nf : Formula.substVar0 B (.app .succ (.var .vz)) = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.var (.vs .vz))) (.var .vz)) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) (.app .succ (.var (.vs .vz)))) Term.zero →ᶠ
       Formula.eq0 (.app .succ (.var (.vs .vz))) (.var .vz)) := by
    simp only [B, C, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  rw [step_nf]
  exact .forall_rule (monus_antisym_step_body (Premises := Premises) (adm := adm) (Γ := Γ))

def monus_eq_zero_antisym (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.monus x y) Term.zero ∧ᶠ
      Formula.eq0 (Term.app2 Term.monus y x) Term.zero →ᶠ Formula.eq0 x y) :=
  let C : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) Term.zero ∧ᶠ
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) Term.zero →ᶠ
    Formula.eq0 (.var (.vs .vz)) (.var .vz)
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat C
  -- Base: B[0] = ∀y. monus(0,y)=0 ∧ monus(y,0)=0 → 0=y
  -- From monus(y,0)=y (monus_zero) and premise: y=0. Then 0=y by sym.
  have base_nf : B.subst0 Term.zero = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus Term.zero (.var .vz)) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) Term.zero) Term.zero →ᶠ
       Formula.eq0 Term.zero (.var .vz)) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  have base : Derivable F EqX al Premises (B.subst0 Term.zero) := base_nf ▸
    let kv : Term F (Ty.nat :: Γ) _ := .var .vz
    -- From premise: monus(y,0)=0. monus_zero y: monus(y,0)=y. Trans: y=0. Sym: 0=y.
    -- From monus(y,0)=0 ∧ monus(0,y)=0: extract monus(y,0)=0.
    -- monus_zero y: monus(y,0)=y. sym: y=monus(y,0). With monus(y,0)=0: trans → y=0. sym → 0=y.
    -- premise: monus(0,y)=0 ∧ monus(y,0)=0. Extract monus(y,0)=0 (second).
    -- sym(monus_zero y): y = monus(y,0). Pair with monus(y,0)=0. Trans: y=0. Sym: 0=y.
    univ_gen (.syllogism (pair_h (weaken_intro_h (.mp (monus_zero adm kv) .sym0))
      (.syllogism .and_perm .and_weak)) (.syllogism .trans0 .sym0))
  -- Step: monus_antisym_step
  let step := @monus_antisym_step _ _ _ _ Premises adm Γ
  -- Normalize B.subst0 y
  have B_y_nf : B.subst0 y = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus y.weaken (.var .vz)) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) y.weaken) Term.zero →ᶠ
       Formula.eq0 y.weaken (.var .vz)) := by
    simp only [B, C, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  -- Normalize inner.subst0 x: result is monus(y,x)=0 ∧ monus(x,y)=0 → y=x
  have inner_x_nf :
      (Formula.eq0 (Term.app2 Term.monus y.weaken (.var .vz)) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) y.weaken) Term.zero →ᶠ
       Formula.eq0 y.weaken (.var .vz)).subst0 x =
      (Formula.eq0 (Term.app2 Term.monus y x) Term.zero ∧ᶠ
       Formula.eq0 (Term.app2 Term.monus x y) Term.zero →ᶠ Formula.eq0 y x) := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst']
    have hw := Term.weaken_subst0 y x; simp only [Term.subst0] at hw; rw [hw]
  let ind := Derivable.induction base (univ_gen step)
  let at_y_raw := .mp ind (.forall_ax y)
  let at_y := Eq.mp (congrArg (Derivable F EqX al Premises) B_y_nf) at_y_raw
  let at_xy := .mp at_y (.forall_ax x)
  -- at_xy_typed : monus(y,x)=0 ∧ monus(x,y)=0 → y=x
  let at_xy_typed := Eq.mp (congrArg (Derivable F EqX al Premises) inner_x_nf) at_xy
  -- Convert: swap conjunction with and_perm, swap conclusion with sym0
  .syllogism .and_perm (.syllogism at_xy_typed .sym0)

-- abs_diff body normalization
private theorem abs_diff_body_nf (x y : Term F Γ Ty.nat) :
    ((Term.app2 Term.add
        (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))
        (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))
      : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat).subst0 (y.weaken)).subst0 x =
    Term.app2 Term.add (Term.app2 Term.monus x y) (Term.app2 Term.monus y x) := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
    add_closed_subst', monus_closed_subst']
  have hw := Term.weaken_subst0 y x; simp only [Term.subst0] at hw; rw [hw]

-- helper for qfer on add(monus(•,y), monus(y,•))
private theorem add_monus_subst0_nf (x t : Term F Γ Ty.nat) :
    (Term.app2 Term.add
      (Term.app2 Term.monus x.weaken (.var .vz))
      (Term.app2 Term.monus (.var .vz) x.weaken)
      : Term F (Ty.nat :: Γ) Ty.nat).subst0 t =
    Term.app2 Term.add (Term.app2 Term.monus x t) (Term.app2 Term.monus t x) := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map,
    add_closed_subst', monus_closed_subst']
  have hw := Term.weaken_subst0 x t; simp only [Term.subst0] at hw; rw [hw]

def abs_diff_eq_zero_iff (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      ((Formula.eq0 (Term.app2 Term.abs_diff x y) Term.zero →ᶠ Formula.eq0 x y) ∧ᶠ
       (Formula.eq0 x y →ᶠ Formula.eq0 (Term.app2 Term.abs_diff x y) Term.zero)) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))
  -- abs_diff x y = add(monus x y)(monus y x)
  let unfold := lam2_correct_nf adm body x y (abs_diff_body_nf x y)
  -- ── Forward: abs_diff x y = 0 → x = y ──
  -- add(monus x y)(monus y x) = 0 → monus x y = 0 ∧ monus y x = 0 → x = y
  let add_fwd := .mp (add_eq_zero_iff adm (Term.app2 Term.monus x y) (Term.app2 Term.monus y x)) .and_weak
  -- unfold_eq0: abs_diff x y = add(...) as eq0
  let unfold_eq0 : Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.abs_diff x y)
      (Term.app2 Term.add (Term.app2 Term.monus x y) (Term.app2 Term.monus y x))) := unfold
  -- fwd: abs_diff x y = 0 → abs_diff = add(...) [sym] ∧ add(...)=0 → 0=add(...) → chain
  -- abs_diff=0 → add(...)=0: chain sym(unfold) with the premise via trans
  let unfold_sym : Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.add (Term.app2 Term.monus x y) (Term.app2 Term.monus y x))
      (Term.app2 Term.abs_diff x y)) := .mp unfold_eq0 .sym0
  let abs_to_add := .syllogism (pair_h (weaken_intro_h unfold_sym) I_comb) .trans0
  -- abs_to_add : abs_diff x y = 0 → add(monus x y)(monus y x) = 0
  let fwd := .syllogism abs_to_add (.syllogism add_fwd (monus_eq_zero_antisym (Premises := Premises) adm x y))
  -- ── Backward: x = y → abs_diff x y = 0 ──
  -- x = y → add(monus x y)(monus y x) = add(monus x x)(monus x x) = add 0 0 = 0
  let qf_monus_raw := qfer_nat_nf (by rfl) (by rfl) I_comb
    (add_monus_subst0_nf x x) (add_monus_subst0_nf x y)
  -- qf_monus_raw : x=y → add(monus x x)(monus x x) = add(monus x y)(monus y x)
  -- Flip: x=y → add(monus x y)(monus y x) = add(monus x x)(monus x x)
  let qf_monus := .syllogism qf_monus_raw .sym0
  let ms := monus_self adm x  -- monus x x = 0
  -- add(monus x x)(monus x x) = add(0)(0) via qfer on add(vz)(vz)
  let add_congr := qfer_no_premise_nat_nf ms
    (r := Term.app2 Term.add (.var .vz) (.var .vz))
    (by simp [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst'])
    (by simp [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst'])
  -- add00: add(monus x x)(monus x x) = 0  via add_congr + add_zero
  let add00 := .mp (.mp (add_zero_r adm Term.zero) (.mp add_congr and_intro)) .trans0
  -- chain1_2: x=y → add(monus x y)(monus y x) = 0
  let chain1_2 := .syllogism (pair_h qf_monus (weaken_intro_h add00)) .trans0
  -- bwd: x=y → abs_diff x y = 0  (via unfold + chain1_2 + trans)
  let bwd := .syllogism (pair_h (weaken_intro_h unfold) chain1_2) .trans0
  .mp bwd (.mp fwd and_intro)

-- ── monus_disjunct: x∸y=0 ∨ y∸x=0 (totality of ≤) ──────────────────────────

private def monus_disjunct_step_body {Γ : Ctx ι} :
    let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
    let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
    let sxv := Term.app Term.succ xv
    let Q : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) .zero ∨ᶠ
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) .zero
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat Q
    Derivable F EqX al Premises (B.weakenBy Ty.nat →ᶠ
      (Formula.eq0 (Term.app2 Term.monus sxv yv) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus yv sxv) .zero)) :=
  let xv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var (.vs .vz)
  let yv : Term F (Ty.nat :: Ty.nat :: Γ) _ := .var .vz
  let sxv := Term.app Term.succ xv
  let pdy := Term.app Term.pd yv
  let spdy := Term.app Term.succ pdy
  let Q : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) .zero ∨ᶠ
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) .zero
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat Q
  let Q_step :=
    Formula.eq0 (Term.app2 Term.monus sxv yv) .zero ∨ᶠ
    Formula.eq0 (Term.app2 Term.monus yv sxv) .zero
  have ih_nf : (Q.renameF (Renaming.ext Renaming.shift)).subst0 pdy =
      (Formula.eq0 (Term.app2 Term.monus xv pdy) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus pdy xv) .zero) := by
    simp only [Q, Formula.renameF, Formula.subst0, Formula.substF, Term.rename, Term.subst,
      Term.Renaming.ext, Term.Renaming.shift, Term.subst0_map, Term.Subst.ext,
      Term.app2, monus_closed_rename, monus_closed_subst',
      Term.weaken, Term.pd]; rfl
  let ih_inst := Eq.mp (congrArg (fun f => Derivable F EqX al Premises (B.weakenBy Ty.nat →ᶠ f)) ih_nf)
    (Derivable.forall_ax pdy)
  let dec_y := .mp eq0_decidable' (.forall_ax yv)
  let case1 : Derivable F EqX al Premises (Formula.eq0 yv .zero →ᶠ Q_step) :=
    .syllogism (.syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) (I_comb (EqX := EqX))
        (monus_subst0_lw_nf sxv yv) (monus_subst0_lw_nf sxv .zero))
      (weaken_intro_h (monus_zero_l adm sxv))) .trans0) or_inr
  let f : Derivable F EqX al Premises (Formula.eq0 yv .zero →ᶠ (B.weakenBy Ty.nat →ᶠ Q_step)) :=
    .exportation (.syllogism .and_weak case1)
  let ne_succ := ne_zero_eq_succ_pd adm yv
  let msl_l := monus_succ_l adm xv pdy
  let msl_r := monus_succ_l adm pdy xv
  let chain_l :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) ne_succ
        (monus_subst0_rw_nf sxv yv) (monus_subst0_rw_nf sxv spdy))
      (weaken_intro_h msl_l)) .trans0
  let chain_r :=
    .syllogism (pair_h
      (qfer_nat_nf (by rfl) (by rfl) ne_succ
        (monus_subst0_lw_nf sxv yv) (monus_subst0_lw_nf sxv spdy))
      (weaken_intro_h msl_r)) .trans0
  let convert_l : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ Formula.eq0 (Term.app2 Term.monus xv pdy) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus sxv yv) .zero) :=
    .syllogism (pair_h (.syllogism .and_weak chain_l) (.syllogism .and_perm .and_weak)) .trans0
  let convert_r : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ Formula.eq0 (Term.app2 Term.monus pdy xv) .zero →ᶠ
       Formula.eq0 (Term.app2 Term.monus yv sxv) .zero) :=
    .syllogism (pair_h (.syllogism .and_weak chain_r) (.syllogism .and_perm .and_weak)) .trans0
  let get_ne := @Derivable.and_weak _ _ EqX al _ _ (¬ᶠFormula.eq0 yv .zero) _
  let get_bw : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ (B.weakenBy Ty.nat) →ᶠ B.weakenBy Ty.nat) :=
    .syllogism .and_perm .and_weak
  let get_ih := .syllogism get_bw ih_inst
  let ne_and_or := pair_h get_ne get_ih
  let dist : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ
        (Formula.eq0 (Term.app2 Term.monus xv pdy) .zero ∨ᶠ
         Formula.eq0 (Term.app2 Term.monus pdy xv) .zero) →ᶠ
       (¬ᶠFormula.eq0 yv .zero ∧ᶠ Formula.eq0 (Term.app2 Term.monus xv pdy) .zero) ∨ᶠ
       (¬ᶠFormula.eq0 yv .zero ∧ᶠ Formula.eq0 (Term.app2 Term.monus pdy xv) .zero)) :=
    .syllogism .and_perm
      (.importation (or_elim_rule
        (.exportation (.syllogism .and_perm .or_weak))
        (.exportation (.syllogism .and_perm or_inr))))
  let g_inner : Derivable F EqX al Premises
      (¬ᶠFormula.eq0 yv .zero ∧ᶠ (B.weakenBy Ty.nat) →ᶠ Q_step) :=
    .syllogism ne_and_or (.syllogism dist
      (or_elim_rule (.syllogism convert_l .or_weak) (.syllogism convert_r or_inr)))
  let g := .exportation g_inner
  .mp dec_y (or_elim_rule f g)

private def monus_disjunct_step {Γ : Ctx ι} :
    let Q : Formula F (Ty.nat :: Ty.nat :: Γ) :=
      Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) .zero ∨ᶠ
      Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) .zero
    let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat Q
    Derivable F EqX al Premises (B →ᶠ Formula.substVar0 B (.app .succ (.var .vz))) := by
  intro Q B
  have step_nf : Formula.substVar0 B (.app .succ (.var .vz)) = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus (.app .succ (.var (.vs .vz))) (.var .vz)) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) (.app .succ (.var (.vs .vz)))) .zero) := by
    simp only [B, Q, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  rw [step_nf]
  exact .forall_rule (monus_disjunct_step_body (Premises := Premises) (adm := adm) (Γ := Γ))

def monus_disjunct (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus x y) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus y x) .zero) :=
  let Q : Formula F (Ty.nat :: Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz)) .zero ∨ᶠ
    Formula.eq0 (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))) .zero
  let B : Formula F (Ty.nat :: Γ) := Formula.all Ty.nat Q
  have base_nf : B.subst0 Term.zero = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus Term.zero (.var .vz)) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) Term.zero) .zero) := by
    simp only [B, Q, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  have base : Derivable F EqX al Premises (B.subst0 Term.zero) := base_nf ▸
    univ_gen (.mp (monus_zero_l adm (.var .vz : Term F (Ty.nat :: Γ) _)) .or_weak)
  let step := @monus_disjunct_step _ _ _ _ Premises adm Γ
  have B_y_nf : B.subst0 y = Formula.all Ty.nat
      (Formula.eq0 (Term.app2 Term.monus y.weaken (.var .vz)) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) y.weaken) .zero) := by
    simp only [B, Q, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.Subst.ext, Term.app2, monus_closed_subst',
      Term.weaken, Term.rename, Term.Renaming.shift]
  have inner_x_nf :
      (Formula.eq0 (Term.app2 Term.monus y.weaken (.var .vz)) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus (.var .vz) y.weaken) .zero).subst0 x =
      (Formula.eq0 (Term.app2 Term.monus y x) .zero ∨ᶠ
       Formula.eq0 (Term.app2 Term.monus x y) .zero) := by
    simp only [Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst']
    have hw := Term.weaken_subst0 y x; simp only [Term.subst0] at hw; rw [hw]
  let ind := Derivable.induction base (univ_gen step)
  let at_y_raw := .mp ind (.forall_ax y)
  let at_y := Eq.mp (congrArg (Derivable F EqX al Premises) B_y_nf) at_y_raw
  let at_xy := .mp at_y (.forall_ax x)
  let at_xy_typed := Eq.mp (congrArg (Derivable F EqX al Premises) inner_x_nf) at_xy
  .mp at_xy_typed .or_perm

/-- |x - y| = |y - x|. From abs_diff unfolding + add_comm on monus summands. -/
def abs_diff_comm (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.abs_diff x y) (Term.app2 Term.abs_diff y x)) :=
  let body : Term F (Ty.nat :: Ty.nat :: Γ) Ty.nat :=
    Term.app2 Term.add
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz)))
  -- abs_diff x y = add(monus x y)(monus y x)
  let unfold_xy := lam2_correct_nf adm body x y (abs_diff_body_nf x y)
  -- abs_diff y x = add(monus y x)(monus x y)
  let unfold_yx := lam2_correct_nf adm body y x (abs_diff_body_nf y x)
  -- add_comm: add(monus x y)(monus y x) = add(monus y x)(monus x y)
  let ac := add_comm adm (Term.app2 Term.monus x y) (Term.app2 Term.monus y x)
  -- Chain: abs_diff x y = add(mx_y)(my_x) = add(my_x)(mx_y) = abs_diff y x
  let c1 := .mp (.mp ac (.mp unfold_xy and_intro)) .trans0
  .mp (.mp (.mp unfold_yx .sym0) (.mp c1 and_intro)) .trans0

-- ── Congruence helpers for add ──────────────────────────────────────────────

private theorem add_vz_w_subst0 (u s : Term F Γ Ty.nat) :
    (Term.app2 Term.add (.var .vz) u.weaken : Term F (Ty.nat :: Γ) _).subst0 s =
    Term.app2 Term.add s u := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, add_closed_subst']
  have := Term.weaken_subst0 u s; simp only [Term.subst0] at this; rw [this]

/-- s =₀ t → add(s, u) =₀ add(t, u). -/
def add_congr_l {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add s u) (Term.app2 Term.add t u)) :=
  qfer_no_premise_nat_nf h (add_vz_w_subst0 u s) (add_vz_w_subst0 u t)

/-- s =₀ t → add(u, s) =₀ add(u, t). -/
def add_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.add u s) (Term.app2 Term.add u t)) :=
  qfer_no_premise_nat_nf h (add_w_vz_subst0 u s) (add_w_vz_subst0 u t)

-- ── mul_succ_l and mul_comm ─────────────────────────────────────────────────

/-- Sx * y = x*y + y. By induction on y. -/
def mul_succ_l (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (.app .succ x) y)
      (Term.app2 Term.add (Term.app2 Term.mul x y) y)) :=
  let xw := x.weaken (σ := Ty.nat)
  let sx := Term.app Term.succ xw
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul sx (.var .vz))
      (Term.app2 Term.add (Term.app2 Term.mul xw (.var .vz)) (.var .vz))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.mul (.app .succ x) Term.zero)
        (Term.app2 Term.add (Term.app2 Term.mul x Term.zero) Term.zero) := by
    simp only [A, sx, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst, mul_closed_subst', xw_subst0]
  have base := base_nf ▸ (
    let lhs := mul_zero adm (.app .succ x)
    let mz := mul_zero adm x
    let az := add_zero_r adm (Term.app2 Term.mul x Term.zero)
    let rhs := .mp (.mp mz (.mp az and_intro)) .trans0
    .mp (.mp (.mp rhs .sym0) (.mp lhs and_intro)) .trans0)
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.mul sx (.app .succ (.var .vz)))
        (Term.app2 Term.add (Term.app2 Term.mul xw (.app .succ (.var .vz))) (.app .succ (.var .vz))) := by
    simp only [A, sx, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, add_closed_subst, mul_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let mxwy := Term.app2 Term.mul xw vz
    let ms1 := mul_succ (Premises := Premises) adm sx vz
    let ih_congr := qfer_nat_nf (by rfl) (by rfl) I_comb
      (add_vz_w_subst0 sx (Term.app2 Term.mul sx vz))
      (add_vz_w_subst0 sx (Term.app2 Term.add mxwy vz))
    let c1 := .syllogism (pair_h (weaken_intro_h ms1) ih_congr) .trans0
    let assoc1 := add_assoc adm mxwy vz sx
    let as1 := add_succ adm vz xw
    let cr1 := add_congr_r mxwy as1
    let lhs := .syllogism (pair_h c1 (weaken_intro_h (.mp (.mp cr1 (.mp assoc1 and_intro)) .trans0))) .trans0
    let ms2 := mul_succ (Premises := Premises) adm xw vz
    let ms2_congr := add_congr_l ms2 (.app .succ vz)
    let assoc2 := add_assoc adm mxwy xw (.app .succ vz)
    let as2 := add_succ adm xw vz
    let cr2 := add_congr_r mxwy as2
    let rhs := .mp (.mp cr2 (.mp (.mp (.mp assoc2 (.mp ms2_congr and_intro)) .trans0) and_intro)) .trans0
    let comm := add_comm adm vz xw
    let sc := succ_congr comm
    let eq_mid := add_congr_r mxwy sc
    .syllogism (pair_h lhs (weaken_intro_h (.mp (.mp (.mp rhs .sym0) (.mp eq_mid and_intro)) .trans0))) .trans0)
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.mul (.app .succ x) y)
        (Term.app2 Term.add (Term.app2 Term.mul x y) y) := by
    simp only [A, sx, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst, mul_closed_subst', xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- x * y = y * x. By induction on y. -/
def mul_comm (x y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul x y) (Term.app2 Term.mul y x)) :=
  let xw := x.weaken (σ := Ty.nat)
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul xw (.var .vz)) (Term.app2 Term.mul (.var .vz) xw)
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.mul x Term.zero) (Term.app2 Term.mul Term.zero x) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst', xw_subst0]
  have base := base_nf ▸
    .mp (.mp (.mp (mul_zero_l adm x) .sym0) (.mp (mul_zero adm x) and_intro)) .trans0
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.mul xw (.app .succ (.var .vz)))
        (Term.app2 Term.mul (.app .succ (.var .vz)) xw) := by
    simp only [A, xw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map, Term.app2,
      mul_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let ms := mul_succ (Premises := Premises) adm xw vz
    let ih_congr := qfer_nat_nf (by rfl) (by rfl) I_comb
      (add_vz_w_subst0 xw (Term.app2 Term.mul xw vz))
      (add_vz_w_subst0 xw (Term.app2 Term.mul vz xw))
    let msl := mul_succ_l (Premises := Premises) adm vz xw
    let c1 := .syllogism (pair_h (weaken_intro_h ms) ih_congr) .trans0
    .syllogism (pair_h c1 (weaken_intro_h (.mp msl .sym0))) .trans0)
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.mul x y) (Term.app2 Term.mul y x) := by
    simp only [A, xw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map, Term.app2,
      mul_closed_subst', xw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

/-- 1 * y = y. From mul_succ_l: S0 * y = 0*y + y = 0 + y = y. -/
def mul_one_l (y : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (.app .succ .zero) y) y) :=
  -- S0 * y = 0*y + y
  let h1 := mul_succ_l (Premises := Premises) adm .zero y
  -- 0*y = 0
  let h2 := mul_zero_l adm y
  -- 0*y + y = 0 + y
  let h3 := add_congr_l h2 y
  -- 0 + y = y
  let h4 := add_zero_l adm y
  -- Chain: S0*y = 0*y + y = 0 + y = y
  let c1 := .mp (.mp h3 (.mp h1 and_intro)) .trans0
  .mp (.mp h4 (.mp c1 and_intro)) .trans0

/-- x * 1 = x. From mul_one_l and mul_comm. -/
def mul_one_r (x : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul x (.app .succ .zero)) x) :=
  let c := mul_comm adm x (.app .succ .zero)
  let m := mul_one_l adm x
  .mp (.mp m (.mp c and_intro)) .trans0

-- ── Congruence helpers for mul ──────────────────────────────────────────────

private theorem mul_vz_w_subst0 (u s : Term F Γ Ty.nat) :
    (Term.app2 Term.mul (.var .vz) u.weaken : Term F (Ty.nat :: Γ) _).subst0 s =
    Term.app2 Term.mul s u := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst']
  have := Term.weaken_subst0 u s; simp only [Term.subst0] at this; rw [this]

private theorem mul_w_vz_subst0 (u s : Term F Γ Ty.nat) :
    (Term.app2 Term.mul u.weaken (.var .vz) : Term F (Ty.nat :: Γ) _).subst0 s =
    Term.app2 Term.mul u s := by
  simp only [Term.subst0, Term.app2, Term.subst, Term.subst0_map, mul_closed_subst']
  have := Term.weaken_subst0 u s; simp only [Term.subst0] at this; rw [this]

/-- s =₀ t → mul(s, u) =₀ mul(t, u). -/
def mul_congr_l {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul s u) (Term.app2 Term.mul t u)) :=
  qfer_no_premise_nat_nf h (mul_vz_w_subst0 u s) (mul_vz_w_subst0 u t)

/-- s =₀ t → mul(u, s) =₀ mul(u, t). -/
def mul_congr_r (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises (Formula.eq0 (Term.app2 Term.mul u s) (Term.app2 Term.mul u t)) :=
  qfer_no_premise_nat_nf h (mul_w_vz_subst0 u s) (mul_w_vz_subst0 u t)

-- ── mul_add and mul_assoc ───────────────────────────────────────────────────

/-- x * (a + b) = x*a + x*b. By induction on b. -/
def mul_add (x a b : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul x (Term.app2 Term.add a b))
      (Term.app2 Term.add (Term.app2 Term.mul x a) (Term.app2 Term.mul x b))) :=
  let xw := x.weaken (σ := Ty.nat)
  let aw := a.weaken (σ := Ty.nat)
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  have aw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) a.weaken = a := Term.weaken_subst0 a
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0
      (Term.app2 Term.mul xw (Term.app2 Term.add aw (.var .vz)))
      (Term.app2 Term.add (Term.app2 Term.mul xw aw) (Term.app2 Term.mul xw (.var .vz)))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0
        (Term.app2 Term.mul x (Term.app2 Term.add a Term.zero))
        (Term.app2 Term.add (Term.app2 Term.mul x a) (Term.app2 Term.mul x Term.zero)) := by
    simp only [A, xw, aw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst', mul_closed_subst', xw_subst0, aw_subst0]
  have base := base_nf ▸ (
    -- LHS: mul(x, add(a, 0)) =₀ mul(x, a)
    let lhs := mul_congr_r x (add_zero_r adm a)
    -- mul(x, 0) =₀ 0
    let mz := mul_zero adm x
    -- add(mul(x,a), mul(x,0)) =₀ add(mul(x,a), 0)
    let rhs1 := add_congr_r (Term.app2 Term.mul x a) mz
    -- add(mul(x,a), 0) =₀ mul(x,a)
    let rhs2 := add_zero_r adm (Term.app2 Term.mul x a)
    -- chain: add(mul(x,a), mul(x,0)) =₀ mul(x,a)
    let rhs := .mp (.mp rhs2 (.mp rhs1 and_intro)) .trans0
    -- combine: mul(x,a) =₀ add(mul(x,a), mul(x,0)) → mul(x, add(a,0)) =₀ add(mul(x,a), mul(x,0))
    .mp (.mp (.mp rhs .sym0) (.mp lhs and_intro)) .trans0)
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0
        (Term.app2 Term.mul xw (Term.app2 Term.add aw (.app .succ (.var .vz))))
        (Term.app2 Term.add (Term.app2 Term.mul xw aw) (Term.app2 Term.mul xw (.app .succ (.var .vz)))) := by
    simp only [A, xw, aw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, add_closed_subst', mul_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- mul(xw, add(aw, Svz)) =₀ mul(xw, S(add(aw, vz))) via mul_congr_r(add_succ)
    let as1 := add_succ adm aw vz
    let step1 := mul_congr_r xw as1
    -- mul(xw, S(add(aw, vz))) =₀ add(mul(xw, add(aw, vz)), xw) via mul_succ
    let ms := mul_succ (Premises := Premises) adm xw (Term.app2 Term.add aw vz)
    -- chain: mul(xw, add(aw, Svz)) =₀ add(mul(xw, add(aw,vz)), xw)
    let c1 := .mp (.mp ms (.mp step1 and_intro)) .trans0
    -- IH gives: add(mul(xw, add(aw,vz)), xw) =₀ add(add(mul(xw,aw), mul(xw,vz)), xw)
    -- Use add_congr_l(IH) for this
    -- We go: IH → mul(xw, add(aw,vz)) =₀ add(mul(xw,aw), mul(xw,vz))
    --        → add(..., xw) =₀ add(add(mul(xw,aw), mul(xw,vz)), xw)  via add_congr_l
    let ih_add_congr := qfer_nat_nf (by rfl) (by rfl) I_comb
      (add_vz_w_subst0 xw (Term.app2 Term.mul xw (Term.app2 Term.add aw vz)))
      (add_vz_w_subst0 xw (Term.app2 Term.add (Term.app2 Term.mul xw aw) (Term.app2 Term.mul xw vz)))
    -- chain lhs: A → mul(xw, add(aw,Svz)) =₀ add(add(mul(xw,aw), mul(xw,vz)), xw)
    let lhs := .syllogism (pair_h (weaken_intro_h c1) ih_add_congr) .trans0
    -- add_assoc: add(add(mul(xw,aw), mul(xw,vz)), xw) =₀ add(mul(xw,aw), add(mul(xw,vz), xw))
    let assoc := add_assoc adm (Term.app2 Term.mul xw aw) (Term.app2 Term.mul xw vz) xw
    -- mul_succ sym: mul(xw, Svz) =₀ add(mul(xw,vz), xw)
    let mss := .mp (mul_succ (Premises := Premises) adm xw vz) .sym0
    -- add_congr_r: add(mul(xw,aw), mul(xw,Svz)) =₀ add(mul(xw,aw), add(mul(xw,vz), xw))
    let rhs_congr := add_congr_r (Term.app2 Term.mul xw aw) mss
    -- chain rhs: add(add(mul(xw,aw), mul(xw,vz)), xw) =₀ add(mul(xw,aw), mul(xw,Svz))
    -- assoc then rhs_congr (which goes add(xa,add(xb,xw)) → add(xa,mul(xw,Svz))):
    let c2 := .mp (.mp rhs_congr (.mp assoc and_intro)) .trans0
    .syllogism (pair_h lhs (weaken_intro_h c2)) .trans0)
  have inst_nf : A.subst0 b =
      Formula.eq0
        (Term.app2 Term.mul x (Term.app2 Term.add a b))
        (Term.app2 Term.add (Term.app2 Term.mul x a) (Term.app2 Term.mul x b)) := by
    simp only [A, xw, aw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst', mul_closed_subst', xw_subst0, aw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax b)

/-- (x * y) * z = x * (y * z). By induction on z. -/
def mul_assoc (x y z : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (Term.app2 Term.mul x y) z)
      (Term.app2 Term.mul x (Term.app2 Term.mul y z))) :=
  let xw := x.weaken (σ := Ty.nat)
  let yw := y.weaken (σ := Ty.nat)
  let xyw := Term.app2 Term.mul xw yw
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  have yw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) y.weaken = y := Term.weaken_subst0 y
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0
      (Term.app2 Term.mul xyw (.var .vz))
      (Term.app2 Term.mul xw (Term.app2 Term.mul yw (.var .vz)))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0
        (Term.app2 Term.mul (Term.app2 Term.mul x y) Term.zero)
        (Term.app2 Term.mul x (Term.app2 Term.mul y Term.zero)) := by
    simp only [A, xw, yw, xyw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst', mul_closed_subst', xw_subst0, yw_subst0]
  have base := base_nf ▸ (
    -- mul(x*y, 0) =₀ 0
    let lhs := mul_zero adm (Term.app2 Term.mul x y)
    -- mul(y, 0) =₀ 0
    let myz := mul_zero adm y
    -- mul(x, mul(y, 0)) =₀ mul(x, 0) via mul_congr_r
    let rhs1 := mul_congr_r x myz
    -- mul(x, 0) =₀ 0
    let rhs2 := mul_zero adm x
    -- chain: mul(x, mul(y, 0)) =₀ 0
    let rhs := .mp (.mp rhs2 (.mp rhs1 and_intro)) .trans0
    .mp (.mp (.mp rhs .sym0) (.mp lhs and_intro)) .trans0)
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0
        (Term.app2 Term.mul xyw (.app .succ (.var .vz)))
        (Term.app2 Term.mul xw (Term.app2 Term.mul yw (.app .succ (.var .vz)))) := by
    simp only [A, xw, yw, xyw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, add_closed_subst', mul_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- IH: mul(xyw, vz) =₀ mul(xw, mul(yw, vz))
    -- mul(xyw, Svz) =₀ add(mul(xyw, vz), xyw) via mul_succ
    let ms := mul_succ (Premises := Premises) adm xyw vz
    -- IH gives: add(mul(xyw, vz), xyw) =₀ add(mul(xw, mul(yw, vz)), xyw) via add_congr_l(IH)
    let ih_add_congr := qfer_nat_nf (by rfl) (by rfl) I_comb
      (add_vz_w_subst0 xyw (Term.app2 Term.mul xyw vz))
      (add_vz_w_subst0 xyw (Term.app2 Term.mul xw (Term.app2 Term.mul yw vz)))
    -- chain: A → mul(xyw, Svz) =₀ add(mul(xw, mul(yw, vz)), xyw)
    let lhs := .syllogism (pair_h (weaken_intro_h ms) ih_add_congr) .trans0
    -- mul_add: mul(xw, add(mul(yw, vz), yw)) =₀ add(mul(xw, mul(yw,vz)), mul(xw, yw))
    -- We need: add(mul(xw, mul(yw,vz)), xyw) =₀ mul(xw, add(mul(yw,vz), yw))
    -- i.e. mul_add reversed: mul(xw, add(mul(yw,vz), yw)) =₀ add(mul(xw,mul(yw,vz)), mul(xw,yw))
    --      and xyw = mul(xw, yw), so add(mul(xw, mul(yw,vz)), xyw) = add(mul(xw,mul(yw,vz)), mul(xw,yw))
    -- So we need sym(mul_add): add(mul(xw,mul(yw,vz)), mul(xw,yw)) =₀ mul(xw, add(mul(yw,vz), yw))
    let ma := .mp (mul_add (Premises := Premises) adm xw (Term.app2 Term.mul yw vz) yw) .sym0
    -- mul_succ: mul(yw, Svz) =₀ add(mul(yw, vz), yw)
    let msy := mul_succ (Premises := Premises) adm yw vz
    -- mul_congr_r: mul(xw, mul(yw, Svz)) =₀ mul(xw, add(mul(yw,vz), yw))
    let rhs_congr := mul_congr_r xw (.mp msy .sym0)
    -- chain rhs: add(mul(xw,mul(yw,vz)), mul(xw,yw)) =₀ mul(xw, mul(yw, Svz))
    -- ma ends at mul(xw, add(mul(yw,vz), yw)), rhs_congr starts there:
    let c_rhs := .mp (.mp rhs_congr (.mp ma and_intro)) .trans0
    -- full chain: A → mul(xyw, Svz) =₀ mul(xw, mul(yw, Svz))
    .syllogism (pair_h lhs (weaken_intro_h c_rhs)) .trans0)
  have inst_nf : A.subst0 z =
      Formula.eq0
        (Term.app2 Term.mul (Term.app2 Term.mul x y) z)
        (Term.app2 Term.mul x (Term.app2 Term.mul y z)) := by
    simp only [A, xw, yw, xyw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, add_closed_subst', mul_closed_subst', xw_subst0, yw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax z)

-- ── Truncated subtraction against multiplication, and `geq` ────────────────
--
-- `monus` had a theory of its own — `monus_zero/succ/cancel/self/zero_l/succ_l`,
-- `monus_eq_zero_antisym`, `monus_disjunct` — but nothing relating it to `mul`, and `geq` had
-- no theory at all. These five are what the ℚ order theory needs: `add_Q`'s opposite-sign
-- branch takes an `abs_diff` of two cross products and compares them with `geq`, and both
-- have to survive being scaled by a denominator.

/-- Transitivity of `=₀` in the shape the equational chains are actually written in. The
development spells this out as `.mp (.mp h₂ (.mp h₁ and_intro)) .trans0` several hundred
times. -/
def qtrans {a b c : Term F Γ Ty.nat}
    (h₁ : Derivable F EqX al Premises (Formula.eq0 a b))
    (h₂ : Derivable F EqX al Premises (Formula.eq0 b c)) :
    Derivable F EqX al Premises (Formula.eq0 a c) :=
  .mp (.mp h₂ (.mp h₁ and_intro)) .trans0

private def monus_congr_fst {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) (u : Term F Γ Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus s u) (Term.app2 Term.monus t u)) :=
  qfer_no_premise_nat_nf h (monus_subst0_lw_nf u s) (monus_subst0_lw_nf u t)

private def monus_congr_snd (u : Term F Γ Ty.nat) {s t : Term F Γ Ty.nat}
    (h : Derivable F EqX al Premises (Formula.eq0 s t)) :
    Derivable F EqX al Premises
      (Formula.eq0 (Term.app2 Term.monus u s) (Term.app2 Term.monus u t)) :=
  qfer_no_premise_nat_nf h (monus_subst0_rw_nf u s) (monus_subst0_rw_nf u t)

/-- `a ∸ (b + c) =₀ (a ∸ b) ∸ c`. By induction on `c`: the successor step is `monus_succ` on
both sides against `add_succ` on the left, with the two `pd`s matched by the IH. -/
def monus_monus (a b c : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.monus a (Term.app2 Term.add b c))
      (Term.app2 Term.monus (Term.app2 Term.monus a b) c)) :=
  let aw := a.weaken (σ := Ty.nat)
  let bw := b.weaken (σ := Ty.nat)
  have aw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) a.weaken = a := Term.weaken_subst0 a
  have bw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) b.weaken = b := Term.weaken_subst0 b
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.monus aw (Term.app2 Term.add bw (.var .vz)))
      (Term.app2 Term.monus (Term.app2 Term.monus aw bw) (.var .vz))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.monus a (Term.app2 Term.add b Term.zero))
        (Term.app2 Term.monus (Term.app2 Term.monus a b) Term.zero) := by
    simp only [A, aw, bw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst', add_closed_subst', aw_subst0, bw_subst0]
  have base := base_nf ▸ (
    -- a ∸ (b+0) = a ∸ b = (a∸b) ∸ 0
    qtrans (monus_congr_snd a (add_zero_r adm b))
      (.mp (monus_zero adm (Term.app2 Term.monus a b)) .sym0))
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.monus aw (Term.app2 Term.add bw (.app .succ (.var .vz))))
        (Term.app2 Term.monus (Term.app2 Term.monus aw bw) (.app .succ (.var .vz))) := by
    simp only [A, aw, bw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, monus_closed_subst', add_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let vz : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let ab := Term.app2 Term.monus aw bw
    -- a ∸ (b + Sc) = a ∸ S(b+c) = pd(a ∸ (b+c))
    let u1 := qtrans (monus_congr_snd aw (add_succ adm bw vz))
      (monus_succ adm aw (Term.app2 Term.add bw vz))
    -- IH → pd(a ∸ (b+c)) = pd((a∸b) ∸ c)
    let u2 := qfer_nat_nf (by rfl) (by rfl) I_comb (r := .app Term.pd (.var .vz)) rfl rfl
    -- pd((a∸b) ∸ c) = (a∸b) ∸ Sc
    let u3 := .mp (monus_succ adm ab vz) .sym0
    let c1 := .syllogism (pair_h (weaken_intro_h u1) u2) .trans0
    .syllogism (pair_h c1 (weaken_intro_h u3)) .trans0)
  have inst_nf : A.subst0 c =
      Formula.eq0 (Term.app2 Term.monus a (Term.app2 Term.add b c))
        (Term.app2 Term.monus (Term.app2 Term.monus a b) c) := by
    simp only [A, aw, bw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, monus_closed_subst', add_closed_subst', aw_subst0, bw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax c)

/-- `pd(m) · k =₀ m · k ∸ k`. By induction on `m`, though the successor step does not use the
induction hypothesis: `pd(Sm)·k = m·k` and `(Sm)·k ∸ k = (m·k + k) ∸ k = m·k` both hold
outright. Induction is only how the `m = 0` / `m = S_` split is taken. -/
def pd_mul (m k : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (.app Term.pd m) k)
      (Term.app2 Term.monus (Term.app2 Term.mul m k) k)) :=
  let kw := k.weaken (σ := Ty.nat)
  have kw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) k.weaken = k := Term.weaken_subst0 k
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul (.app Term.pd (.var .vz)) kw)
      (Term.app2 Term.monus (Term.app2 Term.mul (.var .vz) kw) kw)
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.mul (.app Term.pd Term.zero) k)
        (Term.app2 Term.monus (Term.app2 Term.mul Term.zero k) k) := by
    simp only [A, kw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', pd_closed_subst, kw_subst0]
  have base := base_nf ▸ (
    -- both sides are `0`
    let lhs := qtrans (mul_congr_l (pd_zero (Γ := Γ)) k) (mul_zero_l adm k)
    let rhs := qtrans (monus_congr_fst (mul_zero_l adm k) k) (monus_zero_l adm k)
    qtrans lhs (.mp rhs .sym0))
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.mul (.app Term.pd (.app .succ (.var .vz))) kw)
        (Term.app2 Term.monus (Term.app2 Term.mul (.app .succ (.var .vz)) kw) kw) := by
    simp only [A, kw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', pd_closed_subst, weaken_substVar0]
  have step_body := step_nf ▸ weaken_intro_h (
    let mv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    -- pd(Sm)·k = m·k
    let s1 := mul_congr_l (pd_succ adm mv) kw
    -- (Sm)·k ∸ k = (m·k + k) ∸ k = m·k
    let s2 := qtrans (monus_congr_fst (mul_succ_l adm mv kw) kw)
      (monus_cancel adm (Term.app2 Term.mul mv kw) kw)
    qtrans s1 (.mp s2 .sym0))
  have inst_nf : A.subst0 m =
      Formula.eq0 (Term.app2 Term.mul (.app Term.pd m) k)
        (Term.app2 Term.monus (Term.app2 Term.mul m k) k) := by
    simp only [A, kw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', pd_closed_subst, kw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax m)

/-- `(x ∸ y) · k =₀ x·k ∸ y·k`. By induction on `y`: the successor step turns the left side
into `(x∸y)·k ∸ k` by `monus_succ` and `pd_mul`, and the right side into `(x·k ∸ y·k) ∸ k` by
`mul_succ_l` and `monus_monus`; the induction hypothesis matches the two. -/
def monus_mul_distrib (x y k : Term F Γ Ty.nat) :
    Derivable F EqX al Premises (Formula.eq0
      (Term.app2 Term.mul (Term.app2 Term.monus x y) k)
      (Term.app2 Term.monus (Term.app2 Term.mul x k) (Term.app2 Term.mul y k))) :=
  let xw := x.weaken (σ := Ty.nat)
  let kw := k.weaken (σ := Ty.nat)
  have xw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) x.weaken = x := Term.weaken_subst0 x
  have kw_subst0 : ∀ s : Term F Γ Ty.nat,
      Term.subst (fun {τ} ↦ Term.subst0_map s) k.weaken = k := Term.weaken_subst0 k
  let A : Formula F (Ty.nat :: Γ) :=
    Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.monus xw (.var .vz)) kw)
      (Term.app2 Term.monus (Term.app2 Term.mul xw kw) (Term.app2 Term.mul (.var .vz) kw))
  have base_nf : A.subst0 Term.zero =
      Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.monus x Term.zero) k)
        (Term.app2 Term.monus (Term.app2 Term.mul x k) (Term.app2 Term.mul Term.zero k)) := by
    simp only [A, xw, kw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', xw_subst0, kw_subst0]
  have base := base_nf ▸ (
    -- both sides are `x·k`
    let lhs := mul_congr_l (monus_zero adm x) k
    let rhs := qtrans (monus_congr_snd (Term.app2 Term.mul x k) (mul_zero_l adm k))
      (monus_zero adm (Term.app2 Term.mul x k))
    qtrans lhs (.mp rhs .sym0))
  have step_nf : Formula.substVar0 A (.app .succ (.var .vz)) =
      Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.monus xw (.app .succ (.var .vz))) kw)
        (Term.app2 Term.monus (Term.app2 Term.mul xw kw)
          (Term.app2 Term.mul (.app .succ (.var .vz)) kw)) := by
    simp only [A, xw, kw, Formula.substVar0, Formula.substF, Term.subst, Term.substVar0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', weaken_substVar0]
  have step_body := step_nf ▸ (
    let yv : Term F (Ty.nat :: Γ) Ty.nat := .var .vz
    let xy := Term.app2 Term.monus xw yv
    let xk := Term.app2 Term.mul xw kw
    let yk := Term.app2 Term.mul yv kw
    -- (x ∸ Sy)·k = pd(x∸y)·k = (x∸y)·k ∸ k
    let u1 := qtrans (mul_congr_l (monus_succ adm xw yv) kw) (pd_mul adm xy kw)
    -- IH → (x∸y)·k ∸ k = (x·k ∸ y·k) ∸ k
    let u2 := qfer_nat_nf (by rfl) (by rfl) I_comb
      (monus_subst0_lw_nf kw (Term.app2 Term.mul xy kw))
      (monus_subst0_lw_nf kw (Term.app2 Term.monus xk yk))
    -- x·k ∸ (Sy)·k = x·k ∸ (y·k + k) = (x·k ∸ y·k) ∸ k, reversed
    let u3 := .mp (qtrans (monus_congr_snd xk (mul_succ_l adm yv kw))
      (monus_monus adm xk yk kw)) .sym0
    let c1 := .syllogism (pair_h (weaken_intro_h u1) u2) .trans0
    .syllogism (pair_h c1 (weaken_intro_h u3)) .trans0)
  have inst_nf : A.subst0 y =
      Formula.eq0 (Term.app2 Term.mul (Term.app2 Term.monus x y) k)
        (Term.app2 Term.monus (Term.app2 Term.mul x k) (Term.app2 Term.mul y k)) := by
    simp only [A, xw, kw, Formula.subst0, Formula.substF, Term.subst, Term.subst0_map,
      Term.app2, mul_closed_subst', monus_closed_subst', xw_subst0, kw_subst0]
  inst_nf ▸ .mp (Derivable.induction base (univ_gen step_body)) (.forall_ax y)

end ArithProps

-- ============================================================================
-- Section 6: eq0 decidability
-- ============================================================================
-- From arithmetic.tex Prop prop:eq0-decidable.
-- This is proved by induction and does NOT require the arithmetic infrastructure.

def eq0_decidable {Γ : Ctx ι} :
    Derivable F EqX al Premises (Formula.all Ty.nat
      (Formula.eq0 (Γ := Ty.nat :: Γ) (.var .vz) Term.zero ∨ᶠ
       ¬ᶠFormula.eq0 (.var .vz) Term.zero)) :=
  eq0_decidable'

-- ============================================================================
-- Section 7: QF decision function (prop:qf-equiv-term from wehax.tex)
-- ============================================================================
-- For each QF formula A₀, we construct a term qf_term A₀ such that
-- qf_term A₀ x̄ =₀ 0 ↔ A₀(x̄) in WE-HA^ω.

section QFDecision

/-- The decision term for a QF formula A₀.
    Defined by structural recursion on A₀:
    - bot      → S0         (always 1 ≠ 0, since ⊥ is never true)
    - eq0 s t  → |s − t|   (= 0 iff s = t)
    - and A B  → t_A + t_B  (= 0 iff both are 0)
    - or  A B  → t_A · t_B  (= 0 iff at least one is 0)
    - imp A B  → sḡ(t_A) · t_B  (= 0 iff t_A = 0 → t_B = 0)
    - all/ex   → not QF (undefined; return 0 as a stub) -/
def qf_term {Γ : Ctx ι} : Formula F Γ → Term F Γ Ty.nat
  | .bot        => Term.app Term.succ Term.zero      -- S0 ≠ 0
  | .eq0 s t    => Term.app2 Term.abs_diff s t       -- |s − t|
  | .and A B    => Term.app2 Term.add (qf_term A) (qf_term B)
  | .or  A B    => Term.app2 Term.mul (qf_term A) (qf_term B)
  | .imp A B    => Term.app2 Term.mul (Term.app Term.sg_bar (qf_term A)) (qf_term B)
  | .all _ _    => Term.zero   -- not QF; stub
  | .ex  _ _    => Term.zero   -- not QF; stub

/-- The decision term correctly encodes A₀: qf_term A₀ =₀ 0 ↔ A₀.
    Proved by structural induction on A₀ (using the arithmetic properties from §5). -/
def qf_term_correct {Γ : Ctx ι} {A : Formula F Γ} (hqf : A.isQF = true) :
    Derivable F EqX al Premises
      ((Formula.eq0 (qf_term A) Term.zero →ᶠ A) ∧ᶠ (A →ᶠ Formula.eq0 (qf_term A) Term.zero)) :=
  match A with
  | .bot =>
    -- qf_term ⊥ = S0.  S0 =₀ 0 ↔ ⊥.
    -- Forward: eq0(S0)0 → ⊥ from succ_ne_zero at 0.  Backward: exfalso.
    let fwd : Derivable F EqX al Premises (Formula.eq0 (Term.app Term.succ Term.zero) Term.zero →ᶠ ⊥ᶠ) :=
      .mp .succ_ne_zero (.forall_ax Term.zero)
    let bwd : Derivable F EqX al Premises (⊥ᶠ →ᶠ Formula.eq0 (Term.app Term.succ Term.zero) Term.zero) :=
      .exfalso
    .mp bwd (.mp fwd and_intro)
  | .eq0 s t =>
    -- qf_term (s =₀ t) = |s − t|.  |s − t| =₀ 0 ↔ s =₀ t.
    abs_diff_eq_zero_iff adm s t
  | .and A B =>
    -- qf_term (A ∧ B) = t_A + t_B.  t_A + t_B = 0 ↔ t_A = 0 ∧ t_B = 0 ↔ A ∧ B.
    have hAB : A.isQF = true ∧ B.isQF = true := by
      simp only [Formula.isQF, Bool.and_eq_true] at hqf; exact hqf
    have ihA := qf_term_correct hAB.1
    have ihB := qf_term_correct hAB.2
    let add_iff := add_eq_zero_iff adm (qf_term A) (qf_term B)
    let add_fwd := Derivable.mp add_iff .and_weak
    let add_bwd := Derivable.mp add_iff and_proj2
    let ihA_fwd := Derivable.mp ihA .and_weak
    let ihA_bwd := Derivable.mp ihA and_proj2
    let ihB_fwd := Derivable.mp ihB .and_weak
    let ihB_bwd := Derivable.mp ihB and_proj2
    -- Forward: add(tA,tB)=0 → tA=0∧tB=0 → A∧B
    let fwd := Derivable.syllogism add_fwd
      (pair_h (Derivable.syllogism .and_weak ihA_fwd) (Derivable.syllogism and_proj2 ihB_fwd))
    -- Backward: A∧B → tA=0∧tB=0 → add(tA,tB)=0
    let bwd := Derivable.syllogism
      (pair_h (Derivable.syllogism .and_weak ihA_bwd) (Derivable.syllogism and_proj2 ihB_bwd))
      add_bwd
    .mp bwd (.mp fwd and_intro)
  | .or A B =>
    -- qf_term (A ∨ B) = t_A · t_B.  t_A · t_B = 0 ↔ t_A = 0 ∨ t_B = 0 ↔ A ∨ B.
    have hAB : A.isQF = true ∧ B.isQF = true := by
      simp only [Formula.isQF, Bool.and_eq_true] at hqf; exact hqf
    have ihA := qf_term_correct hAB.1
    have ihB := qf_term_correct hAB.2
    let mul_iff := mul_eq_zero_iff adm (qf_term A) (qf_term B)
    let mul_fwd := Derivable.mp mul_iff .and_weak
    let mul_bwd := Derivable.mp mul_iff and_proj2
    let ihA_fwd := Derivable.mp ihA .and_weak
    let ihA_bwd := Derivable.mp ihA and_proj2
    let ihB_fwd := Derivable.mp ihB .and_weak
    let ihB_bwd := Derivable.mp ihB and_proj2
    -- Forward: mul(tA,tB)=0 → tA=0∨tB=0 → A∨B
    let fwd := Derivable.syllogism mul_fwd
      (or_elim_rule (.syllogism ihA_fwd .or_weak) (.syllogism ihB_fwd or_inr))
    -- Backward: A∨B → tA=0∨tB=0 → mul(tA,tB)=0
    let bwd := Derivable.syllogism
      (or_elim_rule (.syllogism ihA_bwd .or_weak) (.syllogism ihB_bwd or_inr))
      mul_bwd
    .mp bwd (.mp fwd and_intro)
  | .imp A B =>
    -- qf_term (A → B) = sḡ(t_A) · t_B.  sḡ(t_A)·t_B=0 ↔ (t_A=0→t_B=0) ↔ (A→B).
    have hAB : A.isQF = true ∧ B.isQF = true := by
      simp only [Formula.isQF, Bool.and_eq_true] at hqf; exact hqf
    have ihA := qf_term_correct hAB.1
    have ihB := qf_term_correct hAB.2
    let sgm_iff := sg_bar_mul_eq_zero_iff adm (qf_term A) (qf_term B)
    let sgm_fwd := Derivable.mp sgm_iff .and_weak       -- sḡ(tA)·tB=0 → (tA=0→tB=0)
    let sgm_bwd := Derivable.mp sgm_iff and_proj2        -- (tA=0→tB=0) → sḡ(tA)·tB=0
    let ihA_fwd := Derivable.mp ihA .and_weak             -- tA=0 → A
    let ihA_bwd := Derivable.mp ihA and_proj2             -- A → tA=0
    let ihB_fwd := Derivable.mp ihB .and_weak             -- tB=0 → B
    let ihB_bwd := Derivable.mp ihB and_proj2             -- B → tB=0
    -- Forward: sḡ(tA)·tB=0 → (tA=0→tB=0) → (A→B)
    -- (tA=0→tB=0) ∧ A → tA=0 ∧ (tA=0→tB=0) → tB=0 → B
    let fwd_inner : Derivable F EqX al Premises
        ((Formula.eq0 (qf_term A) Term.zero →ᶠ Formula.eq0 (qf_term B) Term.zero) →ᶠ A →ᶠ B) :=
      .exportation (.syllogism
        (.syllogism (pair_h (.syllogism and_proj2 ihA_bwd) .and_weak)
          (.syllogism .and_perm (.importation mp_form)))
        ihB_fwd)
    let fwd := .syllogism sgm_fwd fwd_inner
    -- Backward: (A→B) → (tA=0→tB=0) → sḡ(tA)·tB=0
    let bwd_inner : Derivable F EqX al Premises
        ((A →ᶠ B) →ᶠ Formula.eq0 (qf_term A) Term.zero →ᶠ Formula.eq0 (qf_term B) Term.zero) :=
      .exportation (.syllogism
        (.syllogism (pair_h (.syllogism and_proj2 ihA_fwd) .and_weak)
          (.syllogism .and_perm (.importation mp_form)))
        ihB_bwd)
    let bwd := .syllogism bwd_inner sgm_bwd
    .mp bwd (.mp fwd and_intro)
  | .all _ _ => by simp [Formula.isQF] at hqf
  | .ex  _ _ => by simp [Formula.isQF] at hqf
end QFDecision

-- ============================================================================
-- Section 8: QF-LEM and double-negation elimination
-- ============================================================================
-- From wehax.tex Prop prop:qf-lem and Cor cor:qf-double-neg-elim.

section QFLEM

/-- Law of excluded middle for QF formulas: ⊢ A₀ ∨ ¬A₀.

    Proof: by qf_term_correct, A₀ ↔ (t_{A₀} = 0).
    By eq0_decidable, ⊢ t_{A₀} = 0 ∨ t_{A₀} ≠ 0.
    Substituting the equivalence gives A₀ ∨ ¬A₀. -/
def qf_lem {Γ : Ctx ι} {A : Formula F Γ} (hqf : A.isQF = true) :
    Derivable F EqX al Premises (A ∨ᶠ ¬ᶠA) :=
  -- qf_term_correct: eq0(t_A, 0) ↔ A
  let corr := qf_term_correct (adm := adm) hqf
  let fwd : Derivable F EqX al Premises (Formula.eq0 (qf_term A) Term.zero →ᶠ A) :=
    .mp corr .and_weak
  let bwd : Derivable F EqX al Premises (A →ᶠ Formula.eq0 (qf_term A) Term.zero) :=
    .mp corr and_proj2
  -- eq0_decidable instantiated at qf_term A: ⊢ eq0(t_A, 0) ∨ ¬eq0(t_A, 0)
  let dec := @eq0_decidable ι F EqX al Premises Γ
  let dec_at := .mp dec (.forall_ax (qf_term A))
  -- Two cases from the decidability
  let case_t : Derivable F EqX al Premises (Formula.eq0 (qf_term A) Term.zero →ᶠ A ∨ᶠ ¬ᶠA) :=
    .syllogism fwd .or_weak
  let case_f : Derivable F EqX al Premises (¬ᶠFormula.eq0 (qf_term A) Term.zero →ᶠ A ∨ᶠ ¬ᶠA) :=
    .syllogism (contrapositive bwd) or_inr
  .mp dec_at (or_elim_rule case_t case_f)

/-- Double-negation elimination for QF formulas: ⊢ ¬¬A₀ → A₀.

    Proof: from qf_lem, we have A₀ ∨ ¬A₀.
    Use or-elimination: if A₀, done; if ¬A₀, then ¬¬A₀ gives ⊥ by mp, then A₀ by exfalso. -/
def qf_double_neg_elim {Γ : Ctx ι} {A : Formula F Γ} (hqf : A.isQF = true) :
    Derivable F EqX al Premises (¬ᶠ¬ᶠA →ᶠ A) :=
  let lem := qf_lem (Premises := Premises) (adm := adm) hqf
  -- Case A: from A ignore ¬¬A and return A (K combinator)
  let case_A : Derivable F EqX al Premises (A →ᶠ ¬ᶠ¬ᶠA →ᶠ A) :=
    .exportation .and_weak
  -- Case ¬A: from ¬A ∧ ¬¬A derive ⊥ via eval_h, then A via exfalso
  let case_neg_A : Derivable F EqX al Premises (¬ᶠA →ᶠ ¬ᶠ¬ᶠA →ᶠ A) :=
    .exportation (.syllogism
      (eval_h (.syllogism .and_perm .and_weak) .and_weak)
      .exfalso)
  .mp lem (or_elim_rule case_A case_neg_A)

end QFLEM

end Metatheorems
