/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.StrongMajorizability
import Metatheorems.NDTranslation


namespace Metatheorems

/-!
# General Logical Metatheorem (Theorem 6.1)

The general metatheorem: from a classical proof of
`∀x^ρ (∀u⁰ B(x,u) → ∃v⁰ C(x,v))`, extract a computable bound Φ such that
`∀u ≤ Φ(x*) B(x,u) → ∃v ≤ Φ(x*) C(x,v)` for all x* ≥*_ρ x.

The proof factors into:
1. **Core bound construction** (`metatheorem_core`): given semantic witnesses
   U, V with `∀x, B(x, U(x)) → C(x, V(x))`, construct Φ using majorizability.
2. **Witness extraction**: connect `nd_soundness` to the core via Dialectica
   witness extraction for the specific formula shape.
-/

open Formula

-- ============================================================================
-- Dialectica matrix reduction for QF ∨-free formulas
-- ============================================================================

/-- For QF ∨-free formulas, the Dialectica matrix equals the formula's
    semantic interpretation, regardless of witness and counter values.
    This is because W(A) and C(A) are subsingletons (all Unit). -/
theorem dialecticaMatrix_iff_interpFormula
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι}
    (A : Formula F Γ) (hqf : A.isQF = true) (hvf : A.isVFree = true)
    (env : Ctx.interpret X Γ) (w : 𝕎 X A) (c : ℂ X A) :
    dialecticaMatrix si A env w c ↔ Formula.interpret si A env :=
  match A, hqf, hvf, env, w, c with
  | .bot, _, _, _, _, _ => Iff.rfl
  | .eq0 .., _, _, _, _, _ => Iff.rfl
  | .and A B, hqf, hvf, env, (wA, wB), (cA, cB) => by
    simp only [isQF, isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    exact Iff.and
      (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA cA)
      (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env wB cB)
  | .or .., _, hvf, _, _, _ => by simp [isVFree] at hvf
  | .imp A B, hqf, hvf, env, (f, g), (wA, cB) => by
    simp only [isQF, isVFree, Bool.and_eq_true] at hqf hvf
    simp only [dialecticaMatrix, Formula.interpret]
    constructor
    · intro h hA
      have := (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA (g wA cB)).mpr hA
      exact (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env (f wA) cB).mp (h this)
    · intro h hM
      have := (dialecticaMatrix_iff_interpFormula si A hqf.1 hvf.1 env wA (g wA cB)).mp hM
      exact (dialecticaMatrix_iff_interpFormula si B hqf.2 hvf.2 env (f wA) cB).mpr (h this)

-- ============================================================================
-- General Metatheorem (Theorem 6.1)
-- ============================================================================

/-- **General Metatheorem** (Theorem 6.1), Dialectica step.

Takes a derivation in the extended system (post-NT) and applies Dialectica
directly. The matrix has no ¬¬ layers, making extraction clean.
The full metatheorem composes `negTrans_sound` (external) with this. -/
def general_metatheorem
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.extended Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  -- Step 1: Apply Dialectica directly (no NT)
  let r := @dialectica_soundness_ctx' ι X F si EqX eqxi Premises premise_realizer _ _ prf
  -- r : ∀ env, dialecticaRealizerCtx si (all ρ (imp (all .nat B₀) (ex .nat C₀))) env
  -- Specialize to empty env
  let r₀ := r ()
  let w := r₀.val
  let h := r₀.property
  -- Step 2: Extract U, V from the Dialectica witness
  -- w : Ty.interpret X ρ → W(imp (all .nat B₀) (ex .nat C₀))
  -- W(imp P Q) = (W(P) → W(Q)) × (W(P) → C(Q) → C(P))
  -- W(all .nat B₀) = ℕ → W(B₀)
  -- W(ex .nat C₀) = ℕ × W(C₀)
  -- C(ex .nat C₀) = C(C₀)
  -- C(all .nat B₀) = ℕ × C(B₀)
  -- Extract V: feed default W(∀u B₀) into first component, project .1
  let V : Ty.interpret X ρ → Nat := fun x => ((w x).1 (dialecticaDefaultWitness si _)).1
  -- Extract U: feed defaults into second component, project .1
  let U : Ty.interpret X ρ → Nat := fun x =>
    ((w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  -- Step 3: Prove B(x, U(x)) → C(x, V(x)) from the Dialectica matrix
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (U x, (x, ())) → Formula.interpret si C₀ (V x, (x, ())) := by
    intro x hBx
    -- Specialize h to counter (x, (defaultW(all .nat B₀), defaultC(ex .nat C₀)))
    let wP := dialecticaDefaultWitness si (all Ty.nat B₀)
    let cQ := dialecticaDefaultCounter si (ex Ty.nat C₀)
    have h_spec := h (x, (wP, cQ))
    -- h_spec : matrix(imp (all .nat B₀) (ex .nat C₀), (x, ()), w x, (wP, cQ))
    -- which is: matrix(all .nat B₀, ..., wP, (w x).2 wP cQ) → matrix(ex .nat C₀, ..., (w x).1 wP, cQ)
    -- Unfold: matrix(all .nat B₀, (x,()), wP, (U x, ...)) = matrix(B₀, (U x, x, ()), wP(U x), ...)
    -- and:    matrix(ex .nat C₀, (x,()), (V x, ...), cQ) = matrix(C₀, (V x, x, ()), ..., cQ)
    simp only [dialecticaMatrix] at h_spec
    -- Use the QF∨-free reduction for B₀ and C₀
    rw [dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf] at h_spec
    exact h_spec hBx
  -- Step 4: Construct Φ using majorizability
  exact ⟨fun x_star =>
    Nat.max (mj.majorizer (ρ := ρ →ₜ .nat) U x_star)
            (mj.majorizer (ρ := ρ →ₜ .nat) V x_star),
    fun x x_star hx hB => by
      have hV_le : V x ≤ mj.majorizer (ρ := ρ →ₜ .nat) V x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) V) hx)
      have hU_le : U x ≤ mj.majorizer (ρ := ρ →ₜ .nat) U x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) U) hx)
      exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..),
             hUV x (hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..)))⟩⟩

-- ============================================================================
-- Prenexification: (∀u B₀ → ∃v C₀) → ∃u ∃v (B₀ → C₀)  [classical]
-- ============================================================================

/-- Classical prenexification: `(∀u B₀ → ∃v C₀) → ∃u ∃v (B₀' → C₀')`.

    B₀, C₀ are in context `[Ty.nat, ρ, Γ]` (bound var 0 + x at var 1).
    The prenexified form `∃u ∃v (B₀' → C₀')` lives in `[ρ, Γ]` with:
    - B₀' = B₀.weakenBy Ty.nat (u at var 1, x at var 2)
    - C₀' = C₀.renameF (ext shift) (v at var 0, x at var 2)

    Proof by LEM on the conclusion:
    - Positive case: done
    - Negative case: ¬∃u∃v(B₀'→C₀') gives ∀u∀v ¬(B₀'→C₀'). From ¬(P→Q) and
      qf_lem on P: B₀ holds for all u (→ ∃v C₀ from hypothesis) and ¬C₀ holds
      for all v (→ contradiction). -/
def prenexify
    {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {ρ : Ty ι}
    {B₀ C₀ : Formula F (Ty.nat :: ρ :: Γ)}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true) :
    let B₀' := B₀.weakenBy Ty.nat
    let C₀' := C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
    @Derivable ι F EqX Allowed.classical Premises (ρ :: Γ)
      ((all Ty.nat B₀ →ᶠ ex Ty.nat C₀) →ᶠ
       ex Ty.nat (ex Ty.nat (B₀' →ᶠ C₀'))) :=
  let G := ex Ty.nat (ex Ty.nat (B₀.weakenBy Ty.nat →ᶠ
    C₀.renameF (Term.Renaming.ext Term.Renaming.shift)))
  let H := all Ty.nat B₀ →ᶠ ex Ty.nat C₀
  let lem_G := @Derivable.lem _ F EqX Allowed.classical Premises _ G (by decide)
  -- ── Local helper: A → (∃σ A).weakenBy σ  (exist intro at var 0) ──
  let eav {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F EqX Allowed.classical Premises (A →ᶠ (ex σ A).weakenBy σ) :=
    Eq.mp (congrArg (Derivable F EqX Allowed.classical Premises ·)
      (congrArg (· →ᶠ (ex σ A).weakenBy σ) (substF_renameF_id
        (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
        (fun {_} v => match v with
          | .vz => rfl
          | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]) A)))
      (.exist_ax (.var .vz) (A.renameF (Renaming.ext Renaming.shift)))
  -- ── Local helper: (∀σ A).weakenBy σ → A  (forall elim at var 0) ──
  let fav {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F EqX Allowed.classical Premises ((all σ A).weakenBy σ →ᶠ A) :=
    Eq.mp (congrArg (Derivable F EqX Allowed.classical Premises ·)
      (congrArg ((all σ A).weakenBy σ →ᶠ ·) (substF_renameF_id
        (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
        (fun {_} v => match v with
          | .vz => rfl
          | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]) A)))
      (.forall_ax (.var .vz))
  -- ── Sub-lemma: ¬∃x P(x) → ∀x ¬P(x) ──
  let neg_ex_to_all_neg {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F EqX Allowed.classical Premises (¬ᶠ(ex σ A) →ᶠ all σ (¬ᶠA)) :=
    .forall_rule (.exportation (eval_h .and_weak (.syllogism and_proj2 (eav A))))
  -- ── Sub-lemma: ¬(P → Q) → P  (classical, uses LEM on P) ──
  let not_imp_left {Δ : Ctx ι} (P Q : Formula F Δ) :
      Derivable F EqX Allowed.classical Premises (¬ᶠ(P →ᶠ Q) →ᶠ P) :=
    let lem_P := @Derivable.lem _ F EqX Allowed.classical Premises _ P (by decide)
    let neg_P_imp : Derivable F EqX Allowed.classical Premises (¬ᶠP →ᶠ (P →ᶠ Q)) :=
      .exportation (.syllogism (eval_h .and_weak and_proj2) .exfalso)
    Derivable.mp lem_P (or_elim_rule
      (.exportation .and_weak)
      (.exportation (.syllogism (eval_h and_proj2 (.syllogism .and_weak neg_P_imp)) .exfalso)))
  -- ── Sub-lemma: ¬(P → Q) → ¬Q ──
  let not_imp_right {Δ : Ctx ι} (_P Q : Formula F Δ) :
      Derivable F EqX Allowed.classical Premises (¬ᶠ(_P →ᶠ Q) →ᶠ ¬ᶠQ) :=
    -- ¬(P→Q) ∧ Q → ⊥: from Q get P→Q (weaken_intro), contradicts ¬(P→Q)
    .exportation (eval_h .and_weak (.syllogism and_proj2 (.exportation .and_weak)))
  -- ── Negative case: H ∧ ¬G → G ──
  let B₀w := B₀.weakenBy Ty.nat
  let C₀r := C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
  -- ¬G → ∀u ¬∃v(B₀w→C₀r) → ∀u ∀v ¬(B₀w→C₀r)
  let neg_G_to_all : Derivable F EqX Allowed.classical Premises
      (¬ᶠG →ᶠ all Ty.nat (all Ty.nat (¬ᶠ(B₀w →ᶠ C₀r)))) :=
    .syllogism (neg_ex_to_all_neg _) (forall_map (neg_ex_to_all_neg _))
  -- ∀u∀v ¬(B₀w→C₀r) → ∀u B₀
  -- Strategy: forall_map on (∀v ¬(B₀w→C₀r) → B₀), where the inner step
  -- instantiates ∀v at 0, gets ¬(B₀w→C₀r), extracts B₀w via not_imp_left,
  -- then B₀w.subst0(0) = B₀ by normalization.
  -- (A.weakenBy σ).subst0 t = A for any context
  let wsf {Δ : Ctx ι} {σ : Ty ι} (A : Formula F Δ) (t : Term F Δ σ) :
      (A.weakenBy σ).subst0 t = A :=
    substF_renameF_id Term.Renaming.shift (Term.subst0_map t) (fun {_} _ => rfl) A
  let get_B₀ : Derivable F EqX Allowed.classical Premises
      (all Ty.nat (all Ty.nat (¬ᶠ(B₀w →ᶠ C₀r))) →ᶠ all Ty.nat B₀) :=
    let C₀r_z := C₀r.subst0 Term.zero
    have nf : (¬ᶠ(B₀w →ᶠ C₀r)).subst0 (Term.zero : Term F (Ty.nat :: ρ :: Γ) _) =
        (¬ᶠ(B₀ →ᶠ C₀r_z)) := by
      show Formula.imp (Formula.imp (B₀w.subst0 Term.zero) C₀r_z) ⊥ᶠ =
           Formula.imp (Formula.imp B₀ C₀r_z) ⊥ᶠ
      rw [wsf B₀ (Term.zero : Term F (Ty.nat :: ρ :: Γ) _)]
    forall_map (.syllogism (.forall_ax Term.zero)
      (Eq.mp (congrArg (Derivable F EqX Allowed.classical Premises ·)
        (congrArg (· →ᶠ B₀) nf.symm)) (not_imp_left B₀ C₀r_z)))
  -- ∀u∀v ¬(B₀w→C₀r) → ∀v ¬C₀
  -- Strategy: instantiate ∀u at 0, get ∀v ¬(B₀w→C₀r), then forall_map
  -- with (¬(B₀w→C₀r) → ¬C₀r), then C₀r.subst0(0) normalizes to C₀.
  let get_neg_C₀ : Derivable F EqX Allowed.classical Premises
      (all Ty.nat (all Ty.nat (¬ᶠ(B₀w →ᶠ C₀r))) →ᶠ all Ty.nat (¬ᶠC₀)) :=
    -- Instantiate outer ∀u at zero: get ∀v ¬(B₀w' → C₀r')
    -- where B₀w' = B₀w.subst0 zero, C₀r' = C₀r.subst0 zero
    -- C₀r = C₀.renameF (ext shift), so C₀r.subst0 zero = C₀ by substF_renameF_id
    -- Then forall_map with not_imp_right gives ∀v ¬C₀
    let B₀w_z := B₀w.subst0 Term.zero
    -- C₀r.substF(Subst.ext(subst0_map zero)) = C₀
    -- This is NOT C₀r.subst0 zero (which is direct subst0_map).
    -- The ∀v binder pushes subst0 through Subst.ext.
    -- C₀r = C₀.renameF(ext shift). Under Subst.ext(subst0_map zero):
    -- vz → vz (by Subst.ext), vs w → (subst0_map(zero)(w)).weaken
    -- At ext_shift(vz) = vz: Subst.ext gives var vz. ✓
    -- At ext_shift(vs w) = vs(vs w): Subst.ext(vs(vs w)) = (subst0_map(zero)(vs w)).weaken = (var w).weaken = var(vs w). ✓
    -- Step 1: forall_map with not_imp_right on inner ∀v
    -- ∀u∀v ¬(B₀w→C₀r) → ∀u∀v ¬C₀r
    let step1 := forall_map (forall_map (not_imp_right B₀w C₀r))
    -- Step 2: instantiate ∀u at zero → ∀v ¬C₀r becomes ∀v ¬C₀
    -- C₀r.substF(Subst.ext(subst0_map zero)) = C₀ (identity on C₀'s variables)
    have C₀r_nf : C₀r.substF (Term.Subst.ext (Term.subst0_map (Term.zero : Term F (ρ :: Γ) _))) = C₀ :=
      substF_renameF_id (Term.Renaming.ext Term.Renaming.shift)
        (Term.Subst.ext (Term.subst0_map Term.zero))
        (fun {_} v => match v with
          | .vz => rfl
          | .vs _ => rfl) C₀
    have nf_neg : (all Ty.nat (¬ᶠC₀r)).subst0 (Term.zero : Term F (ρ :: Γ) _) =
        all Ty.nat (¬ᶠC₀) := by
      change all Ty.nat (Formula.imp (C₀r.substF (Term.Subst.ext (Term.subst0_map Term.zero))) ⊥ᶠ) =
             all Ty.nat (¬ᶠC₀)
      rw [C₀r_nf]; rfl
    .syllogism step1 (.syllogism (.forall_ax Term.zero)
      (Eq.mp (congrArg (Derivable F EqX Allowed.classical Premises ·)
        (congrArg (· →ᶠ all Ty.nat (¬ᶠC₀)) nf_neg.symm)) I_comb))
  -- ∃v C₀ ∧ ∀v ¬C₀ → ⊥
  let exist_all_neg : Derivable F EqX Allowed.classical Premises
      (ex Ty.nat C₀ ∧ᶠ all Ty.nat (¬ᶠC₀) →ᶠ ⊥ᶠ) :=
    .importation (.exist_rule
      (.exportation (eval_h (.syllogism and_proj2 (fav (¬ᶠC₀))) .and_weak)))
  -- Chain: H ∧ ¬G → G
  let neg_case : Derivable F EqX Allowed.classical Premises (H ∧ᶠ ¬ᶠG →ᶠ G) :=
    let to_forall_B := .syllogism and_proj2 (.syllogism neg_G_to_all get_B₀)
    let to_exist_C := eval_h .and_weak to_forall_B
    let to_all_neg_C := .syllogism and_proj2 (.syllogism neg_G_to_all get_neg_C₀)
    .syllogism (pair_h to_exist_C to_all_neg_C)
      (.syllogism exist_all_neg .exfalso)
  -- Combine: H → G using LEM
  Derivable.mp lem_G (or_elim_rule
    (.exportation (.and_weak (A := G) (B := H)))
    (.exportation (.syllogism .and_perm neg_case)))

-- ============================================================================
-- Classical version (Theorem 6.1 as in the paper)
-- ============================================================================

/-- **General Metatheorem from classical proof** (Theorem 6.1).

Takes a classical derivation (with LEM + QF-AC) and composes
`nd_soundness` with witness extraction. The ¬¬ layers from the
negative translation are eliminated using `Classical.not_not`. -/
def general_metatheorem_classical
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (adm : AdmissibleEqX EqX)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (nts : NTStableD EqX Premises)
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.classical Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  -- Step 1: Apply ND-interpretation (NT + Dialectica)
  let r := nd_soundness_closed si eqxi adm nts premise_realizer prf
  let w := r.val
  let h := r.property
  -- h : ∀ y, dialecticaMatrix si NT(∀x(∀u B₀ → ∃v C₀)) () w y
  -- NT introduces ¬¬ layers. Extract through them using Classical.not_not.
  -- Step 2: Extract U, V (same projections as extended version, through ¬¬)
  let ki_w := (w.2 (dialecticaDefaultWitness si _) ()).1
  let imp_w := fun x => ((ki_w x).2 (dialecticaDefaultWitness si _) ()).1
  let V : Ty.interpret X ρ → Nat := fun x =>
    ((imp_w x).1 (dialecticaDefaultWitness si _)).1
  let U : Ty.interpret X ρ → Nat := fun x =>
    ((imp_w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  -- Step 3: Prove B(x, U(x)) → C(x, V(x))
  -- Unfold h through the ¬¬ layers using Classical.not_not
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (U x, (x, ())) → Formula.interpret si C₀ (V x, (x, ())) := by
    -- **THIS SKELETON IS THE WRONG ROUTE. Do not try to finish it here.** (2026-09-02)
    --
    -- Everything above takes the *direct* ND interpretation of `∀x(∀u B₀ → ∃v C₀)`, which
    -- CLAUDE.md note 2 says explicitly not to do: it produces entangled witness/counter
    -- types, and FEASIBILITY R1 confirmed mechanically that the default challenge fed to
    -- `imp_w`/`U`/`V` above ignores its argument, so those `U, V` are sound only against one
    -- junk challenge. R1's conclusion was "the entry point must change", NOT that the
    -- theorem is unprovable.
    --
    -- The prescribed route, per note 2 and R1's "route back (prenexify → Markov →
    -- extended)":
    --   1. `prenexify` under `∀x` (via `forall_map`) — PROVED at line 155, clean axioms,
    --      and currently called from nowhere. It is the LEM-using step, i.e. the hard part.
    --   2. `negTrans_sound` on the prenexified `∀x ∃u∃v(B₀' → C₀')`.
    --   3. Dialectica: the matrix is now an implication between two QF formulas, so its
    --      witness/counter types are singletons and `dialecticaMatrix_iff_interpFormula`
    --      reduces it.
    -- Unverified: the `∃u∃v` under NT's `¬¬` needs Markov (available in the extended
    -- system). R1 calls this "a fresh probe, not a fix" and that is still right.
    sorry
  -- Step 4: Construct Φ (same as extended version)
  exact ⟨fun x_star =>
    Nat.max (mj.majorizer (ρ := ρ →ₜ .nat) U x_star)
            (mj.majorizer (ρ := ρ →ₜ .nat) V x_star),
    fun x x_star hx hB => by
      have hV_le : V x ≤ mj.majorizer (ρ := ρ →ₜ .nat) V x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) V) hx)
      have hU_le : U x ≤ mj.majorizer (ρ := ρ →ₜ .nat) U x_star :=
        mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) U) hx)
      exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..),
             hUV x (hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..)))⟩⟩

-- ============================================================================
-- Core bound construction (Theorem 6.1, step 3–5)
-- ============================================================================

/-- **Core of the General Metatheorem** (Theorem 6.1).

Given semantic witness functions `U V : Ty.interpret X ρ → ℕ` satisfying
`∀x, B(x, U(x)) → C(x, V(x))` (the "extracted content" from the
ND-interpretation), construct a computable bound Φ such that for all
`x* ≥*_ρ x`: `(∀u ≤ Φ(x*), B(x,u)) → (∃v ≤ Φ(x*), C(x,v))`. -/
theorem metatheorem_core
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    (mj : Majorizability si)
    {ρ : Ty ι}
    (B C : Ty.interpret X ρ → Nat → Prop)
    (U V : Ty.interpret X ρ → Nat)
    (hUV : ∀ x : Ty.interpret X ρ, B x (U x) → C x (V x)) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      mj.maj ρ x_star x →
      (∀ u : Nat, u ≤ Φ x_star → B x u) →
      ∃ v : Nat, v ≤ Φ x_star ∧ C x v := by
  -- Define Φ(x*) = max(U*(x*), V*(x*)) where U* = majorizer(U), V* = majorizer(V)
  refine ⟨fun x_star =>
    Nat.max (mj.majorizer (ρ := ρ →ₜ .nat) U x_star)
            (mj.majorizer (ρ := ρ →ₜ .nat) V x_star), ?_⟩
  intro x x_star hx hB
  -- V(x) ≤ V*(x*) ≤ Φ(x*)
  have hV_le : V x ≤ mj.majorizer (ρ := ρ →ₜ .nat) V x_star :=
    mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) V) hx)
  -- U(x) ≤ U*(x*) ≤ Φ(x*)
  have hU_le : U x ≤ mj.majorizer (ρ := ρ →ₜ .nat) U x_star :=
    mj.maj_le (mj.maj_app (mj.majorizer_maj (ρ := ρ →ₜ .nat) U) hx)
  -- B(x, U(x)) holds since U(x) ≤ Φ(x*)
  have hBU : B x (U x) := hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..))
  -- C(x, V(x)) holds by the semantic content
  exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..), hUV x hBU⟩

/-- `metatheorem_core` with the majorants supplied explicitly instead of obtained from a
total `majorizer`.

This is the form that is actually usable: it needs only `MajorizabilityRel` (which is
inhabited — `bezemRel`) together with majorants for the two extracted functionals. The
total-majorizer version is the special case `U_star := majorizer U`, `V_star := majorizer V`.
-/
theorem metatheorem_core_of_majorants
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    (mj : MajorizabilityRel si)
    {ρ : Ty ι}
    (B C : Ty.interpret X ρ → Nat → Prop)
    (U V : Ty.interpret X ρ → Nat)
    (U_star V_star : Ty.interpret X (ρ →ₜ Ty.nat).hat)
    (hU : mj.maj (ρ →ₜ Ty.nat) U_star U)
    (hV : mj.maj (ρ →ₜ Ty.nat) V_star V)
    (hUV : ∀ x : Ty.interpret X ρ, B x (U x) → C x (V x)) :
    ∃ Φ : Ty.interpret X ρ.hat → Nat,
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      mj.maj ρ x_star x →
      (∀ u : Nat, u ≤ Φ x_star → B x u) →
      ∃ v : Nat, v ≤ Φ x_star ∧ C x v := by
  refine ⟨fun x_star => Nat.max (U_star x_star) (V_star x_star), ?_⟩
  intro x x_star hx hB
  have hV_le : V x ≤ V_star x_star := mj.maj_le (mj.maj_app hV hx)
  have hU_le : U x ≤ U_star x_star := mj.maj_le (mj.maj_app hU hx)
  have hBU : B x (U x) := hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..))
  exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..), hUV x hBU⟩

/-- **The extraction half of the metatheorem**, on its own.

Steps 1–3 of `general_metatheorem` — apply Dialectica soundness, project the two
functionals `U`, `V` out of the witness, and reduce the matrix back to the interpreted
formula. No majorizability is involved, and the result is data: `.val.1` and `.val.2` are
Lean functions that compute.

Compose with `metatheorem_core_of_majorants` to obtain a uniform bound. -/
def general_metatheorem_extract
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι F EqX Allowed.extended Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { UV : (Ty.interpret X ρ → Nat) × (Ty.interpret X ρ → Nat) //
      ∀ x : Ty.interpret X ρ,
        Formula.interpret si B₀ (UV.1 x, (x, ())) →
        Formula.interpret si C₀ (UV.2 x, (x, ())) } :=
  let r := @dialectica_soundness_ctx' ι X F si EqX eqxi Premises premise_realizer _ _ prf
  let r₀ := r ()
  let w := r₀.val
  let h := r₀.property
  let V : Ty.interpret X ρ → Nat := fun x => ((w x).1 (dialecticaDefaultWitness si _)).1
  let U : Ty.interpret X ρ → Nat := fun x =>
    ((w x).2 (dialecticaDefaultWitness si _) (dialecticaDefaultCounter si _)).1
  ⟨(U, V), by
    intro x hBx
    let wP := dialecticaDefaultWitness si (all Ty.nat B₀)
    let cQ := dialecticaDefaultCounter si (ex Ty.nat C₀)
    have h_spec := h (x, (wP, cQ))
    simp only [dialecticaMatrix] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si B₀ hB_qf hB_vf] at h_spec
    rw [dialecticaMatrix_iff_interpFormula si C₀ hC_qf hC_vf] at h_spec
    exact h_spec hBx⟩

end Metatheorems
