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
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
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

**VESTIGIAL — cannot be applied.** It takes a `Majorizability`, i.e. a *total* majorizer, and
that structure has no instances and cannot have any (see its docstring for the refutation).
Kept as the faithful transcription of the document's Def. 6.0.1. **Use
`syntactic_general_metatheorem`**, which needs only `AbstractMajorizability` and gets the
majorants free from `all_closed_terms_majorizable`.

Takes a derivation in the extended system (post-NT) and applies Dialectica
directly. The matrix has no ¬¬ layers, making extraction clean.
The full metatheorem composes `negTrans_sound` (external) with this. -/
def general_metatheorem
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F)
    (eqxi : EqXInterp X F si)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  -- Step 1: Apply Dialectica directly (no NT)
  let r := @dialectica_soundness_ctx' ι κ X F si eqxi Premises premise_realizer _ _ prf
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
-- Renaming lemmas used by the classical (prenexified) route
-- ============================================================================

/-- `renameF` preserves quantifier-freeness. -/
theorem isQF_renameF {ι κ : Type} {F : κ → Ty ι} {Γ Δ : Ctx ι}
    (r : Term.Renaming Γ Δ) (A : Formula F Γ) :
    (A.renameF r).isQF = A.isQF := by
  induction A generalizing Δ with
  | bot => rfl
  | eq0 _ _ => rfl
  | and _ _ ihA ihB => simp only [Formula.renameF, Formula.isQF, ihA r, ihB r]
  | or _ _ ihA ihB => simp only [Formula.renameF, Formula.isQF, ihA r, ihB r]
  | imp _ _ ihA ihB => simp only [Formula.renameF, Formula.isQF, ihA r, ihB r]
  | all _ _ _ => rfl
  | ex _ _ _ => rfl

/-- `renameF` preserves ∨-freeness. -/
theorem isVFree_renameF {ι κ : Type} {F : κ → Ty ι} {Γ Δ : Ctx ι}
    (r : Term.Renaming Γ Δ) (A : Formula F Γ) :
    (A.renameF r).isVFree = A.isVFree := by
  induction A generalizing Δ with
  | bot => rfl
  | eq0 _ _ => rfl
  | and _ _ ihA ihB => simp only [Formula.renameF, Formula.isVFree, ihA r, ihB r]
  | or _ _ _ _ => rfl
  | imp _ _ ihA ihB => simp only [Formula.renameF, Formula.isVFree, ihA r, ihB r]
  | all _ _ ih => simp only [Formula.renameF, Formula.isVFree, ih (Term.Renaming.ext r)]
  | ex _ _ ih => simp only [Formula.renameF, Formula.isVFree, ih (Term.Renaming.ext r)]

theorem isQF_weakenBy {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F Γ) :
    (A.weakenBy ρ).isQF = A.isQF := isQF_renameF _ A

theorem isVFree_weakenBy {ι κ : Type} {F : κ → Ty ι} {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F Γ) :
    (A.weakenBy ρ).isVFree = A.isVFree := isVFree_renameF _ A

/-- Semantic counterpart of `Term.interpret_rename_gen`: a renamed formula evaluated in
`envΔ` means the same as the original evaluated in `envΓ`, provided the two environments
agree on variable lookups through the renaming. -/
theorem Formula.interpret_renameF_gen {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι}
    (r : Term.Renaming Γ Δ) (A : Formula F Γ)
    (envΔ : Ctx.interpret X Δ) (envΓ : Ctx.interpret X Γ)
    (h : ∀ {σ} (v : Var Γ σ), Ctx.lookup (r v) envΔ = Ctx.lookup v envΓ) :
    Formula.interpret si (A.renameF r) envΔ = Formula.interpret si A envΓ := by
  induction A generalizing Δ with
  | bot => rfl
  | eq0 s t =>
    simp only [Formula.renameF, Formula.interpret,
      Term.interpret_rename_gen si r s envΔ envΓ h,
      Term.interpret_rename_gen si r t envΔ envΓ h]
  | and _ _ ihA ihB =>
    simp only [Formula.renameF, Formula.interpret, ihA r envΔ envΓ h, ihB r envΔ envΓ h]
  | or _ _ ihA ihB =>
    simp only [Formula.renameF, Formula.interpret, ihA r envΔ envΓ h, ihB r envΔ envΓ h]
  | imp _ _ ihA ihB =>
    simp only [Formula.renameF, Formula.interpret, ihA r envΔ envΓ h, ihB r envΔ envΓ h]
  | all σ A ih =>
    have hstep : ∀ x : Ty.interpret X σ,
        Formula.interpret si (A.renameF (Term.Renaming.ext r)) (x, envΔ) =
        Formula.interpret si A (x, envΓ) := fun x =>
      ih (Term.Renaming.ext r) (x, envΔ) (x, envΓ)
        (fun {_} v => match v with | .vz => rfl | .vs w => h w)
    simp only [Formula.renameF, Formula.interpret, hstep]
  | ex σ A ih =>
    have hstep : ∀ x : Ty.interpret X σ,
        Formula.interpret si (A.renameF (Term.Renaming.ext r)) (x, envΔ) =
        Formula.interpret si A (x, envΓ) := fun x =>
      ih (Term.Renaming.ext r) (x, envΔ) (x, envΓ)
        (fun {_} v => match v with | .vz => rfl | .vs w => h w)
    simp only [Formula.renameF, Formula.interpret, hstep]

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
    {ι κ : Type} {F : κ → Ty ι}
    {Premises : PremiseSet F}
    {Γ : Ctx ι} {ρ : Ty ι}
    {B₀ C₀ : Formula F (Ty.nat :: ρ :: Γ)}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true) :
    let B₀' := B₀.weakenBy Ty.nat
    let C₀' := C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
    @Derivable ι κ F Allowed.classical Premises (ρ :: Γ)
      ((all Ty.nat B₀ →ᶠ ex Ty.nat C₀) →ᶠ
       ex Ty.nat (ex Ty.nat (B₀' →ᶠ C₀'))) :=
  let G := ex Ty.nat (ex Ty.nat (B₀.weakenBy Ty.nat →ᶠ
    C₀.renameF (Term.Renaming.ext Term.Renaming.shift)))
  let H := all Ty.nat B₀ →ᶠ ex Ty.nat C₀
  let lem_G := @Derivable.lem _ _ F Allowed.classical Premises _ G (by decide)
  -- ── Local helper: A → (∃σ A).weakenBy σ  (exist intro at var 0) ──
  let eav {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F Allowed.classical Premises (A →ᶠ (ex σ A).weakenBy σ) :=
    Eq.mp (congrArg (Derivable F Allowed.classical Premises ·)
      (congrArg (· →ᶠ (ex σ A).weakenBy σ) (substF_renameF_id
        (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
        (fun {_} v => match v with
          | .vz => rfl
          | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]) A)))
      (.exist_ax (.var .vz) (A.renameF (Renaming.ext Renaming.shift)))
  -- ── Local helper: (∀σ A).weakenBy σ → A  (forall elim at var 0) ──
  let fav {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F Allowed.classical Premises ((all σ A).weakenBy σ →ᶠ A) :=
    Eq.mp (congrArg (Derivable F Allowed.classical Premises ·)
      (congrArg ((all σ A).weakenBy σ →ᶠ ·) (substF_renameF_id
        (Renaming.ext Renaming.shift) (Term.subst0_map (.var .vz))
        (fun {_} v => match v with
          | .vz => rfl
          | .vs _ => by simp [Term.Renaming.ext, Term.subst0_map, Term.Renaming.shift]) A)))
      (.forall_ax (.var .vz))
  -- ── Sub-lemma: ¬∃x P(x) → ∀x ¬P(x) ──
  let neg_ex_to_all_neg {σ : Ty ι} {Δ : Ctx ι} (A : Formula F (σ :: Δ)) :
      Derivable F Allowed.classical Premises (¬ᶠ(ex σ A) →ᶠ all σ (¬ᶠA)) :=
    .forall_rule (.exportation (eval_h .and_weak (.syllogism and_proj2 (eav A))))
  -- ── Sub-lemma: ¬(P → Q) → P  (classical, uses LEM on P) ──
  let not_imp_left {Δ : Ctx ι} (P Q : Formula F Δ) :
      Derivable F Allowed.classical Premises (¬ᶠ(P →ᶠ Q) →ᶠ P) :=
    let lem_P := @Derivable.lem _ _ F Allowed.classical Premises _ P (by decide)
    let neg_P_imp : Derivable F Allowed.classical Premises (¬ᶠP →ᶠ (P →ᶠ Q)) :=
      .exportation (.syllogism (eval_h .and_weak and_proj2) .exfalso)
    Derivable.mp lem_P (or_elim_rule
      (.exportation .and_weak)
      (.exportation (.syllogism (eval_h and_proj2 (.syllogism .and_weak neg_P_imp)) .exfalso)))
  -- ── Sub-lemma: ¬(P → Q) → ¬Q ──
  let not_imp_right {Δ : Ctx ι} (_P Q : Formula F Δ) :
      Derivable F Allowed.classical Premises (¬ᶠ(_P →ᶠ Q) →ᶠ ¬ᶠQ) :=
    -- ¬(P→Q) ∧ Q → ⊥: from Q get P→Q (weaken_intro), contradicts ¬(P→Q)
    .exportation (eval_h .and_weak (.syllogism and_proj2 (.exportation .and_weak)))
  -- ── Negative case: H ∧ ¬G → G ──
  let B₀w := B₀.weakenBy Ty.nat
  let C₀r := C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
  -- ¬G → ∀u ¬∃v(B₀w→C₀r) → ∀u ∀v ¬(B₀w→C₀r)
  let neg_G_to_all : Derivable F Allowed.classical Premises
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
  let get_B₀ : Derivable F Allowed.classical Premises
      (all Ty.nat (all Ty.nat (¬ᶠ(B₀w →ᶠ C₀r))) →ᶠ all Ty.nat B₀) :=
    let C₀r_z := C₀r.subst0 Term.zero
    have nf : (¬ᶠ(B₀w →ᶠ C₀r)).subst0 (Term.zero : Term F (Ty.nat :: ρ :: Γ) _) =
        (¬ᶠ(B₀ →ᶠ C₀r_z)) := by
      show Formula.imp (Formula.imp (B₀w.subst0 Term.zero) C₀r_z) ⊥ᶠ =
           Formula.imp (Formula.imp B₀ C₀r_z) ⊥ᶠ
      rw [wsf B₀ (Term.zero : Term F (Ty.nat :: ρ :: Γ) _)]
    forall_map (.syllogism (.forall_ax Term.zero)
      (Eq.mp (congrArg (Derivable F Allowed.classical Premises ·)
        (congrArg (· →ᶠ B₀) nf.symm)) (not_imp_left B₀ C₀r_z)))
  -- ∀u∀v ¬(B₀w→C₀r) → ∀v ¬C₀
  -- Strategy: instantiate ∀u at 0, get ∀v ¬(B₀w→C₀r), then forall_map
  -- with (¬(B₀w→C₀r) → ¬C₀r), then C₀r.subst0(0) normalizes to C₀.
  let get_neg_C₀ : Derivable F Allowed.classical Premises
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
      (Eq.mp (congrArg (Derivable F Allowed.classical Premises ·)
        (congrArg (· →ᶠ all Ty.nat (¬ᶠC₀)) nf_neg.symm)) I_comb))
  -- ∃v C₀ ∧ ∀v ¬C₀ → ⊥
  let exist_all_neg : Derivable F Allowed.classical Premises
      (ex Ty.nat C₀ ∧ᶠ all Ty.nat (¬ᶠC₀) →ᶠ ⊥ᶠ) :=
    .importation (.exist_rule
      (.exportation (eval_h (.syllogism and_proj2 (fav (¬ᶠC₀))) .and_weak)))
  -- Chain: H ∧ ¬G → G
  let neg_case : Derivable F Allowed.classical Premises (H ∧ᶠ ¬ᶠG →ᶠ G) :=
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

/-- **The proof-theoretic half of the classical metatheorem**, on its own.

Steps 1–4 of `general_metatheorem_classical`: no semantics, no majorizability, no
Dialectica — just

1. `prenexify` under `∀x` (`forall_map`), the LEM-using step;
2. `negTrans_sound` (`kurodaInner` is the identity on the QF body);
3. `nn_all_nn`, pushing the outer `¬¬` inside the `∀`;
4. `castAllowed` into `Allowed.extended`.

**The surviving inner `¬¬` is real** and every consumer must go through it — semantically
(`Classical.not_not`, as `general_metatheorem_classical` does) or otherwise. It is not
strippable here: `Derivable.markov` wants a quantifier-free body and `∃v(B₀' → C₀')` is not
one.

Factored out so that both the semantic (`general_metatheorem_classical`) and the syntactic
(`syntactic_general_metatheorem_classical`) entry points share it. -/
def classical_to_prenex_extended
    {ι κ : Type} {F : κ → Ty ι}
    {Premises : PremiseSet F}
    (nts : NTStableD Premises)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    @Derivable ι κ F Allowed.extended Premises []
      (all ρ (¬ᶠ¬ᶠ(ex Ty.nat (ex Ty.nat
        (B₀.weakenBy Ty.nat →ᶠ
          C₀.renameF (Term.Renaming.ext Term.Renaming.shift)))))) := by
  let B₀' : Formula F [Ty.nat, Ty.nat, ρ] := B₀.weakenBy Ty.nat
  let C₀' : Formula F [Ty.nat, Ty.nat, ρ] :=
    C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
  have hB'_qf : B₀'.isQF = true := by rw [show B₀'.isQF = B₀.isQF from isQF_weakenBy B₀, hB_qf]
  have hC'_qf : C₀'.isQF = true := by
    rw [show C₀'.isQF = C₀.isQF from isQF_renameF _ C₀, hC_qf]
  have hP_qf : (B₀' →ᶠ C₀').isQF = true := by
    simp only [Formula.isQF, hB'_qf, hC'_qf, Bool.and_self]
  -- ── Step 1: prenexify under ∀x ─────────────────────────────────────────────
  let pren : Derivable F Allowed.classical Premises
      (((Formula.all Ty.nat B₀) →ᶠ (Formula.ex Ty.nat C₀)) →ᶠ
        Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))) :=
    prenexify hB_qf hB_vf hC_qf hC_vf
  let prf' : Derivable F Allowed.classical Premises
      (Formula.all ρ (Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀')))) :=
    Derivable.mp prf (forall_map pren)
  -- ── Step 2: negative translation ───────────────────────────────────────────
  have hEki :
      (Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))).kurodaInner =
        Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀')) := by
    change Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀').kurodaInner) = _
    rw [kurodaInner_qf (B₀' →ᶠ C₀') hP_qf]
  let nt := negTrans_sound nts prf'
  have hNT : (Formula.all ρ (Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))))ᴺᵀ =
      (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀')))))) := by
    change (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠ
      (Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))).kurodaInner))) = _
    rw [hEki]
  let nt' : Derivable F Allowed.nt_target Premises
      (¬ᶠ¬ᶠ(Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀')))))) :=
    Eq.mp (congrArg (Derivable F Allowed.nt_target Premises ·) hNT) nt
  -- ── Step 3: push the outer ¬¬ inside the ∀ (D-1) ───────────────────────────
  let stripped : Derivable F Allowed.nt_target Premises
      (Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))))) :=
    Derivable.mp nt' nn_all_nn
  -- ── Step 4: into the extended system ───────────────────────────────────────
  exact stripped.castAllowed (by constructor <;> decide)

/-- **General Metatheorem from classical proof** (Theorem 6.1).

**VESTIGIAL as an entry point — cannot be applied**, for the same reason as
`general_metatheorem`: the `Majorizability` argument has no instances. **Use
`syntactic_general_metatheorem_classical`.**

It is *not* wasted work, and this is worth knowing: proving it is what produced
`classical_to_prenex_extended` (steps 1–4 below), and the syntactic classical metatheorem
calls exactly that. So this theorem is the origin of the shared proof-theoretic factor, even
though the theorem itself is now superseded.

Takes a classical derivation (with LEM + QF-AC) and produces a bound, via the
**prenexified** route — the one the paper takes, and the one CLAUDE.md note 2 prescribes:

1. `prenexify` under `∀x` (`forall_map`), turning `∀x(∀u B₀ → ∃v C₀)` into
   `∀x ∃u ∃v (B₀' → C₀')`. This is the LEM-using step.
2. `negTrans_sound`, giving `⊢ ¬¬(∀x ¬¬ ∃u∃v(B₀' → C₀'))` in `Allowed.nt_target`
   (`kurodaInner` is the identity on the QF body).
3. `nn_all_nn` pushes the outer `¬¬` inside the `∀` (FEASIBILITY decision D-1).
4. `castAllowed` into `Allowed.extended` and apply Dialectica soundness.

The remaining single `¬¬` is discharged **semantically**, by `Classical.not_not` on the
matrix, rather than by an object-level Markov step. That is sound and cheap here precisely
*because* of the prenexification: the body `∃u∃v(B₀' → C₀')` has a quantifier-free ∨-free
matrix, so `dialecticaMatrix_iff_interpFormula` reduces its matrix to the formula's
interpretation **for every counter**, and the counter the `¬¬` layer hands us is therefore
irrelevant. This is exactly what fails on the unprenexified route, where the witness depends
on a challenge that genuinely matters (FEASIBILITY R1).

An object-level Markov step is *not* available at this shape without new machinery: Markov
needs a quantifier-free body, and `∃v(B₀' → C₀')` is not one. Collapsing `∃u∃v` to a single
`∃w` over `nat ×ₜ nat` would need `Term.fst (Term.mkPair a b) = a` as a *derivable* equation,
and the proof system has no product β-rules (only `beta_eq` for `lam`); the Cantor-pairing
route has the equations but drags in `RationalNumbers` (the 43 s module). Both are avoidable:
Markov's principle is *true in the model*, and `Classical.not_not` is precisely its semantic
content. Note that `dialectica_soundness_ctx'` already uses `Classical.choice` (via the
Markov case), so nothing is lost. -/
def general_metatheorem_classical
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F)
    (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (mj : Majorizability si)
    (nts : NTStableD Premises)
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.classical Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { Φ : Ty.interpret X ρ.hat → Nat //
      ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
        mj.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si C₀ (v, (x, ())) } := by
  classical
  -- The prenexified matrix, in context [nat, nat, ρ]: variable 0 is `v`, 1 is `u`, 2 is `x`.
  let B₀' : Formula F [Ty.nat, Ty.nat, ρ] := B₀.weakenBy Ty.nat
  let C₀' : Formula F [Ty.nat, Ty.nat, ρ] :=
    C₀.renameF (Term.Renaming.ext Term.Renaming.shift)
  have hB'_qf : B₀'.isQF = true := by rw [show B₀'.isQF = B₀.isQF from isQF_weakenBy B₀, hB_qf]
  have hB'_vf : B₀'.isVFree = true := by
    rw [show B₀'.isVFree = B₀.isVFree from isVFree_weakenBy B₀, hB_vf]
  have hC'_qf : C₀'.isQF = true := by
    rw [show C₀'.isQF = C₀.isQF from isQF_renameF _ C₀, hC_qf]
  have hC'_vf : C₀'.isVFree = true := by
    rw [show C₀'.isVFree = C₀.isVFree from isVFree_renameF _ C₀, hC_vf]
  have hP_qf : (B₀' →ᶠ C₀').isQF = true := by
    simp only [Formula.isQF, hB'_qf, hC'_qf, Bool.and_self]
  have hP_vf : (B₀' →ᶠ C₀').isVFree = true := by
    simp only [Formula.isVFree, hB'_vf, hC'_vf, Bool.and_self]
  -- ── Steps 1–4: the proof-theoretic reduction, factored out ─────────────────
  let extd : Derivable F Allowed.extended Premises
      (Formula.all ρ (¬ᶠ¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀'))))) :=
    classical_to_prenex_extended nts hB_qf hB_vf hC_qf hC_vf prf
  -- ── Step 5: Dialectica, then read off U and V ──────────────────────────────
  -- Destructed with `obtain`, not `let`: the realizer is a huge term, and leaving it as a
  -- let-value makes every later defeq check try to `whnf` it (a heartbeat timeout).
  obtain ⟨w, hw⟩ :=
    (@dialectica_soundness_ctx' ι κ X F si eqxi Premises premise_realizer _ _ extd) ()
  -- The counter for the inner `¬¬` is a witness for `¬E`; any one will do, because the
  -- E-counter it produces is only ever fed to a QF ∨-free matrix.
  let aW : 𝕎 X (¬ᶠ(Formula.ex Ty.nat (Formula.ex Ty.nat (B₀' →ᶠ C₀')))) :=
    dialecticaDefaultWitness si _
  let U : Ty.interpret X ρ → Nat := fun x => ((w x).2 aW ()).1.1
  let V : Ty.interpret X ρ → Nat := fun x => ((w x).2 aW ()).1.2.1
  have hUV : ∀ x : Ty.interpret X ρ,
      Formula.interpret si B₀ (U x, (x, ())) → Formula.interpret si C₀ (V x, (x, ())) := by
    intro x hBx
    have hb : Formula.interpret si B₀' (V x, (U x, (x, ()))) =
        Formula.interpret si B₀ (U x, (x, ())) :=
      Formula.interpret_renameF_gen si (Term.Renaming.shift (σ := Ty.nat)) B₀
        (V x, (U x, (x, ()))) (U x, (x, ())) (fun {_} _ => rfl)
    have hc : Formula.interpret si C₀' (V x, (U x, (x, ()))) =
        Formula.interpret si C₀ (V x, (x, ())) :=
      Formula.interpret_renameF_gen si
        (Term.Renaming.ext (σ := Ty.nat) (Term.Renaming.shift (σ := Ty.nat))) C₀
        (V x, (U x, (x, ()))) (V x, (x, ()))
        (fun {_} v => match v with | .vz => rfl | .vs _ => rfl)
    have key := hw (x, (aW, ()))
    simp only [Formula.neg, dialecticaMatrix] at key
    rw [dialecticaMatrix_iff_interpFormula si B₀' hB'_qf hB'_vf,
        dialecticaMatrix_iff_interpFormula si C₀' hC'_qf hC'_vf] at key
    -- key : ¬¬(‖B₀'‖ → ‖C₀'‖) at the environment (V x, (U x, (x, ())))
    by_contra hCn
    exact key (fun himp => hCn (Eq.mp hc (himp (Eq.mpr hb hBx))))
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

#print axioms general_metatheorem
#print axioms general_metatheorem_classical

-- ============================================================================
-- Core bound construction (Theorem 6.1, step 3–5)
-- ============================================================================

/-- **Core of the General Metatheorem** (Theorem 6.1).

Given semantic witness functions `U V : Ty.interpret X ρ → ℕ` satisfying
`∀x, B(x, U(x)) → C(x, V(x))` (the "extracted content" from the
ND-interpretation), construct a computable bound Φ such that for all
`x* ≥*_ρ x`: `(∀u ≤ Φ(x*), B(x,u)) → (∃v ≤ Φ(x*), C(x,v))`. -/
theorem metatheorem_core
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
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

/-! `metatheorem_core` with the majorants supplied explicitly instead of obtained from a
total `majorizer`.

This is the form that is actually usable: it needs only `MajorizabilityRel` (which is
inhabited — `bezemRel`) together with majorants for the two extracted functionals. The
total-majorizer version is the special case `U_star := majorizer U`, `V_star := majorizer V`.

Since 2026-09-04 it comes in the project's usual two flavours: `coreBound` names the witness,
`metatheorem_core_of_majorants_at` is the statement about it, and `metatheorem_core_of_majorants`
is the `∃`-valued original, now a one-liner over those two. -/

/-- **The bound, named.** `Φ` is the pointwise max of the two majorants — that is the whole
content of `metatheorem_core_of_majorants`'s witness, and naming it is what lets a bound be
*computed* rather than merely shown to exist. Same `_at` convention as `bezem_prec_maj_at`
and `MetricModel.dist_maj_at`. -/
def coreBound {ι : Type} {X : ι → Type} {ρ : Ty ι}
    (U_star V_star : Ty.interpret X (ρ →ₜ Ty.nat).hat) :
    Ty.interpret X ρ.hat → Nat :=
  fun x_star => Nat.max (U_star x_star) (V_star x_star)

/-- `metatheorem_core_of_majorants` with the bound named instead of existentially bound. -/
theorem metatheorem_core_of_majorants_at
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
    ∀ (x : Ty.interpret X ρ) (x_star : Ty.interpret X ρ.hat),
      mj.maj ρ x_star x →
      (∀ u : Nat, u ≤ coreBound U_star V_star x_star → B x u) →
      ∃ v : Nat, v ≤ coreBound U_star V_star x_star ∧ C x v := by
  intro x x_star hx hB
  have hV_le : V x ≤ V_star x_star := mj.maj_le (mj.maj_app hV hx)
  have hU_le : U x ≤ U_star x_star := mj.maj_le (mj.maj_app hU hx)
  have hBU : B x (U x) := hB (U x) (Nat.le_trans hU_le (Nat.le_max_left ..))
  exact ⟨V x, Nat.le_trans hV_le (Nat.le_max_right ..), hUV x hBU⟩

theorem metatheorem_core_of_majorants
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
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
      ∃ v : Nat, v ≤ Φ x_star ∧ C x v :=
  ⟨coreBound U_star V_star,
   metatheorem_core_of_majorants_at mj B C U V U_star V_star hU hV hUV⟩

/-- **The extraction half of the metatheorem**, on its own.

Steps 1–3 of `general_metatheorem` — apply Dialectica soundness, project the two
functionals `U`, `V` out of the witness, and reduce the matrix back to the interpreted
formula. No majorizability is involved, and the result is data: `.val.1` and `.val.2` are
Lean functions that compute.

Compose with `metatheorem_core_of_majorants` to obtain a uniform bound. -/
def general_metatheorem_extract
    {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}
    (si : SpaceInterp X F)
    (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    {ρ : Ty ι}
    {B₀ C₀ : Formula F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable ι κ F Allowed.extended Premises []
      (all ρ (imp (all .nat B₀) (ex .nat C₀)))) :
    { UV : (Ty.interpret X ρ → Nat) × (Ty.interpret X ρ → Nat) //
      ∀ x : Ty.interpret X ρ,
        Formula.interpret si B₀ (UV.1 x, (x, ())) →
        Formula.interpret si C₀ (UV.2 x, (x, ())) } :=
  let r := @dialectica_soundness_ctx' ι κ X F si eqxi Premises premise_realizer _ _ prf
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
