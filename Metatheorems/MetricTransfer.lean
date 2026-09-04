/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.MetricSpaces

namespace Metatheorems

/-!
# The metric `EqXInterp`, transferred to any signature over a metric model

`MetricSpaces.lean` builds `MetricModel.eqXInterp`, `abstractMajorizability`'s two metric
obligations and `MetricModel.soundness` for the **specific** signature `MetricSpace.F`
(`κ = Unit`, `F () = Ty.unit`, no function constants). Every space further up the tower —
W-hyperbolic, CAT(0), normed — is a metric model *plus* function constants, so its
`SpaceInterp` has a different `F` and the metric results do not apply as stated.

They do apply *in substance*: `EqXInterp`'s nine fields mention only `Term.dist` and
`eqAtType` at base types, and the five semantic ones were proved through
`MetricModel.interp_dist`, which is the **only** place `M.si`'s definition was unfolded. So
this file restates that development for an arbitrary
`si : SpaceInterp (fun () => M.carrier) F` with the one hypothesis

    hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y)

and everything else goes through verbatim. The proofs below are those of `MetricSpaces.lean`
with `M.si` replaced by `si` and `hd` where `interp_dist` used to unfold the model; nothing
new is proved. **That is the finding**: a new space instance pays nothing for `eqXInterp`.

Naming: `_gen` suffix throughout, matching the project's convention for the `si`-generic
version of a result (`add_zero_R_gen`, `syntactic_general_metatheorem_gen`).
-/

open Formula

section Transfer

variable (M : MetricModel) {κ : Type} {F : κ → Ty MetricSpace.ι}
variable (si : SpaceInterp (fun () => M.carrier) F)

-- ============================================================================
-- The distance evaluates
-- ============================================================================

/-- `d_X` is interpreted by `(d(x,y))◦` — under `hd`, for any `si`. -/
theorem MetricModel.interp_dist_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    {Γ : Ctx MetricSpace.ι}
    (s t : Term F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Term.interpret si (Term.app2 (Term.dist ()) s t) env
      = Rounding.roundR (M.d (Term.interpret si s env) (Term.interpret si t env)) := by
  simp only [Term.app2, Term.interpret]
  exact hd _ _

/-- `0ℝ` is the constant zero sequence, at the `qval` level. `si`-generic already in
`MetricSpaces.lean`'s proof; only the statement was tied to `M.si`. -/
theorem MetricModel.qval_interp_zero_R_gen {Γ : Ctx MetricSpace.ι}
    (env : Ctx.interpret (fun () => M.carrier) Γ) (k : ℕ) :
    Rounding.qval (Term.interpret si (Term.zero_R (F := F) (Γ := Γ)) env k) = 0 := by
  have hstep : Term.interpret si (Term.zero_R (F := F) (Γ := Γ)) env
      = fun v => Term.interpret si (Term.zero_Q (F := F) (Γ := Ty.nat :: Γ)) (v, env) := by
    simp only [Term.zero_R, Term.interpret]
  rw [hstep]
  exact QBridge.qval_interpret_zero_Q (si := si) (Δ := Ty.nat :: Γ) (k, env)

/-- `cauchyfy` fixes `0ℝ`. -/
theorem MetricModel.cauchyfyN_zero_R_gen {Γ : Ctx MetricSpace.ι}
    (env : Ctx.interpret (fun () => M.carrier) Γ) (n : ℕ) :
    Rounding.qval (QBridge.cauchyfyN
      (Term.interpret si (Term.zero_R (F := F) (Γ := Γ)) env) n) = 0 := by
  rw [QBridge.cauchyfyN_id_of_cauchy _ (fun k => by
    rw [M.qval_interp_zero_R_gen si env k, M.qval_interp_zero_R_gen si env (k + 1)]
    simp)]
  exact M.qval_interp_zero_R_gen si env n

-- ============================================================================
-- The two directions of `=_X`
-- ============================================================================

/-- The model fact behind `realize`: equal interpretations make `s =_X t` true. -/
theorem MetricModel.eqAtType_base_holds_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    {Γ : Ctx MetricSpace.ι}
    (s t : Term F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : Term.interpret si s env = Term.interpret si t env) :
    Formula.interpret si (eqAtType (Ty.base ()) s t) env := by
  change Formula.interpret si (eq_R (Term.app2 (Term.dist ()) s t) Term.zero_R) env
  rw [QBridge.interpret_eq_R]
  intro n
  rw [M.interp_dist_gen si hd s t env, h, M.d_self, cauchyfyN_roundR 0 le_rfl, qval_roundR_zero,
    M.cauchyfyN_zero_R_gen si env]
  simp

/-- The model fact behind `extract` — separation, `M.d_eq_zero`, is used here and only here. -/
theorem MetricModel.eq_of_eqAtType_base_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    {Γ : Ctx MetricSpace.ι}
    (s t : Term F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : Formula.interpret si (eqAtType (Ty.base ()) s t) env) :
    Term.interpret si s env = Term.interpret si t env := by
  refine M.d_eq_zero _ _ ?_
  set r := M.d (Term.interpret si s env) (Term.interpret si t env) with hr_def
  have hr : 0 ≤ r := M.d_nonneg _ _
  rw [show eqAtType (Ty.base ()) s t
      = eq_R (Term.app2 (Term.dist ()) s t) Term.zero_R from rfl,
    QBridge.interpret_eq_R] at h
  have hq : ∀ n : ℕ, |((Rounding.qval (Rounding.roundR r (n + 1)) : ℚ) : ℝ)| < 1 / 2 ^ n := by
    intro n
    have hn := h n
    rw [M.interp_dist_gen si hd s t env, ← hr_def, cauchyfyN_roundR r hr,
      M.cauchyfyN_zero_R_gen si env] at hn
    have hQ : |Rounding.qval (Rounding.roundR r (n + 1))| < 1 / 2 ^ n := by simpa using hn
    calc |((Rounding.qval (Rounding.roundR r (n + 1)) : ℚ) : ℝ)|
        = ((|Rounding.qval (Rounding.roundR r (n + 1))| : ℚ) : ℝ) := (Rat.cast_abs _).symm
      _ < ((1 / 2 ^ n : ℚ) : ℝ) := by exact_mod_cast hQ
      _ = 1 / 2 ^ n := by push_cast; ring
  refine le_antisymm ?_ hr
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1:ℝ)/2 < 1)
  have hpow : (1:ℝ) / 2 ^ n < ε / 2 := by
    rw [div_pow] at hn; simpa using hn
  have hdist := Rounding.qval_roundR_dist_le r hr (n + 1)
  have h1 : |((Rounding.qval (Rounding.roundR r (n + 1)) : ℚ) : ℝ)| < 1 / 2 ^ n := hq n
  have h2 : (1:ℝ) / 2 ^ (n + 1 + 1) ≤ 1 / 2 ^ n := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : r ≤ 1 / 2 ^ n + 1 / 2 ^ n := by
    have habs := abs_le.mp (le_of_lt h1)
    have hd' := abs_le.mp hdist
    linarith [hd'.1, hd'.2, habs.1, habs.2, h2]
  linarith

/-- `extract`'s content, isolated (keep `i` a parameter; `cases i` inside). -/
theorem MetricModel.eqAtType_base_extract_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι} (s t : Term F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ)
    (r : dialecticaRealizerCtx si (eqAtType (Ty.base i) s t) env) :
    Term.interpret si s env = Term.interpret si t env := by
  cases i
  exact M.eq_of_eqAtType_base_gen si hd s t env
    (interp_of_realizer_pu si (eqAtType (Ty.base ()) s t) rfl rfl env r)

-- ============================================================================
-- Symmetry and triangle inequality in the model
-- ============================================================================

/-- `dist_comm_holds`'s content. -/
theorem MetricModel.dist_comm_interp_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι} (x y : Term F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret si
      (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env := by
  cases i
  rw [QBridge.interpret_eq_R]
  intro n
  rw [M.interp_dist_gen si hd x y env, M.interp_dist_gen si hd y x env, M.d_comm]
  simp

/-- `dist_tri_holds`'s content. -/
theorem MetricModel.dist_tri_interp_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι} (x y z : Term F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret si
      (le_R_pu (Term.app2 (Term.dist i) x z)
        (Term.app2 Term.add_R
          (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))) env := by
  cases i
  set A := M.d (Term.interpret si x env) (Term.interpret si y env) with hA
  set B := M.d (Term.interpret si y env) (Term.interpret si z env) with hB
  set C := M.d (Term.interpret si x env) (Term.interpret si z env) with hC
  have hA0 : 0 ≤ A := M.d_nonneg _ _
  have hB0 : 0 ≤ B := M.d_nonneg _ _
  have hC0 : 0 ≤ C := M.d_nonneg _ _
  set S : ℕ → ℕ := fun m =>
    QBridge.addQN (Rounding.roundR A (m + 1)) (Rounding.roundR B (m + 1)) with hS
  have hgfun : Term.interpret si
      (Term.app2 Term.add_R (Term.app2 (Term.dist ()) x y)
        (Term.app2 (Term.dist ()) y z)) env = S := by
    funext m
    rw [QBridge.interpret_add_R_app2, M.interp_dist_gen si hd, M.interp_dist_gen si hd,
      ← hA, ← hB, cauchyfyN_roundR A hA0, cauchyfyN_roundR B hB0]
  have hSq : ∀ m : ℕ, Rounding.qval (S m)
      = Rounding.qval (Rounding.roundR A (m + 1))
        + Rounding.qval (Rounding.roundR B (m + 1)) := fun m => QBridge.qval_addQN _ _
  have hScauchy : ∀ k : ℕ, |Rounding.qval (S k) - Rounding.qval (S (k + 1))|
      < 1 / 2 ^ (k + 1) := by
    intro k
    have ha := Rounding.roundR_cauchy A hA0 (k + 1)
    have hb := Rounding.roundR_cauchy B hB0 (k + 1)
    have hhalf : (1:ℚ) / 2 ^ (k + 1 + 1) + 1 / 2 ^ (k + 1 + 1) = 1 / 2 ^ (k + 1) := by
      rw [pow_succ]; ring
    rw [hSq k, hSq (k + 1)]
    calc |(Rounding.qval (Rounding.roundR A (k + 1)) + Rounding.qval (Rounding.roundR B (k + 1)))
            - (Rounding.qval (Rounding.roundR A (k + 1 + 1))
              + Rounding.qval (Rounding.roundR B (k + 1 + 1)))|
        = |(Rounding.qval (Rounding.roundR A (k + 1))
              - Rounding.qval (Rounding.roundR A (k + 1 + 1)))
            + (Rounding.qval (Rounding.roundR B (k + 1))
              - Rounding.qval (Rounding.roundR B (k + 1 + 1)))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ < 1 / 2 ^ (k + 1 + 1) + 1 / 2 ^ (k + 1 + 1) := by exact add_lt_add ha hb
      _ = 1 / 2 ^ (k + 1) := hhalf
  rw [QBridge.interpret_le_R_pu]
  intro n
  rw [M.interp_dist_gen si hd x z env, ← hC, cauchyfyN_roundR C hC0, hgfun,
    QBridge.cauchyfyN_id_of_cauchy S hScauchy, hSq]
  have key : ((Rounding.qval (Rounding.roundR C (n + 1)) : ℚ) : ℝ)
      - (((Rounding.qval (Rounding.roundR A (n + 1 + 1)) : ℚ) : ℝ)
        + ((Rounding.qval (Rounding.roundR B (n + 1 + 1)) : ℚ) : ℝ)) < 1 / 2 ^ n := by
    have hc := abs_le.mp (Rounding.qval_roundR_dist_le C hC0 (n + 1))
    have ha := abs_le.mp (Rounding.qval_roundR_dist_le A hA0 (n + 1 + 1))
    have hb := abs_le.mp (Rounding.qval_roundR_dist_le B hB0 (n + 1 + 1))
    have htri : C ≤ A + B := M.d_triangle _ _ _
    have hu : (0:ℝ) < 1 / 2 ^ n := by positivity
    have f2 : (1:ℝ) / 2 ^ (n + 1 + 1) = (1 / 2 ^ n) / 4 := by
      rw [pow_succ, pow_succ]; ring
    have f3 : (1:ℝ) / 2 ^ (n + 1 + 1 + 1) = (1 / 2 ^ n) / 8 := by
      rw [pow_succ, pow_succ, pow_succ]; ring
    rw [f2] at hc
    rw [f3] at ha hb
    linarith [hc.2, ha.1, hb.1]
  have hcast : ((Rounding.qval (Rounding.roundR C (n + 1))
      - (Rounding.qval (Rounding.roundR A (n + 1 + 1))
        + Rounding.qval (Rounding.roundR B (n + 1 + 1))) : ℚ) : ℝ) < ((1 / 2 ^ n : ℚ) : ℝ) := by
    push_cast
    exact key
  exact_mod_cast hcast

-- ============================================================================
-- The `EqXInterp`, for any signature over the metric model
-- ============================================================================

/-- **The `EqXInterp` of any `si` whose distance is `(d(x,y))◦`.** Field for field
`MetricModel.eqXInterp`, which is the instance `si := M.si`, `hd := fun _ _ => rfl`. -/
noncomputable def MetricModel.eqXInterp_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y)) :
    EqXInterp (fun () => M.carrier) F si where
  witnessSubsingleton := fun _ _ _ _ => ⟨fun _ _ => funext fun _ => rfl⟩
  witnessDefault := fun i _ s t => dialecticaDefaultWitness si (eqAtType (Ty.base i) s t)
  counterDefault := fun i _ s t => dialecticaDefaultCounter si (eqAtType (Ty.base i) s t)
  realize := fun () {_Γ} s t env h =>
    realizer_of_pu_at si _ rfl rfl env (M.eqAtType_base_holds_gen si hd s t env h)
  extract := fun i {_Γ} s t env r => M.eqAtType_base_extract_gen si hd i s t env r
  realizeTerm := fun _ _ _ _ => Term.lam Term.unitI
  realizeTerm_sound := fun () {_Γ} s t env h y => by
    have R := realizer_of_pu_at si (eqAtType (Ty.base ()) s t) rfl rfl env
      (M.eqAtType_base_holds_gen si hd s t env h)
    have hsub : Subsingleton
        (dialecticaWitness (fun () => M.carrier) (eqAtType (Ty.base ()) s t)) :=
      ⟨fun _ _ => funext fun _ => rfl⟩
    have hw : Term.interpret si (Term.lam Term.unitI) env = R.val := hsub.elim _ _
    rw [hw]
    exact R.property y
  dist_comm_holds := fun i {_Γ} x y env => M.dist_comm_interp_gen si hd i x y env
  dist_tri_holds := fun i {_Γ} x y z env => M.dist_tri_interp_gen si hd i x y z env

-- ============================================================================
-- Soundness, for any signature over the metric model
-- ============================================================================

/-- **Semantic soundness for any `si` over a metric model**, relative to the truth of the
signature's own premises (`hprem`). The four metric facts `Soundness.lean` asks for are
discharged from `hd` as in `MetricModel.soundness`. -/
theorem MetricModel.soundness_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y))
    {Premises : PremiseSet F}
    (hprem : ∀ {Γ : Ctx MetricSpace.ι} (A : Formula F Γ), Premises ⟨Γ, A⟩ →
      ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret si A env)
    {Γ : Ctx MetricSpace.ι} {allowed : Allowed} {A : Formula F Γ}
    (h : Derivable F allowed Premises A) :
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret si A env :=
  Metatheorems.soundness si hprem
    (fun i {_Γ} x env => by cases i; exact M.eqAtType_base_holds_gen si hd x x env rfl)
    (fun i {_Γ} x y env => M.dist_comm_interp_gen si hd i x y env)
    (fun i {_Γ} x y z env => M.dist_tri_interp_gen si hd i x y z env)
    (fun i {_Γ} x y env hxy => by cases i; exact M.eq_of_eqAtType_base_gen si hd x y env hxy)
    h

-- ============================================================================
-- The two metric majorizability obligations, for any `si`
-- ============================================================================

/-- `0_X` is majorizable, whatever `si` interprets it as: `⌈d(a, 0_X)⌉` works. -/
theorem MetricModel.zeroX_maj_gen (N : ℕ) :
    ∃ z_star : ℕ → Nat, ∀ n ≥ N,
      bezemMaj (X := fun () => M.carrier) M.base (Ty.base ()) (z_star n)
        (si.zeroInterp ()) :=
  ⟨fun _ => ⌈M.d M.ref (si.zeroInterp ())⌉₊, fun _ _ => Nat.le_ceil _⟩

/-- `d_X` is majorized by `distMajorant = λn₁n₂.(n₁+n₂)∘`, for any `si` with `hd`. The proof
is `MetricModel.dist_maj_at`'s, with one `rw [hd]` where the model used to unfold. -/
theorem MetricModel.dist_maj_at_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y)) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι)
        M.distMajorant (si.distInterp ()) := by
  intro _ _
  unfold MetricModel.distMajorant
  have key : ∀ (n₁ n₂ : ℕ) (x y : M.carrier),
      M.base () n₁ x → M.base () n₂ y → M.d x y ≤ ((n₁ + n₂ : ℕ) : ℝ) := by
    intro n₁ n₂ x y hx hy
    have h := M.d_triangle x M.ref y
    rw [M.d_comm x M.ref] at h
    push_cast
    exact h.trans (add_le_add hx hy)
  have self : ∀ a b : ℕ, b ≤ a →
      hatMaj (X := fun () => M.carrier) (xTy →ₜ realTy MetricSpace.ι)
        (fun (p : ℕ) => Rounding.roundR ((a + p : ℕ) : ℝ))
        (fun (q : ℕ) => Rounding.roundR ((b + q : ℕ) : ℝ)) := by
    intro a b hba
    refine ⟨?_, ?_⟩
    · intro p q hpq
      exact Rounding.roundR_maj_pair (by positivity)
        (by exact_mod_cast Nat.add_le_add hba hpq)
    · intro p q hpq
      exact Rounding.roundR_maj_pair (by positivity)
        (by exact_mod_cast Nat.add_le_add_left hpq a)
  refine ⟨?_, ?_⟩
  · intro n₁ x hx
    refine ⟨?_, ?_⟩
    · intro n₂ y hy
      rw [hd]
      exact Rounding.roundR_maj_pair (by positivity) (key n₁ n₂ x y hx hy)
    · exact (self n₁ n₁ (Nat.le_refl _)).2
  · exact fun a b h => self a b h

/-- `dist_maj_at_gen`, `∃`-packaged for `bezemAbstract`. -/
theorem MetricModel.dist_maj_gen
    (hd : ∀ x y, si.distInterp () x y = Rounding.roundR (M.d x y)) (N : ℕ) :
    ∃ f_star : ℕ →
      Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι).hat,
      ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι)
        (f_star n) (si.distInterp ()) :=
  ⟨fun _ => M.distMajorant, M.dist_maj_at_gen si hd N⟩

end Transfer

-- ============================================================================
-- Axiom hygiene
-- ============================================================================

#print axioms MetricModel.eqXInterp_gen
#print axioms MetricModel.soundness_gen
#print axioms MetricModel.dist_maj_gen
#print axioms MetricModel.zeroX_maj_gen

end Metatheorems
