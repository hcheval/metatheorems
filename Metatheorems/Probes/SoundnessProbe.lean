/-
SCRATCH PROBE — deliberately NOT imported by `Metatheorems.lean`.

Question: does a *parameterised* semantic soundness theorem

    Derivable F allowed Premises A → ∀ env, Formula.interpret si A env

taking the `dist` model-facts as explicit hypotheses break the circularity, and thereby
discharge three of the five sorried fields of `MetricModel.eqXInterp`?

This file does NOT prove soundness. It ASSUMES soundness as a section variable and checks
(a) whether the needed interpretation-congruence exists / is cheap, and
(b) which fields then actually follow.

VERDICT (everything below compiles, zero `sorry`):

* The congruence question is CHEAP. `eq_R_interp_congr` / `le_R_pu_interp_congr` are
  three-line `simp only`s; they did not exist, and they are the reusable part of this probe.
  One genuinely missing general lemma turned up: `Formula.interpret_substF`, the formula-level
  counterpart of `Term.interpret_substF`. It is 10 lines and any soundness theorem needs it
  (`forall_ax`, `exist_ax`, `qfer`, `induction`, `ac`, `qfac`).
  `Formula.interpret_renameF_gen` (weakening) already exists in `MetatheoremPrereqs.lean`.

* Given soundness, `realize`, `realizeTerm_sound` and `dist_comm_holds` do follow — see
  `probe_realize_truth`, `probe_realize`, `probe_dist_comm`.

* BUT soundness is NOT provable from the two `dist_comm`/`dist_tri` facts alone. See
  `probe_beta_needs_dist_self` at the bottom: the `beta_eq` case at a base type reduces,
  by the very same congruence, to `eq_R (d w w) 0ℝ` — which IS `realize`'s model content.
  So the parameterised soundness would have to take `realize` as a hypothesis, and
  `realize` is therefore not freed. `rec_zero`, `rec_succ` and `qfer` force the same thing;
  `qfer` additionally forces `extract` (it must turn semantic `eqAtType` back into Lean
  equality of interpretations before substituting).
-/
import Metatheorems.MetricSpaces

namespace Metatheorems
namespace SoundnessProbe

-- Step 2a. The congruence question.

/-- **The congruence lemma.** `eq_R f g` mentions `f`, `g` only as `f.weaken`, `g.weaken`
under a single `∀n`, so its interpretation factors through the interpreted values. -/
theorem eq_R_interp_congr {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (f f' g g' : Term F Γ (realTy ι))
    (env : Ctx.interpret X Γ)
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

/-- Same for the purely-universal `≤ℝ`, which `dist_tri_holds` is stated with. -/
theorem le_R_pu_interp_congr {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (f f' g g' : Term F Γ (realTy ι))
    (env : Ctx.interpret X Γ)
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

-- A lemma the project does NOT have, and which any soundness theorem needs
-- (`forall_ax`, `exist_ax`, `qfer`, `induction`, `ac`, `qfac` all use it).
-- Mirrors `Term.interpret_substF`, which does exist.

theorem Formula.interpret_substF {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ Δ : Ctx ι} (A : Formula F Γ) (σ : Term.Subst F Γ Δ)
    (env : Ctx.interpret X Δ) :
    Formula.interpret si (A.substF σ) env
      = Formula.interpret si A (Ctx.interpretSubst si σ env) := by
  induction A generalizing Δ with
  | bot => rfl
  | eq0 a b => simp only [Formula.substF, Formula.interpret, Term.interpret_substF]
  | and _ _ ihA ihB => simp only [Formula.substF, Formula.interpret, ihA, ihB]
  | or _ _ ihA ihB => simp only [Formula.substF, Formula.interpret, ihA, ihB]
  | imp _ _ ihA ihB => simp only [Formula.substF, Formula.interpret, ihA, ihB]
  | all _ _ ih =>
      simp only [Formula.substF, Formula.interpret, ih, Ctx.interpretSubst_ext]
  | ex _ _ ih =>
      simp only [Formula.substF, Formula.interpret, ih, Ctx.interpretSubst_ext]

theorem Formula.interpret_subst0 {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} {ρ : Ty ι} (A : Formula F (ρ :: Γ))
    (u : Term F Γ ρ) (env : Ctx.interpret X Γ) :
    Formula.interpret si (A.subst0 u) env
      = Formula.interpret si A (Term.interpret si u env, env) := by
  simp only [Formula.subst0, Formula.interpret_substF, Ctx.interpretSubst_subst0_map]

-- Steps 2b / 3. Assume soundness; see which fields fall out.

section Assumed

variable (M : MetricModel)

/-- Soundness, ASSUMED. -/
abbrev Soundness : Prop :=
  ∀ {Γ : Ctx MetricSpace.ι} (A : Formula MetricSpace.F Γ),
    @Derivable MetricSpace.ι MetricSpace.ι MetricSpace.F Allowed.extended
      MetricSpace.Premises Γ A →
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env

variable (snd : Soundness M)

include snd

/-- **The `realize` field's model content, from assumed soundness.**
`Derivable.dist_self` gives `eq_R (d s s) 0ℝ`; congruence moves it to `eq_R (d s t) 0ℝ`. -/
theorem probe_realize_truth (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι}
    (s t : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : Term.interpret M.si s env = Term.interpret M.si t env) :
    Formula.interpret M.si (eqAtType (Ty.base i) s t) env := by
  have hself := snd _ (Derivable.dist_self (Γ := Γ) i s) env
  refine (eq_R_interp_congr M.si _ _ _ _ env ?_ rfl).mp hself
  simp only [Term.app2, Term.interpret, h]

/-- The lift to a realizer.  Note the shape mismatch: `realizer_of_pu` asks for the formula
to be true at EVERY env, while `EqXInterp.realize` supplies its hypothesis at ONE env. So the
hypothesis here is strengthened to `∀ e`.  This is not a real obstacle — `realizer_of_pu`'s
`.all` case only ever needs truth at *extensions* of the given env, so a single-env variant
is a routine restatement — but it is an extra lemma the project does not have. -/
noncomputable def probe_realize (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι}
    (s t : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : ∀ e : Ctx.interpret (fun () => M.carrier) Γ,
      Term.interpret M.si s e = Term.interpret M.si t e) :
    dialecticaRealizerCtx M.si (eqAtType (Ty.base i) s t) env :=
  realizer_of_pu M.si _ rfl rfl (fun e => probe_realize_truth M snd i s t e (h e)) env

/-- **`dist_comm_holds` from assumed soundness**: `M.d_comm` makes both sides interpret to
the *same* `ℕ → ℕ`, so congruence reduces it to `eq_R f f`, i.e. soundness applied to the
`dist`-free object-level `eq_R_refl`. -/
theorem probe_dist_comm (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι}
    (x y : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env := by
  have hall := snd _ (eq_R_refl (F := MetricSpace.F) (al := Allowed.extended)
    (Premises := MetricSpace.Premises) (Γ := Γ)) env
  -- instantiate the object-level `∀f` at `d(x,y)`, using the substitution semantics
  have hinst := hall (Term.interpret M.si (Term.app2 (Term.dist i) x y) env)
  have hrefl : Formula.interpret M.si
      (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) x y)) env := by
    have hsub := Formula.interpret_subst0 M.si (eq_R (Γ := _) (.var .vz) (.var .vz))
      (Term.app2 (Term.dist i) x y) env
    have h2 : Formula.interpret M.si
        ((eq_R (Γ := _) (.var .vz) (.var .vz)).subst0
          (Term.app2 (Term.dist i) x y)) env := by
      rw [hsub]; exact hinst
    rw [Formula.subst0, eq_R_substF] at h2
    exact h2
  refine (eq_R_interp_congr M.si _ _ _ _ env rfl ?_).mp hrefl
  cases i
  simp only [Term.app2, Term.interpret, MetricModel.si, MetricSpaceInterp.toSpaceInterp,
    MetricModel.toMetricSpaceInterp, M.d_comm]

end Assumed

-- THE OBSTRUCTION. Soundness cannot be proved without `realize`'s own content.

section Obstruction

variable (M : MetricModel)

/-- `dist_self_holds`: the model fact that `Derivable.dist_self` needs. It is
`EqXInterp.realize`'s content, modulo `realizer_of_pu` (see `probe_realize`). -/
abbrev DistSelfHolds : Prop :=
  ∀ (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι} (s : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ),
    Formula.interpret M.si (eq_R (Term.app2 (Term.dist i) s s) Term.zero_R) env

/-- **The `beta_eq` case of soundness, at a base type, IS `dist_self_holds`.**

`beta_eq` is stated with `eqAtType τ`, and at `τ = .base i` that is `eq_R (d · ·) 0ℝ`. The two
interpretations are equal by `Term.interpret_subst0`, so congruence reduces the case to
`eq_R (d w w) 0ℝ` — i.e. exactly `hself`, which is `EqXInterp.realize`'s model content.

Hence a *parameterised* soundness taking only the two `dist_comm`/`dist_tri` facts is NOT
provable: it must also take this one, and taking it means `realize` is assumed, not derived.
The same obligation arises from `rec_zero`, `rec_succ` and `qfer` at base types. -/
theorem probe_beta_needs_dist_self (hself : DistSelfHolds M)
    (i : MetricSpace.ι) {Γ : Ctx MetricSpace.ι} {ρ : Ty MetricSpace.ι}
    (body : Term MetricSpace.F (ρ :: Γ) (Ty.base i)) (u : Term MetricSpace.F Γ ρ)
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (eqAtType (Ty.base i) (Term.app (Term.lam body) u) (Term.subst0 body u)) env := by
  refine (eq_R_interp_congr M.si _
    (Term.app2 (Term.dist i) (Term.subst0 body u) (Term.subst0 body u)) _ _ env ?_ rfl).mpr
    (hself i _ env)
  simp only [Term.app2, Term.interpret, Term.interpret_subst0]

end Obstruction

#print axioms eq_R_interp_congr
#print axioms le_R_pu_interp_congr
#print axioms Formula.interpret_substF
#print axioms Formula.interpret_subst0
#print axioms probe_realize_truth
#print axioms probe_realize
#print axioms probe_dist_comm
#print axioms probe_beta_needs_dist_self

end SoundnessProbe
end Metatheorems
