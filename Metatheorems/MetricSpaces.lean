/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable
import Metatheorems.RealNumbers
import Metatheorems.Rounding
import Metatheorems.QValBridge
import Metatheorems.Majorizability
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Soundness

namespace Metatheorems

/-!
# Metric Spaces as Abstract Spaces

Instantiates the WE-HA^{ω,X} framework for a single metric space (X, d).
Following §5.1 (Definition 5.1.2) of the reference document:

* One abstract base type X (so `ι = Unit`)
* One function constant `d_X : X → X → ℝ` (the metric)
* Zero element `0_X : X` (a distinguished point)
* Equality at type X: `x =_X y ≡ d_X(x,y) =_ℝ 0_ℝ`
* Axioms: reflexivity, symmetry, triangle inequality — a **pseudometric theory**

The theory is a pseudometric one and the intended **models are genuine metric spaces**
(`MetricModel.d_eq_zero`). That gap is deliberate, not an oversight: weaker axioms mean the
derivations apply to more structures, while `EqXInterp.extract` needs separation on the model
side. See `MetricModel`'s docstring.

## Main Definitions

* `MetricSpace.ι` — the index type `Unit`
* `MetricSpace.F` — the function constant types (there are none; `F () = Ty.unit`)
* `MetricSpace.Premises` — empty: the three axioms are `Derivable` constructors
* `MetricModel` — a separated model, with `abstractMajorizability` and `eqXInterp`
-/

open Formula

-- Basic setup

/-- Index type for a single metric space: one base type. -/
abbrev MetricSpace.ι := Unit

/-- Abbreviation for the base type X. -/
abbrev xTy : Ty MetricSpace.ι := Ty.base ()

/-- Function constant types for a metric space. **There are none**: the metric is the
structural `Term.dist`. `F` assigns `Ty.unit` to the one index. -/
def MetricSpace.F : MetricSpace.ι → Ty MetricSpace.ι
  | () => Ty.unit

/-- Shorthand for the metric term d_X in any context: the **structural** `Term.dist ()`. -/
abbrev d_X {Γ : Ctx MetricSpace.ι} :
    Term MetricSpace.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.dist ()

-- Equality at type X

-- Equality at `X` is `eqAtType (Ty.base ())`, defined in the core as `d_X(s,t) =ℝ 0ℝ`.
-- Facts about it live in `BaseEquality.lean`: `eqAtType_refl_base`, `eqAtType_sym_base`.

-- Metric space axioms (Premises)

-- Following Definition 5.1.2 of the reference document.

/-- Axiom 1: ∀x^X. d(x,x) =_ℝ 0_ℝ  (reflexivity of the metric).
    Context-polymorphic: axiom is closed (no free variables), valid in any context. -/
def MetricSpace.ax_refl {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy
    (eq_R (Term.app2 d_X (Term.var .vz) (Term.var .vz)) Term.zero_R)

/-- Axiom 2: ∀x^X,y^X. d(x,y) =_ℝ d(y,x)  (symmetry of the metric).
    Context-polymorphic. -/
def MetricSpace.ax_sym {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy (Formula.all xTy
    (eq_R (Term.app2 d_X (Term.var (.vs .vz)) (Term.var .vz))
          (Term.app2 d_X (Term.var .vz) (Term.var (.vs .vz)))))

/-- Axiom 3: ∀x^X,y^X,z^X. d(x,z) ≤_ℝ d(x,y) +_ℝ d(y,z)
    (triangle inequality). Uses le_R_pu for purely universal form.
    Context-polymorphic. -/
def MetricSpace.ax_triangle {Γ : Ctx MetricSpace.ι} : Formula MetricSpace.F Γ :=
  Formula.all xTy (Formula.all xTy (Formula.all xTy
    (le_R_pu
      (Term.app2 d_X (Term.var (.vs (.vs .vz))) (Term.var .vz))
      (Term.app2 Term.add_R
        (Term.app2 d_X (Term.var (.vs (.vs .vz))) (Term.var (.vs .vz)))
        (Term.app2 d_X (Term.var (.vs .vz)) (Term.var .vz))))))

-- Verify axioms are purely universal (needed for Premises)
theorem MetricSpace.ax_refl_pu :
    (MetricSpace.ax_refl (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem MetricSpace.ax_sym_pu :
    (MetricSpace.ax_sym (Γ := Γ)).isPurelyUniversal = true := by rfl

theorem MetricSpace.ax_triangle_pu :
    (MetricSpace.ax_triangle (Γ := Γ)).isPurelyUniversal = true := by rfl

/-- The metric-space premise set is **empty**: the three axioms above are the constructors
`Derivable.dist_self`, `.dist_comm`, `.dist_tri`. -/
def MetricSpace.Premises : PremiseSet MetricSpace.F :=
  fun _ => False

/-- `ax_refl` is derivable — it is `dist_self`, universally generalised. -/
def MetricSpace.ax_refl_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    {P : PremiseSet MetricSpace.F} :
    Derivable MetricSpace.F a P (MetricSpace.ax_refl (Γ := Γ)) :=
  univ_gen (.dist_self () (Term.var .vz))

/-- `ax_sym` is derivable — it is `dist_comm`, universally generalised twice. -/
def MetricSpace.ax_sym_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    {P : PremiseSet MetricSpace.F} :
    Derivable MetricSpace.F a P (MetricSpace.ax_sym (Γ := Γ)) :=
  univ_gen (univ_gen (.dist_comm () (Term.var (.vs .vz)) (Term.var .vz)))

/-- `ax_triangle` is derivable — it is `dist_tri`, universally generalised three times. -/
def MetricSpace.ax_triangle_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    {P : PremiseSet MetricSpace.F} :
    Derivable MetricSpace.F a P (MetricSpace.ax_triangle (Γ := Γ)) :=
  univ_gen (univ_gen (univ_gen
    (.dist_tri () (Term.var (.vs (.vs .vz))) (Term.var (.vs .vz)) (Term.var .vz))))

-- Semantic interpretation

/-- The type of metric space interpretations. Packages the carrier type,
    the metric function, and the distinguished point. -/
structure MetricSpaceInterp where
  /-- The carrier type of the metric space. -/
  carrier : Type
  /-- The metric function d : X × X → (ℕ → ℕ) (encoded reals). -/
  metric : carrier → carrier → (Nat → Nat)
  /-- The distinguished point 0_X. -/
  zero : carrier

/-- Build a `SpaceInterp` from a `MetricSpaceInterp`. -/
def MetricSpaceInterp.toSpaceInterp (m : MetricSpaceInterp) :
    SpaceInterp (fun () => m.carrier) MetricSpace.F where
  -- `F () = Ty.unit`: there are no function constants any more, the metric is structural.
  funcInterp := fun () => ()
  zeroInterp := fun () => m.zero
  distInterp := fun () => fun x y => m.metric x y

-- Lemma 17.8(4): `≤` on reals gives strong majorization of the codes

open Rounding in
/-- **Lemma 17.8(4)**: if `0 ≤ x ≤ y` then `(y)◦` strongly majorizes `(x)◦` at type `1`.

The first conjunct chains 17.8(2) (`(x)◦ ≤₁ (y)◦`) with 17.8(3) (`(y)◦` monotone in the
precision index); the second conjunct *is* 17.8(3). -/
theorem roundR_smaj_of_le {ι : Type} {X : ι → Type}
    {base : (i : ι) → Nat → X i → Prop} {x y : ℝ}
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    bezemMaj (X := X) base (Ty.nat →ₜ Ty.nat) (roundR y) (roundR x) := by
  have hmono : ∀ (a : ℝ), 0 ≤ a → Monotone (roundR a) :=
    fun a ha => monotone_nat_of_le_succ (roundR_mono ha)
  refine ⟨?_, ?_⟩
  · -- majorization: (y)◦(n*) ≥ (x)◦(n) whenever n* ≥ n
    intro n_star n h
    exact Nat.le_trans (roundR_le₁_of_le hxy n) (hmono y hy h)
  · -- self-majorization: (y)◦ is monotone in the precision index
    intro n_star n h
    exact hmono y hy h

-- The model, built from a genuine real metric

/-! A metric model is built from a genuine real metric, `[dX]_M := λx,y ∈ X.(d(x,y))◦`
(p. 430). **The theory is a pseudometric; the model is a genuine metric space**: separation
(`d_eq_zero` below) is a *model* condition with no object-level counterpart. -/
structure MetricModel where
  /-- The carrier. -/
  carrier : Type
  /-- The genuine real-valued metric. -/
  d : carrier → carrier → ℝ
  /-- Distances are non-negative. Needed for `(·)◦`, whose domain is `[0,∞)`. -/
  d_nonneg : ∀ x y, 0 ≤ d x y
  /-- `ax_refl`. -/
  d_self : ∀ x, d x x = 0
  /-- `ax_sym`. -/
  d_comm : ∀ x y, d x y = d y x
  /-- `ax_triangle`. -/
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z
  /-- **Separation** — the model is a genuine metric space, not merely a pseudometric. It has
      **no object-level counterpart**; `EqXInterp.extract` needs it. -/
  d_eq_zero : ∀ x y, d x y = 0 → x = y
  /-- The distinguished point `0_X`. -/
  zeroX : carrier
  /-- The reference point `a` of Definition 17.50. Majorants depend on it; the *domains* of
      the majorizable functionals do not. -/
  ref : carrier

/-- The interpretation: `d_X` is interpreted by `(d(x,y))◦`. -/
noncomputable def MetricModel.toMetricSpaceInterp (M : MetricModel) : MetricSpaceInterp where
  carrier := M.carrier
  metric := fun x y => Rounding.roundR (M.d x y)
  zero := M.zeroX

/-- The `SpaceInterp` this model induces. -/
noncomputable def MetricModel.si (M : MetricModel) :
    SpaceInterp (fun () => M.carrier) MetricSpace.F :=
  M.toMetricSpaceInterp.toSpaceInterp

/-- **The `X`-clause of `≽ᵃ`** (Definition 17.50): `n ≽ᵃ_X x :≡ (n)ℝ ≥ℝ d(a, x)`.

Kohlenbach notes (p. 430) this is equivalent to `n ≥ d(a,x)` outright, which is how we state
it — the `(·)◦` wrapper on the left would only be undone again. -/
def MetricModel.base (M : MetricModel) : (i : MetricSpace.ι) → Nat → M.carrier → Prop
  | (), n, x => M.d M.ref x ≤ (n : ℝ)

/-- **`0_X` is majorizable**: take any `n ≥ d(a, 0_X)`. -/
theorem MetricModel.zeroX_maj (M : MetricModel) (N : ℕ) :
    ∃ z_star : ℕ → Nat, ∀ n ≥ N,
      bezemMaj (X := fun () => M.carrier) M.base (Ty.base ()) (z_star n)
        (M.si.zeroInterp ()) :=
  ⟨fun _ => ⌈M.d M.ref M.zeroX⌉₊, fun _ _ => Nat.le_ceil _⟩

/-- **`d_X` is majorizable**, by `λx⁰,y⁰.(x + y)∘` — the document's majorant
(`particular-cases-metric-spaces.tex:100`), justified by the triangle inequality.

If `n₁ ≽ᵃ_X x` and `n₂ ≽ᵃ_X y`, i.e. `d(a,x) ≤ n₁` and `d(a,y) ≤ n₂`, then
`d(x,y) ≤ d(x,a) + d(a,y) = d(a,x) + d(a,y) ≤ n₁ + n₂`, and Lemma 17.8(4) turns that into
`(n₁+n₂)∘ s-maj₁ (d(x,y))∘`. The majorant is named (`distMajorant`) and the proof is
`dist_maj_at`; `dist_maj` itself is the `∃`-packaging `bezemAbstract` consumes. -/
noncomputable def MetricModel.distMajorant (M : MetricModel) :
    Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι).hat :=
  -- the binder ascriptions are load-bearing: `Ty.hat` is not reducible, so without them
  -- instance search cannot see that `Ty.interpret X xTy.hat` is `ℕ` and `+` fails to elaborate
  fun (n₁ : ℕ) (n₂ : ℕ) => Rounding.roundR ((n₁ + n₂ : ℕ) : ℝ)

/-- **`distMajorant` evaluates**: at naturals `n₁, n₂` and precision `k` it is the closed
ℕ-expression `j(2·(n₁+n₂)·2^{k+1}, 2^{k+1} − 1)`. `Rounding.roundR_natCast`, specialised. -/
theorem MetricModel.distMajorant_apply (M : MetricModel) (n₁ n₂ k : ℕ) :
    M.distMajorant n₁ n₂ k =
      Rounding.pairN (2 * ((n₁ + n₂) * 2 ^ (k + 1))) (2 ^ (k + 1) - 1) :=
  Rounding.roundR_natCast (n₁ + n₂) k

/-- `dist_maj` with its witness named. Same relationship as `bezem_prec_maj_at` to
`bezem_prec_maj`. The majorant `λn₁⁰n₂⁰.(n₁+n₂)∘` mentions the model only through its *type*
(the carrier family), never through `M.d`: it is a closed `ℕ → ℕ → (ℕ → ℕ)`, and at natural
arguments it evaluates by `Rounding.roundR_natCast`. -/
theorem MetricModel.dist_maj_at (M : MetricModel) (N : ℕ) :
    ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι)
        M.distMajorant (M.si.distInterp ()) := by
  intro _ _
  unfold MetricModel.distMajorant
  -- `d(x,y) ≤ n₁ + n₂` from the two `X`-clause hypotheses and the triangle inequality
  have key : ∀ (n₁ n₂ : ℕ) (x y : M.carrier),
      M.base () n₁ x → M.base () n₂ y → M.d x y ≤ ((n₁ + n₂ : ℕ) : ℝ) := by
    intro n₁ n₂ x y hx hy
    have h := M.d_triangle x M.ref y
    rw [M.d_comm x M.ref] at h
    push_cast
    exact h.trans (add_le_add hx hy)
  -- the self-majorization block, shared: `(a + ·)∘` dominates `(b + ·)∘` whenever `b ≤ a`
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
  · -- majorization
    intro n₁ x hx
    refine ⟨?_, ?_⟩
    · intro n₂ y hy
      exact Rounding.roundR_maj_pair (by positivity) (key n₁ n₂ x y hx hy)
    · -- `(n₁ + ·)∘` majorizes itself
      exact (self n₁ n₁ (Nat.le_refl _)).2
  · -- self-majorization of the whole majorant. `bezemMaj`'s second conjunct is a single
    -- ∀-statement, not a nested pair — so this is exactly `self`.
    exact fun a b h => self a b h

/-- **`d_X` is majorizable** — `dist_maj_at`, `∃`-packaged for `bezemAbstract`. -/
theorem MetricModel.dist_maj (M : MetricModel) (N : ℕ) :
    ∃ f_star : ℕ →
      Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι).hat,
      ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι)
        (f_star n) (M.si.distInterp ()) :=
  ⟨fun _ => M.distMajorant, M.dist_maj_at N⟩

/-- The metric base relation is upward closed in its numeric argument: if `n ≥ m` and
`d(a,x) ≤ m` then `d(a,x) ≤ n`. This is `BaseMono`, the one extra hypothesis the two-clause
`bezemMaj` forces, and for a metric it is immediate. -/
theorem MetricModel.base_mono (M : MetricModel) :
    BaseMono (X := fun () => M.carrier) M.base := by
  intro i n m x hnm hm
  exact hm.trans (by exact_mod_cast hnm)

/-- **The metric space is an abstract majorizability** — the document's Proposition
(`particular-cases-metric-spaces.tex:51`), assembled from `bezemAbstract` and the two
space-specific obligations `zeroX_maj` / `func_maj`. `N` is `0`. -/
noncomputable def MetricModel.abstractMajorizability (M : MetricModel) :
    AbstractMajorizability M.si :=
  bezemAbstract M.si M.base M.base_mono 0
    (bezem_zero_maj M.base 0)
    (bezem_succ_maj M.base 0)
    (fun ρ => bezem_prec_maj M.base_mono 0 ρ)
    -- `F () = Ty.unit`, so the function-constant obligation is vacuous.
    (fun () => ⟨fun _ => (), fun _ _ => trivial⟩)
    (fun () => M.zeroX_maj 0)
    (fun () => M.dist_maj 0)

-- The majorants as DATA: `ConstMajorants` for the metric model

/-! `constMajorants` below is the six majorants of `abstractMajorizability` as data, which is
what `termMajorizer`/`closedMajorizer` need to run: `0`, `S`, `R`, `unitI`-typed `F ()` as
for `bezemConstMajorantsEmpty`; `d_X ↦ distMajorant`; and `0_X ↦ n₀`, the one
space-dependent number, `n₀ ≥ d(a, 0_X)`, a *parameter*. -/

/-- **The metric model's constant majorants, as data**, parameterised by a bound
`n₀ ≥ d(a, 0_X)`. The one hypothesis `h` is `M.base () n₀ M.zeroX`, i.e. `n₀ ≽ᵃ_X 0_X`.

`noncomputable` only through `distMajorant`'s `Rounding.roundR` on a Mathlib real; see
`Rounding.roundR_natCast` for why that does not stop the numbers from coming out. -/
noncomputable def MetricModel.constMajorants (M : MetricModel) (n₀ : ℕ)
    (h : M.d M.ref M.zeroX ≤ (n₀ : ℝ)) : ConstMajorants M.abstractMajorizability where
  zeroM := fun _ => 0
  zeroM_maj := fun _ _ => Nat.le_refl 0
  succM := fun _ => Nat.succ
  succM_maj := fun _ _ =>
    ⟨fun _ _ h => Nat.succ_le_succ h, fun _ _ h => Nat.succ_le_succ h⟩
  precM := fun ρ _ => fun y_star z_star n => recMaj ρ y_star z_star n
  precM_maj := fun ρ => bezem_prec_maj_at M.base_mono 0 ρ
  -- `F () = Ty.unit`: the majorant is `()` and the obligation is `True`
  funcM := fun () _ => ()
  funcM_maj := fun () _ _ => trivial
  zeroXM := fun _ _ => n₀
  zeroXM_maj := fun () _ _ => h
  distM := fun _ _ => M.distMajorant
  distM_maj := fun () => M.dist_maj_at 0

/-! ### The majorants compute

Kernel-checked, not `#eval`ed. `M` and `h` are variables throughout: the majorant depends on
the model only through the number `n₀` it was handed. -/

section ComputesDemo

/-- `0_X`'s majorant is the parameter, for any `n₀`. -/
example (M : MetricModel) (n₀ : ℕ) (h : M.d M.ref M.zeroX ≤ (n₀ : ℝ)) :
    n₀ = closedMajorizer (M.constMajorants n₀ h)
      (Term.zeroX (F := MetricSpace.F) (Γ := []) ()) := by
  simp [closedMajorizer, termMajorizer, MetricModel.constMajorants,
    MetricModel.abstractMajorizability, bezemAbstract]

/-- **`d_X(0_X, 0_X)`'s majorant, evaluated at precision index `0`, with `n₀ = 5`**:
`(5 + 5)∘(0) = j(2·10·2¹, 2¹ − 1) = j(40, 1) = triag(41) + 40 = 861 + 40 = 901`. -/
example (M : MetricModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (901 : ℕ) = closedMajorizer (M.constMajorants 5 h)
      (Term.app (Term.app (Term.dist (F := MetricSpace.F) (Γ := []) ())
        (Term.zeroX ())) (Term.zeroX ())) ((0 : ℕ)) := by
  simp only [closedMajorizer, termMajorizer, MetricModel.constMajorants,
    MetricModel.abstractMajorizability, bezemAbstract, MetricModel.distMajorant_apply]
  decide

end ComputesDemo

-- The equality interpretation

/-! ### `EqXInterp` for a metric model — what each field costs

`MetricModel.eqXInterp` below constructs the interface in full. The structural part is not a
field at all (`eqAtTypeBaseWitness`, `eqAtTypeBaseCounter`, `eqAtTypeBaseRealizeTerm`); the
four semantic fields `realize`, `extract`, `dist_comm_holds` and `dist_tri_holds` rest on the
evaluation bridge of `QValBridge.lean` (`interpret_lt_Q_dec` and its companions). No
`EqXInterp` field is weakened. -/

-- Evaluating the two sides of `eqAtType` at a base type

/-- `(0)◦` denotes the rational `0` at every precision. -/
theorem qval_roundR_zero (n : ℕ) : Rounding.qval (Rounding.roundR 0 n) = 0 := by
  rw [Rounding.qval_roundR]
  simp [Rounding.k0]

/-- `d_X` is interpreted by `(d(x,y))◦`.  Unfolding the three wrappers by hand, once. -/
theorem MetricModel.interp_dist (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    (s t : Term MetricSpace.F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Term.interpret M.si (Term.app2 (Term.dist ()) s t) env
      = Rounding.roundR (M.d (Term.interpret M.si s env) (Term.interpret M.si t env)) := by
  simp only [Term.app2, Term.interpret, MetricModel.si, MetricSpaceInterp.toSpaceInterp,
    MetricModel.toMetricSpaceInterp]

/-- `0ℝ` is the constant zero sequence, at the `qval` level. -/
theorem MetricModel.qval_interp_zero_R (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    (env : Ctx.interpret (fun () => M.carrier) Γ) (k : ℕ) :
    Rounding.qval (Term.interpret M.si (Term.zero_R (F := MetricSpace.F) (Γ := Γ)) env k) = 0 := by
  -- Take the `lam` step with `Term.interpret`'s own equations and stop there: `zero_Q` is a
  -- `def`, so `simp only` cannot descend into its `pair` spine.  A `rfl` here instead would
  -- force that descent and blow the heartbeat budget.
  have hstep : Term.interpret M.si (Term.zero_R (F := MetricSpace.F) (Γ := Γ)) env
      = fun v => Term.interpret M.si (Term.zero_Q (F := MetricSpace.F) (Γ := Ty.nat :: Γ))
          (v, env) := by
    simp only [Term.zero_R, Term.interpret]
  rw [hstep]
  -- Name the implicits: leaving `si`/`Δ` to unification makes it search through
  -- `Ty.interpret X Ty.nat` (only *reducibly* `ℕ`) and exhaust the heartbeat budget.
  exact QBridge.qval_interpret_zero_Q (si := M.si) (Δ := Ty.nat :: Γ) (k, env)

/-- `cauchyfy` fixes `0ℝ`: the constant sequence passes every check. -/
theorem MetricModel.cauchyfyN_zero_R (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    (env : Ctx.interpret (fun () => M.carrier) Γ) (n : ℕ) :
    Rounding.qval (QBridge.cauchyfyN
      (Term.interpret M.si (Term.zero_R (F := MetricSpace.F) (Γ := Γ)) env) n) = 0 := by
  rw [QBridge.cauchyfyN_id_of_cauchy _ (fun k => by
    rw [M.qval_interp_zero_R env k, M.qval_interp_zero_R env (k + 1)]
    simpa using (by positivity : (0:ℚ) < 1 / 2 ^ (k + 1)))]
  exact M.qval_interp_zero_R env n

/-- `cauchyfy` fixes a distance code: `(r)◦` is Cauchy at the sharp rate, by 17.8(1). -/
theorem cauchyfyN_roundR (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    QBridge.cauchyfyN (Rounding.roundR r) n = Rounding.roundR r n :=
  QBridge.cauchyfyN_id_of_cauchy _ (fun k => Rounding.roundR_cauchy r hr k) n

/-- **The model fact behind `realize`**: if two base-type terms have the same interpretation,
the object-level `s =_X t` holds in the model.  `M.d_self` collapses the distance to `0`, and
both sides are then the constant zero rational sequence. -/
theorem MetricModel.eqAtType_base_holds (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    (s t : Term MetricSpace.F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : Term.interpret M.si s env = Term.interpret M.si t env) :
    Formula.interpret M.si (eqAtType (Ty.base ()) s t) env := by
  show Formula.interpret M.si (eq_R (Term.app2 (Term.dist ()) s t) Term.zero_R) env
  rw [QBridge.interpret_eq_R]
  intro n
  rw [M.interp_dist s t env, h, M.d_self, cauchyfyN_roundR 0 le_rfl, qval_roundR_zero,
    M.cauchyfyN_zero_R env]
  simpa using (by positivity : (0:ℚ) < 1 / 2 ^ n)

/-- **The model fact behind `extract`**, and the one place separation is used.

If `s =_X t` holds in the model then every rounding `(d(s,t))◦(n+1)` is within `2^{-n}` of
zero, and `(·)◦` is within `2^{-(n+2)}` of the real it rounds (17.8), so `d(s,t)` is below
every positive bound and hence `0`.  `M.d_eq_zero` — separation — then gives `s = t`.
A pseudometric model would stop one step short here, which is exactly why the field exists. -/
theorem MetricModel.eq_of_eqAtType_base (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    (s t : Term MetricSpace.F Γ (Ty.base ())) (env : Ctx.interpret (fun () => M.carrier) Γ)
    (h : Formula.interpret M.si (eqAtType (Ty.base ()) s t) env) :
    Term.interpret M.si s env = Term.interpret M.si t env := by
  refine M.d_eq_zero _ _ ?_
  set r := M.d (Term.interpret M.si s env) (Term.interpret M.si t env) with hr_def
  have hr : 0 ≤ r := M.d_nonneg _ _
  rw [show eqAtType (Ty.base ()) s t
      = eq_R (Term.app2 (Term.dist ()) s t) Term.zero_R from rfl,
    QBridge.interpret_eq_R] at h
  -- Every rounding of `r` is within `2^{-n}` of `0`, as a rational.
  have hq : ∀ n : ℕ, |((Rounding.qval (Rounding.roundR r (n + 1)) : ℚ) : ℝ)| < 1 / 2 ^ n := by
    intro n
    have hn := h n
    rw [M.interp_dist s t env, ← hr_def, cauchyfyN_roundR r hr, M.cauchyfyN_zero_R env] at hn
    have hQ : |Rounding.qval (Rounding.roundR r (n + 1))| < 1 / 2 ^ n := by simpa using hn
    calc |((Rounding.qval (Rounding.roundR r (n + 1)) : ℚ) : ℝ)|
        = ((|Rounding.qval (Rounding.roundR r (n + 1))| : ℚ) : ℝ) := (Rat.cast_abs _).symm
      _ < ((1 / 2 ^ n : ℚ) : ℝ) := by exact_mod_cast hQ
      _ = 1 / 2 ^ n := by push_cast; ring
  -- `(·)◦` is within `2^{-(n+2)}` of the real it rounds, so `r` is below every positive bound.
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
    have hd := abs_le.mp hdist
    linarith [hd.1, hd.2, habs.1, habs.2, h2]
  linarith

/-- `extract`'s content, isolated from the structure instance so that its elaboration cost is
paid once and its errors are legible. -/
theorem MetricModel.eqAtType_base_extract (M : MetricModel) (i : MetricSpace.ι)
    {Γ : Ctx MetricSpace.ι} (s t : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ)
    (r : dialecticaRealizerCtx M.si (eqAtType (Ty.base i) s t) env) :
    Term.interpret M.si s env = Term.interpret M.si t env := by
  -- Keep `i` a parameter rather than matching `()` in the field: matching there forces the
  -- elaborator to reduce `dialecticaRealizerCtx` at the specialised index while unifying `r`,
  -- which exhausts the heartbeat budget.  Here the reduction is paid once, in isolation.
  cases i
  exact M.eq_of_eqAtType_base s t env
    (interp_of_realizer_pu M.si (eqAtType (Ty.base ()) s t) rfl rfl env r)

/-- **`dist_comm_holds`'s content**, isolated from the structure instance for the same reason
`eqAtType_base_extract` is: `i` stays a parameter and is cased inside.

`M.d_comm` makes the two sides interpret to *literally the same* `ℕ → ℕ`, so after
`interpret_eq_R` the goal is `|q −ℚ q| <ℚ 2^{-n}`, i.e. `0 < 2^{-n}`.  No `cauchyfy` analysis
is needed at all — the two `cauchyfyN` applications are applied to the same argument. -/
theorem MetricModel.dist_comm_interp (M : MetricModel) (i : MetricSpace.ι)
    {Γ : Ctx MetricSpace.ι} (x y : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (eq_R (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y x)) env := by
  cases i
  rw [QBridge.interpret_eq_R]
  intro n
  rw [M.interp_dist x y env, M.interp_dist y x env, M.d_comm]
  simpa using (by positivity : (0:ℚ) < 1 / 2 ^ n)

/-- **`dist_tri_holds`'s content.**

This is the one field the S3 sidestep does not close by itself: `le_R_pu`'s right-hand side is
`add_R (d x y) (d y z)`, so the outer `cauchyfy` wraps a *constructed* sum sequence rather than
a rounding.  That sequence is Cauchy nonetheless, and at the sharp rate: by
`interpret_add_R_app2` its `k`-th value is `(A)◦(k+1) + (B)◦(k+1)`, so consecutive values differ
by at most twice `2^{-(k+2)}` — exactly `2^{-(k+1)}`, which is what the check tests.

The estimate is then the triangle inequality with three rounding errors: `2^{-(n+2)}` on the
left and `2^{-(n+3)}` on each summand, totalling `2^{-(n+1)} < 2^{-n}`. -/
theorem MetricModel.dist_tri_interp (M : MetricModel) (i : MetricSpace.ι)
    {Γ : Ctx MetricSpace.ι} (x y z : Term MetricSpace.F Γ (Ty.base i))
    (env : Ctx.interpret (fun () => M.carrier) Γ) :
    Formula.interpret M.si
      (le_R_pu (Term.app2 (Term.dist i) x z)
        (Term.app2 Term.add_R
          (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))) env := by
  cases i
  set A := M.d (Term.interpret M.si x env) (Term.interpret M.si y env) with hA
  set B := M.d (Term.interpret M.si y env) (Term.interpret M.si z env) with hB
  set C := M.d (Term.interpret M.si x env) (Term.interpret M.si z env) with hC
  have hA0 : 0 ≤ A := M.d_nonneg _ _
  have hB0 : 0 ≤ B := M.d_nonneg _ _
  have hC0 : 0 ≤ C := M.d_nonneg _ _
  -- The sum sequence, with both summands already known Cauchy so `cauchyfy` is the identity.
  set S : ℕ → ℕ := fun m =>
    QBridge.addQN (Rounding.roundR A (m + 1)) (Rounding.roundR B (m + 1)) with hS
  have hgfun : Term.interpret M.si
      (Term.app2 Term.add_R (Term.app2 (Term.dist ()) x y)
        (Term.app2 (Term.dist ()) y z)) env = S := by
    funext m
    rw [QBridge.interpret_add_R_app2, M.interp_dist, M.interp_dist, ← hA, ← hB,
      cauchyfyN_roundR A hA0, cauchyfyN_roundR B hB0]
  -- `qval` of the sum sequence, once and for all.
  have hSq : ∀ m : ℕ, Rounding.qval (S m)
      = Rounding.qval (Rounding.roundR A (m + 1))
        + Rounding.qval (Rounding.roundR B (m + 1)) := fun m => QBridge.qval_addQN _ _
  -- `S` is Cauchy at the sharp rate: each summand drifts by `< 2^{-(k+2)}`.
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
  rw [M.interp_dist x z env, ← hC, cauchyfyN_roundR C hC0, hgfun,
    QBridge.cauchyfyN_id_of_cauchy S hScauchy, hSq]
  -- Now a purely real estimate, transported back to ℚ.
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

/-- The `EqXInterp` a metric model induces. -/
noncomputable def MetricModel.eqXInterp (M : MetricModel) :
    EqXInterp (fun () => M.carrier) MetricSpace.F M.si where
  -- `eq_R` is purely universal and ∨-free, so a realizer carries no information and the whole
  -- content is the model fact `eqAtType_base_holds`.
  realize := fun () {_Γ} s t env h =>
    realizer_of_pu_at M.si _ rfl rfl env (M.eqAtType_base_holds s t env h)
  -- The bridge read the other way, plus `M.d_eq_zero` (separation).
  extract := fun i {_Γ} s t env r => M.eqAtType_base_extract i s t env r
  -- `M.d_comm` makes the two sides interpret to the same `ℕ → ℕ`; what is left is `0 < 2^{-n}`.
  dist_comm_holds := fun i {_Γ} x y env => M.dist_comm_interp i x y env
  -- `M.d_triangle` plus `Rounding.qval_roundR_dist_le` on the three distances, and the
  -- Cauchy-ness of the constructed sum sequence `add_R` builds.
  dist_tri_holds := fun i {_Γ} x y z env => M.dist_tri_interp i x y z env

-- Semantic soundness for the metric model

/-! `Soundness.lean`'s five model facts are discharged as follows:

| hypothesis | discharged by |
|---|---|
| `hprem` | vacuous — `MetricSpace.Premises` is `fun _ => False` |
| `hdist_self` | `eqAtType_base_holds x x rfl` |
| `hdist_comm` | `dist_comm_interp` |
| `hdist_tri` | `dist_tri_interp` |
| `hsep` | `eq_of_eqAtType_base` — separation, i.e. `M.d_eq_zero` |

So the metric model is a genuine model of the whole theory, with no side conditions. -/

/-- **Semantic soundness for a metric model**, unconditionally: everything derivable in
WE-HA^{ω,X} over one metric space is true in that space. -/
theorem MetricModel.soundness (M : MetricModel) {Γ : Ctx MetricSpace.ι}
    {allowed : Allowed} {A : Formula MetricSpace.F Γ}
    (h : Derivable MetricSpace.F allowed MetricSpace.Premises A) :
    ∀ env : Ctx.interpret (fun () => M.carrier) Γ, Formula.interpret M.si A env :=
  Metatheorems.soundness M.si
    (fun _ hp => hp.elim)
    (fun i {_Γ} x env => by cases i; exact M.eqAtType_base_holds x x env rfl)
    (fun i {_Γ} x y env => M.dist_comm_interp i x y env)
    (fun i {_Γ} x y z env => M.dist_tri_interp i x y z env)
    (fun i {_Γ} x y env hxy => by cases i; exact M.eq_of_eqAtType_base x y env hxy)
    h

/-- **The object theory is consistent**, relative to the existence of one metric space:
`⊥ᶠ` is not derivable. A direct corollary of soundness, and the first statement in the
project that rules anything *out*. -/
theorem MetricModel.not_derivable_bot (M : MetricModel) {allowed : Allowed}
    (h : Derivable MetricSpace.F allowed MetricSpace.Premises (Γ := []) ⊥ᶠ) : False :=
  M.soundness h ()

-- The metric-space metatheorem

/-- **The metric-space metatheorem.** The document's Theorem for `≽ᵃ`
(`particular-cases-metric-spaces.tex`, item 4), obtained by feeding
`MetricModel.abstractMajorizability` to `syntactic_general_metatheorem`.

From a derivation of `∀x^ρ (∀u B₀ → ∃v C₀)` in the extended system, we get a bound `Φ`
depending **only on a majorant of `x`** — i.e. for the base type `X`, only on a natural
`n ≥ d(a,x)`, and not on `x` itself. That independence is the whole point of the metric
metatheorem, and here it is exactly the `X`-clause of `MetricModel.base`.

The premise set is empty, so the premise-realizer obligation is discharged inline, and the
equality interpretation is `MetricModel.eqXInterp`. The `#print axioms` block at the bottom of
the file is the authority for what the theorem rests on. -/
theorem MetricModel.metric_metatheorem (M : MetricModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.ι MetricSpace.F Allowed.extended
      MetricSpace.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem M.eqXInterp (fun _ _ h => h.elim) M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- Every metric-space premise is purely universal — **vacuously**, since there are no
premises. The three axioms are constructors of `Derivable` now, not assumptions. -/
theorem MetricSpace.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula MetricSpace.F Γ'),
      MetricSpace.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true :=
  fun _ _ h => h.elim

-- Equality at the base type

-- Base-type equality is *defined*, so reflexivity, symmetry and transitivity are
-- `Derivable.dist_self` and the theorems `BaseEquality.eqAtType_sym_base` /
-- `eqAtType_trans_base`.

/-- `d(t,t) =ℝ 0ℝ` at an arbitrary term.

Once `Term.dist` became structural this stopped needing a premise at all — it is the
`dist_self` constructor. -/
def MetricSpace.d_self_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    {P : PremiseSet MetricSpace.F} (t : Term MetricSpace.F Γ xTy) :
    Derivable MetricSpace.F a P (eq_R (Term.app2 d_X t t) Term.zero_R) :=
  .dist_self () t

/-- **The metric-space metatheorem, from a classical proof.**

`MetricModel.metric_metatheorem` takes an `Allowed.extended` derivation; this one takes a
genuinely classical one (LEM + QF-AC), which is what an actual proof-mining application
produces. It is `syntactic_general_metatheorem_classical` at this model.
`MetricSpace.Premises` is empty, so `spremise` and `nts` are supplied inline.

The `#print axioms` block at the bottom of the file is the authority for what this theorem
rests on: `[propext, Classical.choice, Quot.sound]`. -/
theorem MetricModel.metric_metatheorem_classical (M : MetricModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.ι MetricSpace.F Allowed.classical
      MetricSpace.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem_classical M.eqXInterp
    (ntStable_of_pu MetricSpace.premises_pu) (fun _ _ h => h.elim)
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

-- Axiom hygiene
-- `MetricModel.eqXInterp` is fully constructed, so both metatheorems are `sorryAx`-free.
-- `Classical.choice` is expected and unavoidable: `Rounding.qval` lands in Mathlib `ℚ` and
-- `roundR` is a `Nat.floor`. These prints are the evidence — a falling `sorry` count is not.
-- Extend this block, do not delete from it, when anything above changes.

#print axioms MetricModel.abstractMajorizability
#print axioms MetricModel.dist_maj
#print axioms MetricModel.dist_maj_at
#print axioms MetricModel.zeroX_maj
#print axioms MetricModel.constMajorants
#print axioms MetricModel.distMajorant_apply
#print axioms MetricModel.eqAtType_base_holds
#print axioms MetricModel.eq_of_eqAtType_base
#print axioms MetricModel.eqAtType_base_extract
#print axioms MetricModel.dist_comm_interp
#print axioms MetricModel.dist_tri_interp
#print axioms MetricModel.eqXInterp
#print axioms MetricModel.soundness
#print axioms MetricModel.not_derivable_bot
#print axioms MetricModel.metric_metatheorem
#print axioms MetricModel.metric_metatheorem_classical

end Metatheorems
