/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Semantics
import Metatheorems.Derivable
import Metatheorems.RealNumbers
import Metatheorems.Rounding
import Metatheorems.Majorizability
import Metatheorems.SyntacticMetatheorem

namespace Metatheorems

/-!
# Metric Spaces as Abstract Spaces

Instantiates the WE-HA^{ω,X} framework for a single metric space (X, d).
Following §5.1 (Definition 5.1.2) of the reference document:

* One abstract base type X (so `ι = Unit`)
* One function constant `d_X : X → X → ℝ` (the metric)
* Zero element `0_X : X` (a distinguished point)
* Equality at type X: `x =_X y ≡ d_X(x,y) =_ℝ 0_ℝ`
* Axioms: reflexivity, symmetry, triangle inequality (pseudo-metric)

## Main Definitions

* `MetricSpace.ι` — the index type `Unit`
* `MetricSpace.F` — the function constant types
* `MetricSpace.EqX` — equality at type X via d
* `MetricSpace.Premises` — the pseudo-metric axioms
* `MetricSpace.admissibleEqX` — EqX is admissible
-/

open Formula

-- ============================================================================
-- Basic setup
-- ============================================================================

/-- Index type for a single metric space: one base type. -/
abbrev MetricSpace.ι := Unit

/-- Abbreviation for the base type X. -/
abbrev xTy : Ty MetricSpace.ι := Ty.base ()

/-- Function constant types for a metric space.
    The single function constant is `d_X : X → X → ℝ` (the metric).
    `ℝ` is encoded as `Ty.nat →ₜ Ty.nat` (type level 1). -/
def MetricSpace.F : MetricSpace.ι → Ty MetricSpace.ι
  | () => xTy →ₜ xTy →ₜ realTy MetricSpace.ι

/-- Shorthand for the metric term d_X in any context. -/
abbrev d_X {Γ : Ctx MetricSpace.ι} :
    Term MetricSpace.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.func ()

-- ============================================================================
-- Equality at type X
-- ============================================================================

/-- Equality at the base type X: `x =_X y ≡ d_X(x,y) =_ℝ 0_ℝ`.
    This is a Π₁⁰ (purely universal) formula since `eq_R` is `∀n. (QF body)`. -/
def MetricSpace.EqX : (i : MetricSpace.ι) →
    {Γ : Ctx MetricSpace.ι} →
    Term MetricSpace.F Γ (Ty.base i) →
    Term MetricSpace.F Γ (Ty.base i) →
    Formula MetricSpace.F Γ :=
  fun () {_} s t => eq_R (Term.app (Term.app (Term.func ()) s) t) Term.zero_R

-- ============================================================================
-- Metric space axioms (Premises)
-- ============================================================================

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

/-- The set of metric space axioms as a `PremiseSet`.
    Context-polymorphic: axioms are closed formulas, available at any context. -/
def MetricSpace.Premises : PremiseSet MetricSpace.F :=
  fun ⟨Γ, A⟩ => A = MetricSpace.ax_refl ∨
                 A = MetricSpace.ax_sym ∨
                 A = MetricSpace.ax_triangle

-- ============================================================================
-- Semantic interpretation
-- ============================================================================

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
  funcInterp := fun () => fun x y => m.metric x y
  zeroInterp := fun () => m.zero

-- ============================================================================
-- Lemma 17.8(4): `≤` on reals gives strong majorization of the codes
-- ============================================================================

/-! `Rounding.lean` proves Lemma 17.8 parts (2),(3),(5),(6); part (4) was blocked there
because it mentions `s-maj₁`, which lives in `StrongMajorizability.lean`. With the two-clause
`bezemMaj` (2026-09-02) it is a corollary of (2) and (3): at type `1 = nat →ₜ nat` the
relation unfolds to a *pair* of monotonicity statements, and (3) discharges the
self-majorization one outright. -/

open Rounding in
/-- **Lemma 17.8(4)**: if `0 ≤ x ≤ y` then `(y)◦` strongly majorizes `(x)◦` at type `1`.

The first conjunct chains 17.8(2) (`(x)◦ ≤₁ (y)◦`) with 17.8(3) (`(y)◦` monotone in the
precision index); the second conjunct *is* 17.8(3).

`_hx` is unused: only `0 ≤ y` is needed, since `roundR_le₁_of_le` rests on `Nat.floor_mono`,
which does not care about sign. The hypothesis is kept because the book states 17.8 for
`x, y ∈ [0,∞)` and callers will have it anyway. -/
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

-- ============================================================================
-- The model, built from a genuine real metric
-- ============================================================================

/-! `MetricSpaceInterp` above takes `metric : carrier → carrier → (ℕ → ℕ)`, i.e. the metric
*already in code form*. That is the wrong starting point for majorization: to majorize `d_X`
one has to know the codes came from actual reals. Kohlenbach builds the model the other way
round — `[dX]_M := λx,y ∈ X.(d(x,y))◦` (p. 430) — so we do too.

Axioms are passed explicitly rather than via a `PseudoMetricSpace` instance, matching the
project's `AdmissibleEqX` precedent. Note this is a **pseudo**metric: the document's premises
are `ax_refl`/`ax_sym`/`ax_triangle` with no separation axiom, and `EqX` is
`d(x,y) =ℝ 0` precisely because points at distance 0 are to be identified. -/
structure MetricModel where
  /-- The carrier. -/
  carrier : Type
  /-- The genuine real-valued (pseudo)metric. -/
  d : carrier → carrier → ℝ
  /-- Distances are non-negative. Needed for `(·)◦`, whose domain is `[0,∞)`. -/
  d_nonneg : ∀ x y, 0 ≤ d x y
  /-- `ax_refl`. -/
  d_self : ∀ x, d x x = 0
  /-- `ax_sym`. -/
  d_comm : ∀ x y, d x y = d y x
  /-- `ax_triangle`. -/
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z
  /-- The distinguished point `0_X`. -/
  zeroX : carrier
  /-- The reference point `a` of Definition 17.50. Majorants depend on it; the *domains* of
      the majorizable functionals do not. -/
  ref : carrier

/-- The interpretation: `d_X` is interpreted by `(d(x,y))◦`.

`noncomputable` because `(·)◦` is `Nat.floor` on a Mathlib real. This does **not** violate the
project's "no `noncomputable` on the extraction path": that path is
`Derivable → NegTrans → Dialectica → Term`, and it stays computable. What is noncomputable is
the *model the extracted bound is interpreted in*, which is a set-theoretic object and was
never going to be executable. -/
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

/-- The two monotonicity facts about `(·)◦` that both `bezemMaj` and `hatMaj` need at type
`1 = nat →ₜ nat`. Stated once because at that type the two relations unfold to *the same*
pair: `bezemMaj` at `.nat` and `hatMaj` at `.nat` are both `≥`. -/
theorem Rounding.roundR_maj_pair {a b : ℝ} (hb : 0 ≤ b) (hab : a ≤ b) :
    (∀ p q : ℕ, p ≥ q → Rounding.roundR b p ≥ Rounding.roundR a q) ∧
    (∀ p q : ℕ, p ≥ q → Rounding.roundR b p ≥ Rounding.roundR b q) := by
  have hmono : Monotone (Rounding.roundR b) :=
    monotone_nat_of_le_succ (Rounding.roundR_mono hb)
  exact ⟨fun p q h => Nat.le_trans (Rounding.roundR_le₁_of_le hab q) (hmono h),
         fun p q h => hmono h⟩

/-- **`d_X` is majorizable**, by `λx⁰,y⁰.(x + y)∘` — the document's majorant
(`particular-cases-metric-spaces.tex:100`), justified by the triangle inequality.

If `n₁ ≽ᵃ_X x` and `n₂ ≽ᵃ_X y`, i.e. `d(a,x) ≤ n₁` and `d(a,y) ≤ n₂`, then
`d(x,y) ≤ d(x,a) + d(a,y) = d(a,x) + d(a,y) ≤ n₁ + n₂`, and Lemma 17.8(4) turns that into
`(n₁+n₂)∘ s-maj₁ (d(x,y))∘`.

The self-majorization half is what the document flags separately — *"We also need to check
that `λx⁰,y⁰.(x+y)∘` majorizes itself"* — and it needs no metric input at all, only that
`m ≥ n → (m)∘ s-maj₁ (n)∘`. -/
theorem MetricModel.func_maj (M : MetricModel) (N : ℕ) :
    ∃ f_star : ℕ → Ty.interpret (fun () => M.carrier) (MetricSpace.F ()).hat,
      ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base (MetricSpace.F ())
        (f_star n) (M.si.funcInterp ()) := by
  -- the binder ascriptions are load-bearing: `Ty.hat` is not reducible, so without them
  -- instance search cannot see that `Ty.interpret X xTy.hat` is `ℕ` and `+` fails to elaborate
  refine ⟨fun _ => fun (n₁ : ℕ) (n₂ : ℕ) => Rounding.roundR ((n₁ + n₂ : ℕ) : ℝ),
          fun _ _ => ?_⟩
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

/-- The metric base relation is upward closed in its numeric argument: if `n ≥ m` and
`d(a,x) ≤ m` then `d(a,x) ≤ n`. This is `BaseMono`, the one extra hypothesis the two-clause
`bezemMaj` forces, and for a metric it is immediate. -/
theorem MetricModel.base_mono (M : MetricModel) :
    BaseMono (X := fun () => M.carrier) M.base := by
  intro i n m x hnm hm
  exact hm.trans (by exact_mod_cast hnm)

/-- **The metric space is an abstract majorizability** — the document's Proposition
(`particular-cases-metric-spaces.tex:51`), assembled.

Every obligation is now discharged:

* the structural conditions and `arrow_intro` — `bezemAbstract`, definitionally;
* `0`, `S` — `bezem_zero_maj` / `bezem_succ_maj`, for any base relation;
* `R` — `bezem_prec_maj`, which is what the two-clause widening bought;
* `0_X`, `d_X` — `zeroX_maj` / `func_maj` above, the only space-specific ones.

`N` is `0`: nothing here needs a threshold, since every majorant is uniform in the index.
That the `ℕ →` indexing does no work is discussed in CLAUDE.md. -/
noncomputable def MetricModel.abstractMajorizability (M : MetricModel) :
    AbstractMajorizability M.si :=
  bezemAbstract M.si M.base 0
    (bezem_zero_maj M.base 0)
    (bezem_succ_maj M.base 0)
    (fun ρ => bezem_prec_maj M.base_mono 0 ρ)
    (fun () => M.func_maj 0)
    (fun () => M.zeroX_maj 0)

-- ============================================================================
-- The metric-space metatheorem
-- ============================================================================

/-- **The metric-space metatheorem.** The document's Theorem for `≽ᵃ`
(`particular-cases-metric-spaces.tex`, item 4), obtained by feeding
`MetricModel.abstractMajorizability` to `syntactic_general_metatheorem`.

From a derivation of `∀x^ρ (∀u B₀ → ∃v C₀)` in the extended system over the pseudo-metric
premises, we get a bound `Φ` depending **only on a majorant of `x`** — i.e. for the base type
`X`, only on a natural `n ≥ d(a,x)`, and not on `x` itself. That independence is the whole
point of the metric metatheorem, and here it is exactly the `X`-clause of `MetricModel.base`.

The two hypotheses that remain are the honest ones:

* `eqxi` — that `EqX () s t ≡ d(s,t) =ℝ 0ℝ` is interpreted correctly in this model;
* `spremise` — a realizing **term** for each of `ax_refl`, `ax_sym`, `ax_triangle`.

Neither is a majorizability question, which is why they are parameters here. `spremise` is
where `MetricModel`'s `d_self` / `d_comm` / `d_triangle` fields will be consumed. -/
theorem MetricModel.metric_metatheorem (M : MetricModel)
    (eqxi : EqXInterp (fun () => M.carrier) MetricSpace.F M.si MetricSpace.EqX)
    (spremise : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula MetricSpace.F Γ'),
      MetricSpace.Premises ⟨Γ', B⟩ → SRealizer M.si B)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.F MetricSpace.EqX Allowed.extended
      MetricSpace.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem eqxi spremise M.abstractMajorizability
    hB_qf hB_vf hC_qf hC_vf prf

/-- Every metric-space premise is purely universal — `eq_R` and `le_R_pu` are Π₁⁰ by
construction, and the axioms only prefix them with `∀x^X`. -/
theorem MetricSpace.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula MetricSpace.F Γ'),
      MetricSpace.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true := by
  rintro Γ' B (rfl | rfl | rfl)
  · exact MetricSpace.ax_refl_pu
  · exact MetricSpace.ax_sym_pu
  · exact MetricSpace.ax_triangle_pu

-- ============================================================================
-- AdmissibleEqX for the metric space EqX
-- ============================================================================

-- substF_nat: follows from eq_R_substF (proved in RealNumbers)
-- eqx_pu:     eq_R is Π₁⁰ by construction (Formula.all over eq0)
-- eqx_refl/sym/trans: derivable from the metric axioms in `MetricSpace.Premises`.
--
-- These are the *whole* of what "instantiating the metric case" means on the equality
-- side, and they are not ℝ-arithmetic debts. `EqX () s t ≡ d(s,t) =ℝ 0ℝ`, so:
--
--   eqx_refl  ← `ax_refl` instantiated at `t`.
--   eqx_sym   ← `ax_sym` + an `eq_R` congruence.
--   eqx_trans ← `ax_triangle` + `add_eq_zero_R` (proved) + `le_zero_eq_zero_R` with its
--               missing non-negativity hypothesis. Non-negativity of `d` is itself
--               derivable — `0 =ℝ d(x,x) ≤ℝ d(x,y) + d(y,x) =ℝ 2·d(x,y)` by ax_refl,
--               ax_triangle and ax_sym — modulo an ℝ lemma `0 ≤ℝ f + f → 0 ≤ℝ f`.
--
-- Before the `Premises` parameter was added to `AdmissibleEqX` these fields quantified
-- over *every* premise set, including the empty one, and were therefore unsatisfiable:
-- `d_X` is an uninterpreted constant, so `metric x y = fun _ => 1` refutes `d(t,t) =ℝ 0ℝ`.
-- The `sorry`s below now stand for unfinished work rather than for a false claim.
-- `eqx_refl` was proved 2026-09-02 (see `MetricSpace.d_self_derivable`); two remain, and they
-- differ from it in kind: `eqx_refl` is a direct instance of `ax_refl`, while these two need
-- *reasoning about* `=ℝ` and so pull in the ℚ/ℝ tower, which takes an `AdmissibleEqX` — the
-- record being defined. See `ARCHITECTURE.md` §1 and §8.

/-- `ax_refl` instantiated at an arbitrary term: `⊢ d(t,t) =ℝ 0ℝ`.

This is `eqx_refl` modulo unfolding `EqX`, and it is the first thing in the file that
*uses* a metric axiom rather than merely stating it. Note the premise set is fixed: this
is not derivable in the empty theory, which is exactly why `AdmissibleEqX` carries
`Premises`. -/
def MetricSpace.d_self_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    (t : Term MetricSpace.F Γ xTy) :
    Derivable MetricSpace.F MetricSpace.EqX a MetricSpace.Premises
      (eq_R (Term.app2 d_X t t) Term.zero_R) := by
  have hax : Derivable MetricSpace.F MetricSpace.EqX a MetricSpace.Premises
      (MetricSpace.ax_refl (Γ := Γ)) := .premise (Or.inl rfl)
  have hinst := Derivable.mp hax
    (Derivable.forall_ax (EqX := MetricSpace.EqX) (allowed := a)
      (Premises := MetricSpace.Premises)
      (A := eq_R (Term.app2 d_X (Term.var .vz) (Term.var .vz)) Term.zero_R) t)
  -- `forall_ax` lands on `A.subst0 t`; push the substitution through `eq_R`.
  simpa only [Formula.subst0, eq_R_substF, Term.subst, Term.subst0_map,
    Term.app2, zero_R_closed_subst] using hinst

def MetricSpace.admissibleEqX : AdmissibleEqX MetricSpace.EqX MetricSpace.Premises where
  substF_nat := fun {_ _} () u v σ => by
    simp only [MetricSpace.EqX, eq_R_substF, Term.subst, Term.app2,
      zero_R_closed_subst]
  eqx_refl := fun {_} {_} {i} t => match i with
    | () => MetricSpace.d_self_derivable t
  eqx_sym := sorry
  eqx_trans := sorry
  eqx_pu := fun () {_} _ _ => eq_R_isPurelyUniversal _ _

/-- **The metric-space metatheorem, from a classical proof.**

`MetricModel.metric_metatheorem` takes an `Allowed.extended` derivation; this one takes a
genuinely classical one (LEM + QF-AC), which is what an actual proof-mining application
produces. It is `syntactic_general_metatheorem_classical` at this model.

This is the combination that `general_metatheorem_classical` cannot deliver: that theorem
asks for a `Majorizability`, i.e. a total majorizer on every semantic value, and a metric
model supplies only an `AbstractMajorizability` (`MetricModel.abstractMajorizability`).

**`adm` is discharged here, not assumed.** `AdmissibleEqX` is a hypothesis of the *general*
metatheorem precisely because `EqX` is abstract there; supplying it is part of what
instantiating to metric spaces consists of, alongside `eqxi` and `spremise`. Taking it back
as a parameter would make this theorem a second abstract metatheorem rather than an
instantiation, and would hide `MetricSpace.admissibleEqX`'s three open fields inside a
binder. So this theorem currently depends on `sorryAx`, visibly and in one place.

`nts` is likewise not a parameter: the premises are purely universal, so `ntStable_of_pu`
supplies it. -/
theorem MetricModel.metric_metatheorem_classical (M : MetricModel)
    (eqxi : EqXInterp (fun () => M.carrier) MetricSpace.F M.si MetricSpace.EqX)
    (spremise : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula MetricSpace.F Γ'),
      MetricSpace.Premises ⟨Γ', B⟩ → SRealizer M.si B)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.F MetricSpace.EqX Allowed.classical
      MetricSpace.Premises []
      (Formula.all ρ (Formula.imp (Formula.all .nat B₀) (Formula.ex .nat C₀)))) :
    ∃ Φ : Ty.interpret (fun () => M.carrier) ρ.hat → Nat,
      ∀ (x : Ty.interpret (fun () => M.carrier) ρ)
        (x_star : Ty.interpret (fun () => M.carrier) ρ.hat),
        M.abstractMajorizability.toRel.maj ρ x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret M.si B₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret M.si C₀ (v, (x, ())) :=
  syntactic_general_metatheorem_classical eqxi MetricSpace.admissibleEqX
    (ntStable_of_pu MetricSpace.admissibleEqX MetricSpace.premises_pu) spremise
    M.abstractMajorizability hB_qf hB_vf hC_qf hC_vf prf

end Metatheorems
