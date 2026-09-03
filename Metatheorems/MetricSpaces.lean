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

-- ============================================================================
-- Basic setup
-- ============================================================================

/-- Index type for a single metric space: one base type. -/
abbrev MetricSpace.ι := Unit

/-- Abbreviation for the base type X. -/
abbrev xTy : Ty MetricSpace.ι := Ty.base ()

/-- Function constant types for a metric space.

**There are none.** The metric is no longer a function constant: every base type carries a
structural `Term.dist`, and equality at `X` is *defined* from it (`EqAtType.lean`). `F` must
still assign a type to the one index, so it gets `Ty.unit` — a constant carrying no
information, and one that `Term.unitI` already inhabits.

Leaving the slot free is the point: `F ()` is now available for the next structure in the
tower — W-hyperbolic's `W`, for instance — without needing the `ι`/`κ` split first. -/
def MetricSpace.F : MetricSpace.ι → Ty MetricSpace.ι
  | () => Ty.unit

/-- Shorthand for the metric term d_X in any context.

Now the **structural** `Term.dist ()`, not a function constant. Before this, the model had
two unrelated distances — `Term.func ()`, which the premises spoke about, and `Term.dist ()`,
which `eqAtType` used — interpreted by the same function but joined by no axiom. -/
abbrev d_X {Γ : Ctx MetricSpace.ι} :
    Term MetricSpace.F Γ (xTy →ₜ xTy →ₜ realTy MetricSpace.ι) :=
  Term.dist ()

-- ============================================================================
-- Equality at type X
-- ============================================================================

-- `MetricSpace.EqX` — DELETED. Equality at `X` is now `eqAtType (Ty.base ())`, defined in
-- the core as `d_X(s,t) =ℝ 0ℝ`, so a metric-space-specific restatement would be a synonym.
-- Facts about it live in `BaseEquality.lean`: `eqAtType_refl_base`, `eqAtType_sym_base`.

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

/-- The metric-space premise set is **empty**.

The three axioms above are no longer assumed: `Term.dist` is structural, and `d(x,x) =ℝ 0ℝ`,
`d(x,y) =ℝ d(y,x)`, `d(x,z) ≤ℝ d(x,y) +ℝ d(y,z)` are the constructors `Derivable.dist_self`,
`.dist_comm`, `.dist_tri`. They are kept above as *formulas* — the theorems just below show
each is derivable — because the document names them, and because a future theory may want
to state something relative to them.

An empty premise set is what makes `MetricSpace.premises_pu` and the `spremise` hypothesis
of both metatheorems vacuous. -/
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
  -- `F () = Ty.unit`: there are no function constants any more, the metric is structural.
  funcInterp := fun () => ()
  zeroInterp := fun () => m.zero
  distInterp := fun () => fun x y => m.metric x y

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

Axioms are passed explicitly rather than via a `MetricSpace` instance, matching the project's
precedent for structures of this kind.

**The theory is a pseudometric; the model is a genuine metric space.** The two are
deliberately not the same, and the asymmetry is the point:

* the *theory*'s axioms are `dist_self`/`dist_comm`/`dist_tri` — reflexivity, symmetry,
  triangle — with **no separation**. Keeping the theory weak is what makes every derivation
  in it apply to more structures, so nothing here should ever add separation to `Derivable`;
* the *models* are the separated ones. `EqXInterp.extract` has to turn a Dialectica realizer
  of `d(x,y) =ℝ 0ℝ` into **Lean equality** `x = y` of the interpretations, and only
  separation gives that. A pseudometric model would satisfy every axiom of the theory and
  still fail `extract`.

So `d_eq_zero` below is a *model* condition with no object-level counterpart, exactly as
Kohlenbach's `A^ω[X,d]` is interpreted in genuine metric spaces while its axioms are the
pseudometric ones. -/
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
  /-- **Separation** — the model is a genuine metric space, not merely a pseudometric.

      This has **no object-level counterpart**: the theory deliberately stops at
      reflexivity/symmetry/triangle, so that derivations in it apply to pseudometric
      structures too. It is asked of the *model* because `EqXInterp.extract` must produce
      Lean equality `x = y` from a realizer of `d(x,y) =ℝ 0ℝ`, and nothing weaker than
      separation delivers that. See the structure docstring. -/
  d_eq_zero : ∀ x y, d x y = 0 → x = y
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

/-- **`d_X` is majorizable**, by `λx⁰,y⁰.(x + y)∘` — the document's majorant
(`particular-cases-metric-spaces.tex:100`), justified by the triangle inequality.

If `n₁ ≽ᵃ_X x` and `n₂ ≽ᵃ_X y`, i.e. `d(a,x) ≤ n₁` and `d(a,y) ≤ n₂`, then
`d(x,y) ≤ d(x,a) + d(a,y) = d(a,x) + d(a,y) ≤ n₁ + n₂`, and Lemma 17.8(4) turns that into
`(n₁+n₂)∘ s-maj₁ (d(x,y))∘`.

The self-majorization half is what the document flags separately — *"We also need to check
that `λx⁰,y⁰.(x+y)∘` majorizes itself"* — and it needs no metric input at all, only that
`m ≥ n → (m)∘ s-maj₁ (n)∘`. -/
theorem MetricModel.dist_maj (M : MetricModel) (N : ℕ) :
    ∃ f_star : ℕ →
      Ty.interpret (fun () => M.carrier) (xTy →ₜ xTy →ₜ realTy MetricSpace.ι).hat,
      ∀ n ≥ N, bezemMaj (X := fun () => M.carrier) M.base
        (xTy →ₜ xTy →ₜ realTy MetricSpace.ι)
        (f_star n) (M.si.distInterp ()) := by
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
    -- `F () = Ty.unit`, so the function-constant obligation is vacuous.
    (fun () => ⟨fun _ => (), fun _ _ => trivial⟩)
    (fun () => M.zeroX_maj 0)
    (fun () => M.dist_maj 0)

-- ============================================================================
-- The equality interpretation
-- ============================================================================

/-! ### `EqXInterp` for a metric model — four fields of nine, and why the other five stall

`EqXInterp` is the last hypothesis of the two metric metatheorems that nothing constructed.
`MetricModel.eqXInterp` below constructs it, and is honest about what it cannot yet prove.

**The four structural fields are free.** `eqAtType (.base ()) s t` is `eq_R (d s t) 0ℝ`, a
`Formula.all Ty.nat (Formula.eq0 _ _)`, so `wTy` of it is `nat →ₜ unit` and `cTy` is
`nat ×ₜ unit`. The witness type is therefore `ℕ → Unit`: a subsingleton, canonically
inhabited, and syntactically realized by `λn.⋆`. Nothing about the model enters.

**The five semantic fields all stall on one missing piece, and it is not a metric fact.**
`realize`, `extract`, `realizeTerm_sound`, `dist_comm_holds` and `dist_tri_holds` each ask for
`Formula.interpret M.si (eq_R … ) env` or the `le_R_pu` analogue — that is, for the *value*
of the object-level decision term

    lt_Q_dec (abs_Q (sub_Q (cauchyfy f (n+1)) (cauchyfy g (n+1)))) (pow2neg_Q n)

in the standard model. Every ingredient of that term is a `Term`-level `prec` recursion
(`div2`, `inv_triag`, `lt_Q_dec`, …), and **nothing in the project evaluates one**.
`QVal.lean` says so in as many words: it defines `qval : ℕ → ℚ`, proves
`qval_roundR`/`qval_roundR_dist_le`/`roundR_cauchy` — everything needed *about rationals* —
and then states that connecting `qval` to `Term.interpret` of `Term.rat_num`/`Term.lt_Q_dec`
"is a separate bridge … and is not attempted here".

So the missing lemma is the **evaluation bridge**, of which the load-bearing instance is

```lean
theorem interpret_lt_Q_dec (si : SpaceInterp X F) (a b : Term F Γ Ty.nat) (env) :
    Term.interpret si (Term.app2 Term.lt_Q_dec a b) env = 0
      ↔ Rounding.qval (Term.interpret si a env) < Rounding.qval (Term.interpret si b env)
```

together with its companions for `abs_Q`, `sub_Q`, `pow2neg_Q`, `add_Q` and `cauchyfy`
(`Term.interpret si (Term.app2 Term.cauchyfy f n) env = …`). *With* that bridge the five
fields are short: `dist_comm_holds` is `M.d_comm` (the two sides then have **literally the
same** interpretation, so `qval` reflexivity finishes it), `dist_tri_holds` is `M.d_triangle`
plus `Rounding.qval_roundR_dist_le`, and `realize`/`extract`/`realizeTerm_sound` are
`M.d_self` and `M.d_eq_zero` plus `Rounding.qval_roundR`.

The alternative route — a soundness theorem `Derivable … A → ∀ env, Formula.interpret si A env`,
which would let the object-level `lt_Q_abs_sub_self` discharge `dist_comm_holds` — is
**circular**: soundness's `dist_comm`/`dist_tri` cases are *exactly* these two fields. There
is no soundness theorem in the project, and this is why writing one would not be free.

No `EqXInterp` field is weakened; the five stalled ones carry a `sorry`. See the report and
`ARCHITECTURE.md` §3. -/

-- ============================================================================
-- Evaluating the two sides of `eqAtType` at a base type
-- ============================================================================

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
  -- `wTy (eq_R _ _) = nat →ₜ unit`, so the witness type is `ℕ → Unit`.
  witnessSubsingleton := fun _ _ _ _ => ⟨fun _ _ => funext fun _ => rfl⟩
  witnessDefault := fun i _ s t => dialecticaDefaultWitness M.si (eqAtType (Ty.base i) s t)
  counterDefault := fun i _ s t => dialecticaDefaultCounter M.si (eqAtType (Ty.base i) s t)
  -- `eq_R` is purely universal and ∨-free, so a realizer carries no information and the whole
  -- content is the model fact `eqAtType_base_holds`.
  realize := fun () {_Γ} s t env h =>
    realizer_of_pu_at M.si _ rfl rfl env (M.eqAtType_base_holds s t env h)
  -- The bridge read the other way, plus `M.d_eq_zero` (separation).
  extract := fun i {_Γ} s t env r => M.eqAtType_base_extract i s t env r
  -- MISSING: as `realize` — the realizing term `λn.⋆` carries no information, so this field
  -- is exactly the model fact `realize` needs.
  realizeTerm := fun _ _ _ _ => Term.lam Term.unitI
  -- The witness type is `ℕ → Unit`, a subsingleton, so the realizing *term* carries no
  -- information either: its interpretation is forced to equal the semantic realizer's witness.
  realizeTerm_sound := fun () {_Γ} s t env h y => by
    have R := realizer_of_pu_at M.si (eqAtType (Ty.base ()) s t) rfl rfl env
      (M.eqAtType_base_holds s t env h)
    have hsub : Subsingleton
        (dialecticaWitness (fun () => M.carrier) (eqAtType (Ty.base ()) s t)) :=
      ⟨fun _ _ => funext fun _ => rfl⟩
    have hw : Term.interpret M.si (Term.lam Term.unitI) env = R.val := hsub.elim _ _
    rw [hw]
    exact R.property y
  -- `M.d_comm` makes the two sides interpret to the same `ℕ → ℕ`; what is left is `0 < 2^{-n}`.
  dist_comm_holds := fun i {_Γ} x y env => M.dist_comm_interp i x y env
  -- `M.d_triangle` plus `Rounding.qval_roundR_dist_le` on the three distances, and the
  -- Cauchy-ness of the constructed sum sequence `add_R` builds.
  dist_tri_holds := fun i {_Γ} x y z env => M.dist_tri_interp i x y z env

-- ============================================================================
-- Semantic soundness for the metric model
-- ============================================================================

/-! `Soundness.lean` proves soundness relative to five model facts, taken as section
`variable`s. Until 2026-09-03 none of them was dischargeable for `MetricModel` — `hsep` in
particular *is* `EqXInterp.extract`, and nothing in the project could build one. All five are
now available, and every one is a result proved above:

| hypothesis | discharged by |
|---|---|
| `hprem` | vacuous — `MetricSpace.Premises` is `fun _ => False` |
| `hdist_self` | `eqAtType_base_holds x x rfl` |
| `hdist_comm` | `dist_comm_interp` |
| `hdist_tri` | `dist_tri_interp` |
| `hsep` | `eq_of_eqAtType_base` — separation, i.e. `M.d_eq_zero` |

So the metric model is a genuine model of the whole theory, with no side conditions. -/

/-- **Semantic soundness for a metric model**, unconditionally: everything derivable in
WE-HA^{ω,X} over one metric space is true in that space.

This is the syntactic and semantic halves of the project meeting. Note it is *not* circular
with the metatheorems: `hsep` comes from `M.d_eq_zero` and the evaluation bridge, never from
soundness itself. -/
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

-- ============================================================================
-- The metric-space metatheorem
-- ============================================================================

/-- **The metric-space metatheorem.** The document's Theorem for `≽ᵃ`
(`particular-cases-metric-spaces.tex`, item 4), obtained by feeding
`MetricModel.abstractMajorizability` to `syntactic_general_metatheorem`.

From a derivation of `∀x^ρ (∀u B₀ → ∃v C₀)` in the extended system, we get a bound `Φ`
depending **only on a majorant of `x`** — i.e. for the base type `X`, only on a natural
`n ≥ d(a,x)`, and not on `x` itself. That independence is the whole point of the metric
metatheorem, and here it is exactly the `X`-clause of `MetricModel.base`.

**`spremise` is gone.** `MetricSpace.Premises` is empty — the pseudometric axioms are
constructors of `Derivable`, not assumptions — so the premise-realizer obligation is vacuous
and is discharged inline. One of the three unconstructed hypotheses this theorem used to
carry has therefore ceased to exist rather than been satisfied.

**`eqxi` is gone too, as of the `dist_nonneg` session**: it is discharged internally with
`MetricModel.eqXInterp`. That is the honest state, and it comes at a price stated loudly
here — **`MetricModel.eqXInterp` has five `sorry`-ed fields**, so this theorem now depends on
`sorryAx` where before it merely *assumed* an `EqXInterp` nobody could build. Nothing was
lost: re-abstracting a hypothesis with exactly one intended inhabitant is a `sorry` moved into
a binder (ARCHITECTURE.md §3). The five fields all wait on one missing evaluation bridge; see
the note above `MetricModel.eqXInterp`.

Historical note, kept because it is the shape of a mistake worth not repeating: `spremise`
was where `MetricModel`'s `d_self`/`d_comm`/`d_triangle` were *going* to be consumed. They
are consumed by `EqXInterp` now instead, on the semantic side, which is cheaper — the
obligation is real-number arithmetic in Mathlib `ℝ` rather than object-level ℝ codes. -/
theorem MetricModel.metric_metatheorem (M : MetricModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.F Allowed.extended
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
premises. The three axioms are constructors of `Derivable` now, not assumptions.

The `ax_*_pu` theorems above are kept: they still record that the three *formulas* are Π⁰₁,
which is what makes the corresponding constructors' Dialectica witness types singletons. -/
theorem MetricSpace.premises_pu :
    ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula MetricSpace.F Γ'),
      MetricSpace.Premises ⟨Γ', B⟩ → B.isPurelyUniversal = true :=
  fun _ _ h => h.elim

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

Once `Term.dist` became structural this stopped needing a premise at all — it is the
`dist_self` constructor. Kept under its old name because the notes refer to it, and because
it records where the metric-space `=_X` reflexivity comes from.

The history is worth keeping: this used to be `.premise ax_refl` + `forall_ax`, and it was
the *only* one of the three `=_X` equivalence properties that worked that way. Symmetry and
transitivity are not instances of an axiom — they need reasoning about `=ℝ` — and that
asymmetry is what exposed the whole `AdmissibleEqX` circularity. See ARCHITECTURE.md §1. -/
def MetricSpace.d_self_derivable {Γ : Ctx MetricSpace.ι} {a : Allowed}
    {P : PremiseSet MetricSpace.F} (t : Term MetricSpace.F Γ xTy) :
    Derivable MetricSpace.F a P (eq_R (Term.app2 d_X t t) Term.zero_R) :=
  .dist_self () t

-- `MetricSpace.admissibleEqX` is GONE, because the structure it inhabited is gone: `EqX` is
-- no longer a parameter and `AdmissibleEqX` was deleted with it (Stage 3). Each of its five
-- fields survives somewhere else, which is the whole point of the restructuring:
--
--   `substF_nat` → `eqAtType_base_substF`  (a theorem, `EqAtType.lean`)
--   `eqx_pu`     → `eqAtType_base_isPurelyUniversal`  (a theorem, `EqAtType.lean`)
--   `eqx_refl`   → `Derivable.dist_self`  (a constructor; cf. `d_self_derivable` above,
--                  which is the same statement for the *premise*-based `d_X = func ()`)
--   `eqx_sym`    → owed: `Derivable.dist_comm` + symmetry of `eq_R`
--   `eqx_trans`  → owed: `Derivable.dist_tri` + transitivity of `eq_R`
--
-- The last two were `sorry` here and are now the two `sorry`s in `Arithmetic.lean`'s
-- `eqAtType_sym`/`eqAtType_trans` at `.base`. Nothing was proved and nothing was lost; the
-- obligation moved to where the ℝ layer can discharge it. See ARCHITECTURE.md §8.

/-- **The metric-space metatheorem, from a classical proof.**

`MetricModel.metric_metatheorem` takes an `Allowed.extended` derivation; this one takes a
genuinely classical one (LEM + QF-AC), which is what an actual proof-mining application
produces. It is `syntactic_general_metatheorem_classical` at this model.

This is the combination that `general_metatheorem_classical` cannot deliver: that theorem
asks for a `Majorizability`, i.e. a total majorizer on every semantic value, and a metric
model supplies only an `AbstractMajorizability` (`MetricModel.abstractMajorizability`).

**`adm` is gone, not discharged.** This theorem used to take an `AdmissibleEqX` parameter,
and then (correctly) to discharge it with `MetricSpace.admissibleEqX` — which was `sorry`-ed,
so the theorem depended on `sorryAx`. The structure no longer exists: base-type equality is
defined rather than parameterised, and its equivalence properties are theorems
(`BaseEquality.lean`) or constructors (`Derivable.dist_self`/`dist_comm`/`dist_tri`).

`spremise` and `nts` are likewise gone: `MetricSpace.Premises` is empty, so both are vacuous
and are supplied inline.

**And `eqxi` is now discharged rather than assumed**, by `MetricModel.eqXInterp` — so all
three of the hypotheses this theorem once carried have gone. Read the loud caveat on
`MetricModel.metric_metatheorem`: `eqXInterp` has five `sorry`-ed fields, so this theorem
depends on `sorryAx`. That is the truthful accounting of what instantiating to metric spaces
still owes, and it was previously hidden inside the `eqxi` binder. -/
theorem MetricModel.metric_metatheorem_classical (M : MetricModel)
    {ρ : Ty MetricSpace.ι} {B₀ C₀ : Formula MetricSpace.F [Ty.nat, ρ]}
    (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
    (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
    (prf : @Derivable MetricSpace.ι MetricSpace.F Allowed.classical
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

-- ============================================================================
-- Axiom hygiene
-- ============================================================================
-- `MetricModel.eqXInterp`'s five fields were `sorry` until 2026-09-03; all five are now
-- constructed, so both metatheorems are `sorryAx`-free. `Classical.choice` is expected and
-- unavoidable: `Rounding.qval` lands in Mathlib `ℚ` and `roundR` is a `Nat.floor`.
-- These prints are the evidence — a falling `sorry` count is not (CLAUDE.md note 5).

#print axioms MetricModel.abstractMajorizability
#print axioms MetricModel.dist_maj
#print axioms MetricModel.zeroX_maj
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
