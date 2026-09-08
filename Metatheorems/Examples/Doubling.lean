/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems

/-!
# The doubling example: `∀x ( ∀u (f (S u) =₀ f u +ᵗ f u) → ∃v (f k =₀ v) )`

*If `f` doubles at every step, then `f k` is bounded* — and the metatheorem's `v ≤ Φ x*` is
that bound. `Φ x* = 2^{k*} · f*(0)`, which is exactly `f k`; the doubling in the **proof**
comes out as an exponential in the bound.

This file holds the derivation and nothing else. It is written from **raw `Derivable`
constructors** — `induction`, `forall_ax`, `exist_ax`, `exist_rule`, `syllogism`,
`exportation`, and one quantifier-free extensionality step — 145 constructors in total, with
no proof mode at all. `x = (k, f)` at type `nat ×ₜ (nat →ₜ nat)`, with `k := fst x`,
`f := snd x`. The contexts grow inward: `[x]`, then `[k, x]` under the induction, then
`[u, k, x]` or `[v, k, x]` under the inner quantifier; the abbreviations `f₀ f₁ f₂`, `k₁ k₂`,
`v₂` name the variables by role at each depth.

**Why it lives here rather than in `Demo/Walkthrough.lean`.** The de Bruijn bookkeeping above
is a page of `abbrev`s and intermediate formulas that says nothing about proof mining, and on
a screen it buries the one line that does. The walkthrough now shows the statement, the alias
`Demo.doubling := Examples.Doubling.derivation`, and the extraction; the bookkeeping is here.

**Why raw constructors and not the proof mode.** Measured, in
`Probes/ContentExampleNat.lean`, where this derivation was first built: the *same argument*
written with `pmode/pinduction/pinst/papply/pobtain/pexists/ptrans/prwby` is **42,747**
constructors — 295× — and its bound reduces only at `k* = 0`, against `k* = 7` here. On this
example the proof mode is a liability for extraction, not the route to it (`ARCHITECTURE.md`
§14.8).

Two things that make the extraction a demonstration rather than an anecdote. The premise is
genuinely **consumed** — `forall_ax k` instantiates `∀u B₀` at `u := k`, once per step, so the
extracted `U` reports a property of the proof and not a default. And **no witness term written
by hand mentions `Term.prec`** (the surface-recursor ban, `ProofMode/Linter.lean`): the
iteration in the bound is produced by the extraction, not smuggled into the derivation.
-/

namespace Metatheorems
namespace Examples
namespace Doubling

open Formula ProofMode

/-- The metatheorem's quantified type: `x = (k, f)`. -/
abbrev sTy : Ty Empty := Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat)

abbrev G0 : Ctx Empty := [sTy]
abbrev G1 : Ctx Empty := Ty.nat :: G0
abbrev G2 : Ctx Empty := Ty.nat :: G1

/-- `⊢` in the pure system, at a fixed context. -/
abbrev D (Γ : Ctx Empty) (A : Formula PureWEHA.F Γ) :=
  Derivable PureWEHA.F Allowed.extended PureWEHA.Premises A

abbrev f0 : Term PureWEHA.F G0 (Ty.nat →ₜ Ty.nat) := Term.snd (.var .vz)
abbrev f1 : Term PureWEHA.F G1 (Ty.nat →ₜ Ty.nat) := Term.snd (.var (.vs .vz))
abbrev f2 : Term PureWEHA.F G2 (Ty.nat →ₜ Ty.nat) := Term.snd (.var (.vs (.vs .vz)))
abbrev k1 : Term PureWEHA.F G1 Ty.nat := .var .vz
abbrev k2 : Term PureWEHA.F G2 Ty.nat := .var (.vs .vz)
abbrev v2 : Term PureWEHA.F G2 Ty.nat := .var .vz

/-- `f (S u) =₀ f u +ᵗ f u` — the premise matrix, `u` the bound variable. -/
def B2 : Formula PureWEHA.F G2 := f2 ⬝ S v2 =₀ f2 ⬝ v2 +ᵗ f2 ⬝ v2
/-- `f k =₀ v` — the conclusion matrix. -/
def C2 : Formula PureWEHA.F G2 := f2 ⬝ k2 =₀ v2
/-- `f (S k) =₀ v` — the conclusion matrix at `k+1`. -/
def CS : Formula PureWEHA.F G2 := f2 ⬝ S k2 =₀ v2

/-- The formula inducted on: `∀u B₀ →ᶠ ∃v (f k =₀ v)`. -/
def A1 : Formula PureWEHA.F G1 := Formula.all Ty.nat B2 →ᶠ Formula.ex Ty.nat C2
def P1 : Formula PureWEHA.F G1 := Formula.all Ty.nat B2
def Q1 : Formula PureWEHA.F G1 := Formula.ex Ty.nat C2
def R1 : Formula PureWEHA.F G1 := Formula.ex Ty.nat CS

/-- The premise instance at `u := k`: `f (S k) =₀ f k +ᵗ f k`. -/
def E1f : Formula PureWEHA.F G1 := f1 ⬝ S k1 =₀ f1 ⬝ k1 +ᵗ f1 ⬝ k1
/-- …the same, one binder in. -/
def E2f : Formula PureWEHA.F G2 := f2 ⬝ S k2 =₀ f2 ⬝ k2 +ᵗ f2 ⬝ k2

theorem E2f_eq : Formula.weakenBy Ty.nat E1f = E2f := rfl

/-- **The premise is consumed**, at `u := k`: `(∀u B₀) →ᶠ f (S k) =₀ f k + f k`. -/
def hi : D G1 (P1 →ᶠ E1f) := Derivable.forall_ax (A := B2) k1

/-- The step's one arithmetic fact, a single QF-ER at `r := x₀ +ᵗ x₀`:
`f k =₀ v ⊢ f k + f k =₀ v + v`. -/
def cong2 : D G2 (C2 →ᶠ (f2 ⬝ k2 +ᵗ f2 ⬝ k2 =₀ v2 +ᵗ v2)) :=
  qfer_nat_nf (A₀ := C2) rfl rfl I_comb
    (r := Term.app2 Term.add (.var .vz) (.var .vz)) (by rfl) (by rfl)

/-- `CS` under one more binder: `f (S k) =₀ w`, in `[w, v, k, x]`. -/
def CS3 : Formula PureWEHA.F (Ty.nat :: G2) :=
  Formula.eq0
    (Term.app (Term.snd (.var (.vs (.vs (.vs .vz))))) (Term.app Term.succ (.var (.vs (.vs .vz)))))
    (.var .vz)

theorem CS3_eq : Formula.weakenBy Ty.nat R1 = Formula.ex Ty.nat CS3 := rfl

/-- **The witness is built from the induction hypothesis's witness**: under the `∃`, from
`f k =₀ v` and the premise instance, `f (S k) =₀ v +ᵗ v`, and `exist_ax` at `v +ᵗ v`. -/
def inner3 : D G2 (C2 ∧ᶠ E2f →ᶠ Formula.weakenBy Ty.nat R1) :=
  Derivable.syllogism
    (pair_h and_proj2 (Derivable.syllogism and_proj1 cong2))
    (Derivable.syllogism Derivable.trans0
      (Derivable.exist_ax (v2 +ᵗ v2) CS3))

/-- The ∃-elimination: `ex_and_left` keeps the premise instance available across it. -/
def keyEA : D G1 (E1f ∧ᶠ Q1 →ᶠ R1) :=
  Derivable.syllogism Derivable.and_perm
    (Derivable.syllogism ex_and_left (Derivable.exist_rule inner3))

def key : D G1 (P1 →ᶠ Q1 →ᶠ R1) :=
  Derivable.syllogism hi (Derivable.exportation keyEA)

/-- The induction step, `A1 →ᶠ A1[k := S k]`, by `S_comb` (the premise is used on both
sides of the implication). -/
def stepBody : D G1 ((P1 →ᶠ Q1) →ᶠ (P1 →ᶠ R1)) := Derivable.mp key S_comb

def dummy0 : Formula PureWEHA.F G0 := Term.zero =₀ Term.zero

def stepW : D G1 (Formula.weakenBy Ty.nat dummy0 →ᶠ
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp stepBody (Derivable.exportation Derivable.and_weak)

def stepD : D G0 (Formula.all Ty.nat
    (A1 →ᶠ Formula.substVar0 A1 (Term.app Term.succ (.var .vz)))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule stepW)

/-- The `∃`-body at `k := 0`: `f 0 =₀ v`. -/
def C0 : Formula PureWEHA.F (Ty.nat :: G0) :=
  Formula.eq0 (Term.app (Term.snd (.var (.vs .vz))) Term.zero) (.var .vz)

/-- The base case: witness `f 0`. -/
def baseD : D G0 (A1.subst0 Term.zero) :=
  Derivable.mp
    (Derivable.mp Derivable.refl0 (Derivable.exist_ax (f0 ⬝ Term.zero) C0))
    (Derivable.exportation Derivable.and_weak)

/-- `⊢ ∀k ( ∀u (f (S u) =₀ f u + f u) → ∃v (f k =₀ v) )`, in context `[x]`. -/
def Lraw : D G0 (Formula.all Ty.nat A1) := Derivable.induction baseD stepD

/-- The premise matrix in the metatheorem's shape, `B₀ := f (S u) =₀ f u +ᵗ f u` in `[u, x]`:
`x` is `x₀` (the outer binder), `u` is `x₁`, `f := snd x`. -/
def eB : Formula PureWEHA.F [Ty.nat, sTy] :=
  Term.snd x₀ ⬝ S x₁ =₀ Term.snd x₀ ⬝ x₁ +ᵗ Term.snd x₀ ⬝ x₁

/-- The conclusion matrix, `C₀ := f k =₀ v` in `[v, x]`: `x` is `x₀`, `v` is `x₁`,
`k := fst x`. -/
def eC : Formula PureWEHA.F [Ty.nat, sTy] :=
  Term.snd x₀ ⬝ Term.fst x₀ =₀ x₁

/-- `∀k` instantiated at `k := fst x`. -/
def innerD : D G0 (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC) :=
  Derivable.mp Lraw (Derivable.forall_ax (Term.fst (Term.var .vz)))

def eDummy : Formula PureWEHA.F ([] : Ctx Empty) := Term.zero =₀ Term.zero

def eInnerW : D [sTy] (Formula.weakenBy sTy eDummy →ᶠ
    (Formula.all Ty.nat eB →ᶠ Formula.ex Ty.nat eC)) :=
  Derivable.mp innerD (Derivable.exportation Derivable.and_weak)

/-- **The theorem**:

    ⊢ ∀x^(nat × (nat→nat)) ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f k =₀ v ) )

with `f := snd x`, `k := fst x`. The type is written out rather than stated through `eB`/`eC`,
so that `Demo.doubling` can be a bare alias for it. -/
def derivation : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (Γ := [])
    (Formula.all (Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat))
      (Formula.all Ty.nat (Term.snd x₀ ⬝ S x₁ =₀ Term.snd x₀ ⬝ x₁ +ᵗ Term.snd x₀ ⬝ x₁)
        →ᶠ Formula.ex Ty.nat (Term.snd x₀ ⬝ Term.fst x₀ =₀ x₁))) :=
  Derivable.mp Derivable.refl0 (Derivable.forall_rule eInnerW)

#print axioms derivation

end Doubling
end Examples
end Metatheorems
