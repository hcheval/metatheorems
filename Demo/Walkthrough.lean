/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems
import Metatheorems.Hilbert
import Metatheorems.Examples.Doubling
-- Nothing from `Metatheorems/Probes/`: probes are measurements. The `ι = Empty` setting is
-- `Metatheorems/PureWEHA.lean`, `kernel_rfl` is `Metatheorems/KernelRfl.lean`, and both
-- derivations of §6 are written out below.

/-!
# The live walkthrough — scroll from the top, one part at a time

A Lean 4 formalization of **WE-HA^{ω,X}** (Kohlenbach's weakly extensional Heyting arithmetic
in all finite types over an abstract space `X`), Gödel's **Dialectica** interpretation, and the
proof-mining **metatheorems** that turn a proof into a bound.

Six parts, in the order they are meant to be shown:

| § | what is on the screen | costs |
|---|---|---|
| 1 | the proof mode: first contact on pure logic, then `x + y = y + x` by induction | instant |
| 1c–1d | the two questions the mode invites: QF-ER, the deduction theorem | instant |
| 2 | the same tactics at a **metric space**: the chained triangle inequality | ~2 s |
| 3 | …and at a **W-hyperbolic space**: extensionality of the convex combination `W` | ~1 s |
| 4 | the **same theorem as §1 from bare `Derivable` constructors** — the contrast | instant |
| 5 | `#hilbert`: what those seven tactic lines actually *denote* | ~2 s |
| 6 | **extraction** — one premise, two proofs: a linear bound and an exponential one, each printed | see below |

**Every extraction in §6 is written twice**: once here, commented out, ready to be
uncommented and run on stage with its measured wall-clock time beside it; and once,
uncommented and kernel-checked on every build, in `Metatheorems/Probes/DemoChecks.lean`
(which imports *this* file, so the derivations checked there are literally the ones below —
commented code cannot rot into a lie).

## How to build it

    scripts/build.sh Demo        -- this file
    scripts/build.sh Probes      -- this file plus DemoChecks, which verifies §6

`Demo` is a `lean_lib` but is **not** in `defaultTargets`, so a plain `lake build` is
unaffected.

## Two things to say out loud, because a number on a slide invites the wrong reading

* The bounds below are **magnitudes**, deliberately. Anything routed through this project's
  ℚ/ℝ encoding comes out as a Cantor **pairing code** (`pairN a b = triagN (a+b) + a`), and
  comparing two such codes compares encoded rationals, not sizes. §6 stays at `ι = Empty`,
  where every value is a plain natural number.
* The claim this project defends is **verified mechanical extraction**, not competitive
  bounds. Kohlenbach's own tool is the monotone functional interpretation applied by hand with
  simplification at every step; a machine that never simplifies pays for it.
-/

namespace Metatheorems
namespace Demo

open Formula ProofMode

/-! ============================================================================
# §1. First contact: the proof mode, on pure logic and then on arithmetic

`Derivable F al Premises A` is a **`Type`**: a proof is a term whose head constructors are the
inference rules of the object logic. That makes the object logic a first-class citizen — but a
Hilbert system has no deduction theorem, so writing anything by hand is combinator soup (§4).

The proof mode supplies the deduction theorem. `Seq Δ B` is *definitionally*
`Derivable … (pack Δ B)`, where `pack` folds the hypothesis list `Δ` into a chain of `→ᶠ`, so
`pintro` costs nothing and there is **nothing to verify about the proof mode**: a buggy tactic
can only fail to elaborate. There is no soundness theorem for it and there does not need to be.

The statement below is composition of implications — `(A → B) → (B → C) → (A → C)` — in the
*object* language. `→ᶠ` is object implication; `A`, `B`, `C` are arbitrary object formulas over
an arbitrary signature, so nothing about arithmetic, spaces or the real numbers is involved.
============================================================================ -/

section PureLogic

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}
variable {Γ : Ctx ι} {A B C : Formula F Γ}

/-- **Composition of implications**, in the object logic:
`⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)`.

Seven tactic lines. `pmode` opens the hypothesis context; each `pintro` moves an antecedent
into it; `papply h in ha with h1` is forward reasoning — apply the hypothesis `h` to the
hypothesis `ha`, naming the result `h1`; `pexact` closes.

Read on screen, this is an ordinary natural-deduction proof. What it *is* is a term of an
inductive type whose constructors are Hilbert axioms — §5 prints it. -/
def compose_pm : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := by
  pmode
  pintro hAB
  pintro hBC
  pintro ha
  papply hAB in ha with hb
  papply hBC in hb with hc
  pexact hc

/-- The same tactics, one step shorter: contraction, `⊢ (A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B`.
Kept because it is the cheapest possible `#hilbert` target in §5 — abstract formulas, so no
arithmetic constant can enter the rendering and the listing measures the *proof-mode layer*
rather than the size of the formulas in it. -/
def contract_pm : Derivable F al Premises ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) := by
  pmode
  pintro h
  pintro ha
  papply h in ha with h1
  papply h1 in ha with h2
  pexact h2

end PureLogic

/-! ## 1b. The same mode with induction and rewriting: `x + y = y + x`

Pure logic needs neither. Arithmetic needs both, and they are the two things a Hilbert system
makes painful: induction is a *rule* whose premises are stated through substitution (`A[0]`
and `∀n (A[n] → A[Sn])`), and "substituting equals for equals" exists only as
quantifier-free extensionality (`Derivable.qfer`) — the system is *weakly* extensional, and
full extensionality is deliberately unavailable because it would break the metatheorems.

The script below is the textbook one — induct on the second argument, rewrite by the two
defining equations of `+`, use the induction hypothesis — and it is Mathlib's `Nat.add_comm`
script with two differences. `anorm` normalises the substitutions `pinduction` leaves in the
goal (`A.subst0 0`, `A[Sn]`), which the hand-written proof pays as three separate `simp only`
lemmas. And the rewrite splits in two: `prw` rewrites by a *closed* equation, `prwby` by a
*hypothesis* — forced by QF-ER carrying a premise.

`x₀` is the bound variable (a token, `Term.var Var.vz`), and `x` is used under the `∀`
binder as itself: a `scoped` coercion inserts the weakening, so the goal reads `x`, never
`x.weaken`.

Compare `Metatheorems.add_comm` in `Arithmetic.lean`: the same theorem from raw constructors,
using the same four lemmas, in 38 lines — the §1/§4 contrast with induction in it. §5 renders
this proof too: 49 Hilbert steps at depth 0, 198 at depth 4, arithmetic constants and all.
(Restated from `ProofMode.ByScript.add_comm`.) -/

section Arithmetic

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **Commutativity of addition**: `⊢ ∀y (x + y =₀ y + x)`, by induction on `y`. -/
def demo_add_comm (x : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.eq0 (x +ᵗ x₀) (x₀ +ᵗ x))) := by
  pmode
  pinduction
  · -- x + 0 = 0 + x
    anorm
    prw (add_zero_r x)
    prw (add_zero_l x)
    prefl
  · pforall
    pintro ih
    anorm
    -- x + Sy = S(x + y) = S(y + x) = Sy + x
    prw (add_succ _ _)
    prw (add_succ_l _ _)
    prwby ih
    prefl

end Arithmetic

/-! ============================================================================
# §1c. "Doesn't `prw` let you cheat on quantifier-free extensionality?"

It cannot, and the refusals are on screen below.

`WE-HA^{ω,X}` is **weakly** extensional: the only substitution-of-equals it has is
`Derivable.qfer`, which turns `s =₀ t` into `r[s] =₀ r[t]` for a *term* abstraction `r`, under
the side conditions that the premise formula be quantifier-free and ∨-free. Full
extensionality is not merely absent, it is **deliberately excluded** — it is what would break
the metatheorems.

`prw`/`prwby` are the tactics that look like Lean's `rw`, and each one *emits a `qfer`
application*, discharging `A₀.isQF = true` and `A₀.isVFree = true` by `rfl`
(`ProofMode/Rewrite.lean`). Nothing else is available to them, so anything QF-ER does not
license is refused at elaboration time.

Two refusals follow, each of a rewrite Lean's own `rw` performs without blinking, each
checked on **every build** by `#guard_msgs` (the expected error is the docstring; if the
tactic ever stopped refusing, this file would fail to compile), and each paired with the
legitimate route to the same theorem.
============================================================================ -/

section WeakExtensionality

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}

/-- **What QF-ER does license**: rewrite inside a *term*, under a hypothesis. -/
def demo_qfer_ok (f : Term F Γ (Ty.nat →ₜ Ty.nat)) (s t : Term F Γ Ty.nat) :
    Derivable F al Premises (s =₀ t →ᶠ f ⬝ s =₀ f ⬝ t) := by
  pmode
  pintro h
  prwby h
  prefl

-- **Refusal 1 — under a quantifier.** `rw [h]` would rewrite happily inside `∀z (…)`. Here
-- the goal is a `Formula.all`, not an equation, so there is no term abstraction to hand
-- `qfer` and the tactic stops. The expected error is the docstring below, so this refusal is
-- re-checked on every build.
/--
error: prwby: the goal is not an equation
  ∀ᶠ x₀ : nat, x₀ +ᵗ s =₀ x₀ +ᵗ t
-/
#guard_msgs in
example (s t : Term F Γ Ty.nat) :
    Derivable F al Premises (s =₀ t →ᶠ Formula.all Ty.nat (x₀ +ᵗ s =₀ x₀ +ᵗ t)) := by
  pmode
  pintro h
  prwby h

/-- …and the legitimate route: introduce the `∀` **first** (`pforall`, whose eigenvariable
condition is the §1d point), and then the goal *is* an equation and QF-ER applies. -/
def demo_rewrite_under_forall (s t : Term F Γ Ty.nat) :
    Derivable F al Premises (s =₀ t →ᶠ Formula.all Ty.nat (x₀ +ᵗ s =₀ x₀ +ᵗ t)) := by
  pmode
  pintro h
  pforall
  prwby h
  prefl

-- **Refusal 2 — a quantified equation as the rewrite rule.** `rw` unifies a `∀`-quantified
-- equation against the goal. QF-ER's premise is the equation *itself*, and it must be
-- quantifier-free; `∀u (f u =₀ g u)` is not.
/--
error: prwby: `h` is not an equation
  ∀ᶠ x₀ : nat, f ⬝ x₀ =₀ g ⬝ x₀
-/
#guard_msgs in
example (f g : Term F Γ (Ty.nat →ₜ Ty.nat)) (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.all Ty.nat (f ⬝ x₀ =₀ g ⬝ x₀) →ᶠ f ⬝ c =₀ g ⬝ c) := by
  pmode
  pintro h
  prwby h

/-- …and its legitimate route: instantiate the `∀` at the term you want (`pinst`), which is
`Derivable.forall_ax`, and then rewrite by the *instance*, which is quantifier-free. -/
def demo_rewrite_from_forall (f g : Term F Γ (Ty.nat →ₜ Ty.nat)) (c : Term F Γ Ty.nat) :
    Derivable F al Premises
      (Formula.all Ty.nat (f ⬝ x₀ =₀ g ⬝ x₀) →ᶠ f ⬝ c =₀ g ⬝ c) := by
  pmode
  pintro h
  pinst h c with hc
  anorm          -- `pinst` leaves the substitution `(f ⬝ x₀ =₀ g ⬝ x₀)[x₀ := c]` unevaluated
  pexact hc

end WeakExtensionality

/-! ============================================================================
# §1d. "A Hilbert system has no deduction theorem — where did `pintro` come from?"

From nowhere: it is the identity function.

`pack Δ B` folds the hypothesis list into a chain of object implications, with the **head of
`Δ` innermost**, and `Seq F al Premises Δ B` is a *notation* for
`Derivable F al Premises (pack Δ B)`. So `Δ, A ⊢ B` and `Δ ⊢ A →ᶠ B` are not merely
interderivable, they are **the same type**, and `seq_intro`/`seq_revert` — the moves `pintro`
and `prevert` call — are literally `id` (`ProofMode/Packing.lean`). Nothing is assumed, no
rule is added, and a buggy tactic can only fail to elaborate: `SeqD` is `@[reducible]` over
`Derivable`, so there is no soundness theorem for the proof mode and there does not need to
be one.

The one place a deduction theorem *would* be unsound is the eigenvariable condition, and the
de Bruijn indices discharge it. `Derivable.forall_rule` concludes `B →ᶠ ∀x A` only from
`weakenBy ρ B →ᶠ A`: the side formula must literally be a *weakening*, so "x not free in B"
is not a check, it is a typing constraint. `seq_allI` (which is `pforall`) maps the **whole**
hypothesis context through `weakenBy ρ`, one hypothesis at a time via `forall_imp_pull` — so
after `pforall` every hypothesis lives one context out and none of them can mention the new
variable. That is why generalising under assumptions is safe here without any side condition
being tested anywhere.
============================================================================ -/

section DeductionTheorem

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι}
variable {A B C : Formula F Γ} {Δ : ProofMode.HCtx F Γ} {ρ : Ty ι}

/-- A sequent **is** a kernel derivation of the packed implication — by `rfl`, on the types. -/
example : ProofMode.Seq F al Premises [A, B] C
        = Derivable F al Premises (B →ᶠ A →ᶠ C) := rfl

/-- …so introducing a hypothesis is the identity function, not a theorem. -/
example : (ProofMode.seq_intro : ProofMode.Seq F al Premises (A :: Δ) B →
    ProofMode.Seq F al Premises Δ (A →ᶠ B)) = id := rfl

/-- …and so is reverting one. -/
example : (ProofMode.seq_revert : ProofMode.Seq F al Premises Δ (A →ᶠ B) →
    ProofMode.Seq F al Premises (A :: Δ) B) = id := rfl

/-- **Universal generalisation is a rule, and `A →ᶠ ∀x A` is not a theorem** — unless the
body is a weakening, which is exactly what the type of `forall_rule` demands. This is the
implication form, and it needs no side condition because `weakenBy ρ B` cannot mention the
new variable. -/
example : Derivable F al Premises (B →ᶠ Formula.all ρ (Formula.weakenBy ρ B)) :=
  .forall_rule I_comb

/-- Generalising **under a hypothesis**, in the mode. `h` is still available after `pforall` —
but it now sits at the *outer* context, wrapped in `Formula.weakenBy`, which is why it cannot
mention the variable just introduced. The eigenvariable condition is structural here, not a
check that some tactic performs. -/
def demo_forall_under_hyp (x : Term F Γ Ty.nat) :
    Derivable F al Premises
      (x =₀ x →ᶠ Formula.all Ty.nat (x₀ +ᵗ x =₀ x₀ +ᵗ x)) := by
  pmode
  pintro h
  pforall
  prefl

end DeductionTheorem

/-! ============================================================================
# §2. The same tactics at a metric space

The metric is **structural**: `Term.dist i` is a term former, not a signature constant, and
equality at a base type is *defined* — `s =_X t` **is** `d(s,t) =ℝ 0ℝ`, where `=ℝ` is a formula
about the encoded reals (a `∀n` over a quantifier-free rational comparison). So the
pseudometric axioms are free `Derivable` constructors — `dist_self`, `dist_comm`, `dist_tri` —
and everything below holds in **every** `Derivable F al Premises`, at every `Allowed`: no
excluded middle, no Markov, no premise set.

The theorem is the chained triangle inequality. It is the project's first *derived*
object-level theorem about a space: everything else said about metric, W-hyperbolic, CAT(0) or
normed spaces is an axiom, a model fact, or a statement about the encoding.

It was **impossible until the `≤ℝ` order package existed**. `Derivable.dist_tri` delivers its
conclusion in the purely universal form `le_R_pu`, and for a long time the `≤ℝ` API was
conversions only — no transitivity, no monotonicity. Chaining two triangle inequalities is the
smallest thing you cannot do without them, which is why four complete space towers derived
nothing at all.
============================================================================ -/

section MetricSpace

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}

/-- **The chained triangle inequality**:
`⊢ d(x,w) ≤ℝ (d(x,y) +ℝ d(y,z)) +ℝ d(z,w)`.

`papplym` applies a *kernel* theorem to the object-level goal, `psplit` splits the
`∧ᶠ`-antecedent it leaves, `pthm` discharges a leaf with a closed derivation. Two uses of the
`dist_tri` constructor, one transitivity, one additive monotonicity, one re-association.

(Adapted from `Metatheorems.dist_tri_chain` in `BaseEquality.lean`.) -/
def demo_dist_tri_chain {Γ : Ctx ι} (i : ι) (x y z w : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (le_R (Term.app2 (Term.dist i) x w)
        (Term.app2 Term.add_R
          (Term.app2 Term.add_R
            (Term.app2 (Term.dist i) x y) (Term.app2 (Term.dist i) y z))
          (Term.app2 (Term.dist i) z w))) :=
  let dxy : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x y
  let dyz : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y z
  let dzw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) z w
  let dyw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y w
  let dxw : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x w
  let rassoc : Term F Γ (realTy ι) := Term.app2 Term.add_R dxy (Term.app2 Term.add_R dyz dzw)
  let lassoc : Term F Γ (realTy ι) := Term.app2 Term.add_R (Term.app2 Term.add_R dxy dyz) dzw
  by
  pmode
  papplym (le_R_trans_core dxw rassoc lassoc)
  psplit
  · papplym (le_R_trans_core dxw (Term.app2 Term.add_R dxy dyw) rassoc)
    psplit
    · -- `d(x,w) ≤ℝ d(x,y) +ℝ d(y,w)` — the constructor, converted out of `le_R_pu`
      pthm (Derivable.mp (Derivable.dist_tri i x y w)
        (le_R_of_le_R_pu dxw (Term.app2 Term.add_R dxy dyw)))
    · -- `d(y,w) ≤ℝ d(y,z) +ℝ d(z,w)`, under `d(x,y) +ℝ ·`
      papplym (le_R_add_mono_l_core dxy dyw (Term.app2 Term.add_R dyz dzw))
      pthm (Derivable.mp (Derivable.dist_tri i y z w)
        (le_R_of_le_R_pu dyw (Term.app2 Term.add_R dyz dzw)))
  · -- re-associate: `a +ℝ (b +ℝ c) =ℝ (a +ℝ b) +ℝ c`
    papplym (le_R_of_eq_R_core rassoc lassoc)
    pthm (Derivable.mp (add_assoc_R_core dxy dyz dzw) (eq_R_sym_core lassoc rassoc))

/-- **The reverse triangle inequality**, the other orientation:
`⊢ d(y,z) −ℝ d(x,z) ≤ℝ d(x,y)`.

Six lines. `Metatheorems.dist_rev_tri` at `(y,x,z)` gives it with `d(y,x)` on the right;
`dist_comm` — again a free constructor — turns that into `d(x,y)`.

`Probes/RevTriangleDemo.lean` reads this back through `MetricModel.soundness` in an
*arbitrary* Mathlib `MetricSpace` as `M.d a c − M.d b c ≤ M.d a b`: the first time a *derived*
object-level theorem was checked in a model, rather than an axiom being discharged into one. -/
def demo_dist_rev_tri {Γ : Ctx ι} (i : ι) (x y z : Term F Γ (Ty.base i)) :
    Derivable F al Premises
      (le_R (Term.app2 Term.sub_R
              (Term.app2 (Term.dist i) y z) (Term.app2 (Term.dist i) x z))
            (Term.app2 (Term.dist i) x y)) :=
  let dyx : Term F Γ (realTy ι) := Term.app2 (Term.dist i) y x
  let dxy : Term F Γ (realTy ι) := Term.app2 (Term.dist i) x y
  let s : Term F Γ (realTy ι) :=
    Term.app2 Term.sub_R (Term.app2 (Term.dist i) y z) (Term.app2 (Term.dist i) x z)
  by
  pmode
  papply (le_R_trans_core s dyx dxy)
  psplit
  · pthm (dist_rev_tri i y x z)
  · papply (le_R_of_eq_R_core dyx dxy)
    pthm (Derivable.dist_comm i y x)

end MetricSpace

/-! ============================================================================
# §3. …and at a W-hyperbolic space

A W-hyperbolic space is a metric space with a convex-combination operation
`W(x,y,λ)` for `λ ∈ [0,1]`, satisfying (W1)–(W4). Here `ι = Unit` (one base type `X`) and the
signature has exactly **one** constant, `W : X →ₜ X →ₜ ℝ →ₜ X`; the four axioms are the
project's first non-empty `Premises`, and `WHyperbolicModel.axiomsHold` discharges all four in
any Mathlib-level model, so the metatheorems for this space take no axioms argument.

`λ ∈ [0,1]` is a quantifier over a *subset* of type 1, which the metatheorem cannot take. The
standard move is Kohlenbach's: a retraction `λ̃ = clamp01 λ` under which **every** `f : ℕ → ℕ`
codes an element of `[0,1]`. That is why `W`'s third argument is written `clamp01 l`
everywhere below, and it is what makes the majorant of `W` independent of `λ`.

## Why extensionality has to be *derived*

The ambient system is **weakly** extensional: `WE-HA^{ω,X}` has only quantifier-free
extensionality (`Derivable.qfer`), and full extensionality is deliberately unavailable — it is
exactly what would break the metatheorems. So adding a constant `W` to the signature is only
legitimate if `W`'s extensionality follows from the space's own axioms. For W-hyperbolic
spaces it does, and the proof below is that derivation: (W4) supplies the two carrier
arguments, (W2) the parameter.

The mechanism is worth stating once, because it is what makes the proof short: `s =_X t`
**is** `d(s,t) =ℝ 0ℝ`, so a nonexpansiveness bound `d(W…, W…) ≤ℝ c ·ℝ d(s,t)` collapses as
soon as the product does — and a product with a known-zero factor needs no order theory about
`·ℝ` at all.
============================================================================ -/

section WHyperbolicSpace

variable {Γ : Ctx MetricSpace.ι} {a : Allowed}

/-- **Full extensionality of `W`**:

    x =_X x'  ∧  y =_X y'  ∧  λ =ℝ μ   →   W(x,y,λ̃) =_X W(x',y',μ̃)

Stated as an object-level implication from the conjunction, so it is a *theorem of the
theory*, not a derived rule. The three one-argument cases (`W_ext_left`, `W_ext_right`,
`W_ext_param`, each ~5 lines in `WHyperbolicLemmas.lean`) chained by transitivity of base-type
equality. `pdestruct` takes the conjunction apart; `∧ᶠ` is left-associative, so the hypothesis
is `(x =_X x' ∧ y =_X y') ∧ λ =ℝ μ`.

(Adapted from `Metatheorems.WHyperbolic.W_ext`.) -/
def demo_W_ext (x x' y y' : Term WHyperbolic.F Γ xTy) (l m : Term WHyperbolic.F Γ rTy) :
    Derivable WHyperbolic.F a WHyperbolic.Premises
      (eqAtType xTy x x' ∧ᶠ eqAtType xTy y y' ∧ᶠ eq_R l m →ᶠ
        eqAtType xTy
          (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
          (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 m))) := by
  pmode
  pintro hyp
  pdestruct hyp with hxy hl
  pdestruct hxy with hx hy
  papplym (eqAtType_trans_base ()
    (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
    (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 l))
    (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 m)))
  psplit
  · papplym (eqAtType_trans_base ()
      (Term.app3 WHyperbolic.W x y (.app Term.clamp01 l))
      (Term.app3 WHyperbolic.W x' y (.app Term.clamp01 l))
      (Term.app3 WHyperbolic.W x' y' (.app Term.clamp01 l)))
    psplit
    · papplym (WHyperbolic.W_ext_left x x' y l)
      pexact hx
    · papplym (WHyperbolic.W_ext_right x' y y' l)
      pexact hy
  · papplym (WHyperbolic.W_ext_param x' y' l m)
    pexact hl

end WHyperbolicSpace

/-! ============================================================================
# §4. The same theorem as §1, from bare `Derivable` constructors

This is the contrast. `compose_pm` (§1) and `compose_raw` (here) prove **the same formula**.
One is seven tactic lines; the other is what a Hilbert system actually offers.

There is no `syllogism` *axiom* — `Derivable.syllogism` is a **rule**, so it cannot be
discharged into the object implication. What is available is: conjunction weakening
(`and_weak`), permutation (`and_perm`), contraction (`and_contract`), and the two structural
rules `exportation : (A ∧ᶠ B →ᶠ C) → (A →ᶠ B →ᶠ C)` and `importation`, its converse. Every
step below is one of those.

`pair_h` and `eval_h` are Lean-level helpers from `PropositionalLemmas.lean` — themselves
built from exactly these constructors, no tactics — that build `H →ᶠ X ∧ᶠ Y` from `H →ᶠ X`
and `H →ᶠ Y`, and `H →ᶠ B` from `H →ᶠ (A →ᶠ B)` and `H →ᶠ A`. Without them the same proof is
about thirty `let`s.

**This is not a straw man.** Raw-constructor derivations are what §6 mines: they are 145
constructors where the proof-mode form of the same argument is 42,747, and on the current
evidence the proof mode is a *liability* for extraction, not the route to it. §1–§3 are how
mathematics gets written; §4 is what the extractor prefers to read. Reconciling the two is
open work.
============================================================================ -/

section RawHilbert

variable {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {Premises : PremiseSet F}
variable {Γ : Ctx ι} {A B C : Formula F Γ}

/-- **Composition of implications, from raw constructors**:
`⊢ (A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)` — the same formula `compose_pm` proves in §1.

Write `H := ((A→B) ∧ᶠ (B→C)) ∧ᶠ A` for the fully importated antecedent. Project the three
components out of it with `and_weak`/`and_perm`, apply twice, then `exportation` twice to
peel `H` back into a chain of implications. -/
def compose_raw : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) :=
  -- `H := ((A →ᶠ B) ∧ᶠ (B →ᶠ C)) ∧ᶠ A`, since `∧ᶠ` is left-associative.
  let getAB : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ (A →ᶠ B)) :=
    .syllogism .and_weak .and_weak
  let getBC : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ (B →ᶠ C)) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let getA : Derivable F al Premises ((A →ᶠ B) ∧ᶠ (B →ᶠ C) ∧ᶠ A →ᶠ A) :=
    .syllogism .and_perm .and_weak
  let getB := eval_h getAB getA            -- H →ᶠ B
  let getC := eval_h getBC getB            -- H →ᶠ C
  .exportation (.exportation getC)

/-- The two really are the same theorem — Lean checks it by `rfl` on the *statement*, not on
the two proof terms, which are wildly different objects. -/
example : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := compose_raw
example : Derivable F al Premises ((A →ᶠ B) →ᶠ (B →ᶠ C) →ᶠ (A →ᶠ C)) := compose_pm

end RawHilbert

/-! ============================================================================
# §5. `#hilbert`: what those tactic lines denote

`Derivable` is `Type`-valued, so a proof in this development *is* a proof tree in the object
logic. `#hilbert` walks that term and writes the numbered Hilbert listing, in Markdown and
LaTeX. Sharing is preserved: each distinct subproof is numbered once and cited by line number
afterwards, which is what a paper proof does anyway.

`depth n` says how many definition levels of the proof-mode layer to expand before citing what
remains by name; `keeping g` never expands `g` whatever else is said; `all` expands the
propositional combinators too. (Note `unfolding *` does **not** exist — the parser takes
identifiers.)

**The size is the argument for having a proof mode.** The tactic lines of §1 denote:

| invocation | steps | wall |
|---|---|---|
| `contract_pm` (depth 0) | 12 | 15 ms |
| `contract_pm depth 2` | 54 | 0.24 s |
| `contract_pm depth 4` | 117 | 0.42 s |
| `contract_pm depth 6` and `depth 10` | **120** — a fixed point | 1.1 s |
| `contract_pm all depth 10` | **1844** raw-axiom steps | 15.3 s |
| `compose_pm` (depth 0) | 13 | 15 ms |
| **`compose_pm depth 4`** | **271** | 1.1 s |
| `compose_raw` (§4, raw already) | 14 | 20 ms |
| `demo_add_comm` (§1b, depth 0 / 2 / 4) | 49 / 157 / **198** | 0.13 s / 1.0 s / 1.7 s |

**271 steps from seven tactic lines** is the number to put on the slide, and it is still
scrollable. `Demo/hilbert/compose_pm_d4.md` has it.

(Rows measured by the commands in this file report their own wall time when it is elaborated;
the depth-2/6/10 rows are `Probes/HilbertDepth.lean`'s, on the same machine under load.)

The fixed point at 120 is a genuine Hilbert derivation: 30 modus ponens, 24 `S`, 20
`weaken_intro_h`, 4 `I`, 2 `K`, and no `ProofMode` name anywhere. With `all` the combinators
expand too and the same proof is 1844 steps.

Read the depth-0 listings side by side and the point of §4 becomes visual:
`Demo/hilbert/compose_pm_d0.md` is 13 lines of `seq_id`/`pm_mp`/`pm_intro` that mirror the
tactic script one-for-one, while `Demo/hilbert/compose_raw.md` is 14 lines of
`∧-weakening` / `∧-permutation` / `syllogism` / `exportation` over conjunctions nobody wrote.
They are proofs of the same formula.

Those figures are from `Probes/HilbertDepth.lean`, which also records the ceiling on a *real*
derivation and what causes it: on `ProofMode.mct_descent` (112 steps of ℕ-MCT), `depth 1` is a
heartbeat timeout, and `keeping seq_id` — that one constant, hypothesis lookup, which recurses
on the context through `HVar.rec` with a dependent cast per level — turns it into **1766 steps
in 18.5 s**. Depth 3 does not exist at any `keeping` tried. The wall at the top is the
*delaborator*, not the traversal.

The commands below regenerate `Demo/hilbert/`. Absolute paths: `#hilbert … to` resolves
relative to the process's working directory, which is not this file's.
============================================================================ -/

#hilbert contract_pm
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/contract_pm_d0"
#hilbert contract_pm depth 4
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/contract_pm_d4"
#hilbert compose_pm
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/compose_pm_d0"
#hilbert compose_pm depth 4
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/compose_pm_d4"
#hilbert compose_raw
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/compose_raw"
#hilbert demo_add_comm
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/add_comm_pm_d0"
#hilbert demo_add_comm depth 4
  to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/add_comm_pm_d4"

-- The fixed point, and the fully expanded 1844-step listing — uncomment to run live
-- (≈1.1 s and ≈15.3 s respectively; the second is too slow to sit in the build):
-- #hilbert contract_pm depth 10
--   to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/contract_pm_d10"
-- #hilbert contract_pm all depth 10
--   to "/home/horatiu/LeanMisc/metatheorems/Demo/hilbert/contract_pm_all"
--   ⟹ 120 steps, then 1844. Six tactic lines; 1844 applications of Hilbert axioms.

/-! ============================================================================
# §6. Extraction — the centrepiece

## Presenter's note — say these out loud; the screen cannot show them

* Both derivations below start from the **same** premise. The two growth rates come from the
  *proofs* — one instantiates it once, one inducts and builds each witness from the last — not
  from different logic.
* The numerals are **magnitudes**. At `ι = Empty` nothing routes through the ℚ/ℝ Cantor-pairing
  encoding, so `32` means thirty-two and not a code for a rational.
* `real_mct_p2` (§6e) proves the **metastable** statement — a bare `∃v`, with no bound inside
  it — and *that statement* needs no classical logic. It is not the claim "MCT needs none".

## What the metatheorem says

For a statement in the shape

    ∀x^ρ ( ∀u^ℕ B₀(u,x)  →  ∃v^ℕ C₀(v,x) )

with `B₀`, `C₀` quantifier-free and ∨-free, the metatheorem produces a **computable functional
`Φ`** such that, in every model, for every `x` majorized by `x*`:

    (∀u ≤ Φ x*. B₀)  →  ∃v ≤ Φ x*. C₀

`Φ = max U V`, where `V` bounds the existential witness and `U` bounds *how far into the
premise `∀u B₀` the proof reaches*. Both are extracted from the derivation. `Φ` is **data**:
`monotone_general_metatheorem_at` returns a `Subtype`, not an `∃`, so the bound is a `def` a
tactic can evaluate.

The route used here is the **monotone** functional interpretation (Kohlenbach, *Applied Proof
Theory*, Ch. 9, Thm 9.1): rather than build the Dialectica realizer and then majorize it,
compute a majorant of the realizer directly by recursion on the derivation, leaving the
realizer itself existential. Because `Ty.hat` sends every base type to `nat`, the majorant is a
plain Lean value built from `ℕ`/`unit`/`×`/`→` — no object-level `Term` on the bound path,
hence no `weaken`, no `rename`, no dependent casts for the kernel to reduce.

## The instrument

`kernel_rfl` (`Metatheorems/KernelRfl.lean`) assigns `Eq.refl` and lets the **kernel** decide
the equation. That is the evaluator of record here, not `#eval` and not bare `rfl`: nothing
below rests on compiler trust. Every numeral also has a **refutation control** — a theorem that
the neighbouring value is *not* the bound — because a `rfl` that gets stuck and a `rfl` that
computes are otherwise indistinguishable from a green build.

## The thesis, in one sentence

**The bound mirrors the proof.** Two derivations follow, from the *same* premise,
`∀u (f (S u) =₀ f u +ᵗ f u)`. One instantiates it once and exhibits its witness: the bound is
`f*(k*)`, and `#bound` prints it as such. The other proves the closed form by induction, building
each witness from the previous one: the bound is `2^{k*}·f*(0)`. The difference is visible in the
proofs and nowhere else.
============================================================================ -/

/-! ## The setting: pure `WE-HA^ω`

`PureWEHA` (`Metatheorems/PureWEHA.lean`) is the instance with no space: `PureWEHA.F` has no
constants, `PureWEHA.Premises` is empty, `PureWEHA.cm` is the Bezem majorants of `0`, `S`,
`R`. Every value below is therefore a plain natural number.

Statements are written out. The binder tokens number binders **from the outside**, the way
the `#hilbert` listings print them (`∀ᶠ x₀ : nat, …`): under `∀x`, `x` is `x₀`; a binder
inside it introduces `x₁`, and `x` is still `x₀`. So with `x = (k, f)`, `Term.snd x₀ ⬝ S x₁`
under `∀x ∀u` reads `f (S u)`, and `Term.snd x₀ ⬝ Term.fst x₀` is `f k`.

Both statements below share the premise `∀u ( f (S u) =₀ f u +ᵗ f u )`: `f` doubles at every
step. The majorants they are evaluated at are `x* = (k*, λn. n+1)` and `(k*, λn. n+3)`, so
`f*(0)` is `1` or `3`.

## 6a. Instantiate the premise once, exhibit the witness ⟹ a LINEAR bound

    ∀x ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f (S k) =₀ v +ᵗ v ) )

The conclusion asks for the half of `f (S k)`; the proof instantiates the premise at `u := k`
and hands back `f k`. Nothing recurses, so the bound is a projection of the majorant —
`V(k*, f*) = f*(k*)`, `U(k*) = k*` — and `#bound` prints it in that form. -/

/-- **The derivation**, in the proof mode: instantiate, exhibit, done. -/
def stepOnce : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (Γ := [])
    (Formula.all (Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat))
      (Formula.all Ty.nat (Term.snd x₀ ⬝ S x₁ =₀ Term.snd x₀ ⬝ x₁ +ᵗ Term.snd x₀ ⬝ x₁)
        →ᶠ Formula.ex Ty.nat (Term.snd x₀ ⬝ S (Term.fst x₀) =₀ x₁ +ᵗ x₁))) := by
  pmode
  pforall
  pintro h
  pinst h (Term.fst x₀) with hk
  anorm
  pexists (Term.snd x₀ ⬝ Term.fst x₀)
  pexact hk

/-- Its monotone realizer — an ordinary `def`, elaborates instantly. -/
def stepOnceR := monotone_soundness PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm stepOnce

/-- The majorant `x* = (k*, λn. n+1)`, so `f*(0) = 1`. -/
def xs (k : ℕ) : Ty.interpret PureWEHA.X (Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat)).hat :=
  (k, fun (n : ℕ) => n + 1)
/-- `x* = (k*, λn. n+3)` — the *other* component of the majorant, so `f*(0) = 3`. -/
def ys (k : ℕ) : Ty.interpret PureWEHA.X (Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat)).hat :=
  (k, fun (n : ℕ) => n + 3)

-- The bound, PRINTED. Structural: which `MRealizer` combinator each inference rule became,
-- one level down the derivation. Symbolic: the functional itself, reduced by the kernel with
-- the majorant left as a variable (`#bound … eval`, capped; ≈0.7 s, converges).
#bound stepOnce depth 1
#bound stepOnce depth 1 unfold     -- the same, each combinator opened to the majorant it builds
def stepOnceV := mfiV PureWEHA.cm stepOnceR
#bound stepOnceV eval
--   ⟹ `fun xs => xs.2 xs.1`, i.e. `V(k*, f*) = f*(k*)`. That is the bound, as a term.

-- Extraction at points — uncomment to run live (kernel time ≈0.7–1 s each, `U` ≈1.4 s):
--
-- theorem once_V_3 : (4 : ℕ) = mfiV PureWEHA.cm stepOnceR (xs 3) := by kernel_rfl
-- theorem once_V_5 : (6 : ℕ) = mfiV PureWEHA.cm stepOnceR (xs 5) := by kernel_rfl
-- theorem once_V_ys_3 : (6 : ℕ) = mfiV PureWEHA.cm stepOnceR (ys 3) := by kernel_rfl
-- theorem once_U_3 : (3 : ℕ) = mfiU PureWEHA.cm stepOnceR (xs 3) := by kernel_rfl
-- theorem once_U_5 : (5 : ℕ) = mfiU PureWEHA.cm stepOnceR (xs 5) := by kernel_rfl
-- theorem once_V_3_ne_8 : (8 : ℕ) ≠ mfiV PureWEHA.cm stepOnceR (xs 3) := by
--   rw [← once_V_3]; decide
-- theorem once_Phi_3 : (4 : ℕ) =
--     (monotone_general_metatheorem_at PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm
--       rfl rfl rfl rfl stepOnce).val (xs 3) := by kernel_rfl
--
--   ⟹ V = f*(k*): k*+1 under xs, k*+3 under ys. U = k*: the premise is consulted exactly
--     at k. Φ = max U V = 4 at k* = 3, from the metatheorem's own entry point.

/-! ## 6b. A proof whose witness is built from the previous one ⟹ an EXPONENTIAL bound

Statement (`ρ := nat ×ₜ (nat →ₜ nat)`, `x = (k, f)`):

    ∀x ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f k =₀ v ) )

*If `f` doubles at every step, then `f k` is bounded* — and the metatheorem's `v ≤ Φ x*` is
that bound.

Same premise. Now the closed form `f k` itself, by induction on `k`, and the step case takes
the witness `w` the induction hypothesis supplies and returns `w +ᵗ w`:

```lean
    -- Examples/Doubling.lean, the step under the ∃: from `f k =₀ v` and the premise
    -- instance `f (S k) =₀ f k +ᵗ f k`, conclude `f (S k) =₀ v +ᵗ v`.
    Derivable.exist_ax (v2 +ᵗ v2) CS3
    --                  ^^^^^^^^ the new witness, built from the previous one
```

Dialectica interprets `Derivable.induction` as primitive recursion (`MRealizer.induction` =
`cm.precM` = `recMaj`, Kohlenbach's `t^M`). A witness built *from* the previous witness makes
that recursion iterate, and the doubling in the proof comes out as an exponential in the bound.

Two things that make this a demonstration rather than an anecdote. The premise is genuinely
**consumed** — `forall_ax k` instantiates `∀u B₀` at `u := k`, once per step, so `U` reports a
property of the proof and not a default. And **no witness term written by hand mentions
`Term.prec`**: the surface-recursor ban (`ProofMode/Linter.lean`) is enforced, so the iteration
in the bound is produced by the extraction, not smuggled into the derivation. -/

/-- **The theorem, written out**:

    ⊢ ∀x^(nat × (nat→nat)) ( ∀u ( f (S u) =₀ f u +ᵗ f u )  →  ∃v ( f k =₀ v ) )

with `f := snd x`, `k := fst x`.

The derivation is **raw `Derivable` constructors** — `induction`, `forall_ax`, `exist_ax`,
`exist_rule`, `syllogism`, `exportation`, and one quantifier-free extensionality step, 145 of
them, no proof mode at all. It lives in `Metatheorems/Examples/Doubling.lean`, because the de
Bruijn bookkeeping it needs (a page of contexts and intermediate formulas) says nothing about
proof mining and would bury the extraction below. `Probes/ContentExampleNat.lean` measures
what the proof-mode form of the *same argument* costs: 42,747 constructors, 295×, and a bound
that reduces only at `k* = 0`. -/
def doubling : Derivable PureWEHA.F Allowed.extended PureWEHA.Premises (Γ := [])
    (Formula.all (Ty.nat ×ₜ (Ty.nat →ₜ Ty.nat))
      (Formula.all Ty.nat (Term.snd x₀ ⬝ S x₁ =₀ Term.snd x₀ ⬝ x₁ +ᵗ Term.snd x₀ ⬝ x₁)
        →ᶠ Formula.ex Ty.nat (Term.snd x₀ ⬝ Term.fst x₀ =₀ x₁))) :=
  Examples.Doubling.derivation

/-- Its monotone realizer — an ordinary `def`, elaborates instantly. -/
def doublingR := monotone_soundness PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm doubling

-- The bound, PRINTED. Structurally the realizer is the induction, two levels down; symbolically,
-- at `k* = 1` with `f*` left as a variable, the kernel reduces it to the first unrolling of the
-- closed form (≈2 s, converges).
#bound doubling depth 2
#bound doubling depth 2 unfold     -- `induction` opens to the recursor `R[…]` under `termMajorizer`
def doublingV1 := fun (g : ℕ → ℕ) => mfiV PureWEHA.cm doublingR ((1 : ℕ), g)
#bound doublingV1 eval
--   ⟹ `fun g ↦ Decidable.rec (fun _ ↦ Nat.rec (g 0) (fun k ih ↦ maxT nat (S ih) ih) (g 0)) …`
--     — a `Nat.rec` driven by `g 0`: `recMaj` iterating *value*-many times (the §6c ceiling,
--     visible), which evaluates to `2·f*(0)`, the `k* = 1` case of `2^{k*}·f*(0)`.
--     Against §6a's `xs.2 xs.1`, this is the whole thesis in two printed terms.

-- Extraction, the witness side — uncomment to run live
-- (measured kernel time: 0.06 s at k*=0, 1.3 s at k*=3, 5.5 s at k*=5 — the cost grows with
--  the VALUE, see §6c):
--
-- theorem exp_V_0 : (1 : ℕ) = mfiV PureWEHA.cm doublingR (xs 0) := by kernel_rfl
-- theorem exp_V_3 : (8 : ℕ) = mfiV PureWEHA.cm doublingR (xs 3) := by kernel_rfl
-- theorem exp_V_5 : (32 : ℕ) = mfiV PureWEHA.cm doublingR (xs 5) := by kernel_rfl
-- theorem exp_V_3_ne_7 : (7 : ℕ) ≠ mfiV PureWEHA.cm doublingR (xs 3) := by rw [← exp_V_3]; decide
--
--   ⟹ V(k*, f*) = 2^{k*} · f*(0). Exponential — and it is *tight*: 2^k·f(0) is exactly f k.

-- …and it tracks the function majorant, not only the index (0.05 s, 0.7 s):
--
-- theorem exp_V_ys_0 : (3 : ℕ) = mfiV PureWEHA.cm doublingR (ys 0) := by kernel_rfl
-- theorem exp_V_ys_2 : (12 : ℕ) = mfiV PureWEHA.cm doublingR (ys 2) := by kernel_rfl
--
--   ⟹ f*(0) = 3 triples every value: 2^2 · 3 = 12, not the 4 that f*(0) = 1 would give.

-- The premise side — U is NOT a copy of V, and it is sharp
-- (0.05 s, 0.8 s, 1.6 s, 5.6 s):
--
-- theorem exp_U_0 : (0 : ℕ) = mfiU PureWEHA.cm doublingR (xs 0) := by kernel_rfl
-- theorem exp_U_2 : (1 : ℕ) = mfiU PureWEHA.cm doublingR (xs 2) := by kernel_rfl
-- theorem exp_U_3 : (2 : ℕ) = mfiU PureWEHA.cm doublingR (xs 3) := by kernel_rfl
-- theorem exp_U_5 : (4 : ℕ) = mfiU PureWEHA.cm doublingR (xs 5) := by kernel_rfl
--
--   ⟹ U(k*) = k* − 1, exactly: the step at k consults ∀u B₀ at u := k, for k = 0 … k*−1.
--     "How far into the premise the proof reaches", as a genuine function of x*.

-- Φ, through the metatheorem itself (2.3 s, 10.5 s — the second is a slow cell, warn the room):
--
-- theorem exp_Phi_3 : (8 : ℕ) =
--     (monotone_general_metatheorem_at PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm
--       rfl rfl rfl rfl doubling).val (xs 3) := by kernel_rfl
-- theorem exp_Phi_5 : (32 : ℕ) =
--     (monotone_general_metatheorem_at PureWEHA.eqxi PureWEHA.spremise PureWEHA.cm
--       rfl rfl rfl rfl doubling).val (xs 5) := by kernel_rfl
--
--   ⟹ Φ = max U V, from the metatheorem's own entry point rather than its two components.
--     The four `rfl`s are the metatheorem's side conditions — that `B₀` and `C₀` are
--     quantifier-free and ∨-free — decided on the spot from `doubling`'s own type.

/-! ## 6c. ⚠ THE CEILING — do not type `8` or more on stage

On this **same** 145-constructor derivation, with nothing else changed:

| `k*` | `V` | outcome |
|---|---|---|
| 3 | 8 | 1.3 s |
| 5 | 32 | 5.5 s |
| **7** | **128** | kernel-checked, **9–30 s depending on machine load** (18 s when last run) |
| **8** | 256 | **`INTERNAL PANIC: out of memory` at the 12 GB cap** |

The ceiling is the **value**, not the derivation and not the proof: the majorant of the
object-level `Term.add` is a `prec` term, so `recMaj` iterates *value*-many times with nothing
shared. `k* = 7` is the last one that finishes — and it is a *slow* cell, so run it only if
there is time.

    -- theorem exp_V_7 : (128 : ℕ) = mfiV PureWEHA.cm doublingR (xs 7) := by kernel_rfl  -- 9–30 s
    -- theorem exp_V_8 : (256 : ℕ) = mfiV PureWEHA.cm doublingR (xs 8) := by kernel_rfl  -- OOM

(`exp_V_7` is verified on every build in `Probes/DemoChecks.lean`; `exp_V_8` exists nowhere.)

## 6d. What the two together show

Same premise, two proofs, two growth rates — read off the *proof*, not the theorem, and now
printed from it: `xs.2 xs.1` against a `Nat.rec` driven by `g 0`. That is the whole content of
"a bound is a property of a proof". `ProofMode/MCT.lean`
and `ProofMode/MCTLazy.lean` are the same contrast at scale: two derivations of one ℕ-MCT
statement, one of which is constructive and one of which must be hand-translated.

## 6e. Where this stops, stated plainly

The derivations with real mathematical content — `ProofMode.real_mct_p2` (ℝ-MCT in metastable
form, 655 lines), `dist_tri_chain` of §2, `mct_p2` — have their `Φ` **named and type-checked,
never evaluated**. Their *shape* prints all the same (`#bound … depth 2` below, in 74 ms), which
is exactly the line between what this project can and cannot do. Two blockers, both measured,
both in `ARCHITECTURE.md` §14.7, and neither of them the monotone interpretation, the proof
mode, induction, or formula size (each of those was tested and cleared):

1. **`Eq.mpr` casts buried under the proof-mode layer.** A `closed_subst`-style normalisation
   lemma proves a formula equation *without* computing it; the kernel's K-rule reduction of the
   resulting cast has to redo exactly that computation.
2. **The composition combinators re-evaluate their sub-majorants.** `MRealizer.syllogism` uses
   its first argument three times and its second twice, and neither the kernel nor the compiled
   evaluator shares them — measured at ×3.7 per nesting level at depth 6, which dies around
   depth 8. That is the Dialectica exponential in its last hiding place, and it applies to
   every route equally, classical and intuitionistic alike.

Accuracy notes for anyone quoting this on a slide: `real_mct_p2` proves the **metastable**
statement, a bare `∃v` with no bound in it; and *the metastable form* needs no classical logic
(it holds at every `Allowed`) — which is not the same claim as "MCT needs no classical logic".
============================================================================ -/

-- ℝ-MCT, twice. `real_mct_p2` is the descent proof — among `2^{k+1}` windows one is good —
-- and holds at EVERY `Allowed`. `real_mct_p1` is the lazy proof — assume every window is bad,
-- chain `2^{k+1}` drops below `0`, contradiction — and needs exactly Markov's principle
-- (`hmk : al.markov = true`): its one non-constructive step is `¬¬∃v C → ∃v C` for the
-- quantifier-free `C`, which is `Derivable.markov`, and `pby_contra` refuses any other shape.
-- Same statement, same encoding, same entry point; both bounds named and type-checked.
#check @ProofMode.real_mct_p2
#check @ProofMode.real_mct_p1
#check @ProofMode.real_mct_bound_p2
#check @ProofMode.real_mct_bound_p1
#check @RealMCT.real_mct_of_bound

-- What DOES print for ℝ-MCT: the SHAPE of its extracted functional, two inference rules deep,
-- and the majorants those rules build — nothing evaluated, so this is safe at any depth on any
-- proof (the node cap is the only limit). Its VALUE is what does not compute: `eval` on either
-- realizer is the 12 GB `bad_alloc` of blocker 2 above. At depth 2 the two trees are
-- identical — the proof-mode entry is the same; `p1` is printed at depth 6 (31 nodes, 5 ms),
-- the first depth at which its Markov step appears as a leaf,
-- `MRealizer.ofSRealizer cm (sMarkov hqf hvf)`: the one ineffective step, located in the
-- realizer.
#bound ProofMode.real_mct_p2 depth 2
#bound ProofMode.real_mct_p2 depth 2 unfold
#bound ProofMode.real_mct_p1 depth 6
#bound ProofMode.real_mct_p1 depth 3 unfold

/-! ============================================================================
# Axiom hygiene — the claims, checked

Expected: object-level derivations `[propext, Quot.sound]`; anything mentioning a model,
Mathlib `ℝ`, or Markov's principle `[propext, Classical.choice, Quot.sound]`. `sorryAx` must
never appear anywhere. (`Metatheorems/Headline.lean` does this for every headline declaration
in the project; `Probes/DemoChecks.lean` does it for the §6 numerals.)
============================================================================ -/

#print axioms compose_pm
#print axioms compose_raw
#print axioms demo_add_comm
#print axioms demo_qfer_ok
#print axioms demo_rewrite_under_forall
#print axioms demo_rewrite_from_forall
#print axioms demo_forall_under_hyp
#print axioms demo_dist_tri_chain
#print axioms demo_dist_rev_tri
#print axioms demo_W_ext
#print axioms stepOnce
#print axioms doubling
#print axioms ProofMode.real_mct_p2
#print axioms ProofMode.real_mct_p1

end Demo
end Metatheorems
