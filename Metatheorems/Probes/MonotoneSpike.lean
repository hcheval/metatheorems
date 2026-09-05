/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.ConjBoundDemo

/-!
# Spike G0: the monotone functional interpretation on `acFinal`'s nine constructors

**Question.** `ConjBoundDemo.acFinal` is a 13-constructor derivation with one `and_contract`
whose counter-side bound `acUt_at_5_9` is a kernel `whnf` timeout (`Eq.rec ↦ 60474`,
`Term.rename ↦ 10504` — the kernel executing renamings over dependent indices on the way to
a 2,529-node term, `SizeProbe.lean`). Does computing a **majorant of the realizer by recursion
on the derivation**, as a semantic value at the hat type — Kohlenbach's monotone functional
interpretation, *Applied Proof Theory* Thm 9.1, pp. 141–145 — with the realizer itself only
existentially quantified, clear the stall?

**RESULT: THE GATE PASSES.** `mfi_acFinal_U_at_5_9 : 1709 = mfiU (triCm M h) (acSpike M h) (5,9)`
closes by `have hval : … = max (pairN …) 0 := rfl; rw [hval]; decide`, kernel-checked, at
`[propext, Classical.choice, Quot.sound]`, in **≈0.2 s of elaboration** (`rfl` ≈ 207 ms, `decide`
≈ 2 ms, kernel type-checking ≈ 40–70 ms; `set_option profiler true`, 2026-09-05) — against a
200 000-heartbeat `whnf` timeout for the same number on the term route. The witness side
`mfi_acFinal_V_at_5_9 = 1709` agrees with the term route's `cVtTwice_at_5_9`. The whole module
builds in **7.8 s** with all dependencies replayed. Details at the foot of this header.

## The definition (`MRealizer`)

The statement mirrors `termMajorizer_maj` one level up, over the derivation. Three things
differ from the shape written in the task brief, each forced, none a simplification:

1. **The mixed hypothesis is `MajEnv`, not `SelfMajEnv`.** `SelfMajEnv am Γ e₁ e₂` relates
   two *hat* environments; the brief's `SelfMajEnv am Γ envstar env` with
   `env : Ctx.interpret X Γ` does not typecheck. `MajEnv am Γ envstar env` is the relation the
   content demands (it is what `termMajorizer_maj` uses).
2. **The existential is hoisted outside the environment quantifier** — `∃ x : env → 𝕎 A`,
   uniform in `env`, with correctness `∀ env y` and majorization `∀ envstar env, MajEnv → …`.
   This is exactly the book's `(+)`: `∃x (t* maj x ∧ ∀a,y A_D(x a, y, a))`, where `x` is one
   functional of the free variables `a`. The per-environment form
   `∀ envstar env, MajEnv → ∃ x, …` is **not closable at `forall_rule`**: the premise lives in
   context `ρ :: Γ`, the conclusion's realizer must be correct at *every* `z : ρ`, and the IH
   supplies realizers only at majorized `z` — and even with choice, a realizer chosen from one
   `z*`'s existential need not be majorized by `tstar (z'*, e)` for a second `z'* ≽ z`. The
   hoisted form needs no choice anywhere. `MRealizer.pointwise` derives the brief's shape from
   it, so nothing is lost.
3. **A self-majorization conjunct is carried**, exactly as `termMajorizer_maj` carries one:
   `arrow_intro`'s second clause (Lemma 17.80's self-majorization half) is what `forall_rule`
   needs to show the composed majorant is a majorant at an arrow type, and it is a statement
   about the majorant's monotonicity in its hat-environment, which the mixed clause cannot
   supply.

## The nine cases

| constructor | strategy | majorant |
|---|---|---|
| `and_weak`, `forall_ax`, `exist_ax`, `refl0` | leaf (Howard, p. 142) | `termMajorizer cm (s…).val` |
| `mp` | composition (p. 144 case 5) | `t₂*.1 t₁*` |
| `syllogism` | composition | `(λx. bc.1 (ab.1 x), λx y. ab.2 x (bc.2 (ab.1 x) y))` |
| `exportation` | composition | currying of the sub-majorant |
| `forall_rule` | composition (p. 144 case 6) | `λxB z. (h*(z,e)).1 xB` …, via `arrow_intro` |
| **`and_contract`** | **p. 143 case 1** | `(λx.(x,x), λx y. maxT (cTy A) y.1 y.2)` |

Every other constructor falls to a single, honest, sorry-free **fallback**: the leaf strategy
applied to the whole sub-derivation (`ofSRealizer (syntactic_soundness eqxi spremise prf)`),
i.e. the term route. It is never reached for `acFinal`, whose thirteen constructors are all
among the nine (`derivSize_acFinal` below).

`and_contract` needs `maj ρ (maxT ρ a b) c` from `maj ρ a c` (or `b c`) plus self-majorization
of the other argument, and a `maxT` congruence for `selfMaj`, at every hat type. The abstract
`am.maj` has no `max`, so those three facts are packaged as `MaxCompat am` (a `Prop`), proved
for every `bezemAbstract` from the existing `maxT_bezemMaj_left` / `maxT_hatMaj` plus a new
`maxT_comm`; `WHyperbolicModel.maxCompat` instantiates it. `MaxCompat` is consumed only in
the `Prop` half, so it never appears on the bound path.

## Gate: measured

Setting: `M : WHyperbolicModel`, `h : d(a, 0_X) ≤ 5`, majorants `TriangleBoundDemo.triCm M h`,
derivation `ConjBoundDemo.acFinal` (13 constructors, `derivSize_acFinal`), `x* = (5, 9)`.
`U`/`V` are read off the monotone realizer exactly as `extractUTerm`/`extractVTerm` read them
off the realizing term (`mfiU`/`mfiV`).

| theorem | value | normal form reached by `rfl` |
|---|---|---|
| `mfi_acFinal_U_at_5_9` (**the gate**) | `1709` | `max (pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)) 0` |
| `mfi_acFinal_V_at_5_9` | `1709` | `pairN (2·((5+9)·2^(0+1))) (2^(0+1)−1)` |
| `mfi_acFinal_U_at_5_1` | `349` | `max (pairN (2·((5+1)·2^(0+1))) (2^(0+1)−1)) 0` |
| `mfi_once_U_at_5_9` (`tFinalOnce`, no contraction) | `1709` | `pairN …` — **no `max`** |

**The `max` is `and_contract`'s and it is `max(1709, 0)`, not `max(1709, 1709)`.** The brief
expected the latter; the actual shape of `acFinal` is
`syllogism (syllogism and_contract and_weak) (syllogism (forall_ax s₁) (exist_ax s₁))`, so the
contraction's second copy of `∀u tB` is discarded by `and_weak`, whose counter majorant
supplies the *default* counter `(zeroM, ()) = (0, ())` for it. `maxT (nat ×ₜ unit) (1709,()) (0,())
= (max 1709 0, ())`. Same number, honestly different arithmetic; `tFinalOnce` shows the `max`
absent when the contraction is. Both are what the book's case 1 predicts for this derivation.

Cost: the gate goal is `numObjs = 68, approxDepth = 14` (the stalling term-route goal was
70/12); elaboration of the gate theorem ≈ 0.25 s, kernel ≈ 0.04–0.07 s. No option was raised.
Module wall clock `lake build Metatheorems.Probes.MonotoneSpike` with dependencies replayed:
**7.8 s** (`ConjBoundDemo` alone is 23 s).

Non-vacuity: the live `1708` control below fails at `decide` with the proposition exhibited
(so the `rfl` genuinely reduces — trap 12 is excluded); `mfi_acFinal_U_ne_1708`,
`_ne_1710`, `_ne_zero` are the permanent refutations.

## What did not go as predicted

* The brief's `MRealizer` shape needed the three changes listed above; the second (hoisting the
  `∃`) is a mathematical necessity at `forall_rule`, not a convenience.
* No `Term` ever appears on the bound path for the composition cases, so the `Eq.rec`/
  `Term.rename` traffic that stalls the term route is simply absent; the leaf cases
  (`forall_ax`/`exist_ax`) still go through `termMajorizer` on `Term.castTy`-wrapped terms —
  the same reductions `tFinalOnce` already survives — and cost nothing measurable.
* All four composition cases compiled on the first attempt; the only errors in the session
  were `omega` not seeing `max` at `Ty.interpret X Ty.nat.hat` (replaced by `Nat.max_comm`)
  and a namespace slip on the `MaxCompat` instance.
* Needed and absent from the tree: `maxT_comm` (to get a right-handed `maxT_bezemMaj_left`),
  and the three-field `MaxCompat` packaging, since `AbstractMajorizability` has no `max`.
-/

namespace Metatheorems
namespace MonotoneSpike

open Formula

-- ============================================================================
-- The monotone realizer
-- ============================================================================

section Generic

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

set_option linter.unusedVariables false in
/-- **A monotone realizer** of `A` in context `Γ`: a majorant `tstar` at the hat type, together
with a proof that *some* Dialectica realizer — one functional of the environment — is
majorized by it wherever the environment is, and satisfies the matrix everywhere.
`termMajorizer_maj`'s statement, one level up, with the realizer existentially quantified.
See the module header for the three points at which this differs from the brief's draft.

`cm` does not occur in the body: it is there to pin `am` (the relation the statement is about)
and because the leaf strategy reads its majorants — the same role it has in `termMajorizer`. -/
def MRealizer (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) : Type :=
  { tstar : ℕ → Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X (wTy A).hat //
    ∀ n, n ≥ am.N →
      (∃ x : Ctx.interpret X Γ → dialecticaWitness X A,
        (∀ (envstar : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
          MajEnv am Γ envstar env → am.maj (wTy A) (tstar n envstar) (x env)) ∧
        ∀ (env : Ctx.interpret X Γ) (y : dialecticaCounter X A),
          dialecticaMatrix si A env (x env) y) ∧
      (∀ (e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)), SelfMajEnv am Γ e₁ e₂ →
        am.selfMaj (wTy A) (tstar n e₁) (tstar n e₂)) }

/-- The brief's per-environment shape, derived: at every majorized environment there is a
realizer majorized by `tstar`. -/
theorem MRealizer.pointwise {cm : ConstMajorants am} {Γ : Ctx ι} {A : Formula F Γ}
    (r : MRealizer cm A) :
    ∀ n, n ≥ am.N → ∀ (envstar : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
      MajEnv am Γ envstar env →
      ∃ x : dialecticaWitness X A,
        am.maj (wTy A) (r.val n envstar) x ∧
        ∀ y : dialecticaCounter X A, dialecticaMatrix si A env x y := by
  intro n hn envstar env henv
  obtain ⟨⟨x, hx, hm⟩, _⟩ := r.property n hn
  exact ⟨x env, hx envstar env henv, hm env⟩

/-- The three `max` facts `and_contract` needs, which the abstract structure does not carry. -/
structure MaxCompat (am : AbstractMajorizability si) : Prop where
  maxT_maj_left : ∀ {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} {c : Ty.interpret X ρ},
    am.maj ρ a c → am.selfMaj ρ b b → am.maj ρ (maxT ρ a b) c
  maxT_maj_right : ∀ {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} {c : Ty.interpret X ρ},
    am.maj ρ b c → am.selfMaj ρ a a → am.maj ρ (maxT ρ a b) c
  maxT_selfMaj : ∀ {ρ : Ty ι} {a b c d : Ty.interpret X ρ.hat},
    am.selfMaj ρ a b → am.selfMaj ρ c d → am.selfMaj ρ (maxT ρ a c) (maxT ρ b d)

-- ----------------------------------------------------------------------------
-- Short names for the structure's fields, all arguments implicit
-- ----------------------------------------------------------------------------

private theorem mapp {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)} {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (hf : am.maj (ρ →ₜ τ) f_star f) (hx : am.maj ρ x_star x) :
    am.maj τ (f_star x_star) (f x) :=
  am.app_compat _ _ _ _ hf hx

private theorem mfst {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj ρ p_star.1 p.1 :=
  am.prod_fst _ _ h

private theorem msnd {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj τ p_star.2 p.2 :=
  am.prod_snd _ _ h

private theorem mpair {ρ τ : Ty ι} {a_star : Ty.interpret X ρ.hat} {a : Ty.interpret X ρ}
    {b_star : Ty.interpret X τ.hat} {b : Ty.interpret X τ}
    (ha : am.maj ρ a_star a) (hb : am.maj τ b_star b) :
    am.maj (ρ ×ₜ τ) (a_star, b_star) (a, b) :=
  am.prod_intro _ _ ha hb

private theorem marr {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)}
    (h₁ : ∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
      am.maj ρ x_star x → am.maj τ (f_star x_star) (f x))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat),
      am.selfMaj ρ x y → am.selfMaj τ (f_star x) (f_star y)) :
    am.maj (ρ →ₜ τ) f_star f :=
  am.arrow_intro _ _ h₁ h₂

private theorem sapp {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    {x y : Ty.interpret X ρ.hat} (hf : am.selfMaj (ρ →ₜ τ) f g) (hx : am.selfMaj ρ x y) :
    am.selfMaj τ (f x) (g y) :=
  am.selfMaj_app hf hx

private theorem sfst {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj ρ p.1 q.1 :=
  am.selfMaj_prod_fst _ _ h

private theorem ssnd {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj τ p.2 q.2 :=
  am.selfMaj_prod_snd _ _ h

private theorem spair {ρ τ : Ty ι} {a b : Ty.interpret X ρ.hat} {c d : Ty.interpret X τ.hat}
    (h₁ : am.selfMaj ρ a b) (h₂ : am.selfMaj τ c d) :
    am.selfMaj (ρ ×ₜ τ) (a, c) (b, d) :=
  am.selfMaj_prod_intro _ _ h₁ h₂

private theorem sarr {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    (h₁ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (g y))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (f y)) :
    am.selfMaj (ρ →ₜ τ) f g :=
  am.selfMaj_arrow_intro _ _ h₁ h₂

private theorem mself {ρ : Ty ι} {a : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (h : am.maj ρ a x) : am.selfMaj ρ a a :=
  am.maj_selfMaj h

private theorem sself {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} (h : am.selfMaj ρ a b) :
    am.selfMaj ρ a a :=
  am.selfMaj_self h

/-- Majorization transports along a type equation, on both sides at once. -/
private theorem maj_cast {σ τ : Ty ι} (h : σ = τ)
    (hh : Ty.interpret X σ.hat = Ty.interpret X τ.hat)
    (hs : Ty.interpret X σ = Ty.interpret X τ)
    {a : Ty.interpret X σ.hat} {x : Ty.interpret X σ} (hm : am.maj σ a x) :
    am.maj τ (cast hh a) (cast hs x) := by
  subst h; exact hm

private theorem selfMaj_cast {σ τ : Ty ι} (h : σ = τ)
    (hh : Ty.interpret X σ.hat = Ty.interpret X τ.hat)
    {a b : Ty.interpret X σ.hat} (hm : am.selfMaj σ a b) :
    am.selfMaj τ (cast hh a) (cast hh b) := by
  subst h; exact hm

-- ----------------------------------------------------------------------------
-- The leaf strategy: Howard's construction on a syntactic realizer
-- ----------------------------------------------------------------------------

/-- **Leaf strategy** (book p. 142): a syntactic realizer's term is majorized by its
`termMajorizer`. Used for `and_weak`, `forall_ax`, `exist_ax`, `refl0` — and as the honest
fallback for every constructor this spike does not treat. -/
def MRealizer.ofSRealizer (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F Γ}
    (r : SRealizer si A) : MRealizer cm A :=
  ⟨fun n e => termMajorizer cm r.val n e, fun n hn =>
    ⟨⟨fun env => Term.interpret si r.val env,
      fun es env henv => (termMajorizer_maj cm r.val n hn).1 es env henv,
      fun env y => r.property env y⟩,
     fun e₁ e₂ he => (termMajorizer_maj cm r.val n hn).2 e₁ e₂ he⟩⟩

-- ----------------------------------------------------------------------------
-- Composition: modus ponens (book p. 144, case 5)
-- ----------------------------------------------------------------------------

def MRealizer.mp (cm : ConstMajorants am) {Γ : Ctx ι} {A B : Formula F Γ}
    (hA : MRealizer cm A) (hAB : MRealizer cm (A →ᶠ B)) : MRealizer cm B :=
  ⟨fun n e => (hAB.val n e).1 (hA.val n e), fun n hn => by
    obtain ⟨⟨xA, hxA, hmA⟩, hsA⟩ := hA.property n hn
    obtain ⟨⟨xAB, hxAB, hmAB⟩, hsAB⟩ := hAB.property n hn
    refine ⟨⟨fun env => (xAB env).1 (xA env), ?_, ?_⟩, ?_⟩
    · intro es env henv
      exact mapp (mfst (hxAB es env henv)) (hxA es env henv)
    · intro env yB
      exact hmAB env (xA env, yB) (hmA env ((xAB env).2 (xA env) yB))
    · intro e₁ e₂ he
      exact sapp (sfst (hsAB e₁ e₂ he)) (hsA e₁ e₂ he)⟩

-- ----------------------------------------------------------------------------
-- Composition: syllogism (book p. 144, case 5, "the rule … is treated similarly")
-- ----------------------------------------------------------------------------

def MRealizer.syllogism (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (hAB : MRealizer cm (A →ᶠ B)) (hBC : MRealizer cm (B →ᶠ C)) : MRealizer cm (A →ᶠ C) :=
  ⟨fun n e =>
    (fun xA => (hBC.val n e).1 ((hAB.val n e).1 xA),
     fun xA yC => (hAB.val n e).2 xA ((hBC.val n e).2 ((hAB.val n e).1 xA) yC)),
   fun n hn => by
    obtain ⟨⟨xAB, hxAB, hmAB⟩, hsAB⟩ := hAB.property n hn
    obtain ⟨⟨xBC, hxBC, hmBC⟩, hsBC⟩ := hBC.property n hn
    refine ⟨⟨fun env =>
      (fun xA => (xBC env).1 ((xAB env).1 xA),
       fun xA yC => (xAB env).2 xA ((xBC env).2 ((xAB env).1 xA) yC)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have hab := hxAB es env henv
      have hbc := hxBC es env henv
      have abS := mself hab
      have bcS := mself hbc
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        exact mapp (mfst hbc) (mapp (mfst hab) hx)
      · intro x y hxy
        exact sapp (sfst bcS) (sapp (sfst abS) hxy)
      · intro x_star x hx
        refine marr ?_ ?_
        · intro y_star y hy
          exact mapp (mapp (msnd hab) hx)
            (mapp (mapp (msnd hbc) (mapp (mfst hab) hx)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) (mself hx))
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) (mself hx))) hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) hxy)
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) (sself hxy))
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) (sself hxy))) hy)
    · intro env y hA
      exact hmBC env ((xAB env).1 y.1, y.2)
        (hmAB env (y.1, (xBC env).2 ((xAB env).1 y.1) y.2) hA)
    · intro e₁ e₂ he
      have ab12 := hsAB e₁ e₂ he
      have bc12 := hsBC e₁ e₂ he
      have ab11 := hsAB e₁ e₁ (SelfMajEnv.self _ he)
      have bc11 := hsBC e₁ e₁ (SelfMajEnv.self _ he)
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact sapp (sfst bc12) (sapp (sfst ab12) hxy)
      · intro x y hxy
        exact sapp (sfst bc11) (sapp (sfst ab11) hxy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab12) hxy)
            (sapp (sapp (ssnd bc12) (sapp (sfst ab12) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) (sself hxy))
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) (sself hxy))) hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) hxy)
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) (sself hxy))
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) (sself hxy))) hy)⟩

-- ----------------------------------------------------------------------------
-- Composition: exportation
-- ----------------------------------------------------------------------------

def MRealizer.exportation (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : MRealizer cm (A ∧ᶠ B →ᶠ C)) : MRealizer cm (A →ᶠ B →ᶠ C) :=
  ⟨fun n e =>
    (fun xA => (fun xB => (h.val n e).1 (xA, xB),
                fun xB yC => ((h.val n e).2 (xA, xB) yC).2),
     fun xA p => ((h.val n e).2 (xA, p.1) p.2).1),
   fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    refine ⟨⟨fun env =>
      (fun xA => (fun xB => (xh env).1 (xA, xB),
                  fun xB yC => ((xh env).2 (xA, xB) yC).2),
       fun xA p => ((xh env).2 (xA, p.1) p.2).1), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have hh := hxh es env henv
      have hS := mself hh
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro xA_star xA hxA
        refine mpair (marr ?_ ?_) (marr ?_ ?_)
        · intro xB_star xB hxB
          exact mapp (mfst hh) (mpair hxA hxB)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair (mself hxA) hs)
        · intro xB_star xB hxB
          refine marr ?_ ?_
          · intro y_star y hy
            exact msnd (mapp (mapp (msnd hh) (mpair hxA hxB)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) (mself hxB))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) (sself hs))) hy)
      · intro xA_star xA hxA
        refine marr ?_ ?_
        · intro p_star p hp
          exact mfst (mapp (mapp (msnd hh) (mpair hxA (mfst hp))) (msnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair (mself hxA) (sfst hp))) (ssnd hp))
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair (sself hA) (sfst hp))) (ssnd hp))
    · intro env y hA hB
      exact hmh env ((y.1, y.2.1), y.2.2) ⟨hA, hB⟩
    · intro e₁ e₂ he
      have h12 := hsh e₁ e₂ he
      have h11 := hsh e₁ e₁ (SelfMajEnv.self _ he)
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h12) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h12) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h12) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair (sself hA) (sfst hp))) (ssnd hp))
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair (sself hA) (sfst hp))) (ssnd hp))⟩

-- ----------------------------------------------------------------------------
-- Composition: the ∀-rule (book p. 144, case 6)
-- ----------------------------------------------------------------------------

/-- The realizer is `dialectica_forall_rule`'s, written out; the majorant is the same
λ-term on the hat side, and `arrow_intro`'s two clauses are discharged from the IH at
`(z*, e)` / `(z₁, e₁), (z₂, e₂)`. The type equations `wTy (weakenBy ρ B) = wTy B` and
`cTy (weakenBy ρ B) = cTy B` are propositional, so casts appear on both sides; they are
transported by `maj_cast` / `selfMaj_cast`. -/
def MRealizer.forallRule (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ}
    {A : Formula F (ρ :: Γ)} (h : MRealizer cm (Formula.weakenBy ρ B →ᶠ A)) :
    MRealizer cm (B →ᶠ Formula.all ρ A) :=
  ⟨fun n e =>
    (fun xB z => (h.val n (z, e)).1
        (cast (congrArg (fun σ : Ty ι => Ty.interpret X σ.hat)
          (wTy_cTy_renameF B Term.Renaming.shift).1).symm xB),
     fun xB p => cast (congrArg (fun σ : Ty ι => Ty.interpret X σ.hat)
          (wTy_cTy_renameF B Term.Renaming.shift).2)
        ((h.val n (p.1, e)).2
          (cast (congrArg (fun σ : Ty ι => Ty.interpret X σ.hat)
            (wTy_cTy_renameF B Term.Renaming.shift).1).symm xB) p.2)),
   fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    have hw : wTy (Formula.weakenBy ρ B) = wTy B := (wTy_cTy_renameF B Term.Renaming.shift).1
    have hc : cTy (Formula.weakenBy ρ B) = cTy B := (wTy_cTy_renameF B Term.Renaming.shift).2
    refine ⟨⟨fun env =>
      (fun xB z => (xh (z, env)).1 (cast (dialecticaWitness_weaken ρ B).symm xB),
       fun xB p => cast (dialecticaCounter_weaken ρ B)
         ((xh (p.1, env)).2 (cast (dialecticaWitness_weaken ρ B).symm xB) p.2)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have selfEs := MajEnv.toSelfMajEnv Γ henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro xB_star xB hxB
        refine marr ?_ ?_
        · intro z_star z hz
          exact mapp (mfst (hxh (z_star, es) (z, env) ⟨hz, henv⟩))
            (maj_cast hw.symm _ _ hxB)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩))
            (selfMaj_cast hw.symm _ (mself hxB))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB_star xB hxB
        refine marr ?_ ?_
        · intro p_star p hp
          exact maj_cast hc _ _
            (mapp (mapp (msnd (hxh (p_star.1, es) (p.1, env) ⟨mfst hp, henv⟩))
              (maj_cast hw.symm _ _ hxB)) (msnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ (mself hxB))) (ssnd hp))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))
    · intro env y hprem
      have hcc : cast (dialecticaWitness_weaken ρ B)
          (cast (dialecticaWitness_weaken ρ B).symm y.1) = y.1 :=
        eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
      refine hmh (y.2.1, env) (cast (dialecticaWitness_weaken ρ B).symm y.1, y.2.2) ?_
      refine (dialecticaMatrix_weaken si B env y.2.1 _ _).mpr ?_
      rw [hcc]
      exact hprem
    · intro e₁ e₂ he
      have selfE1 := SelfMajEnv.self Γ he
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₂) ⟨hz, he⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₂) ⟨sfst hp, he⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))⟩

-- ----------------------------------------------------------------------------
-- THE POINT: contraction (book p. 143, case 1)
-- ----------------------------------------------------------------------------

/-- `A → A ∧ A`, monotone: the witness majorant is `λx.(x,x)`, the counter majorant is
`λx y. max(y', y'')` at the hat type. The realizer is `dialectica_and_contract`'s, which
branches on the (decidable) matrix; the majorant does not branch, and mentions no term. -/
def MRealizer.andContract (cm : ConstMajorants am) (hmax : MaxCompat am) {Γ : Ctx ι}
    (A : Formula F Γ) : MRealizer cm (A →ᶠ A ∧ᶠ A) :=
  ⟨fun _ _ => (fun x => (x, x), fun _ y => maxT (cTy A) y.1 y.2),
   fun _ _ => by
    refine ⟨⟨fun env =>
      (fun x => (x, x),
       fun x y => if dialecticaMatrix si A env x y.1 then y.2 else y.1), ?_, ?_⟩, ?_⟩
    · intro es env henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        exact mpair hx hx
      · intro x y hxy
        exact spair hxy hxy
      · intro x_star x hx
        refine marr ?_ ?_
        · intro y_star y hy
          by_cases hd : dialecticaMatrix si A env x y.1
          · simp only [if_pos hd]
            exact hmax.maxT_maj_right (msnd hy) (sfst (mself hy))
          · simp only [if_neg hd]
            exact hmax.maxT_maj_left (mfst hy) (ssnd (mself hy))
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
    · intro env y hm
      simp only [dialecticaMatrix] at hm ⊢
      by_cases hd : dialecticaMatrix si A env y.1 y.2.1
      · simp only [if_pos hd] at hm
        exact ⟨hd, hm⟩
      · simp only [if_neg hd] at hm
        exact absurd hm hd
    · intro e₁ e₂ _
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact spair hxy hxy
      · intro x y hxy
        exact spair hxy hxy
      · intro x y _
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
      · intro x y _
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact hmax.maxT_selfMaj (sfst hy) (ssnd hy)⟩

-- ----------------------------------------------------------------------------
-- The recursion over the derivation
-- ----------------------------------------------------------------------------

variable {Premises : PremiseSet F}

/-- **The monotone functional interpretation, on the nine constructors `acFinal` uses.**

Structural recursion on the derivation. The nine are treated as in the module-header table;
**every other constructor falls to the leaf strategy on the whole sub-derivation** — the term
route, `termMajorizer` of `syntactic_soundness`'s realizer. That fallback is honest (no
`sorry`, a genuine `MRealizer`) and is never reached for `acFinal`. -/
def monotone_spike (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) (hmax : MaxCompat am) :
    {Γ : Ctx ι} → {A : Formula F Γ} →
    @Derivable ι κ F Allowed.extended Premises Γ A → MRealizer cm A
  | _, _, .mp hA hAB       => MRealizer.mp cm (monotone_spike eqxi spremise cm hmax hA)
                                (monotone_spike eqxi spremise cm hmax hAB)
  | _, _, .syllogism h₁ h₂ => MRealizer.syllogism cm (monotone_spike eqxi spremise cm hmax h₁)
                                (monotone_spike eqxi spremise cm hmax h₂)
  | _, _, .exportation h'  => MRealizer.exportation cm (monotone_spike eqxi spremise cm hmax h')
  | _, _, .forall_rule h'  => MRealizer.forallRule cm (monotone_spike eqxi spremise cm hmax h')
  | _, _, .and_contract    => MRealizer.andContract cm hmax _
  | _, _, .and_weak        => MRealizer.ofSRealizer cm sAndWeak
  | _, _, .forall_ax t     => MRealizer.ofSRealizer cm (sForallAx t)
  | _, _, .exist_ax t _    => MRealizer.ofSRealizer cm (sExistAx t)
  | _, _, .refl0           => MRealizer.ofSRealizer cm sRefl0
  -- FALLBACK: every other constructor, via the term route. Never reached for `acFinal`.
  | _, _, prf              => MRealizer.ofSRealizer cm (syntactic_soundness eqxi spremise prf)

-- ----------------------------------------------------------------------------
-- Reading `U` and `V` off a monotone realizer — `extractUTerm`/`extractVTerm`, semantically
-- ----------------------------------------------------------------------------

/-- The `U`-majorant of a monotone realizer of `∀x(∀u B₀ → ∃v C₀)`, read off exactly as
`extractUTerm` reads it off the realizing term: the `.snd` of the implication's majorant,
applied to the majorants of the default witness and counter, first projection. The default
terms live in context `[ρ]`, as in `extractUTerm`; their majorants are environment-independent
(`CounterSideProbe.termMajorizer_defaultOf`). -/
def mfiU {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]} (cm : ConstMajorants am)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).2
    (termMajorizer cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N (xs, ()))
    (termMajorizer cm (defaultCTerm (Formula.ex Ty.nat C₀)) am.N (xs, ()))).1

/-- The `V`-majorant, as `extractVTerm`. -/
def mfiV {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]} (cm : ConstMajorants am)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).1
    (termMajorizer cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N (xs, ()))).1

end Generic

-- ============================================================================
-- `MaxCompat` for every `bezemAbstract`, hence for the W-hyperbolic model
-- ============================================================================

section Max

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι}

/-- `maxT` is commutative at every hat type. Did not exist; needed to get the right-handed
`maxT_bezemMaj_left` from the left-handed one. -/
theorem maxT_comm : ∀ (ρ : Ty ι) (a b : Ty.interpret X ρ.hat), maxT ρ a b = maxT ρ b a
  -- `omega` treats `Ty.interpret X Ty.nat.hat`-typed atoms as opaque (CLAUDE.md), so the
  -- two numeric cases go by the core lemma directly
  | .nat, a, b => by simp only [maxT]; exact Nat.max_comm _ _
  | .base _, a, b => by simp only [maxT]; exact Nat.max_comm _ _
  | .unit, _, _ => rfl
  | .arr _ τ, f, g => funext fun x => maxT_comm τ (f x) (g x)
  | .prod ρ τ, p, q => Prod.ext (maxT_comm ρ p.1 q.1) (maxT_comm τ p.2 q.2)

theorem bezemMaxCompat (si : SpaceInterp X F) {base : (i : ι) → Nat → X i → Prop}
    (hbase : BaseMono base) (N : ℕ) (hz hs hp hf hx hd) :
    MaxCompat (bezemAbstract si base N hz hs hp hf hx hd) where
  maxT_maj_left h₁ h₂ := maxT_bezemMaj_left hbase _ _ _ _ h₁ h₂
  maxT_maj_right h₁ h₂ := by
    rw [maxT_comm]
    exact maxT_bezemMaj_left hbase _ _ _ _ h₁ h₂
  maxT_selfMaj h₁ h₂ := maxT_hatMaj _ _ _ _ _ h₁ h₂

end Max

/-- `MaxCompat` for the W-hyperbolic model: its `abstractMajorizability` is a `bezemAbstract`
over `M.base`, which is `BaseMono`. -/
theorem wMaxCompat (M : WHyperbolicModel) : MaxCompat M.abstractMajorizability :=
  bezemMaxCompat M.si M.base_mono 0 _ _ _ _ _ _

-- ============================================================================
-- THE GATE: `acFinal` at `x* = (5, 9)` under `triCm M h`
-- ============================================================================

section Gate

open TriangleBoundDemo (pTy triCm)
open ConjBoundDemo (tB acFinal tFinalOnce)

/-- Constructor count, copied from `SizeProbe.derivSize` (that file is not imported here). -/
def derivSizeSpike {ι κ : Type} {F : κ → Ty ι} {al : Allowed} {P : PremiseSet F} :
    {Γ : Ctx ι} → {A : Formula F Γ} → @Derivable ι κ F al P Γ A → Nat
  | _, _, .mp a b          => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .syllogism a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, .exportation a   => 1 + derivSizeSpike a
  | _, _, .importation a   => 1 + derivSizeSpike a
  | _, _, .expansion a     => 1 + derivSizeSpike a
  | _, _, .forall_rule a   => 1 + derivSizeSpike a
  | _, _, .exist_rule a    => 1 + derivSizeSpike a
  | _, _, .univ_gen a      => 1 + derivSizeSpike a
  | _, _, .qfer _ _ a      => 1 + derivSizeSpike a
  | _, _, .induction a b   => 1 + derivSizeSpike a + derivSizeSpike b
  | _, _, _                => 1

/-- The scale of the gate: `acFinal` is thirteen constructors. -/
theorem derivSize_acFinal : derivSizeSpike acFinal = 13 := rfl

/-- The monotone realizer of `acFinal`, at the W-hyperbolic model with `d(a, 0_X) ≤ 5`. -/
noncomputable def acSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_spike M.eqXInterp M.spremise (triCm M h) (wMaxCompat M) acFinal

/-- The same for the contraction-free control `tFinalOnce`. -/
noncomputable def onceSpike (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    MRealizer (triCm M h)
      (Formula.all pTy (Formula.imp (Formula.all Ty.nat tB) (Formula.ex Ty.nat tB))) :=
  monotone_spike M.eqXInterp M.spremise (triCm M h) (wMaxCompat M) tFinalOnce

-- DAG measurement only (`numObjs`, never `sizeWithoutSharing`).
open Lean Elab Tactic in
elab "goal_size_mfi" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

set_option linter.unusedTactic false

/-- **THE GATE.** The counter-side bound of `acFinal` — the one that is a `whnf` timeout on the
term route (`ConjBoundDemo.acUt_at_5_9`) — through the monotone interpretation. -/
theorem mfi_acFinal_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  goal_size_mfi
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The witness side of the same derivation, expected to agree with `cVtTwice_at_5_9`'s
term-route value. -/
theorem mfi_acFinal_V_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  goal_size_mfi
  have hval : mfiV (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- The bound moves with `x*`: at `(5,1)` it is `349`, `s₁`'s majorant there
(`ConjBoundDemo.witM1_at_5_1`). -/
theorem mfi_acFinal_U_at_5_1 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (349 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (1 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 1) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

/-- The contraction-free control `tFinalOnce` through the same interpretation: the same
`1709`, and — visibly in the `hval` normal form — **no `max`**. The `max` in the gate's
normal form is `and_contract`'s, and nothing else's. -/
theorem mfi_once_U_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (onceSpike M h) ((5 : ℕ), (9 : ℕ))
      = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1) := rfl
  rw [hval]
  decide

/-- Permanent refutation controls: the gate value is exact from below and above. -/
theorem mfi_acFinal_U_ne_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

theorem mfi_acFinal_U_ne_1710 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1710 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

/-- The `U` is not `0` — the premise is consulted. -/
theorem mfi_acFinal_U_ne_zero (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (0 : ℕ) ≠ mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  rw [← mfi_acFinal_U_at_5_9 M h]; decide

/-! ### The live negative control, run and then removed

The gate theorem with `1708` in place of `1709` — same `hval := rfl`, same `decide`. The `rfl`
step **succeeded** (so the pipeline genuinely reduces to a closed ℕ expression; this is not a
both-sides-stuck no-op, trap 12) and `decide` then refuted it. Verbatim, from
`lake env lean` on 2026-09-05:

```
theorem ctrl_1708 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1708 : ℕ) = mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ)) := by
  have hval : mfiU (triCm M h) (acSpike M h) ((5 : ℕ), (9 : ℕ))
      = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0 := rfl
  rw [hval]
  decide

Metatheorems/Probes/MonotoneSpike.lean:810:2: error: Tactic `decide` proved that the proposition
  1708 = max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) 0
is false
```

Refutation, not merely "the proof did not go through". `mfi_acFinal_U_ne_1708` is the
permanent form. -/

end Gate

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms MRealizer.ofSRealizer
#print axioms MRealizer.mp
#print axioms MRealizer.syllogism
#print axioms MRealizer.exportation
#print axioms MRealizer.forallRule
#print axioms MRealizer.andContract
#print axioms monotone_spike
#print axioms bezemMaxCompat
#print axioms wMaxCompat
#print axioms derivSize_acFinal
#print axioms mfi_acFinal_U_at_5_9
#print axioms mfi_acFinal_V_at_5_9
#print axioms mfi_acFinal_U_at_5_1
#print axioms mfi_once_U_at_5_9
#print axioms mfi_acFinal_U_ne_1708
#print axioms mfi_acFinal_U_ne_1710
#print axioms mfi_acFinal_U_ne_zero

end MonotoneSpike
end Metatheorems
