/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.SeqMpBoundProbe

/-!
# Probe: the quantifier combinators and the `pm_*` layer (Track A item 3)

`SeqMpBoundProbe.lean` carried `termMajorizer` through the three proof-mode primitives on the
witness side; `CounterSideProbe.lean` did the counter side of the propositional combinators.
This file covers the four `SRealizer` combinators still missing — `sForallRule`,
`sExistRule`, `sUnivGen`, `sQfer` — on **both** sides, and then unfolds every `pm_*` tactic
`mct_p2` uses to the three `seq_*` primitives.

Everything is Δ-generic and symbolic: no numeral is ever instantiated, and no arithmetic
constant is unfolded under `termMajorizer`.

## What is here

| combinator | witness lemma | counter lemma |
|---|---|---|
| `sUnivGen`     | `wall_sUnivGen`            | — (a `∀`-realizer has no counter component) |
| `sForallRule`  | `wall_wapp_sForallRule`    | `capp_sForallRule` |
| `sExistRule`   | `wapp_sExistRule`          | `capp_sExistRule` |
| `sQfer`        | `wapp_sQfer`               | `capp_sQfer` |

All four go through by the same discipline as before — unfold one combinator, sub-realizers
as variables, `termMajorizer_weaken`/`_castTy`/`_rename_gen`/`_subst_gen` at the binder
crossings — and **none of them resisted**. The only new ingredient is that `sForallRule` and
`sExistRule` relocate their sub-realizer with a *renaming* or a *substitution* rather than a
`Term.weaken`, so the corresponding general lemma is used with an explicit environment
correspondence (`fun v => by cases v <;> rfl`) instead of the `@[simp]` `_weaken` form.

## The `pm_*` layer

`headStats` (a DAG walk over the elaborated term, never materialising sharing) lists the
constants `mct_p2` actually contains, transitively through `mct_body` and `mct_descent`:

    pm_enter pm_intro pm_have pm_mp pm_cut pm_inst pm_sym pm_trans pm_rw_at pm_andE₁ pm_andE₂
    pm_cases pm_exI pm_allE_here_cut pm_allI pm_induction seq_id
    qfer_at_nf qfer_no_premise_at_nf Eq.mpr

The `pm_*_eq` / `seq_*_eq` block below shows by `rfl` that all of these except **three** are
compositions of `seq_of_thm`/`seq_mp`/`seq_id` applied to kernel theorems:

1. **`pm_allI` = `seq_allI`** does not reduce to the primitives: it recurses on `Δ` with one
   `seq_mono forall_imp_pull` per hypothesis and a raw `.mp I_comb (.forall_rule …)` at the
   bottom. It *is* Δ-generic in the same sense `seq_mp` is, and `wit_seq_allI` below is the
   commutation lemma — the first use-site of `wall_wapp_sForallRule`.
2. **`pm_induction` = `seq_induction`** — out of scope here (CLAUDE.md Track A item 2).
3. **`Eq.mpr`**, which is not a `pm_*` at all: `anorm`/`anorm_ren`/`prw_norm` are `simp only`
   calls on a `SeqD` goal, so they rewrite the goal *formula* and leave an `Eq.mpr` node in the
   derivation term. `syntactic_soundness_eqmpr` handles it: with the formula equation
   `hB : B = B'` in hand the cast is transparent to `syntactic_soundness` (proof irrelevance
   turns the `Eq.mpr` into the identity once `hB` is substituted). The equation is exactly what
   the same `simp only` set proves at the formula level.

## Non-vacuity controls (run 2026-09-04, scratch files, all EXPECTED TO FAIL — 9/9 did)

Every proof here ends in `rfl` or a closing `simp only`, so the `conv`-without-closer trap
cannot occur; the controls check that the *statements* are not vacuous:

| control | change | outcome |
|---|---|---|
| W1 `capp_sForallRule` | `y.2` replaced by `defM` | `rfl` fails |
| W2 `capp_sExistRule`  | environment not extended by `w.1` | `rfl` fails |
| W3 `capp_sQfer`       | `w` replaced by the default witness | `rfl` fails |
| W4 `wall_wapp_sForallRule` | `x` dropped from the environment | `rfl` fails |
| W5 `wall_forall_imp_pull`  | `x` replaced by `defM` on the right | `rfl` fails |
| W6 `wit_seq_allI` at `Δ = [A₀]` | environment not extended by `x` | unsolved goal |
| I1 `capp_sExistRule`, I2 `capp_sForallRule` | no `termMajorizer_subst_gen` | unsolved goals |
| I3 `wall_forall_imp_pull` | no `wall_wapp_sForallRule` | unsolved goal |

Two further controls were run independently by the supervising session, not by the agent
that wrote this file, and both failed as required: `capp_sQfer` with the incoming witness
`w` replaced on the right by `defM` (the error exhibits the real LHS reading
`Ctx.lookupHat Var.vz.vs (y, w, e)`, so `w` really is transmitted), and `capp_sForallRule`
with `y.2` replaced by `defM`.

## What is NOT done

* **The counter side of `seq_allI`** (`cwit_seq_allI`, the analogue of `wit_seq_allI` for
  `capp`). Not attempted; `capp_sForallRule` is the leaf it would need and it is here.
* **Counter-side lemmas for `forall_ax_vz`/`forall_imp_pull`** — same remark.
* **`sInduction` / `seq_induction`** — out of scope by instruction. What a statement would
  have to look like, for the record: `seq_induction` at `A₀ :: Δ` inducts on
  `A' := A₀↑ →ᶠ A`, so the witness type at depth `k` is
  `wTy (A_k↑ →ᶠ … →ᶠ A₁↑ →ᶠ A)` — a *function* of the context. A Δ-generic lemma therefore
  cannot fix `A`; it must quantify over the family `A_Δ := pack (Δ.map (weakenBy nat)) A`
  and relate `wall (wit Δ (tm (ss (seq_induction base step))) as) k` to a `cm.precM`-driven
  recursion whose *base* is `wit Δ (tm (ss base)) as` and whose *step* is
  `wit Δ (tm (ss step)) as` applied at each stage — i.e. the same `Nat.rec` that `sInduction`
  builds, but with `wit Δ … as` pushed inside both arguments through the `seq_cast`
  (`syntactic_soundness_subst` here handles that cast) and the two `seq_mono`s
  (`forall_mono S_comb`, `forall_imp_push`, each needing its own witness lemma). The
  `Δ = []` case is `sInduction base step` directly. So the shape is "`wit` commutes with
  `Nat.rec`", indexed by the packed formula family; no code was written for it.

NOT imported by `Metatheorems.lean`, per the `Probes/` convention.
`CounterSideProbe.lean` is **not** imported either: it cannot be *built* under a 12 GB cap
(`INTERNAL PANIC: out of memory` inside its Stage B `example`), so its `capp`/`cfst`/`defM`
are re-declared here, definitionally identical, so the counter lemmas compose with its once
the two are merged. Building the chain also needed two one-token post-ι/κ-split fixes
(`@Derivable Empty FEmpty …` → `@Derivable Empty Empty FEmpty …`) in `BoundProbe.lean:84`
and `SeqMpBoundProbe.lean:109`, exactly the site class CLAUDE.md's split note predicts.
-/

namespace Metatheorems
namespace CombinatorLemmas

open ProofMode BoundProbe BoundLemmasP2 SeqMpBoundProbe Formula

section Proj
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} (cm : ConstMajorants am) {Γ : Ctx ι}

/-- Counter application (same as `CounterSideProbe.capp`): the second component of a
majorant at an implication's witness type. This is what `extractUTerm` reads. -/
def capp {A B : Formula F Γ} (r : Ty.interpret X (wTy (A →ᶠ B)).hat)
    (a : Ty.interpret X (wTy A).hat) (y : Ty.interpret X (cTy B).hat) :
    Ty.interpret X (cTy A).hat := r.2 a y

/-- First component of a counter at `cTy (∀x A) = ρ ×ₜ cTy A` (same as
`CounterSideProbe.cfst`). -/
def cfst {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (y : Ty.interpret X (cTy (Formula.all ρ A)).hat) : Ty.interpret X ρ.hat := y.1

/-- Apply a `∀`-witness majorant at `wTy (∀x A) = ρ →ₜ wTy A` to a point. -/
def wall {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (w : Ty.interpret X (wTy (Formula.all ρ A)).hat) (x : Ty.interpret X ρ.hat) :
    Ty.interpret X (wTy A).hat := w x

/-- Transport along an equation of object types, at the majorant level. -/
abbrev hatCast {ρ σ : Ty ι} (h : ρ = σ) (v : Ty.interpret X ρ.hat) : Ty.interpret X σ.hat :=
  cast (congrArg (fun ρ => Ty.interpret X ρ.hat) h) v

variable (n : ℕ)

/-- The majorant of `Term.defaultOf ρ` (same as `CounterSideProbe.defM`). -/
def defM : (ρ : Ty ι) → Ty.interpret X ρ.hat
  | .nat      => cm.zeroM n
  | .base i   => cm.zeroXM i n
  | .unit     => ()
  | .arr _ τ  => fun _ => defM τ
  | .prod ρ τ => (defM ρ, defM τ)

theorem termMajorizer_defaultOf : ∀ (ρ : Ty ι) {Δ : Ctx ι} (e : Ctx.interpret X (Δ.map Ty.hat)),
    termMajorizer cm (Term.defaultOf ρ) n e = defM cm n ρ
  | .nat, _, _ => rfl
  | .base _, _, _ => rfl
  | .unit, _, _ => rfl
  | .arr _ τ, _, e => by
      funext x; simp only [Term.defaultOf, termMajorizer, defM]
      exact termMajorizer_defaultOf τ _
  | .prod ρ τ, _, e => by
      simp only [Term.defaultOf, termMajorizer, defM]
      exact Prod.ext (termMajorizer_defaultOf ρ _) (termMajorizer_defaultOf τ _)

variable (e : Ctx.interpret X (Γ.map Ty.hat))

@[simp] theorem termMajorizer_defaultCTerm (A : Formula F Γ) :
    termMajorizer cm (defaultCTerm A) n e = defM cm n (cTy A) :=
  termMajorizer_defaultOf cm n _ _

@[simp] theorem termMajorizer_defaultWTerm (A : Formula F Γ) :
    termMajorizer cm (defaultWTerm A) n e = defM cm n (wTy A) :=
  termMajorizer_defaultOf cm n _ _

end Proj

-- ============================================================================
-- The four combinators
-- ============================================================================

section Combinators
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} (cm : ConstMajorants am) {Γ : Ctx ι}
    (n : ℕ) (e : Ctx.interpret X (Γ.map Ty.hat))

/-- **`sUnivGen`**: the majorant of `∀x A↑`'s realizer is constant in `x` — the
sub-realizer's own majorant, transported along `wTy (A↑) = wTy A`. There is no counter
lemma: a `∀`-formula's realizer is a bare function, the counter `(x, y)` lives outside it. -/
theorem wall_sUnivGen {ρ : Ty ι} {A : Formula F Γ} (r : SRealizer si A)
    (x : Ty.interpret X ρ.hat) :
    wall (termMajorizer cm (sUnivGen (si := si) (ρ := ρ) r).val n e) x
      = hatCast (wTy_cTy_renameF A Term.Renaming.shift).1.symm (termMajorizer cm r.val n e) := by
  simp only [wall, sUnivGen, termMajorizer, termMajorizer_castTy, termMajorizer_weaken]

/-- **`sForallRule`, witness side.** From `h : B↑ →ᶠ A` (in context `ρ :: Γ`) the rule
builds `B →ᶠ ∀x A`; its witness, fed `b` and then applied at `x`, is `h`'s witness at the
environment extended by `x`, fed `b` transported along `wTy (B↑) = wTy B`. -/
theorem wall_wapp_sForallRule {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : SRealizer si (Formula.weakenBy ρ B →ᶠ A))
    (b : Ty.interpret X (wTy B).hat) (x : Ty.interpret X ρ.hat) :
    wall (wapp (termMajorizer cm (sForallRule h).val n e) b) x
      = wapp (termMajorizer cm h.val n (x, e))
          (hatCast (wTy_cTy_renameF B Term.Renaming.shift).1.symm b) := by
  simp only [wall, wapp, sForallRule, SRealizer.imp, termMajorizer, termMajorizer_castTy]
  rw [termMajorizer_rename_gen cm (Γ := ρ :: Γ) (Δ := ρ :: wTy B :: Γ)
    (Term.Renaming.ext Term.Renaming.shift) h.val n (x, b, e) (x, e) ?_]
  · rfl
  · intro τ v; cases v <;> rfl

/-- **`sForallRule`, counter side.** The counter `y = (y.1, y.2)` for `∀x A` is answered by
`h`'s counter at the environment extended by `y.1`, fed the transported `b` and `y.2`,
transported back along `cTy (B↑) = cTy B`. -/
theorem capp_sForallRule {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : SRealizer si (Formula.weakenBy ρ B →ᶠ A))
    (b : Ty.interpret X (wTy B).hat) (y : Ty.interpret X (cTy (Formula.all ρ A)).hat) :
    capp (termMajorizer cm (sForallRule h).val n e) b y
      = hatCast (wTy_cTy_renameF B Term.Renaming.shift).2
          (capp (termMajorizer cm h.val n (y.1, e))
            (hatCast (wTy_cTy_renameF B Term.Renaming.shift).1.symm b) y.2) := by
  simp only [capp, sForallRule, SRealizer.imp, termMajorizer, termMajorizer_castTy]
  rw [termMajorizer_subst_gen cm (Γ := ρ :: Γ) (Δ := cTy (Formula.all ρ A) :: wTy B :: Γ)
    _ h.val n (y, b, e) (y.1, e) ?_]
  · rfl
  · intro τ v; cases v <;> rfl

/-- **`sExistRule`, witness side.** From `h : A →ᶠ B↑` the rule builds `∃x A →ᶠ B`; fed the
pair `w = (w.1, w.2)`, its witness is `h`'s witness at the environment extended by `w.1`,
fed `w.2`, transported along `wTy (B↑) = wTy B`. -/
theorem wapp_sExistRule {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : SRealizer si (A →ᶠ Formula.weakenBy ρ B))
    (w : Ty.interpret X (wTy (Formula.ex ρ A)).hat) :
    wapp (termMajorizer cm (sExistRule h).val n e) w
      = hatCast (wTy_cTy_renameF B Term.Renaming.shift).1
          (wapp (termMajorizer cm h.val n (w.1, e)) w.2) := by
  simp only [wapp, sExistRule, SRealizer.imp, termMajorizer, termMajorizer_castTy]
  rw [termMajorizer_subst_gen cm (Γ := ρ :: Γ) (Δ := wTy (Formula.ex ρ A) :: Γ)
    _ h.val n (w, e) (w.1, e) ?_]
  · rfl
  · intro τ v; cases v <;> rfl

/-- **`sExistRule`, counter side.** The counter for `∃x A` is `cTy A` itself; it is `h`'s
counter at the environment extended by `w.1`, fed `w.2` and the transported `y`. -/
theorem capp_sExistRule {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : SRealizer si (A →ᶠ Formula.weakenBy ρ B))
    (w : Ty.interpret X (wTy (Formula.ex ρ A)).hat) (y : Ty.interpret X (cTy B).hat) :
    capp (termMajorizer cm (sExistRule h).val n e) w y
      = capp (termMajorizer cm h.val n (w.1, e)) w.2
          (hatCast (wTy_cTy_renameF B Term.Renaming.shift).2.symm y) := by
  simp only [capp, sExistRule, SRealizer.imp, termMajorizer, termMajorizer_castTy]
  rw [termMajorizer_subst_gen cm (Γ := ρ :: Γ) (Δ := cTy B :: wTy (Formula.ex ρ A) :: Γ)
    _ h.val n (y, w, e) (w.1, e) ?_]
  · rfl
  · intro τ v; cases v <;> rfl

variable (eqxi : EqXInterp X F si)

/-- **`sQfer`, witness side**: the default witness of the conclusion's equation, ignoring
the premise witness — `eqAtType`'s witness type is a subsingleton and carries nothing. -/
theorem wapp_sQfer {A₀ : Formula F Γ} {ρ σ : Ty ι} {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (ih : SRealizer si (A₀ →ᶠ eqAtType ρ s t)) (w : Ty.interpret X (wTy A₀).hat) :
    wapp (termMajorizer cm (sQfer eqxi (r := r) hqf hvf ih).val n e) w
      = defM cm n (wTy (eqAtType σ (r.subst0 s) (r.subst0 t))) := by
  simp only [wapp, sQfer, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_defaultWTerm]

/-- **`sQfer`, counter side**: the premise counter is the induction hypothesis's counter,
fed the premise witness and the *default* counter of the hypothesis equation — the
conclusion's counter `y` is discarded. -/
theorem capp_sQfer {A₀ : Formula F Γ} {ρ σ : Ty ι} {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (ih : SRealizer si (A₀ →ᶠ eqAtType ρ s t)) (w : Ty.interpret X (wTy A₀).hat)
    (y : Ty.interpret X (cTy (eqAtType σ (r.subst0 s) (r.subst0 t))).hat) :
    capp (termMajorizer cm (sQfer eqxi (r := r) hqf hvf ih).val n e) w y
      = capp (termMajorizer cm ih.val n e) w (defM cm n (cTy (eqAtType ρ s t))) := by
  simp only [capp, sQfer, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_defaultCTerm]
  rfl

end Combinators

-- ============================================================================
-- Casts on derivations: what `anorm` leaves behind
-- ============================================================================

section Casts
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {P : PremiseSet F} (eqxi : EqXInterp X F si)
    (sp : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B) {Γ : Ctx ι}

/-- A `simp only` on a `SeqD`/`Derivable` goal leaves `Eq.mpr e d` in the term, with
`e : Derivable … B = Derivable … B'` built by `congrArg` from a formula equation. Given that
formula equation, the cast is invisible to `syntactic_soundness`: after `subst`, `e` is a
proof of `X = X`, hence definitionally `rfl` by proof irrelevance. -/
theorem syntactic_soundness_eqmpr {B B' : Formula F Γ} (hB : B = B')
    (e' : Derivable F Allowed.extended P B = Derivable F Allowed.extended P B')
    (d : Derivable F Allowed.extended P B') :
    (syntactic_soundness eqxi sp (Eq.mpr e' d)).val
      = Term.castTy (congrArg wTy hB.symm) (syntactic_soundness eqxi sp d).val := by
  subst hB; rfl

/-- The same for `Eq.mp`, the direction `forall_ax_vz` and `qfer_at_nf` use. -/
theorem syntactic_soundness_eqmp {B B' : Formula F Γ} (hB : B = B')
    (e' : Derivable F Allowed.extended P B = Derivable F Allowed.extended P B')
    (d : Derivable F Allowed.extended P B) :
    (syntactic_soundness eqxi sp (Eq.mp e' d)).val
      = Term.castTy (congrArg wTy hB) (syntactic_soundness eqxi sp d).val := by
  subst hB; rfl

/-- And for `▸`, which `seq_cast` uses. -/
theorem syntactic_soundness_subst {B B' : Formula F Γ} (hB : B = B')
    (d : Derivable F Allowed.extended P B) :
    (syntactic_soundness eqxi sp (hB ▸ d)).val
      = Term.castTy (congrArg wTy hB) (syntactic_soundness eqxi sp d).val := by
  subst hB; rfl

end Casts

-- ============================================================================
-- The `pm_*` layer, unfolded to the three primitives
-- ============================================================================

section PM
variable {ι : Type} {F : ι → Ty ι} {a : Allowed} {P : PremiseSet F} {Γ : Ctx ι}
    {ns : List String}

/-! Every lemma here is `rfl`: the `pm_*` and derived `seq_*` definitions are plain
compositions. They are stated so a `simp only` can rewrite a proof-mode term into
`seq_of_thm`/`seq_mp`/`seq_id` applied to kernel theorems, at which point
`wit_seq_of_thm`/`wit_seq_mp`/`wit_seq_id` (and their counter-side counterparts, when
written) take over. -/

-- derived `seq_*`
theorem seq_mono_eq {Δ : HCtx F Γ} {A A' : Formula F Γ} (h : Derivable F a P (A →ᶠ A'))
    (d : Seq F a P Δ A) : seq_mono h d = seq_mp (seq_of_thm h) d := rfl
theorem seq_cut_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (hA : Seq F a P Δ A)
    (hB : Seq F a P (A :: Δ) B) : seq_cut hA hB = seq_mp hB hA := rfl
theorem seq_intro_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : Seq F a P (A :: Δ) B) :
    seq_intro h = h := rfl
theorem seq_lift₂_eq {Δ : HCtx F Γ} {A B C : Formula F Γ} (h : Derivable F a P (A →ᶠ B →ᶠ C))
    (hA : Seq F a P Δ A) (hB : Seq F a P Δ B) :
    seq_lift₂ h hA hB = seq_mp (seq_mp (seq_of_thm h) hA) hB := rfl
theorem seq_lift₃_eq {Δ : HCtx F Γ} {A B C D : Formula F Γ}
    (h : Derivable F a P (A →ᶠ B →ᶠ C →ᶠ D))
    (hA : Seq F a P Δ A) (hB : Seq F a P Δ B) (hC : Seq F a P Δ C) :
    seq_lift₃ h hA hB hC = seq_mp (seq_mp (seq_mp (seq_of_thm h) hA) hB) hC := rfl
theorem seq_andI_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (hA : Seq F a P Δ A) (hB : Seq F a P Δ B) :
    seq_andI hA hB = seq_mp (seq_mp (seq_of_thm and_intro) hA) hB := rfl
theorem seq_andE₁_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : Seq F a P Δ (A ∧ᶠ B)) :
    seq_andE₁ h = seq_mp (seq_of_thm and_proj1) h := rfl
theorem seq_andE₂_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : Seq F a P Δ (A ∧ᶠ B)) :
    seq_andE₂ h = seq_mp (seq_of_thm and_proj2) h := rfl
theorem seq_weaken_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : Seq F a P Δ B) :
    seq_weaken (A := A) h = seq_mp (seq_of_thm K_comb) h := rfl
theorem seq_orE_eq {Δ : HCtx F Γ} {A B C : Formula F Γ} (hAB : Seq F a P Δ (A ∨ᶠ B))
    (hA : Seq F a P (A :: Δ) C) (hB : Seq F a P (B :: Δ) C) :
    seq_orE hAB hA hB = seq_mp (seq_mp (seq_mp (seq_of_thm or_elim_internal) hA) hB) hAB := rfl
theorem seq_exfalso_eq {Δ : HCtx F Γ} {A : Formula F Γ} (h : Seq F a P Δ ⊥ᶠ) :
    seq_exfalso (A := A) h = seq_mp (seq_of_thm .exfalso) h := rfl
theorem seq_allE_eq {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F a P Δ (Formula.all ρ A)) (t : Term F Γ ρ) :
    seq_allE h t = seq_mp (seq_of_thm (.forall_ax t)) h := rfl
theorem seq_allE_here_eq {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : Seq F a P Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    seq_allE_here h = seq_mp (seq_of_thm forall_ax_vz) h := rfl
theorem seq_exI_eq {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F a P Δ (A.subst0 t)) :
    seq_exI t h = seq_mp (seq_of_thm (.exist_ax t A)) h := rfl
theorem seq_bound_eq {Δ : HCtx F Γ} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : Seq F a P Δ (A.subst0 t)) :
    seq_bound t h = seq_mp (seq_of_thm (.exist_ax t A)) h := rfl

-- the `pm_*` used by `mct_p2`, plus the rest of the propositional ones
theorem pm_enter_eq {A : Formula F Γ} (h : SeqD [] F a P [] A) : pm_enter h = h := rfl
theorem pm_intro_eq (nm : String) {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD (nm :: ns) F a P (A :: Δ) B) : pm_intro (ns := ns) nm h = h := rfl
theorem pm_have_eq {Δ : HCtx F Γ} {A : Formula F Γ} (h : Derivable F a P A) :
    pm_have (ns := ns) (Δ := Δ) h = seq_of_thm h := rfl
theorem pm_mp_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (hAB : SeqD ns F a P Δ (A →ᶠ B))
    (hA : SeqD ns F a P Δ A) : pm_mp hAB hA = seq_mp hAB hA := rfl
theorem pm_cut_eq (nm : String) {Δ : HCtx F Γ} {A C : Formula F Γ} (hA : SeqD ns F a P Δ A)
    (k : SeqD (nm :: ns) F a P (A :: Δ) C) : pm_cut nm hA k = seq_mp k hA := rfl
theorem pm_sym_eq {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat}
    (h : SeqD ns F a P Δ (Formula.eq0 t s)) :
    pm_sym h = seq_mp (seq_of_thm .sym0) h := rfl
theorem pm_trans_eq {Δ : HCtx F Γ} {s u : Term F Γ Ty.nat} (t : Term F Γ Ty.nat)
    (h₁ : SeqD ns F a P Δ (Formula.eq0 s t)) (h₂ : SeqD ns F a P Δ (Formula.eq0 t u)) :
    pm_trans t h₁ h₂
      = seq_mp (seq_of_thm .trans0) (seq_mp (seq_mp (seq_of_thm and_intro) h₁) h₂) := rfl
theorem pm_rw_at_eq (nm : String) {Δ : HCtx F Γ} {Pt P' Q Q' : Term F Γ Ty.nat}
    {C : Formula F Γ}
    (congP : SeqD ns F a P Δ (Formula.eq0 Pt P')) (congQ : SeqD ns F a P Δ (Formula.eq0 Q Q'))
    (hf : SeqD ns F a P Δ (Formula.eq0 Pt Q))
    (k : SeqD (nm :: ns) F a P (Formula.eq0 P' Q' :: Δ) C) :
    pm_rw_at nm congP congQ hf k
      = seq_mp k (pm_trans Pt (pm_sym congP) (pm_trans Q hf congQ)) := rfl
theorem pm_sym_at_eq (nm : String) {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat} {C : Formula F Γ}
    (h : SeqD ns F a P Δ (Formula.eq0 s t))
    (k : SeqD (nm :: ns) F a P (Formula.eq0 t s :: Δ) C) :
    pm_sym_at nm h k = seq_mp k (pm_sym h) := rfl
theorem pm_andE₁_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : SeqD ns F a P Δ (A ∧ᶠ B)) :
    pm_andE₁ h = seq_mp (seq_of_thm and_proj1) h := rfl
theorem pm_andE₂_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h : SeqD ns F a P Δ (A ∧ᶠ B)) :
    pm_andE₂ h = seq_mp (seq_of_thm and_proj2) h := rfl
theorem pm_split_eq {Δ : HCtx F Γ} {A B : Formula F Γ} (h₁ : SeqD ns F a P Δ A)
    (h₂ : SeqD ns F a P Δ B) :
    pm_split h₁ h₂ = seq_mp (seq_mp (seq_of_thm and_intro) h₁) h₂ := rfl
theorem pm_cases_eq (nm m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F a P Δ (A ∨ᶠ B)) (h₁ : SeqD (nm :: ns) F a P (A :: Δ) C)
    (h₂ : SeqD (m :: ns) F a P (B :: Δ) C) :
    pm_cases nm m hAB h₁ h₂
      = seq_mp (seq_mp (seq_mp (seq_of_thm or_elim_internal) h₁) h₂) hAB := rfl
theorem pm_exI_eq {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F a P Δ (A.subst0 t)) :
    pm_exI t h = seq_mp (seq_of_thm (.exist_ax t A)) h := rfl
theorem pm_bound_eq {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F a P Δ (A.subst0 t)) :
    pm_bound t h = seq_mp (seq_of_thm (.exist_ax t A)) h := rfl
theorem pm_inst_eq (nm : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    {C : Formula F Γ} (t : Term F Γ ρ) (h : SeqD ns F a P Δ (Formula.all ρ A))
    (k : SeqD (nm :: ns) F a P (A.subst0 t :: Δ) C) :
    pm_inst nm t h k = seq_mp k (seq_mp (seq_of_thm (.forall_ax t)) h) := rfl
theorem pm_allE_here_eq {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F a P Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    pm_allE_here h = seq_mp (seq_of_thm forall_ax_vz) h := rfl
theorem pm_allE_here_cut_eq (nm : String) {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)}
    {A C : Formula F (ρ :: Γ)}
    (h : SeqD ns F a P Δ (Formula.weakenBy ρ (Formula.all ρ A)))
    (k : SeqD (nm :: ns) F a P (A :: Δ) C) :
    pm_allE_here_cut nm h k = seq_mp k (seq_mp (seq_of_thm forall_ax_vz) h) := rfl
theorem pm_exfalso_eq {Δ : HCtx F Γ} {A : Formula F Γ} (h : SeqD ns F a P Δ ⊥ᶠ) :
    pm_exfalso (A := A) h = seq_mp (seq_of_thm .exfalso) h := rfl
theorem pm_conj_eq (nm : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hA : SeqD ns F a P Δ A) (hB : SeqD ns F a P Δ B)
    (k : SeqD (nm :: ns) F a P ((A ∧ᶠ B) :: Δ) C) :
    pm_conj nm hA hB k = seq_mp k (seq_mp (seq_mp (seq_of_thm and_intro) hA) hB) := rfl
theorem pm_impcut_eq (nm : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : SeqD ns F a P Δ (A →ᶠ B)) (hA : SeqD ns F a P Δ A)
    (k : SeqD (nm :: ns) F a P (B :: Δ) C) :
    pm_impcut nm h hA k = seq_mp k (seq_mp h hA) := rfl
theorem pm_andcut_eq (nm m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F a P Δ (A ∧ᶠ B)) (k : SeqD (nm :: m :: ns) F a P (A :: B :: Δ) C) :
    pm_andcut nm m hAB k
      = seq_mp (Δ := Δ) (A := B) (B := C)
          (seq_mp (Δ := B :: Δ) (A := A) (B := C) k
            (seq_mp (Δ := B :: Δ) (A := A ∧ᶠ B) (B := A) (seq_of_thm and_proj1)
              (seq_mp (Δ := Δ) (A := A ∧ᶠ B) (B := B →ᶠ A ∧ᶠ B) (seq_of_thm K_comb) hAB)))
          (seq_mp (Δ := Δ) (A := A ∧ᶠ B) (B := B) (seq_of_thm and_proj2) hAB) := rfl
theorem pm_classic_eq (nm m : String) (hlem : a.lem = true) (A : Formula F Γ)
    {Δ : HCtx F Γ} {C : Formula F Γ}
    (h₁ : SeqD (nm :: ns) F a P (A :: Δ) C) (h₂ : SeqD (m :: ns) F a P ((¬ᶠA) :: Δ) C) :
    pm_classic nm m hlem A h₁ h₂
      = seq_mp (seq_mp (seq_mp (seq_of_thm or_elim_internal) h₁) h₂)
          (seq_of_thm (.lem hlem)) := rfl
theorem pm_markov_eq {Δ : HCtx F Γ} {ρ : Ty ι} {A₀ : Formula F (ρ :: Γ)}
    (hm : a.markov = true) (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : SeqD ns F a P Δ (¬ᶠ¬ᶠ(Formula.ex ρ A₀))) :
    pm_markov hm hqf hvf h = seq_mp (seq_of_thm (.markov hm hqf hvf)) h := rfl
theorem pm_refl_eq {Δ : HCtx F Γ} {t : Term F Γ Ty.nat} :
    (pm_refl (ns := ns) (Δ := Δ) (t := t) : SeqD ns F a P Δ _) = seq_of_thm .refl0 := rfl

/-! What does **not** reduce to the primitives, and why:

* `pm_allI h = seq_allI h`: recursion on `Δ`, one `seq_mono forall_imp_pull` per hypothesis,
  and `.mp I_comb (.forall_rule (.mp h (.exportation .and_weak)))` at `Δ = []`. Not a
  composition of the primitives, but Δ-generic — see `wit_seq_allI`.
* `pm_induction base step = seq_induction base step`: recursion on `Δ` that changes the
  formula inducted on. Out of scope (CLAUDE.md Track A item 2).
* `pm_exE = seq_exE` (not used by `mct_p2`): `seq_lift₂ exist_imp_pull (seq_allI …) hex`, so
  it inherits `seq_allI`'s status.
* The `Eq.mpr` nodes `anorm` leaves: `syntactic_soundness_eqmpr` above. -/

theorem pm_allI_eq {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F a P (Δ.map (Formula.weakenBy ρ)) A) : pm_allI h = seq_allI h := rfl
theorem seq_allI_nil_eq {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F a P (([] : HCtx F Γ).map (Formula.weakenBy ρ)) A) :
    seq_allI (Δ := []) h
      = .mp I_comb (.forall_rule (B := (⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ)) (A := A)
          (.mp h (.exportation .and_weak))) := rfl
theorem seq_allI_cons_eq {ρ : Ty ι} {A₀ : Formula F Γ} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    (h : Seq F a P ((A₀ :: Δ).map (Formula.weakenBy ρ)) A) :
    seq_allI (Δ := A₀ :: Δ) h
      = seq_mp (seq_of_thm forall_imp_pull)
          (seq_allI (Δ := Δ) (A := Formula.weakenBy ρ A₀ →ᶠ A) h) := rfl

end PM

-- ============================================================================
-- `seq_allI` is Δ-generic too: `wit_seq_allI`
-- ============================================================================

section AllI
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} (cm : ConstMajorants am) {Γ : Ctx ι}
    (n : ℕ) (e : Ctx.interpret X (Γ.map Ty.hat))

/-- Same statement as `CounterSideProbe.wapp_sForallAx` (that file cannot be imported, see
the header); needed below through `forall_ax_vz`. -/
theorem wapp_sForallAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (Formula.all ρ A)).hat) :
    wapp (termMajorizer cm (sForallAx (si := si) (A := A) t).val n e) w
      = hatCast (wTy_cTy_substF A (Term.subst0_map t)).1.symm (w (termMajorizer cm t n e)) := by
  simp only [wapp, sForallAx, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_castTy]
  rfl

/-! ### Cast plumbing

The quantifier rules transport along `wTy (A↑) = wTy A`, which is a theorem, not `rfl`, so
the casts do not vanish on their own. Each lemma below is provable by `subst` at the `Ty`
level — where the two sides of the type equation are *variables* — and is then restated at
the formula level for the specific proofs the rules produce. The formula-level versions are
applied with `erw`: their implicit `Prod`/arrow type arguments mention `Formula.weakenBy`
while the goal's mention `Formula.renameF Term.Renaming.shift` (both spellings arise from
unification inside `forall_imp_pull`), and only default transparency identifies them. -/

theorem hatCast_arr_app {ρ τ τ' : Ty ι} (hτ : τ = τ') (h : (ρ →ₜ τ) = (ρ →ₜ τ'))
    (g : Ty.interpret X (ρ →ₜ τ).hat) (x : Ty.interpret X ρ.hat) :
    (hatCast h g) x = hatCast hτ (g x) := by subst hτ; rfl
theorem hatCast_prod_fst {ρ ρ' σ σ' : Ty ι} (hρ : ρ = ρ') (hσ : σ = σ')
    (h : (ρ ×ₜ σ) = (ρ' ×ₜ σ')) (p : Ty.interpret X (ρ ×ₜ σ).hat) :
    (hatCast h p).1 = hatCast hρ p.1 := by
  subst hρ; subst hσ; rfl
theorem hatCast_prod_snd {ρ ρ' σ σ' : Ty ι} (hρ : ρ = ρ') (hσ : σ = σ')
    (h : (ρ ×ₜ σ) = (ρ' ×ₜ σ')) (p : Ty.interpret X (ρ ×ₜ σ).hat) :
    (hatCast h p).2 = hatCast hσ p.2 := by
  subst hρ; subst hσ; rfl

theorem hatCast_wk_and_fst {ρ : Ty ι} (A B : Formula F Γ)
    (h : wTy (A ∧ᶠ B) = wTy (Formula.weakenBy ρ (A ∧ᶠ B)))
    (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) :
    (hatCast h p).1 = hatCast (wTy_cTy_renameF A Term.Renaming.shift).1.symm p.1 :=
  hatCast_prod_fst _ (wTy_cTy_renameF B Term.Renaming.shift).1.symm h p
theorem hatCast_wk_and_snd {ρ : Ty ι} (A B : Formula F Γ)
    (h : wTy (A ∧ᶠ B) = wTy (Formula.weakenBy ρ (A ∧ᶠ B)))
    (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) :
    (hatCast h p).2 = hatCast (wTy_cTy_renameF B Term.Renaming.shift).1.symm p.2 :=
  hatCast_prod_snd (wTy_cTy_renameF A Term.Renaming.shift).1.symm _ h p
theorem hatCast_wk_all_app {ρ : Ty ι} (A : Formula F (ρ :: Γ))
    (h : wTy (Formula.all ρ A) = wTy (Formula.weakenBy ρ (Formula.all ρ A)))
    (g : Ty.interpret X (wTy (Formula.all ρ A)).hat) (x : Ty.interpret X ρ.hat) :
    (hatCast h g) x
      = hatCast (wTy_cTy_renameF A (Term.Renaming.ext Term.Renaming.shift)).1.symm (g x) :=
  hatCast_arr_app _ h g x

/-- A cast along an implication whose antecedent is unchanged commutes with `wapp`. This
is the shape `syntactic_soundness_eqmp` produces for `forall_ax_vz`. -/
theorem wapp_hatCast_imp {A B B' : Formula F Γ} (hB : B = B') (h : (A →ᶠ B) = (A →ᶠ B'))
    (P : Ty.interpret X (wTy (A →ᶠ B)).hat) (c : Ty.interpret X (wTy A).hat) :
    wapp (hatCast (congrArg wTy h) P) c = hatCast (congrArg wTy hB) (wapp P c) := by
  subst hB; rfl

variable {P : PremiseSet F} (eqxi : EqXInterp X F si)
    (sp : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)

/-- **`forall_ax_vz`** (what `pspecialize` emits, via `pm_allE_here_cut`): instantiating a
weakened `∀`-hypothesis at the bound variable is application at the majorant of that
variable — `x`, the head of the extended environment — transported back along
`wTy (A.renameF (ext shift)) = wTy A`. The `Eq.mp` inside `forall_ax_vz` goes through
`syntactic_soundness_eqmp`, with `Formula.subst0_weakenUnder` as the formula equation. -/
theorem wapp_forall_ax_vz {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (w : Ty.interpret X (wTy ((Formula.all ρ A).weakenBy ρ)).hat) (x : Ty.interpret X ρ.hat) :
    wapp (termMajorizer cm (syntactic_soundness eqxi sp
        (forall_ax_vz (a := Allowed.extended) (Premises := P) (A := A))).val n (x, e)) w
      = hatCast (wTy_cTy_renameF A (Term.Renaming.ext Term.Renaming.shift)).1 (w x) := by
  simp only [forall_ax_vz]
  rw [syntactic_soundness_eqmp eqxi sp
    (congrArg ((Formula.all ρ A).weakenBy ρ →ᶠ ·) (Formula.subst0_weakenUnder A))]
  simp only [syntactic_soundness, termMajorizer_castTy]
  rw [wapp_hatCast_imp (Formula.subst0_weakenUnder A)
    (congrArg ((Formula.all ρ A).weakenBy ρ →ᶠ ·) (Formula.subst0_weakenUnder A))]
  simp only [wapp_sForallAx, cast_cast]
  rfl

/-- **`forall_imp_pull`**, the kernel theorem `seq_allI` inserts once per hypothesis: on the
witness side it is exactly "apply at `x`, then feed the hypothesis witness". This is the
first use-site of `wall_wapp_sForallRule`. -/
theorem wall_forall_imp_pull {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (f : Ty.interpret X (wTy (Formula.all ρ (Formula.weakenBy ρ B →ᶠ A))).hat)
    (b : Ty.interpret X (wTy B).hat) (x : Ty.interpret X ρ.hat) :
    wall (wapp (wapp (termMajorizer cm (syntactic_soundness eqxi sp
        (forall_imp_pull (a := Allowed.extended) (Premises := P) (B := B) (A := A))).val n e)
          f) b) x
      = wapp (wall f x) (hatCast (wTy_cTy_renameF B Term.Renaming.shift).1.symm b) := by
  simp only [forall_imp_pull, pair_h, syntactic_soundness, wapp_sExportation]
  rw [wall_wapp_sForallRule]
  simp only [syntactic_soundness, wapp_sSyllogism, wapp_sImportation, wapp_sExportation,
    wapp_sAndWeak, wapp_sAndPerm, wapp_sAndContract, and_proj2, mp_form, I_comb]
  erw [hatCast_wk_and_fst, hatCast_wk_and_snd]
  rw [wapp_forall_ax_vz]
  erw [hatCast_wk_all_app]
  simp only [cast_cast, cast_eq]
  rfl

/-- The hypothesis witnesses of `Δ`, transported to the weakened context `Δ↑`. -/
def HWit.weaken (ρ : Ty ι) : {Δ : HCtx F Γ} → HWit X Δ → HWit X (Δ.map (Formula.weakenBy ρ))
  | [],     _        => ()
  | A :: _, (a, as) =>
      (hatCast (wTy_cTy_renameF A Term.Renaming.shift).1.symm a, HWit.weaken ρ as)

/-- **`seq_allI` commutes**: a `∀` introduced under a hypothesis context, applied at `x`,
is the body's majorant at the environment extended by `x`, fed the weakened hypothesis
witnesses. Structural on `Δ`, like `wit_seq_mp`: the `cons` case is `wit_seq_mp` +
`wit_seq_of_thm` + `wall_forall_imp_pull`; the `nil` case is `wall_wapp_sForallRule` on the
raw `.forall_rule` at the bottom of `seq_allI`. -/
theorem wit_seq_allI : ∀ (Δ : HCtx F Γ) {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (h : Seq F Allowed.extended P (Δ.map (Formula.weakenBy ρ)) A) (as : HWit X Δ)
    (x : Ty.interpret X ρ.hat),
    wall (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp (seq_allI h)).val n e) as) x
      = wit (Δ.map (Formula.weakenBy ρ))
          (termMajorizer cm (syntactic_soundness eqxi sp h).val n (x, e)) (HWit.weaken ρ as)
  | [], ρ, A, h, _, x => by
      change wall (termMajorizer cm (syntactic_soundness eqxi sp
        (Derivable.mp I_comb (.forall_rule (B := (⊥ᶠ →ᶠ ⊥ᶠ : Formula F Γ)) (A := A)
          (.mp h (.exportation .and_weak))))).val n e) x
        = termMajorizer cm (syntactic_soundness eqxi sp h).val n (x, e)
      simp only [syntactic_soundness, tm_sMP, wall_wapp_sForallRule, wapp_sExportation,
        wapp_sAndWeak]
  | A₀ :: Δ, ρ, A, h, (a₀, as), x => by
      change wall (wapp (wit Δ (termMajorizer cm (syntactic_soundness eqxi sp
          (seq_mp (Δ := Δ) (seq_of_thm (Δ := Δ) forall_imp_pull)
            (seq_allI (Δ := Δ) (A := Formula.weakenBy ρ A₀ →ᶠ A) h))).val n e) as) a₀) x
        = wapp (wit (Δ.map (Formula.weakenBy ρ))
            (termMajorizer cm (syntactic_soundness eqxi sp h).val n (x, e)) (HWit.weaken ρ as))
            (hatCast (wTy_cTy_renameF A₀ Term.Renaming.shift).1.symm a₀)
      rw [wit_seq_mp cm n e eqxi sp Δ, wit_seq_of_thm cm n e eqxi sp Δ, wall_forall_imp_pull,
        wit_seq_allI Δ]

end AllI

#print axioms wall_sUnivGen
#print axioms wall_wapp_sForallRule
#print axioms capp_sForallRule
#print axioms wapp_sExistRule
#print axioms capp_sExistRule
#print axioms wapp_sQfer
#print axioms capp_sQfer
#print axioms syntactic_soundness_eqmpr
#print axioms wapp_forall_ax_vz
#print axioms wall_forall_imp_pull
#print axioms wit_seq_allI

end CombinatorLemmas
end Metatheorems
