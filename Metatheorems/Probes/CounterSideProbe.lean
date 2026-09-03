/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.SeqMpBoundProbe

/-!
# Probe: the counter side of the proof-mode primitives

`SeqMpBoundProbe.lean` got the **witness** side through the proof-mode layer with three
Δ-generic commutation lemmas. `extractUTerm` reads `U` off the `.snd` — the **counter**
component — which is where `sSyllogism` (3× and 2×) and `sExportation`/`sImportation` (3×)
duplicate their arguments. This file asks whether the same trick survives there.

Two stages, per that file's closing note: **A**, Δ-generic counter lemmas; **B**, instantiate
to concrete numerals at `ι = Empty` and read an actual number out. B is the one that matters —
concrete numerals are what a real bound extraction wants, and a right-hand side mentioning a
sub-majorant three times is three *numbers* being combined, not a growing expression.

## Stage A — DONE, and the Δ-generic worry does not materialise

Seven counter lemmas (`capp_sSyllogism`, `capp_sExportation`, `capp_wapp_sExportation`,
`capp_sImportation`, `capp_sAndWeak`, `capp_sAndPerm`, `capp_sAndContract`), all Δ-generic,
most closing by `simp only […]; rfl`. Their right-hand sides mention sub-majorants more than
once but are *fixed* expressions, so nothing grows with context depth.

Two by-products that are reusable outside this probe and should be promoted if it is kept:
`termMajorizer_subst_gen` and `termMajorizer_subst0` — the substitution analogue of
`termMajorizer_rename_gen`, mirroring `Term.interpret_subst0`.

## The measurement, and the right way to take it

Goal size along the Stage B reduction chain (`numObjs` / `approxDepth`, 2026-09-04):

| after | numObjs | depth |
|---|---|---|
| the big `simp only` unfold | 1163 | 52 |
| `csimp` (the seven Stage A lemmas) | 2143 | 126 |
| `pack`, `cfst` | 2091 | 126 |
| `matrixTerm` | 4277 | 128 |
| `termMajorizer_subst0`, `Term.rename` | 4204 | 128 |
| `Term.app2`/`app3` | 4315 | 129 |
| `tm_natCase` | 5384 | 223 |
| everything after | 5384 | 223 (stalled) |

**The counter side does not blow up: ×4.6 across the whole chain.** Meanwhile
`goal_tree_size` on the Stage A `S_comb` goal reported **954,412,881** (and 228,417,143 on an
earlier one). Sharing ratio ≈10⁵.

**So measure with `numObjs`, never `sizeWithoutSharing`.** The latter materialises the sharing
and is what eats the machine — the `goal_tree_size` call in the Stage A example is commented
out for that reason, with its measured value kept. Same family as hard rule 3.

## Where Stage B stalls, and the fix

Line ~328, `try simp only [Term.monus, Term.pd, termMajorizer, Ctx.lookupHat]`:
`(deterministic) timeout at whnf`, 200000 heartbeats.

**Two wrong diagnoses, both recorded so they are not retried.** It is *not* a `Ctx.lookupHat`
residue, and `rfl` is the worst available move — `rfl` forces exactly the `whnf` that timed
out.

It is the **delta-expansion pathology one layer up**: that simp set unfolds the closed
arithmetic constants `Term.monus`/`Term.pd` together with an unrestricted `termMajorizer`, so
the tactic must expose constructors underneath them. `CLAUDE.md`'s "Build cost" section is the
same shape for `Term.subst`. The constants are reachable because `Ah` is an `eq0` formula, so
`matrixTerm` is the equality-decision term (`abs_diff`, hence `monus`/`pd`), and
`capp_sAndContract`'s `cm.precM` is *driven by the majorant of that matrix term*.

**The driver's exact value is not needed.** `Majorizability.lean`:

    recMaj ρ y z 0       = y
    recMaj ρ y z (k + 1) = maxT ρ (z (recMaj ρ y z k) k) (recMaj ρ y z k)

`capp_sAndContract` passes the *constant* step function `fun _ _ => y.1`, so by induction

    recMaj ρ y.2 (fun _ _ => y.1) 0       = y.2
    recMaj ρ y.2 (fun _ _ => y.1) (k + 1) = maxT ρ y.1 y.2     -- for every k

i.e. the recursion collapses and the driver matters **only through zero-vs-successor**. So the
route is a constant-driver collapse lemma plus a zero/nonzero fact about the matrix term's
majorant — not an evaluation of the matrix term, and not any unfolding of `monus`/`pd`.

(Note the earlier conjecture that `precM` *fully* absorbs its driver is false: `recMaj`
recurses on it. It collapses only because the step function here is constant.)

Not committed to the library; nothing imports this file.
-/

namespace Metatheorems
namespace CounterSideProbe

open ProofMode BoundProbe BoundLemmasP2 SeqMpBoundProbe Formula

section Ctr
variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} (cm : ConstMajorants am) {Γ : Ctx ι}

/-- Counter application: the second component of a majorant at an implication's witness
type, applied to a witness majorant of the antecedent and a counter majorant of the
consequent. This is what `extractUTerm` reads. -/
def capp {A B : Formula F Γ} (r : Ty.interpret X (wTy (A →ᶠ B)).hat)
    (a : Ty.interpret X (wTy A).hat) (y : Ty.interpret X (cTy B).hat) :
    Ty.interpret X (cTy A).hat := r.2 a y

/-- The first component of a counter majorant at `cTy (∀x A) = ρ ×ₜ cTy A`: the point at
which the premise is tested. -/
def cfst {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (y : Ty.interpret X (cTy (Formula.all ρ A)).hat) : Ty.interpret X ρ.hat := y.1

variable (n : ℕ) (e : Ctx.interpret X (Γ.map Ty.hat))

/-- The majorant of `Term.defaultOf ρ`, as a semantic value: it does not depend on the
environment, and only `cm.zeroM n` at `nat`. -/
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

@[simp] theorem termMajorizer_defaultCTerm (A : Formula F Γ) :
    termMajorizer cm (defaultCTerm A) n e = defM cm n (cTy A) :=
  termMajorizer_defaultOf cm n _ _

@[simp] theorem termMajorizer_defaultWTerm (A : Formula F Γ) :
    termMajorizer cm (defaultWTerm A) n e = defM cm n (wTy A) :=
  termMajorizer_defaultOf cm n _ _

/-- The majorant of the object-level conditional: the recursor majorant on the branches. -/
theorem tm_natCase {ρ : Ty ι} (c : Term F Γ Ty.nat) (a b : Term F Γ ρ) :
    termMajorizer cm (Term.natCase c a b) n e
      = cm.precM ρ n (termMajorizer cm a n e) (fun _ _ => termMajorizer cm b n e)
          (termMajorizer cm c n e) := by
  simp only [Term.natCase, Term.app3, termMajorizer, termMajorizer_weaken]

theorem capp_sAndWeak {A B : Formula F Γ} (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat)
    (y : Ty.interpret X (cTy A).hat) :
    capp (termMajorizer cm (sAndWeak (si := si) (A := A) (B := B)).val n e) p y
      = (y, defM cm n (cTy B)) := by
  simp only [capp, sAndWeak, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_defaultCTerm]
  rfl

theorem capp_sAndPerm {A B : Formula F Γ} (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat)
    (y : Ty.interpret X (cTy (B ∧ᶠ A)).hat) :
    capp (termMajorizer cm (sAndPerm (si := si) (A := A) (B := B)).val n e) p y
      = (y.2, y.1) := rfl

theorem capp_sSyllogism {A B C : Formula F Γ}
    (hAB : SRealizer si (A →ᶠ B)) (hBC : SRealizer si (B →ᶠ C))
    (a : Ty.interpret X (wTy A).hat) (y : Ty.interpret X (cTy C).hat) :
    capp (termMajorizer cm (sSyllogism hAB hBC).val n e) a y
      = capp (termMajorizer cm hAB.val n e) a
          (capp (termMajorizer cm hBC.val n e) (wapp (termMajorizer cm hAB.val n e) a) y) := by
  simp only [capp, wapp, sSyllogism, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem capp_sExportation {A B C : Formula F Γ} (h : SRealizer si (A ∧ᶠ B →ᶠ C))
    (a : Ty.interpret X (wTy A).hat) (y : Ty.interpret X (cTy (B →ᶠ C)).hat) :
    capp (termMajorizer cm (sExportation h).val n e) a y
      = (capp (termMajorizer cm h.val n e) (a, y.1) y.2).1 := by
  simp only [capp, sExportation, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem capp_wapp_sExportation {A B C : Formula F Γ} (h : SRealizer si (A ∧ᶠ B →ᶠ C))
    (a : Ty.interpret X (wTy A).hat) (b : Ty.interpret X (wTy B).hat)
    (y : Ty.interpret X (cTy C).hat) :
    capp (wapp (termMajorizer cm (sExportation h).val n e) a) b y
      = (capp (termMajorizer cm h.val n e) (a, b) y).2 := by
  simp only [capp, wapp, sExportation, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

theorem capp_sImportation {A B C : Formula F Γ} (h : SRealizer si (A →ᶠ B →ᶠ C))
    (p : Ty.interpret X (wTy (A ∧ᶠ B)).hat) (y : Ty.interpret X (cTy C).hat) :
    capp (termMajorizer cm (sImportation h).val n e) p y
      = (capp (termMajorizer cm h.val n e) p.1 (p.2, y),
         capp (wapp (termMajorizer cm h.val n e) p.1) p.2 y) := by
  simp only [capp, wapp, sImportation, SRealizer.imp, termMajorizer, termMajorizer_weaken]
  rfl

/-- Contraction's counter: the recursor majorant over the two counters, driven by the
majorant of the matrix term. Stated with `cm.precM` so it is generic; at
`bezemConstMajorantsEmpty` that is `recMaj`. -/
theorem capp_sAndContract {A : Formula F Γ} (a : Ty.interpret X (wTy A).hat)
    (y : Ty.interpret X (cTy (A ∧ᶠ A)).hat) :
    capp (termMajorizer cm (sAndContract (si := si) (A := A)).val n e) a y
      = cm.precM (cTy A) n y.2 (fun _ _ => y.1)
          (termMajorizer cm (matrixTerm (fun v => .vs (.vs v)) A (.var (.vs .vz))
            (.fst (.var .vz))) n (y, a, e)) := by
  simp only [capp, sAndContract, SRealizer.imp, termMajorizer, tm_natCase]
  rfl

theorem capp_sExistAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (A.subst0 t)).hat) (y : Ty.interpret X (cTy (Formula.ex ρ A)).hat) :
    capp (termMajorizer cm (sExistAx (si := si) (A := A) t).val n e) w y
      = cast (congrArg (fun ρ => Ty.interpret X ρ.hat)
          (wTy_cTy_substF A (Term.subst0_map t)).2.symm) y := by
  simp only [capp, sExistAx, SRealizer.imp, termMajorizer, termMajorizer_castTy]
  rfl

theorem wapp_sExistAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (A.subst0 t)).hat) :
    wapp (termMajorizer cm (sExistAx (si := si) (A := A) t).val n e) w
      = (termMajorizer cm t n e,
         cast (congrArg (fun ρ => Ty.interpret X ρ.hat)
          (wTy_cTy_substF A (Term.subst0_map t)).1) w) := by
  simp only [wapp, sExistAx, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_castTy]
  rfl

theorem wapp_sForallAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (Formula.all ρ A)).hat) :
    wapp (termMajorizer cm (sForallAx (si := si) (A := A) t).val n e) w
      = cast (congrArg (fun ρ => Ty.interpret X ρ.hat)
          (wTy_cTy_substF A (Term.subst0_map t)).1.symm) (w (termMajorizer cm t n e)) := by
  simp only [wapp, sForallAx, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_castTy]
  rfl

theorem tm_sRefl0 {t : Term F Γ Ty.nat} :
    termMajorizer cm (sRefl0 (si := si) (t := t)).val n e = () := rfl

/-- `termMajorizer` commutes with substitution, mirroring `termMajorizer_rename_gen`. -/
theorem termMajorizer_subst_gen :
    ∀ {Γ Δ : Ctx ι} {ρ : Ty ι} (σ : Term.Subst F Γ Δ) (t : Term F Γ ρ) (n : ℕ)
    (eΔ : Ctx.interpret X (Δ.map Ty.hat)) (eΓ : Ctx.interpret X (Γ.map Ty.hat)),
    (∀ {τ} (v : Var Γ τ), termMajorizer cm (σ v) n eΔ = Ctx.lookupHat v eΓ) →
    termMajorizer cm (t.subst σ) n eΔ = termMajorizer cm t n eΓ := by
  intro Γ Δ ρ σ t
  induction t generalizing Δ with
  | var v => intro n eΔ eΓ h; exact h v
  | app f a ihf iha =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ihf σ n eΔ eΓ h, iha σ n eΔ eΓ h]
  | lam body ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer]
    funext x
    exact ih (Term.Subst.ext σ) n (x, eΔ) (x, eΓ) (fun v => by
      cases v with
      | vz => rfl
      | vs w =>
        show termMajorizer cm (Term.weaken (σ w)) n (x, eΔ) = _
        rw [termMajorizer_weaken]; exact h w)
  | zero | succ | prec | func | zeroX | dist | unitI => intros; rfl
  | mkPair a b iha ihb =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, iha σ n eΔ eΓ h, ihb σ n eΔ eΓ h]
  | fst p ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ih σ n eΔ eΓ h]
  | snd p ih =>
    intro n eΔ eΓ h
    simp only [Term.subst, termMajorizer, ih σ n eΔ eΓ h]

/-- The `Term.interpret_subst0` analogue: substitution is environment extension. -/
@[simp] theorem termMajorizer_subst0 {ρ σ : Ty ι} (t : Term F (σ :: Γ) ρ) (s : Term F Γ σ) :
    termMajorizer cm (t.subst0 s) n e = termMajorizer cm t n (termMajorizer cm s n e, e) :=
  termMajorizer_subst_gen cm (Term.subst0_map s) t n e (termMajorizer cm s n e, e)
    (fun v => by cases v with | vz => rfl | vs w => rfl)

theorem capp_sForallAx {ρ : Ty ι} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (w : Ty.interpret X (wTy (Formula.all ρ A)).hat) (y : Ty.interpret X (cTy (A.subst0 t)).hat) :
    capp (termMajorizer cm (sForallAx (si := si) (A := A) t).val n e) w y
      = (termMajorizer cm t n e,
         cast (congrArg (fun ρ => Ty.interpret X ρ.hat)
          (wTy_cTy_substF A (Term.subst0_map t)).2) y) := by
  simp only [capp, sForallAx, SRealizer.imp, termMajorizer, termMajorizer_weaken,
    termMajorizer_castTy]
  rfl

variable {P : PremiseSet F} (eqxi : EqXInterp X F si)
    (sp : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), P ⟨Γ', B⟩ → SRealizer si B)

/-- The counter-side simp set: the seven projection lemmas above plus the witness-side ones
they call. -/
syntax "csimp" : tactic
macro_rules
  | `(tactic| csimp) => `(tactic| simp only [wapp_sExportation,
      wapp_sSyllogism, wapp_sImportation, wapp_sAndWeak, wapp_sAndPerm, wapp_sAndContract,
      capp_wapp_sExportation, capp_sExportation, capp_sSyllogism, capp_sImportation,
      capp_sAndWeak, capp_sAndPerm, capp_sAndContract])

-- Measure the goal: tree size, DAG size (heap objects), depth. Meta-level only — nothing
-- object-level is evaluated.
open Lean Elab Tactic in
elab "goal_size" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let objs ← g.numObjs
  logInfo m!"goal: numObjs = {objs}, approxDepth = {g.approxDepth}"

-- The tree size is `O(tree)` to compute, so it is a separate tactic: only use it where the
-- DAG measurement says it will finish.
open Lean Elab Tactic in
elab "goal_tree_size" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  logInfo m!"goal: sizeWithoutSharing = {g.sizeWithoutSharing}"

/-- **Stage A measurement: the counter side of ONE `S_comb`.** The `sorry` is deliberate —
this `example` exists to print the size of the normal form, not to state it. Compare
`wapp_S`, whose right-hand side `wapp (wapp f a) (wapp g a)` is 7 nodes. -/
example {A B C : Formula F Γ}
    (f : Ty.interpret X (wTy (A →ᶠ B →ᶠ C)).hat) (g : Ty.interpret X (wTy (A →ᶠ B)).hat)
    (a : Ty.interpret X (wTy A).hat) (y : Ty.interpret X (cTy C).hat) :
    capp (wapp (wapp (termMajorizer cm (syntactic_soundness eqxi sp
      (S_comb (a := Allowed.extended) (Premises := P) (A := A) (B := B) (C := C))).val n e)
        f) g) a y
      = sorry := by
  simp only [S_comb, eval_h, pair_h, syntactic_soundness]
  csimp
  goal_size
  -- goal_tree_size   -- reported 954,412,881; O(tree) and costs ~5 GB, so left off by default
  sorry

end Ctr

-- ============================================================================
-- Stage B: a numeral out of the counter component, at `ι = Empty`
-- ============================================================================

/-- The hypothesis with a non-trivial counter type: `∀u (u =₀ u)`, so `cTy Ah = nat ×ₜ unit`
and `wTy Ah = nat →ₜ unit`. This is the shape of the premise `∀u B₀` in `extractUTerm`. -/
abbrev Ah : Formula FEmpty ([] : Ctx Empty) :=
  Formula.all Ty.nat (Formula.eq0 (Term.var Var.vz) (Term.var Var.vz))

/-- The instance at which `Ah` is used: `S (S 0)`, so the expected counter is `2`. -/
abbrev t2 : Term FEmpty ([] : Ctx Empty) Ty.nat :=
  Term.app Term.succ (Term.app Term.succ Term.zero)

def hT2B : D [] (Formula.eq0 t2 t2 →ᶠ B) := .mp hB (.exportation .and_weak)

/-- `Ah →ᶠ B`, using `Ah` at `t2`: the counter for `Ah` is `(t2, ())`. -/
def hAhB : D [] (Ah →ᶠ B) := .syllogism (.forall_ax t2) hT2B

/-- `k` trivial hypotheses on top of `Ah`: `pack (ctxA k) B = Ah →ᶠ T →ᶠ … →ᶠ T →ᶠ B`, so `Ah`
is the outermost antecedent and its counter is the `.2` of the whole majorant. -/
def ctxA : Nat → HCtx FEmpty ([] : Ctx Empty)
  | 0     => [Ah]
  | k + 1 => T :: ctxA k

/-- `Ah` looked up at depth `k`. -/
def vA : (k : Nat) → HVar (ctxA k) Ah
  | 0     => .hz
  | k + 1 => .hs (vA k)

/-- Modus ponens in context: the theorem `Ah →ᶠ B` against the hypothesis `Ah` at depth `k`.
The counter for `Ah` flows through `k` `S_comb`s and `k` `K_comb`s. -/
def derivA (k : Nat) : Seq FEmpty Allowed.extended PremE (ctxA k) B :=
  seq_mp (seq_of_thm hAhB) (seq_id (vA k))

def realA (k : Nat) : SRealizer siE (pack (ctxA k) B) :=
  syntactic_soundness eqxiE spremiseE (derivA k)

/-- The counter for `Ah` read off the majorant, `extractUTerm`-style: `.2`, applied to a
witness for `Ah` and a counter for the rest, then `.1`. Stated at `k = 0` here to fix the
shape; `pack (ctxA k) B` only reduces to `Ah →ᶠ …` at a literal `k`. -/
noncomputable def uA0 : Ty.interpret XEmpty Ty.nat :=
  cfst (capp (closedMajorizer cmE (realA 0).val)
    (Ty.interpret_default siE _) (Ty.interpret_default siE _))

-- exploration k = 0, simp route
example : (2 : ℕ) = uA0 := by
  simp only [uA0, closedMajorizer, realA, derivA, ctxA, vA, seq_mp, seq_of_thm, seq_id,
    seq_mono, syntactic_soundness, hAhB, hT2B, hB, hT, I_comb, K_comb, S_comb, eval_h, pair_h,
    tm_sMP]
  goal_size
  csimp
  goal_size
  simp only [pack, cfst]
  goal_size
  simp only [matrixTerm]
  goal_size
  simp only [termMajorizer_subst0, Term.rename]
  goal_size
  simp only [Term.app2, Term.app3]
  goal_size
  simp only [tm_natCase]
  goal_size
  try simp only [termMajorizer_weaken]
  goal_size
  try simp only [termMajorizer.eq_1]
  goal_size
  try simp only [termMajorizer.eq_12, termMajorizer.eq_13, termMajorizer.eq_10]
  goal_size
  try simp only [termMajorizer.eq_3]
  goal_size
  try simp only [termMajorizer.eq_2]
  goal_size
  try simp only [Ctx.lookupHat]
  goal_size
  -- ⚠ STALL. This line is a `(deterministic) timeout at whnf` (200000 heartbeats), and it is
  -- the reason the chain sits at 5384/223 from here on. Unfolding the closed constants
  -- `Term.monus`/`Term.pd` under an unrestricted `termMajorizer` is the delta-expansion
  -- pathology; `rfl` here is strictly worse. Do not raise `maxHeartbeats`.
  -- The fix does not go through this line at all — see "Where Stage B stalls" in the header:
  -- `capp_sAndContract`'s `precM` has a CONSTANT step function, so `recMaj` collapses to
  -- `maxT ρ y.1 y.2` for every nonzero driver, and only zero-vs-successor of the matrix
  -- term's majorant is needed.
  try simp only [Term.monus, Term.pd, termMajorizer, Ctx.lookupHat]
  goal_size
  simp only [defM, Ty.interpret_default]
  goal_size
  simp only [cmE, bezemConstMajorantsEmpty]
  goal_size
  sorry

end CounterSideProbe
end Metatheorems
