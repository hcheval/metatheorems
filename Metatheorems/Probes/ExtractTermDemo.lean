/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Probes.UPremiseDemo

/-!
# Probe: `extractTerm` — extraction with no model, evaluated **at a space**

`syntactic_soundness eqxi spremise prf : SRealizer si A`, and `SRealizer si A` is
`{ t : Term F Γ (wTy A) // <property mentioning si> }`. The payload's *type* mentions no
`si`; only the property does. `Dialectica/Syntactic.lean`'s `extractTerm` is that recursion
with the model deleted, and `extractTerm_eq` proves the two agree.

**Why it could not be demonstrated before.** Every model in the project — metric,
W-hyperbolic, CAT(0), normed — is built over Mathlib `ℝ`, so `si` is `noncomputable` and any
`#eval` mentioning it is impossible. `UPremiseDemo.uUt` is `noncomputable def` for exactly
that reason. `extractTerm` takes no `si`, so the realizer of a derivation **at a space** is
now an ordinary computable `Term`, and `#eval` on it works.

What is measured here is `UPremiseDemo.uFinal` — the 12-constructor derivation over
`WHyperbolic.Premises` that consumes its premise via `forall_ax`/`exist_ax`. Small by
design; see CLAUDE.md on why `mct_p2`-sized terms cannot be `#eval`ed at all.

NOT imported by `Metatheorems.lean`; reachable from `Probes.lean`.
-/

namespace Metatheorems
namespace ExtractTermDemo

open Formula

/-- Structural node count of a term. `BoundProbe.termSize` predates the `ι`/`κ` split and is
stated at `F : ι → Ty ι`; this is the same function at `F : κ → Ty ι`, which is what a
signature with function constants (W-hyperbolic has `W`) needs. -/
def tSize {ι κ : Type} {F : κ → Ty ι} :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → Nat
  | _, _, .var _      => 1
  | _, _, .app f a    => 1 + tSize f + tSize a
  | _, _, .lam b      => 1 + tSize b
  | _, _, .zero       => 1
  | _, _, .succ       => 1
  | _, _, .prec _     => 1
  | _, _, .func _     => 1
  | _, _, .zeroX _    => 1
  | _, _, .dist _     => 1
  | _, _, .unitI      => 1
  | _, _, .mkPair a b => 1 + tSize a + tSize b
  | _, _, .fst p      => 1 + tSize p
  | _, _, .snd p      => 1 + tSize p

-- ============================================================================
-- The premise realizer, syntactically
-- ============================================================================

/-- **The W-hyperbolic premise realizers as bare terms.** `WHyperbolicModel.spremise` is
`srealizer_of_pu` applied to `axiomsHold`, and `srealizer_of_pu_val` says its payload is
`defaultWTerm B` — the four axioms are purely universal, so the realizing term carries no
information. That value needs no model, hence no `noncomputable`. -/
def wSp : ∀ (Γ' : Ctx MetricSpace.ι) (B : Formula WHyperbolic.F Γ'),
    WHyperbolic.Premises ⟨Γ', B⟩ → Term WHyperbolic.F Γ' (wTy B) :=
  fun _ B _ => defaultWTerm B

/-- …and it is *the same* term the model's premise realizer carries, in every model. -/
theorem wSp_eq (M : WHyperbolicModel) :
    (fun Γ' B hp => (M.spremise Γ' B hp).val) = wSp := by
  funext Γ' B hp
  exact srealizer_of_pu_val B _ _ _

-- ============================================================================
-- The realizer of `uFinal`, computed
-- ============================================================================

/-- **The extracted realizing term of `UPremiseDemo.uFinal` — no model, no `si`, no
`noncomputable`.** Compare `UPremiseDemo.uUt`, which needs `M.eqXInterp` and `M.spremise`
and is therefore `noncomputable def`. -/
def uRealizer := extractTerm wSp UPremiseDemo.uFinal

/-- It is the realizer `syntactic_soundness` produces, at **every** W-hyperbolic model. -/
theorem uRealizer_eq (M : WHyperbolicModel) :
    (syntactic_soundness M.eqXInterp M.spremise UPremiseDemo.uFinal).val = uRealizer := by
  rw [extractTerm_eq, wSp_eq M]
  rfl

-- **The demonstration.** A number, out of a derivation at a space, by evaluation.
#eval tSize uRealizer          -- 533

/-- Kernel-checked, not merely `#eval`ed. -/
theorem uRealizer_size : tSize uRealizer = 533 := by rfl

/-- Non-degeneracy control: the reduction really happens, and `532` is refuted. -/
theorem uRealizer_size_ne : tSize uRealizer ≠ 532 := by decide

/-- The premise-instantiation subderivation, for contrast: strictly smaller. -/
def uInnerRealizer := extractTerm wSp UPremiseDemo.uInner

#eval tSize uInnerRealizer     -- 186

theorem uInnerRealizer_size : tSize uInnerRealizer = 186 := by rfl

-- ============================================================================
-- Does Markov's principle obstruct evaluation? No.
-- ============================================================================

/-! `Classical.choice` reaches the syntactic route from exactly two places, `sMarkov` and
`matrixTerm_correct`. The second is a `Prop`-level correctness theorem and cannot obstruct
extraction. The first was the open question: **is `sMarkov`'s *term* half classical?**

It is not. `sMarkov`'s payload is `wtMarkov` — `mkPair`s, `lam`s and `Term.defaultOf`, with
no `Classical` anywhere; the choice it uses (`Classical.not_not`, `Classical.em`) lives
entirely in the `Prop` component that `extractTerm` discards. So `extractTerm` is computable
on Markov-using derivations too, and `#eval` — not `#reduce` — is the route for future work.

The three checks below are the evidence: `extractTerm` and `wtMarkov` depend on **no
axioms**, and a derivation containing a literal `Derivable.markov` evaluates. -/

/-- A quantifier-free ∨-free matrix, for a Markov instance. -/
def mkA₀ : Formula WHyperbolic.F [Ty.nat] :=
  Formula.eq0 (Term.var Var.vz) (Term.var Var.vz)

/-- A derivation containing a literal `Derivable.markov`. -/
def mkDeriv :
    @Derivable MetricSpace.ι WHyperbolic.κ WHyperbolic.F Allowed.extended
      WHyperbolic.Premises [] (¬ᶠ(¬ᶠ(Formula.ex Ty.nat mkA₀)) →ᶠ Formula.ex Ty.nat mkA₀) :=
  Derivable.markov rfl (A₀ := mkA₀) rfl rfl

def mkRealizer := extractTerm wSp mkDeriv

#eval tSize mkRealizer         -- 27

theorem mkRealizer_size : tSize mkRealizer = 27 := by rfl

#print axioms extractTerm
#print axioms wtMarkov
#print axioms mkRealizer_size

#print axioms uRealizer_eq
#print axioms uRealizer_size

end ExtractTermDemo
end Metatheorems
