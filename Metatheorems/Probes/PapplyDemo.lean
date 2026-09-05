/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.RealNumbers.Cauchyfy
import Metatheorems.ProofMode.Arith

/-!
# Probe PapplyDemo: the unified `papply` (LADDER rung 8)

`papply` now takes either a hypothesis name or a kernel theorem, elaborates the theorem
**once**, unifies its *conclusion* with the goal in the live metavariable context, and builds
the `pm_mp` chain as an expression from the elaborated term. The four things this file shows,
each measured against the tactic as it was at `10104d9` (the numbers and messages in the
comments are from that run, not predictions):

1. **Implicit arguments are inferred, and the rung-6a spelling works.** `LADDER.md` records
   that `papplym (succ_congr_imp (s := pdᵗ x₁) (t := x₀))` failed with
   `x₀: the context has 0 named variable(s)`. Under the old tactic that failure was an
   artifact of the *second* elaboration: the antecedent count was probed on a pinned
   elaboration and then the raw syntax was handed to `refine pm_mp (pm_have $eStx) ?_`, where
   the `xₖ` tokens resolved against the outer context. There is no second elaboration now,
   so both `papply succ_congr_imp` and the named-argument spelling go through.
2. **A goal containing `Term.cauchyfy` is matched at reducible transparency** — the trace
   (`-D pm.papply.trace=true`) reports `matched at reducible` for every application in this
   file and in every control file measured, so the default-transparency fallback that walks
   into `cauchyfy`'s recursor never runs on a successful match.
3. **A theorem whose conclusion does not match** is refused with the theorem's conclusion
   and the goal printed.
4. **An argument that fails to elaborate** gives the elaborator's own error. `papplym`'s old
   error path read `etyArgs[6]!` — in bounds only since the `ι`/`κ` split made `Derivable`
   a 7-argument application — and that indexing is gone; the message is built from the
   inferred type's last argument.
-/

namespace Metatheorems
namespace Probes

open Formula ProofMode

variable {ι κ : Type} {F : κ → Ty ι}
  {al : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B : Formula F Γ}

/-! ## 1. Implicit arguments -/

/-- `succ_congr_imp {s t}` with nothing supplied: `s` and `t` are read off the goal
`S (pd x₁) =₀ S x₀`. Trace: `theorem, elaborated open, 1 antecedent(s), matched at
reducible`. -/
def succ_congr_open :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        ((pdᵗ x₁ =₀ x₀) →ᶠ (S (pdᵗ x₁) =₀ S x₀)))) := by
  pmode; pforall; pforall; pintro h
  papply succ_congr_imp
  pexact h

/-- The rung-6a spelling, verbatim from `LADDER.md`'s record of the failure. It elaborates
now, for the reason given in the header. -/
def succ_congr_named :
    Derivable F al Premises (Γ := Γ)
      (Formula.all Ty.nat (Formula.all Ty.nat
        ((pdᵗ x₁ =₀ x₀) →ᶠ (S (pdᵗ x₁) =₀ S x₀)))) := by
  pmode; pforall; pforall; pintro h
  papplym (succ_congr_imp (s := pdᵗ x₁) (t := x₀))
  pexact h

/-- Four explicit term arguments, all read off the goal. At `Cauchyfy.lean`'s `add_R_check`
the same application used to spell out eleven lines of terms; see the retrofit there. -/
def add_both_placeholders (a b c d : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (lt_Q a c ∧ᶠ lt_Q b d →ᶠ
        lt_Q (Term.app2 Term.add_Q a b) (Term.app2 Term.add_Q c d)) := by
  pmode; pintro h
  papply (lt_Q_add_both _ _ _ _)
  pexact h

/-- A placeholder the conclusion does **not** determine — the midpoint of a transitivity —
becomes a trailing goal, as with Lean's `apply`, and is fixed by the `pexact` that proves
the antecedent mentioning it. -/
def trans_midpoint (a b c : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ) (le_Q a b ∧ᶠ lt_Q b c →ᶠ lt_Q a c) := by
  pmode; pintro h
  papply (le_lt_Q_trans _ _ _)
  pexact h

/-! ## 2. A goal containing `Term.cauchyfy` -/

/-- Two occurrences of `Term.cauchyfy` in the goal; the two open slots of `le_lt_Q_trans`
are read off it at reducible transparency. Trace: `matched at reducible`. -/
def cauchyfy_goal (f g : Term F Γ (realTy ι)) (n c : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (le_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f (.app .succ n))
          (Term.app2 Term.cauchyfy g (.app .succ n)))) c
        ∧ᶠ lt_Q c (.app Term.pow2neg_Q n) →ᶠ
       lt_Q (.app Term.abs_Q (Term.app2 Term.sub_Q
          (Term.app2 Term.cauchyfy f (.app .succ n))
          (Term.app2 Term.cauchyfy g (.app .succ n)))) (.app Term.pow2neg_Q n)) := by
  pmode; pintro h
  papply (le_lt_Q_trans _ c _)
  pexact h

/-- `k = 0`: a closed equation about `cauchyfy` of a sum, all three arguments inferred. -/
def cauchyfy_add_R_placeholders (f g : Term F Γ (realTy ι)) (s : Term F Γ Ty.nat) :
    Derivable F al Premises (Γ := Γ)
      (Formula.eq0 (Term.app2 Term.cauchyfy (Term.app2 Term.add_R f g) s)
        (Term.app2 Term.add_Q
          (Term.app2 Term.cauchyfy f (.app .succ s))
          (Term.app2 Term.cauchyfy g (.app .succ s)))) := by
  pmode
  papply (cauchyfy_add_R _ _ _)

/-! ## 3. Negative control

```
example : SeqD [] F al Premises [] (A →ᶠ B →ᶠ (A ∨ᶠ B)) := by
  pintro ha hb
  papply and_intro
```
fails with

```
papply: this theorem does not conclude the goal.
It proves
  ?m.54 →ᶠ ?m.55 →ᶠ ?m.54 ∧ᶠ ?m.55
and the goal is
  A ∨ᶠ B
```

The metavariables are the implicit `A B` of `and_intro`, which nothing determined.
-/

/-! ## 4. An argument that fails to elaborate

```
example : SeqD [] F al Premises [] (A →ᶠ B →ᶠ (A ∧ᶠ B)) := by
  pintro ha hb
  papply (and_intro (C := A))
```
gives the elaborator's own message,

```
Invalid argument name `C` for function `and_intro`
Hint: Perhaps you meant one of the following parameter names: …
```

and `papply (nonexistent_lemma A)` gives `Unknown identifier `nonexistent_lemma``. Neither
reaches the tactic's own error path. (At `10104d9`, after the `ι`/`κ` split, these two
already produced the same messages: the out-of-bounds read was on the *6-argument*
`Derivable` and had become in-bounds by arity. What changed is that no index is read
at all.)
-/

/-! ## The hypothesis path, unchanged in behaviour -/

example : SeqD [] F al Premises [] ((A →ᶠ B →ᶠ A ∧ᶠ B) →ᶠ A →ᶠ B →ᶠ A ∧ᶠ B) := by
  pintro h ha hb
  papply h
  · pexact ha
  · pexact hb

#print axioms succ_congr_open
#print axioms succ_congr_named
#print axioms add_both_placeholders
#print axioms trans_midpoint
#print axioms cauchyfy_goal
#print axioms cauchyfy_add_R_placeholders

end Probes
end Metatheorems
