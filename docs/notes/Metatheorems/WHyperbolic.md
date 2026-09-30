# WHyperbolic.lean

## module header

### The `[0,1]` parameter

`λ` ranges over **all** of type `1 = ℕ → ℕ`. The axioms are stated at `clamp01 λ`
(`RealNumbers/Interval.lean`), the object-level retraction onto `[0,1]`: `∀λ ∈ [0,1] A(λ)` is
literally `∀λ¹ A(clamp01 λ)`, so no quantifier ranges over a subset of a type. This is
Kohlenbach's device for keeping the metatheorem applicable: every `f : ℕ → ℕ` codes an
element of `[0,1]`, so there is no side condition to discharge, and majorization at that type
is uniform in `λ`.

### The premise set

**The project's first non-empty `Premises`.** All four axioms are purely universal
(`le_R_pu`, `eq_R` and base-type `eqAtType` are all `∀n` over a QF body) and ∨-free, so a
premise realizer is `srealizer_of_pu` applied to the axiom's *truth in the model* —
`WHyperbolicModel.axiomsHold`, proved from the model's `W1`–`W4` through the `codeReal`
homomorphism lemmas of `CodeRealOps.lean`.

### The model

`WHyperbolicModel extends MetricModel` with `W : carrier → carrier → ℝ → carrier` and the four
axioms as Lean-level facts on Mathlib `ℝ`, for `λ, μ ∈ [0,1]`. The constant `W` is interpreted
as `λx y f. W(x, y, clampReal (codeReal f))` — Kohlenbach's `W(x,y,r_λ̃)`: the code `f` is read
as the real it denotes and clamped into `[0,1]` *in the model too*. That is what makes the
majorant of `W` independent of its real argument (`W_maj_at`).

## `WHyperbolic.Premises`

The project's first non-empty premise set — `MetricSpace.Premises` is `fun _ => False`.

## `WHyperbolic.WMajorant`

That independence is the uniformity the `[0,1]`-retraction buys: bounds extracted through this
majorant carry no dependence on `λ`, which is the characteristic feature of proof mining in
hyperbolic spaces. Compare `MetricModel.zeroX_maj`, whose majorant is a space-dependent
parameter `n₀` — here there is not even a parameter.

## the examples (section doc before the uniformity examples)

Bounds *are* mined from derivations at this model elsewhere —
`Probes/WBoundDemo.lean`, `Probes/UPremiseDemo.lean`, `Probes/ContentExampleSpace.lean` and
`Probes/WExtBoundDemo.lean`, the last of these through a `Derivable.premise` on
`WHyperbolic.Premises` itself, with `docs/RESULTS.md` tabulating the values. But none of that
is happening here. Read the numbers below as majorants of terms, not as mined bounds.

## the example "Nesting does not accumulate"

Non-degeneracy is checked and is *positive* evidence here: claiming `902` makes `decide`
report the proposition **false**, exhibiting the residual
`902 = pairN (2 * ((max 5 5 + 5) * 2^(0+1))) (2^(0+1) - 1)` — in which `f`, `g`, `k` do not
appear at all. That absence is the uniformity.

## The premises in the model (section comment)

The statement below has the shape
of `MetricModel.soundness_gen`'s `hprem` (and of `Soundness.lean`'s), but unlike there the
premise set is four fixed formulas over a model that already carries their content, so it is
a theorem, not a hypothesis. A named `Prop` for it once existed and was what let an earlier
pass write `(hax : M.AxiomsHold)` as a binder on `spremise`/`soundness`/the metatheorems and
justify it by analogy with `hprem` — a hidden `sorry`. The analogy fails because
`Soundness.lean`'s premise set is an abstract parameter; these are not.

## `WHyperbolicModel.axiomsHold`

The one obligation the W-hyperbolic instantiation owed; with it, `spremise` and both
metatheorems below take no hypothesis about the model beyond `WHyperbolicModel` itself.

## A worked derivation: `W(x,x,λ̃) =_X x` (section doc)

Two general ℝ-layer facts were missing and are supplied here:

* `mul_eq_zero_R_core : g =ℝ 0ℝ →ᶠ f ·ℝ g =ℝ 0ℝ` — the estimate is `mul_R_check`'s:
  `|f̂| ≤ ⟨f(0)⟩ + 1 < ⟨2^b⟩` and `|ĝ(k+b+1)| < 2^{-(k+b)}`, so the product is below
  `⟨2^b⟩ · 2^{-(k+b)} = 2^{-k}`. It belongs in `RealNumbers/Mul.lean` and is kept here only
  to leave that module untouched in this pass;
* `le_R_of_le_R_pu_nf`, a `le_R_of_le_R_pu` whose antecedent is stated over the *pushed-in*
  weakenings. This is the display-hiding trap again: the instance of an axiom that
  `pinst`/`rnorm` produces
  has `Term.weaken` distributed over the application spine with every closed constant
  restored, while `le_R_pu f g` carries `f.weaken` around the whole composite. Unifying the
  two makes `isDefEq` push `rename` through `clamp01`, `mul_R`, … — the delta-expansion
  pathology, seen as a heartbeat timeout at `papplym`. So the hypothesis is first brought to
  the fully folded form (`wfold`) and the lemma is applied with its two side conditions
  closed by `simp`, never by defeq.

The bookkeeping lesson, recorded for the next space: `rnorm` restores `sub_R`'s weakening
but not `add_R`/`mul_R`/`one_R`/`clamp01`'s, and the `closed_subst` set lacks
`add_R`/`mul_R`/`one_R`/`zero_R`; a *partially* folded hypothesis is the worst case, since
whichever side is folded, the other constant has to be expanded. `wfold`/`znorm` make the
normal form total.

## `mul_eq_zero_R_core`

see the section header for why it lives here for now.
