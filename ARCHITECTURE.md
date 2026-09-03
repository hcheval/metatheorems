# Architecture notes

Reasoning behind the project's parametrisation choices, the bugs found in them, and the
directions considered but not taken. `CLAUDE.md` records *what is true now*; this file records
*why*, and what was rejected. Written 2026-09-02.

Everything below is either verified (a build, a `#print axioms`, a probe that compiled) or
explicitly marked as inferred. Where a claim was checked, the check is named so it can be
re-run.

---

## 1. The `AdmissibleEqX` leak, and its root cause

### The symptom

`MetricSpace.admissibleEqX.eqx_sym` and `.eqx_trans` could not be proved. The proofs need
symmetry and transitivity of `=ℝ` (`eq_R_sym_core`, `eq_R_trans_core`), whose signatures take
`adm : AdmissibleEqX EqX Premises` — at `EqX := MetricSpace.EqX` that is **the record being
defined**. Lean rejects the self-reference.

### Why `eqx_refl` went through but the other two did not

`eqx_refl` is a *direct instance of an axiom*: `.premise ax_refl`, `forall_ax t`, `mp`, then a
substitution computation. No real-number lemma is touched, so no `adm` is wanted.

`eqx_sym` is not an instance of anything. `ax_sym` gives `d(s,t) =ℝ d(t,s)`; the goal is
`d(s,t) =ℝ 0 → d(t,s) =ℝ 0`. Getting there means *combining* two `=ℝ` facts, i.e. using
symmetry and transitivity of `eq_R` — theorems in the ℚ/ℝ tower.

The boundary is therefore **not** "base type vs. not". It is:

| | how it is proved | needs the arithmetic tower |
|---|---|---|
| `eqx_refl` | instantiate a premise | no |
| `eqx_sym`, `eqx_trans` | *reason about* `=ℝ` | yes |

And the reasoning happens at `realTy = nat →ₜ nat`, which contains no base type at all.

### The root cause

`eqAtType` mentions `EqX` in exactly one branch (`Language.lean:328–343`, verified):

```lean
  | Ty.nat,      s, t => Formula.eq0 s t
  | Ty.base i,   s, t => EqX i s t          -- the ONLY occurrence
  | Ty.arr ρ τ,  s, t => Formula.all ρ (eqAtType EqX τ …)   -- no recursion into ρ
```

`eqAtType_refl/sym/trans` are single functions defined by recursion on `ρ`. One branch needs
`adm`. Lean charges that hypothesis to **every instantiation**, including those at `nat` where
the branch is unreachable. `Term.lam2_correct` then chains two β-steps with `eqAtType_trans adm`
at a generic `τ`; `add_zero_r` calls it at `τ = nat`; and because its *body* mentions `adm`,
variable-inclusion puts `adm` in its signature. Repeat ~2,000 times.

> A hypothesis required by one branch of a type-recursive definition is billed to every use,
> whatever the type.

Verified: `adm.eqx_refl/sym/trans` are used in **exactly three places in the project** —
`Arithmetic.lean:164`, `:188`, `:206`. Everything else merely forwards `adm`.

### Why it stayed hidden until 2026-09-02

A *primitive* `=_X` with equivalence axioms gets admissibility free from `.premise`. The
circularity only appears when `=_X` is **defined** — as `d(x,y) =ℝ 0ℝ` is — and its properties
must be *derived*. That is the faithful route, so the architecture penalised exactly the right
thing to do, silently.

---

## 2. `AdmissibleEqX` was polymorphic in `Premises` — an unsatisfiable field

Fixed 2026-09-02, commit `af9de4e`. Recorded here because the reasoning generalises.

`eqx_refl` used to quantify over *every* `Premises`, including the empty one — demanding
`⊢ d(t,t) =ℝ 0ℝ` from no assumptions. `d_X` is `Term.func ()`, uninterpreted, so the
interpretation `metric x y = fun _ => 1` refutes it. The field was **not satisfiable**, and its
`sorry` stood for a false claim rather than for unfinished work. The in-file comment blaming
the ℝ ordered-field axioms was wrong: no amount of `RealNumbers.lean` progress touched it.

`AdmissibleEqX EqX Premises` now carries its theory. `Premises` is a plain parameter with no
monotonicity hypothesis, because every file already has `Premises` as an ambient section
variable — so all ~35 signature sites moved and **zero call sites changed**.

---

## 3. `adm` was discharged into a binder at the metric site

Also fixed in `af9de4e`, after the user pointed it out.

`MetricModel.metric_metatheorem_classical` used to take `adm` as a *parameter* rather than
using `MetricSpace.admissibleEqX`, because the latter was sorried. That is a `sorry` moved
into a binder: the theorem looks finished and the obligation is invisible.

> `AdmissibleEqX` is a hypothesis of the *general* metatheorem precisely because `EqX` is
> abstract there. Discharging it **is** what instantiating to metric spaces consists of.
> Re-abstracting it at the metric site turns the instantiation into a second abstract
> metatheorem.

**The tell**: `adm` does not depend on `M`. `eqxi` and `spremise` genuinely do — they are facts
about a particular model. *A hypothesis with exactly one intended inhabitant that you cannot
construct is a `sorry` moved into a binder.*

### This pattern has now appeared three times

Verified 2026-09-02 (morning): **nothing in the project constructed an `EqXInterp`.** It
occurred only as the hypothesis `eqxi`. `spremise` likewise.

Worse, `EqXInterp.extract` requires a realizer of `EqX i s t` to yield
`Term.interpret si s env = Term.interpret si t env` — **Lean equality of the interpretations**.
For the metric model that is `d(x,y) = 0 → x = y`, i.e. **separation**, which a pseudometric
does not satisfy. `MetricSpaces.lean` called itself a pseudometric in four places and
`MetricModel` had no separation field.

**Resolved 2026-09-02 (afternoon), as predicted.** The docs were wrong, not the code: the
*theory* is a pseudometric one and the *models* are genuine metric spaces. `MetricModel` now
carries `d_eq_zero : ∀ x y, d x y = 0 → x = y`, its docstring says why the two differ (weaker
axioms ⇒ derivations apply to more structures; `extract` needs separation), and the header
comment no longer calls the model a pseudometric. **Do not add separation to `Derivable`.**

`MetricModel.eqXInterp` now exists and both metric metatheorems discharge `eqxi` internally,
so all three of `metric_metatheorem`'s unconstructed hypotheses are gone. The price is
explicit: four of `EqXInterp`'s nine fields are proved (the structural ones — the witness type
is `ℕ → Unit`), and **five are `sorry`**, so both metric metatheorems now depend on `sorryAx`.
All five stall on the *same* missing piece, and it is not a metric fact: an **evaluation
bridge** from object-level ℚ terms to `Rounding.qval`, i.e. the value of
`lt_Q_dec (abs_Q (sub_Q (cauchyfy f (n+1)) (cauchyfy g (n+1)))) (pow2neg_Q n)` in the standard
model. `QVal.lean`'s own header declines exactly this ("a separate bridge … not attempted
here"). The obvious alternative — a soundness theorem for `Derivable` — is **circular**: its
`dist_comm`/`dist_tri` cases *are* two of the five fields.

---

## 4. `ι` does triple duty — a parametrisation bug

```lean
inductive Term {ι : Type} (F : ι → Ty ι) : Ctx ι → Ty ι → Type where
  | func  : (f : ι) → Term F Γ (F f)
  | zeroX : (i : ι) → Term F Γ (Ty.base i)
```

`ι` indexes base types (`Ty.base`), function constants (`func`), and distinguished points
(`zeroX`) — **one of each, in lockstep**. Metric spaces fit exactly (one `X`, one `d`). But
W-hyperbolic needs one base type and **two** constants, `d` and `W`, and no `ι` gives that:
`ι = Bool` buys a second base type, not a second constant.

**Fix**: split the constant index from the base-type index.

```lean
inductive Term {ι κ : Type} (F : κ → Ty ι) : Ctx ι → Ty ι → Type where
  | func  : (f : κ) → Term F Γ (F f)          -- was (f : ι)
  | zeroX : (i : ι) → Term F Γ (Ty.base i)    -- unchanged
```

`Ty ι` is untouched, so `eqAtType`, `hat`, `degree` and the majorizability type recursion are
undisturbed. `SpaceInterp.funcInterp` re-indexes to `κ`, `zeroInterp` stays on `ι`, and
`AbstractMajorizability.func_maj` re-indexes to `κ` while `zeroX_maj` stays.

**`zeroX` stays on `ι`, and this is forced, not taste.** `Dialectica/Syntactic.lean:48` uses it
as `dialecticaDefaultWitness` at a base type. Move it to `κ` and a theory could declare a base
type with no closed term, leaving the default witness nothing to return. So: **`ι` indexes types
and their inhabitants; `κ` indexes function constants.**

Note `zeroX` is *not* the metatheorem's reference point. `MetricModel.ref` is Kohlenbach's `a`
in `n ≥ d(a,x)` and belongs to the majorizability relation; `zeroX` is a language constant we
have for Dialectica totality. Kohlenbach's `A^ω[X,d]` has no distinguished-point constant.
Keep them separate.

Independent confirmation from Neri–Pischke (§9 below): their system needs 6–14 constants over
*two* base types, heterogeneous and cross-base-type (`∈ : 0(S)(Ω)`), and their Skolemisation
step *adds constants dynamically*. Their footnote 18 also shows the inhabitation constant
`c_Ω` is load-bearing for **axiom admissibility**, not only for Dialectica totality.

---

## 5. `eqBaseFree` — `ι = Empty` at the equality index only

The fix for §1, if taken (see §7 for the alternative).

`eqAtType` consults `EqX` only through `ρ`, so constraining `ρ` is exactly enough. The
predicate must **mirror `eqAtType`'s own recursion, not the type's syntax**:

```lean
def Ty.eqBaseFree : Ty ι → Bool
  | .base _      => false
  | .arr _ τ     => τ.eqBaseFree                    -- domain is ONLY a binder
  | .prod ρ τ    => ρ.eqBaseFree && τ.eqBaseFree    -- both: it is a conjunction
  | .nat | .unit => true
```

The obvious wrong version is `| .arr ρ τ => ρ.baseFree && τ.baseFree`. It **fails silently** —
no error, just fewer lemmas applicable — and it wrongly rejects `X →ₜ nat`, whose `eqAtType` is
`∀x^X. eq0 (s x) (t x)` and mentions no `EqX`. Only the codomain spine matters.

### Why this is not `ι = Empty`, and why that difference is the point

| | restricts | terms allowed | transport needed |
|---|---|---|---|
| `ι = Empty` | the **language** | no `d`, no `W` | yes → the `morphism(t)` problem |
| `eqBaseFree` | the **type the equality is asserted at** | anything ambient | none |

`add_zero_r (x : Term F Γ Ty.nat)` still accepts *any* nat-term of the full language —
`cauchyfy (d s t) n` included. `F`, `Γ`, and the terms stay arbitrary; only `ρ` is constrained.
So the `_bf` lemmas are stated over an arbitrary `F` and are *already* theorems of every
extension — nothing to inherit, nothing to transport.

### The unavoidable wart

At an eq-base-free type the requirement is genuinely **empty**, so any parameter recording it is
dead. Once the ~49 `Arithmetic.lean` boundary lemmas stop mentioning `adm`, variable-inclusion
drops it from their signatures and ~2,000 ℚ/ℝ call sites cascade. Two options:

- **D1** — keep a dead parameter on the 49 (~50 edits, permanent cruft unless removed later)
- **D2** — remove it and fix all call sites (~2,000 edits, clean)

Recommended sequencing if this route is taken: D1 first as an explicitly transitional step so
the mathematics stops waiting, D2 later as independent hygiene. Do **not** leave D1 unrecorded.

---

## 6. What "extends" should mean — schemas, not morphisms

The question: W-hyperbolic *extends* metric spaces. What is "extends" when the parametrisation
is fixed up front?

**Rejected — a general theory morphism.** Define `T → T'` (injection on base types and
constants, `Premises ⊆ Premises'`, `EqX` preserved) and prove `Derivable` functorial along it.
It is the right answer to the abstract question and the wrong answer to ours, because of the
objection that killed it:

> If you transport a *proof about `t`*, you get a proof about `map(t)` — and the terms you care
> about in the target (anything mentioning `d` or `W`) are **not in the image**.

The escape is to transport *sentences*, not proofs-about-terms: `∀x,y:nat. x+y = y+x` is closed,
its image is itself, and `forall_ax` then instantiates it at any target term. Instantiation
happens **after** transport, so `t` never needs to be in the image. But our lemmas are stated in
*instantiated* form (`add_comm (x y : Term F Γ nat)`), which is a schema over ambient terms, not
a sentence — so the escape is unavailable without restating ~2,000 uses.

**Adopted — parameterise theory content by the constant terms.**

```lean
def metricAxRefl (d : Term F Γ (X →ₜ X →ₜ ℝ)) : Formula F Γ
def metricAdmissible (d) (h : the three schemas at d are premises) : AdmissibleEqX (eqXof d) Premises
```

W-hyperbolic's `Premises` then contains `metricAxRefl d_h` where `d_h := func (inl ())` — *the
same schema at a different constant*. No translation, because nothing was ever stated in "the
metric language". Premise inclusion is definitional and `metricAdmissible` applies verbatim.

Two supporting facts:

- **Most of Kohlenbach's tower adds axioms, not constants.** CAT(0) over W-hyperbolic is the CN
  inequality — same language. So most extension steps are pure premise growth, i.e.
  `Derivable.weakenPremises`, which is one structural recursion and **does not yet exist**.
- **Majorizability inherits with one field growing.** Verified by reading
  `Majorizability.lean:106–119`: `nat_order`, `app_compat`, `arrow_intro`, the seven `selfMaj_*`,
  the `prod_*` and `zero/succ/prec_maj` depend only on `maj`/`selfMaj`, which in the Bezem
  instance are functions of `ι`, `X` and `base` — **not of `F` or `si`**. Under `κ ⊕ Unit`:
  structural fields verbatim, `zeroX_maj` verbatim, `func_maj` by `Sum.rec`.

### `pm_theory`, the intended surface

```
pm_theory WHyperbolic extends MetricSpace where
  constant W : X →ₜ X →ₜ nat →ₜ X
  axiom w1  : ...
  majorant W := ...
```

Six outputs (`κ`, `F`, `Premises`, `EqX`, admissibility, majorizability), of which four should
inherit. **`zeroX` must not appear under `constant`** — declaring a base type carries an
*inhabitation obligation*, not an axiomatised constant.

Build W-hyperbolic **by hand first** and check the six outputs really fall out; generalise to an
elaborator second.

---

## 7. Dropping `EqX` entirely — probed, feasible, deferred

**The proposal.** Delete `EqX`; give every base type a distance `d_i`, define
`x =_X y :≡ eq_R (d_i x y) 0ℝ` once and for all.

**Probe result (2026-09-02): feasible, no blocker.** Verified two independent ways — a
constant-level dependency oracle over the elaborated environment, and a 630-line verbatim copy
of all required declarations compiling against only `Metatheorems.Language` and
`Metatheorems.SimpSets` **in 4.5 s**. The probe also elaborated a working `eqAtType'` with `EqX`
deleted.

- Transitive closure of `eq_R, lt_R, le_R, zero_R, add_R, cauchyfy` = **124 constants**. From
  `Language`, **exactly 7**: `Formula`, `.bot`, `.eq0`, `.imp`, `.all`, `.ex`, `Formula.neg`.
  **`eqAtType`, `Derivable`, `AdmissibleEqX` are not reached.**
- Must-move set: **41 declarations, ~920 lines**, in three *contiguous prefixes* —
  `Arithmetic.lean` 86–144, `RationalNumbers.lean` 28–362, `RealNumbers.lean` 54–283.
- `Language.lean` splits trivially: `eqAtType` is the **last** declaration with **zero
  dependants inside the file**; a 32-line tail moves.
- Bonus: `eq_R_isPurelyUniversal`, `eq_R_substF` and the `le_R_pu` trio are in the low set, so
  `substF_nat` and `eqx_pu` become **theorems at the definition layer**.

**Not verified**: that the rest of the build survives the reordering. `Derivable.lean`
references `eqAtType`, so it and every proof half move below the ℝ term layer. That is the real
cost and it was out of the probe's scope.

**Deferred, and why.** Its benefits — `pm_theory` simplicity, a canonical majorizability `base`,
deleting `AdmissibleEqX` — are all about the future tower, none about the two open `sorry`s.
Exactly **two declarations in the whole build touch `sorryAx`**; destabilising a core inductive
that four proved metatheorems and 13k lines of ℚ depend on, to close two `sorry`s, is a bad
trade. Revisit when W-hyperbolic forces the question. The probe is banked so it need not be
re-derived.

Interleaving warts found, relevant whenever a reorder happens:
- `Arithmetic.lean` — `self_imp_h` (51), `weaken_intro_h` (55), `forall_ax_inst` (60) are
  `Derivable`-valued and sit *above* the term definitions at 86–144.
- `RationalNumbers.lean` — `lt_Q` (7243) and `le_Q` (7247) are **`Formula` definitions 6,700
  lines below** `eq_Q` (396).

---

## 8. Moving `eqx_refl`/`sym`/`trans` into `Derivable` — the current proposal

Keep `EqX`'s shape abstract; add the three equivalence facts as **constructors** of `Derivable`.

The insight it turns on: `AdmissibleEqX`'s five fields split into two kinds.

| field | kind | metric status |
|---|---|---|
| `substF_nat` | *computational* — naturality through `EqX`'s shape | proved |
| `eqx_pu` | *computational* — `EqX` is Π⁰₁ | proved |
| `eqx_refl`/`sym`/`trans` | *theorems* — require reasoning in the theory | 1 of 3 |

Move exactly the theorems and what remains is **always constructible by computation, never by
proof**. The §1 circularity dissolves — not by removing `adm` from arithmetic, but by making it
cheap enough that arithmetic can have it.

**Cost (both figures verified 2026-09-02).** 3 constructors, 3 field removals, 3 call sites
(`Arithmetic.lean:164/188/206`), 2 `sorry`s deleted; and 3 new cases in each of **4** in-build
recursions over `Derivable` (`Dialectica/Lemmas.lean`, `NegTrans.lean`,
`Syntactic.lean:1032`, `castAllowed`) plus the out-of-build `Hilbert.lean` printer. `adm` stays
threaded for `substF_nat`, so **~2,000 call sites are untouched** and §5 demotes from blocker to
optional hygiene.

**`EqXInterp` needs no new fields** — verified. `realize`/`extract` already pin `EqX`'s
interpretation to Lean `Eq`, which is an equivalence, so the three soundness cases are `rfl`,
`.symm`, `.trans`. (This is also how §3's separation problem surfaced.)

**Dividend.** The metric `eqx_trans` obligation moves from object-level ℝ codes — blocked behind
the `le_zero_eq_zero_R` repair, object-level non-negativity and `0 ≤ℝ f+f → 0 ≤ℝ f` — to
**semantic Mathlib `ℝ`**: `d(x,z) ≤ d(x,y)+d(y,z) = 0` with `d ≥ 0`. It also finally consumes
`MetricModel`'s currently-unused `d_nonneg`/`d_self`/`d_comm`/`d_triangle`.

**What it costs, stated precisely.** Not "assuming what Kohlenbach derives". The extension is
**conservative over any theory in which `EqX` is provably an equivalence**, which includes
`A^ω[X,d]`. It is *not* conservative in general, so the constraint becomes a **soundness
condition on models**. The accurate reading: `Derivable` now means *"derivable in a theory whose
base equality is an equivalence"*, and checking that is the model's job.

**Owed later, and easy to forget**: with `adm` constructible, arithmetic works, so
`d(s,t) =ℝ 0 → d(t,s) =ℝ 0` can then be proved from `ax_sym` **as a theorem** — i.e. the
constructors are *admissible rules* of `A^ω[X,d]`. The content is relocated, not lost. Record it
as a debt or it becomes something we assumed and forgot we assumed.

---

## 9. Neri–Pischke, *Proof mining and probability theory* (arXiv:2403.00659)

Read 2026-09-02 as a test of whether our design over-commits. A **non-metric** metatheorem:
abstract elements are majorized by the probability content rather than by a metric.
Deliberately deferred as future work; recorded because it constrains interfaces we are about to
touch.

### Confirms

- **Bezem strong majorizability verbatim**, with the same hat map (`Ω̂ = Ŝ = 0`). Their
  **Lemma 8.6 is cited as Kohlenbach 17.80** — our `arrow_intro` — used for the same purpose in
  a *combinatory* presentation. Settles the λ-vs-combinators claim in `CLAUDE.md`: combinators
  would have needed it too.
- **Our `base i n x` slot is right.** Theirs is `n ≽_Ω x :≡ n ≥ P(Ω)`, which **does not mention
  `x`**, and compares an `ℕ` with a **real**. An arbitrary predicate slot accommodates both.
- **`ι`/`κ` split is a precondition**, and **`zeroX`'s role is broader than we thought** (§4).
- **Reals as `nat →ₜ nat`** with fixed modulus, the same Cantor pairing, and the `(·)°` rounding
  of Kohlenbach 17.7/17.8 — a direct fit with `Rounding.lean`.
- **Equivalence relation**: both their base equalities are equivalences. `(eq)₂` axiomatises
  reflexivity ∧ symmetry ∧ transitivity of `=_Ω` verbatim. **No refutation of §8.** Their `=_S`
  is *defined* (`A =_S B :≡ ∀x (x ∈ A ↔ x ∈ B)`) with the properties derived, which is a hygiene
  argument against §8, not a soundness one.

### Warns

1. **"Purely universal or NT-stable" is too narrow as the general premise interface.** Five of
   their key axioms are **type Δ** — `∀a ∃b ≤_σ ra ∀c A_qf` — neither PU nor NT-stable, and
   eliminated by Skolemising into a *new constant* plus a purely universal axiom. If we want a
   reusable metatheorem, premise-admissibility should be a **parameter with at least two
   inhabitants**, not a fixed `isPurelyUniversal` check. *We may implement the Δ version later
   (user, 2026-09-02) — retrofitting touches `Derivable`, `NegTrans` and the metatheorem
   statement.*
2. **`eqAtType` is not the only type-recursive relation needed.** `≤_ρ` is a second one, with a
   per-base-type clause, interacting with `≽` via a field we lack:
   `∀x*,x,y (x* ≽_ρ x ∧ x ≥_ρ y → x* ≽_ρ y)`. If `eqAtType`'s "abstract base clause by recursion
   on `ρ`" were generalised into a reusable combinator, `≤_ρ` would come free.
3. **Premises can be rules.** Their `(⋃)₂` is a rule, not a formula; `PremiseSet` has no slot.
4. **Base types are chosen for majorizability, not ontology.** They make the event algebra `S` a
   base type rather than coding it as `Ω →ₜ nat`, so that `A^S` gets its own majorization clause.
   Do not let the metric tower harden an assumption that `ι` tracks *spaces*.
5. **Bar recursion.** Their general case needs `BR`; our `Term` has `prec` only, placing us in
   their case (3) — primitive recursive `Φ`, plain majorization, no DC. A real scope limit worth
   documenting rather than discovering at instantiation.
6. **Negative rounding.** They extend `(·)°` to negative reals (needed for integrals). Our
   `Rounding.lean` is `Nat.floor`-based with `0 ≤ x` throughout.
7. **Check what our conclusion asserts.** Their Theorem 8.9 concludes truth in the full
   set-theoretic structure, via a *small*/*admissible* type analysis. `Ty.degree` as defined does
   not distinguish these.

---

## 9b. Known debts from the `Term.dist` refactor (2026-09-02)

Recorded so they read as *debts*, not as design.

**The `eqBaseFree` `autoParam` is duct tape.** `eqAtType_sym`/`eqAtType_trans` and
`lam2_correct`/`lam3_correct` (+ their `_nf` wrappers) carry
`(hbf : ρ.eqBaseFree = true := by rfl)`. It works — the base case becomes unreachable, and
because `τ` is concrete at every ℚ/ℝ call site Lean fills the proof, so **all ~164 call sites
were untouched**. But it is a side condition threaded for a *layering* reason, not a
mathematical one, and a reader meeting `hbf` has no local way to see why. Options when
polishing: fold the base-free restriction into a separate namespace; or, if the layering is
ever reorganised so `eq_R` symmetry/transitivity land below `Arithmetic.lean`, delete it
entirely. Do not treat its presence as meaningful.

**Two distances in the metric model.** `MetricSpace.ax_refl`/`ax_sym`/`ax_triangle` still
speak about `d_X = Term.func ()` while `eqAtType` uses the structural `Term.dist ()`. They
get the same interpretation in `MetricModel` but nothing *relates* them. Stage 6 drops the
premise-level one; until then, do not assume a fact about one transfers to the other.

**`EqXInterp` grew four fields.** `dist_comm_realize`, `dist_tri_realize`,
`dist_comm_term`, `dist_comm_term_sound`, `dist_tri_term`, `dist_tri_term_sound` — soundness
owes the model's `distInterp` being a pseudometric, since `dist_comm`/`dist_tri` are
constructors and are *not* of the shape `eqAtType (.base i) s t`. Costless today because
nothing constructs an `EqXInterp`, but it widens what instantiating a metric model will cost.

## 9c. Why the theory is pseudometric and the model is metric

Not a compromise — forced, and by the same constraint that shapes everything else here.

`isPurelyUniversal` falls through to `isQF` at `.imp`, so **an implication between Π⁰₁
formulas is not Π⁰₁**. Separation has exactly that shape:

```
∀x,y. ( d(x,y) =ℝ 0ℝ  →  x =_X y )
        └── Π⁰₁ ──┘      └─ Π⁰₁ ─┘
```

The metatheorem's premise interface admits only purely universal (or NT-stable) formulas, so
separation **cannot be an axiom of the theory**. Reflexivity, symmetry and the triangle
inequality can: stated about `d`, they are Π⁰₁ outright.

So separation lives in the *model* — `MetricModel.d_eq_zero` — because that is the only place
it can live. `EqXInterp.extract` needs it (it yields Lean equality of interpretations), and a
model that satisfies the pseudometric axioms *and* is separated is a genuine metric space,
which is what Kohlenbach's models are.

The payoff of keeping the theory weak: derivations use only the three Π⁰₁ axioms, so the
extracted bounds are valid over any structure satisfying them — a strictly stronger theorem
than one that assumed separation.

**This is the same reason symmetry of `=_X` is not an axiom.** `x =_X y → y =_X x` is an
implication between Π⁰₁ formulas, so its Dialectica witness type carries a real `ℕ → ℕ`
counter-transformer instead of being a singleton (§8). Axiomatising `dist_comm` — Π⁰₁, about
`d` — and *deriving* symmetry keeps the whole theory inside the fragment where the
interpretation is trivial. The axiomatisation is chosen for that, not for elegance.

### Could models be pseudometric after all?

Yes, with work — and the reason they currently can't is worth knowing, because "models must
be metric" reads like a mathematical necessity when it is an implementation choice.

`EqXInterp.extract` has **exactly one consumer**: `eqAtType_to_semEq`
(`Dialectica/Lemmas.lean:255`), used in exactly one place — the **`.qfer` soundness case**
(`Lemmas.lean:335`, mirrored at `Syntactic.lean:969`). It turns a realizer of `s =ρ t` into
Lean equality of interpretations so the proof can rewrite inside `r`.

In a pseudometric model that step is *false*: take `d(x,y) = 0` with `x ≠ y` and an `r` whose
interpretation separates them — QF-ER derives `r[x] =σ r[y]` and the model refutes it. So
pseudometric models would make **the rule unsound**, not merely be inconvenient.

Two ways to have them:

- **Quotient.** Any pseudometric space quotients to a metric one (Mathlib's
  `SeparationQuotient`), and `=_X`-invariant statements — exactly the QF-ER-derivable ones —
  transfer back. Costs the user a construction, gains nothing mathematically. This is why the
  restriction is cheap.
- **Setoid semantics.** Replace Lean `Eq` in `extract` by a model-supplied equivalence and
  require every interpretation — `funcInterp`, `distInterp`, `Term.interpret` at every type
  former — to be a congruence for it. Strictly more general, and arguably the faithful reading
  of *weak* extensionality. But it is setoid-ifying the whole semantics for something the
  quotient already gives.

So: **Lean `Eq` in `extract` is doing the setoid's job, cheaply.** Deliberate, with a known
escape hatch. Note this is purely semantic — the *theory* stays pseudometric, so derivations
and extracted bounds are valid over pseudometric structures; you just cannot interpret in one
without quotienting first.

## 10. Scope decisions

- **`general_metatheorem` may narrow to theories whose base types are pointed pseudometric
  spaces** if §7 is ever taken — user decision, 2026-09-02, made deliberately. Not an oversight;
  do not "restore" the generality. It costs nothing at `ι = Empty`, which is where the whole
  ℚ/ℝ layer and both MCT derivations live.
- **Primitive λ is kept.** See `CLAUDE.md`, "Lambda vs. combinators". §9 confirms the reasoning.
- **`AdmissibleEqX` stays a plain structure passed explicitly, never a typeclass** (standing user
  preference).

---

## 11. Plan

| # | item | size | note |
|---|---|---|---|
| 1 | `ι`/`κ` split (§4) | mechanical, wide | a real bug; cost grows with the codebase; §7 and §9 both need it |
| 2 | move `eqx_refl/sym/trans` into `Derivable` (§8) | ~30 lines + 12 cases | unblocks the two `sorry`s; supersedes §5 |
| 3 | `eqx_sym`, `eqx_trans` semantically | small | §8's dividend removes the hard object-level ℝ work |
| 4 | `spremise` via `srealizer_of_pu` | small | see below |
| 5 | construct `EqXInterp` for `MetricModel` (§3) | **done, 4/9 fields** | separation added; the other 5 need the `qval` evaluation bridge (§3) |
| 5b | the `qval` ↔ `Term.interpret` evaluation bridge | unknown, probably large | unblocks 5 of `EqXInterp`'s 9 fields, and would give `Derivable` soundness |
| 6 | `Derivable.weakenPremises` | one recursion | makes axiom-only extensions free (§6) |
| 7 | schema-parameterise `MetricSpaces.lean` (§6) | ~450 lines today | cheapest now; makes `extends` free |
| 8 | the 16 `RealNumbers.lean` sorries | the real remaining work | `REALS_PLAN.md` |
| 9 | `pm_theory` + W-hyperbolic by hand (§6) | design | then revisit §7 and §9.1 |

**Item 4 is smaller than it looks.** Verified by `#reduce`: `wTy` of a purely universal formula
is a **function into `unit`** at any nesting depth and over base types —
`wTy (∀x^X. ∀n. QF) = X →ₜ nat →ₜ unit`. So the realizing term carries no information and all
the content is "the premise is true in the model":

```lean
def srealizer_of_pu (B : Formula F Γ) (hpu : B.isPurelyUniversal = true)
    (hvf : B.isVFree = true) (htrue : ∀ env, Formula.interpret si B env) : SRealizer si B
```

plus three applications feeding `M.d_self`/`d_comm`/`d_triangle`. It mentions no `F`, so it
inherits to every extension verbatim — where hand-built `Term F_metric` realizers would have hit
the `morphism(t)` problem of §6 at the worst possible place. **Unchecked**: whether `le_R_pu` is
`isVFree`, which `dialecticaMatrix_iff_interpFormula` requires alongside QF.

## 12. Decisions D-1, D-2, D-4 — salvaged from the deleted `HANDOFF.md` (2026-09-04)

`HANDOFF.md` was a one-month *talk* plan (thesis, schedule, budgets, Q&A prep, abort states).
That plan is moot and the file was deleted — but its §4 decisions are **enforced in code right
now** and cited **by number in user-facing error messages**, so they are kept here verbatim in
substance, under the same numbering, so those citations still resolve:

- `ProofMode/Linter.lean` — the surface-recursor ban *is* D-2.
- `ProofMode/Tactics.lean:440,453,803` — error text "extraction vacuous (HANDOFF D-2,
  surface-recursor ban)"; `:825,837` — D-4 and D-1.
- `ProofMode/TacticsTest.lean:181,189,242,256,270` — the same, as expected test output.
- `CLAUDE.md` module table — `Linter.lean` (D-2), `MCT.lean` (A2), `MCTLazy.lean` (A3).

**D-1 (¬¬-handling).** Witness-type/extraction is defined on Shoenfield-normal forms; the `¬¬`
over Π₂ cores is collapsed via Markov (validated by Dialectica), never interpreted
monolithically — monolithic Kuroda∘Dialectica is one exponential above Ψ. Literals are Π⁰₁
atoms; normalization passes challenges through and never decides them. There is **no
mechanized translation pass**: `mct_p1` is the *hand-translated* proof, formalized directly in
the intuitionistic system + Markov. This is why `by_contra`'s error message asks "Is this proof
translated?".

**D-2 (linter).** Provenance ∪ identity tagging **and** the surface-recursor ban, both adopted.
Checked against the corpus: honest MCT, Groetsch, and projection-uniqueness all survive the
ban, because iteration lives only in *extracted* content, never in the surface term.
**Standing check for any new input: verify its surface terms are recursor-free before
accepting it as corpus.** The ban is on the *surface language as a whole*, so `pexists` and
`pinst` carry it too.

**D-4.2 (`p₂` before `p₁`), still the reason the two derivations differ.**
`Allowed.extended = {markov, ip, ac, qfac}` has **`lem := false`**, so a `by_contra` reductio
is *not* derivable in the metatheorem's input system. `mct_p2` (dichotomy) is constructive over
decidable ℕ-comparisons via `qf_lem` and needs no translation; `mct_p1` is hand-translated per
D-1. This is a fact about the systems, not a scheduling artifact, and it still holds.

**D-4.4 (`by_contra` = the Markov rule, named as such).** `by_contra_markov`, with a shape
check. Not a restriction suffered but the precise statement of what D-1's hand-translation
produces: the lazy MCT proof's contradiction bottoms out in a Σ₁ statement over decidable
primes, so after Kuroda its classical content is exactly `¬¬∃n(qf) → ∃n(qf)`.

**Deliberately NOT salvaged, because it is now false or dead:** D-3 (superseded by D-4 in the
original); the "out of scope for the month" note protecting the `general_metatheorem_classical`
sorry — *that sorry was closed 2026-09-02*; D-4.1's "ℚ and ℝ are both off the critical path
this cycle" — the ℚ/ℝ tower is complete with zero sorries; and the entire schedule, budget,
claims-calibration and abort-state apparatus. Full text remains in git history.
