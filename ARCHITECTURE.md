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
(`zeroX`) — **one of each, in lockstep**, so `|constants| = |base types|`, forced.

**Count corrected 2026-09-04 — the diagnosis below stands, the example that motivated it no
longer does.** This paragraph used to read "Metric spaces fit exactly (one `X`, one `d`). But
W-hyperbolic needs one base type and **two** constants, `d` and `W`, and no `ι` gives that."
Since the `Term.dist` refactor (2026-09-02) `d` is **not** a constant — it is the structural
constructor `Term.dist`, carried by every base type at every `ι`, because `eqAtType` must name
it without going through a signature. So:

- **Metric spaces use ZERO function constants**: `MetricSpace.F () = Ty.unit`, and `d_X` is
  `Term.dist ()`. The one available constant slot sits unused.
- **W-hyperbolic now needs 1 base type + 1 constant** (`W` alone), which `ι = Unit` supplies.
  **It fits — but by the numbers happening to line up, not because the indices were
  decoupled.** W-hyperbolic can therefore be built *before* this refactor, which is a
  sequencing convenience, not a reprieve.
- **CAT(0) also fits**: it adds the CN inequality, an *axiom*, so it inherits W-hyperbolic's
  signature and only extends `Premises` (cf. §6 below — most of the tower adds axioms).

**The coupling is unchanged and still blocks the tower.** Anything wanting a ratio other than
1:1 has no way to ask for it — in particular **normed and inner-product spaces, which are in
scope** (`SPINOFFS.md`: Banach/Hilbert ⇝ CAT(0) ⇝ W-hyperbolic): one base type but several
constants (`+`, scalar multiplication, `‖·‖`). Bumping `ι` to `Fin 3` buys the constants *and*
two spurious base types, each dragging its own `dist` and `zeroX` that some model then owes an
interpretation for, and each adding a `bezemMaj` case to majorizability. **So this refactor is
still required; it is not optional and W-hyperbolic does not retire it.**

One workaround this section predates, since it needs the products merge: bundle `n` constants
into a single product-typed `F ()` and project. It expresses the right signature without
touching `Term`, but it is not obviously a substitute — how it interacts with
`AbstractMajorizability`'s **per-constant** `func_maj` field is unexamined, and collapsing
distinct constants into one product plausibly degrades exactly the per-constant structure that
field is for.

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

## 13. How our metatheorem differs from Kohlenbach 17.52 (2026-09-04)

**Read this before claiming the project "formalizes Kohlenbach's metatheorem".** It does not,
quite. The gap is narrow and probably costs nothing mathematically, but it was unrecorded until
now, and an unrecorded deviation is how a wrong claim reaches a paper.

Checked against the **primary source**, not the reference document:
`Kohlenbach - Applied Proof Theory (2008)`, **Theorem 17.52, p. 403** ("General theorem on
proof mining: the abstract metric and hyperbolic case", Gerhardy–Kohlenbach):

> Let `ρ` be of degree `(1,X)` or `≤ 2` and let **`B∀(x,u)`, resp. `C∃(x,v)`, be ∀- resp.
> ∃-formulas** that contain only `x,u` free, resp. `x,v` free. **Assume that `0X` does not
> occur in `B∀`, `C∃`.** From a proof in `A^ω[X,d]^{−b}` of
> `∀x^ρ (∀u⁰ B∀(x,u) → ∃v⁰ C∃(x,v))` one can extract a partial functional `Φ : S_ρ̂ ⇀ ℕ` …
> such that … `∀u ≤ Φ(x*) B∀(x,u) → ∃v ≤ Φ(x*) C∃(x,v)`.

`general-metatheorem.tex:63` transcribes this faithfully as `B ≡ ∀b̲ B₀`, `C ≡ ∃c̲ C₀`.

| | Kohlenbach 17.52 | reference document | **ours** |
|---|---|---|---|
| premise matrix | `B∀`, a ∀-formula | `∀b̲ B₀` | `B₀` **quantifier-free** (QF entry points); **`isPurelyUniversal`** in the `_gen` entry points since 2026-09-04 |
| conclusion matrix | `C∃`, an ∃-formula | `∃c̲ C₀` | `C₀` **quantifier-free** (QF entry points); **`isPurelyExistential`** in the `_gen` entry points |
| connectives | unrestricted | unrestricted | **∨-free** |
| type `ρ` | degree `(1,X)` or `≤ 2` | any | any |
| `0_X` in the matrices | **excluded** | — | allowed, majorized |

### The one real gap: QF matrices — CLOSED 2026-09-04 (branch `general-matrices`)

**Status.** `syntactic_general_metatheorem_gen`, `_at_gen`, `_classical_gen` and the
spelled-out `syntactic_general_metatheorem_block` (`SyntacticMetatheorem.lean`, section
"General matrices") take `B.isPurelyUniversal` / `C.isPurelyExistential` (+ ∨-free) in place
of `isQF`, which is 17.52's "`B∀` a ∀-formula, `C∃` an ∃-formula" verbatim. All four are
`[propext, Classical.choice, Quot.sound]`; the QF theorems are untouched and are instances
(`Formula.isPurelyUniversal_of_qf` / `isPurelyExistential_of_qf`). The demo
`Probes/GeneralMatricesDemo.lean` runs a `le_R_pu` premise — `demoB.isQF = false` by `rfl`,
so the old entry point cannot be stated on it — through both the extended and the classical
entry points. **No hypothesis 17.52 lacks was added**, and no type-degree restriction.

What the closing found, in order of surprise:

1. **The extended route needed no prenexification.** The book and the document expand
   `∀u∀b̲ B₀ → ∃v∃c̲ C₀` and prenexify because their input is *classical*. For an
   `Allowed.extended` derivation, Dialectica interprets `∀u B∀ → ∃v C∃` directly and the
   realizer's counter component already returns `(u, (b, …))`, its witness component
   `(v, (c, …))`. `extractUTerm`/`extractVTerm` never depended on the matrices being QF — the
   *only* place the restriction lived was `dialecticaMatrix_iff_interpFormula`, which says a
   QF ∨-free matrix equals its interpretation at every witness/counter. That is false for a
   ∀-formula (the matrix at counter `(b, …)` is the instance at `b`), so it is *replaced by a
   pair*, `dialecticaMatrix_of_interp_pu` and `interp_of_dialecticaMatrix_pe`
   (`Dialectica/Defs.lean`): a true ∀-formula has a true matrix at every witness and counter;
   an ∃-formula with a true matrix is true. Each is a five-line structural recursion.
2. **`prenexify` never used its four QF hypotheses.** The body is LEM on arbitrary formulas.
   It is now a wrapper around `prenexify_gen`, which has no hypothesis at all — the
   classical route reuses it as-is.
3. **The classical route's one new step is restoring `B'` from `B'ₙₜ`.** After the negative
   translation the prenex body is `B'ₙₜ →ᶠ C'ₙₜ`. `C'ₙₜ = C'` outright (`kurodaInner_pe`:
   Kuroda touches only `∀`), and `B' →ᶠ B'ₙₜ` is derivable for a ∀-formula
   (`kurodaInner_iff_pu`, already present), so precomposing under `∃u∃v` and `¬¬` gives back
   `B' →ᶠ C'` (`classical_to_prenex_extended_gen`). Intuitionistic; LEM is still spent only
   in `prenexify_gen`.
4. **The book's tuple is our single block, because we have products** — see the coordinator
   note recorded in the section header of `SyntacticMetatheorem.lean`. `Formula.all` binds any
   `ρ : Ty ι`, so `∀b̲` is `∀b^(ρ₁ ×ₜ … ×ₜ ρₙ)`; `degree (.prod ρ τ) = max …`, so nothing
   changes at the type level. `isPurelyUniversal` allows arbitrary nesting anyway.

The pre-closing analysis is kept below for the record.

`syntactic_general_metatheorem` requires `B₀.isQF = true` and `C₀.isQF = true`, i.e. `b̲` and
`c̲` **empty**. This was a genuine restriction against *both* sources.

**It probably costs nothing mathematically.** Fuse `∀u∀b̲` into one `∀u'` by Cantor pairing (we
have it). We then get `∀u' ≤ Φ B₀' → ∃v ≤ Φ C₀`, and to *use* it you must supply
`∀u' ≤ Φ B₀'` — which any application has, since it holds the full `∀u∀b̲ B₀`, strictly
stronger. Pairing is monotone, so a bound on the code bounds `u`. `c̲` is the same with `∃`.
∨-freeness is likewise harmless for QF matrices over ℕ, where everything is decidable and
`A ∨ B` is `¬A → B`. **This argument has not been formalised; treat it as a plausibility
argument, not a theorem.**

**It costs real ergonomics, and the cost lands on the flagship target.** `le_R_pu` — the
purely-universal `≤ℝ` — *is* a `∀b̲ B₀`. The document and the book consume such a premise
directly; we would have to pair-encode it and then reason about codes inside a proof-mode
derivation. For ℝ-MCT that is the difference between a readable statement and one buried in
`triag`/`inv_triag`. Ergonomics decides whether a large derivation gets written, so this is
the reason to close the gap, not the mathematics.

**Closing it may be cheap.** The book's and the document's proofs both handle `b̲`/`c̲` by
*expanding the hidden quantifiers and prenexifying* (`general-metatheorem.tex:76–82`) — which
is exactly what `classical_to_prenex_extended` already does for the `¬¬` route.

### Where we are safely more general: the type degree

17.52 restricts `ρ` to degree `(1,X)` or `≤ 2`; we restrict nothing. **This is safe because the
restriction is attached to a claim we do not make.** Kohlenbach's Φ is "a partial functional
`Φ : S_ρ̂ ⇀ ℕ` whose restriction to the strongly majorizable elements is a total computable
functional of `M^ω`", sharpening to ordinary type-2 computability at degree `1*`. Our Φ is
`Nat.max` of two `closedMajorizer`s — a total structural recursion — so there is nothing to
classify, and **no bar recursion is involved anywhere in this project**. Do not "fix" this by
adding a degree hypothesis; it would be a restriction with no purpose.

### Where we are deliberately more general, and it is Kohlenbach's own suggestion

17.52 assumes `0_X` does not occur in the matrices. The paragraph immediately preceding it
(p. 402–403) gives the alternative:

> `0X` just is an arbitrary Skolem constant which could have been replaced by any new variable
> of type `X` which — taking the universal closure — would just add another input that had to
> be a-majorized.

That is exactly our arrangement: `zeroX` may occur, and `AbstractMajorizability.zeroX_maj` pays
for it. In `MetricModel.constMajorants` that input is the parameter **`n₀ ≥ d(a, 0_X)`** — the
"another input that had to be a-majorized", made concrete. Kohlenbach also notes that for
normed spaces `0_X` is crucial and one takes `a := 0_X`, making it trivially majorized by `0⁰`;
that is our `n₀ = 0` case, and it is why the normed instantiation should be *cheaper* than the
metric one, not more expensive.

### Related deviations recorded elsewhere

The λ-vs-combinators trade (our `arrow_intro` = Lemma 17.80) is in `CLAUDE.md`, not here; it is
a difference in *term language*, not in the metatheorem's statement. The `AbstractMajorizability`
vs Def. 6.0.1 field count is discussed there too.

## 14. The monotone functional interpretation: bounds without realizer terms (2026-09-05)

**Status: design settled by a passed gate (`Probes/MonotoneSpike.lean`); refactor not started.**
This section records why the extraction pipeline is being re-based, what the new object is, what
the spike established, and what the plan is. `CLAUDE.md` has the measurements; this has the
reasoning.

### 14.1 The problem, stated with the numbers that separated it into two

The pipeline since `syntactic-witnesses` is: `syntactic_soundness` builds a Dialectica realizer
as a closed object-language `Term`; `closedMajorizer` majorizes that term; the metatheorem's
`Φ` is built from the majorants. It produces kernel-checked numerals on derivations of ~12
raw constructors and nothing beyond. Two measurements on 2026-09-05 (`SizeProbe`,
`LemBoundDemo`) showed that "nothing beyond" is **two problems, not one**:

| stall | term size | what the kernel is doing |
|---|---|---|
| `ConjBoundDemo.acFinal` (one `and_contract`) | **2,529 nodes** — smaller than `Term.add_Q` | executing `Term.weaken`/`rename` over dependent indices with `Eq.rec` casts, on the way to a tiny term (`Eq.rec ↦ 16074`, `Term.rename ↦ 2566`, `Var.rec ↦ 1073`) |
| the classical route (any derivation) | does not fit in 12 GB under `#eval` | `negTrans_sound` hands Dialectica **85k constructors** for a 12-constructor input (≈230× per node) |

And underneath both, a representation fact: `dag = tree` for every realizer measured by
pointer identity, because `Term.weaken` is a copying recursion and every `wt*` combinator
weakens its arguments. The compiled evaluator preserves no sharing either.

So the term route has a **structural** cost — the bound path runs through `Term`, and every
step of exposing a `Term`'s constructors to the kernel costs renaming traffic — independent of
how big the term ends up. Making the term smaller does not help; not having a term does.

### 14.2 The book's tool, and exactly what it changes

Kohlenbach, *Applied Proof Theory* Ch. 9, Thm 9.1 (pp. 141–145). The monotone functional
interpretation (MFI) proves `∃x (t* maj x ∧ ∀a,y A_D(x a, y, a))`: the extracted datum is the
**majorant `t*`**; the realizer `x` is existential. Its proof (p. 142) is explicit about the
division of labour, and we follow it exactly:

- **Leaves (axioms), including the Δ-axioms**: take Dialectica's closed realizer and majorize
  it by "every closed term is majorizable" — Howard's Prop. 6.6, our `termMajorizer_maj`.
  Nothing changes here; leaf realizers are fixed-size combinators.
- **Rules (MP, syllogism, …), p. 144 case 5**: the majorant is *composed from the
  sub-majorants* — `t*_4 := λa. t*_3 (t*_1 a)`. Never the composed realizer.
- **`A → A∧A`, p. 143 case 1**: `t*_Y := λ… max(y', y'')`. The book calls contraction "by far
  the most complicated axiom" for the usual interpretation; the monotone one is a `max`. This
  is our `sAndContract`, which branches on `matrixTerm` — the one combinator that flips
  `ConjBoundDemo` from reducing to stuck.
- **Induction, p. 144 case 7**: `t* := t^M`, a `max`-recursion. This is `sInduction`, Track A
  item 2.

MFI does **not** remove composition's duplication — case 5's counter side still mentions the
sub-majorants more than once; on paper that is free because terms are DAGs by notation.
What removes it *for us* is the second decision:

### 14.3 The decision: majorants are semantic values at the hat type

`Ty.hat` sends `base _ ↦ nat` and is homomorphic on `→`/`×`, so `Ty.interpret X ρ.hat` is
built from `ℕ`, `unit`, `×`, `→` and **never mentions the carrier**, at any `ι`. Therefore the
majorant can be a **Lean value**, not a `Term`:

```
MRealizer cm A :=
  { tstar : ℕ → Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X (wTy A).hat //
    ∃ x : (Ctx.interpret X Γ → 𝕎 X A),                       -- one functional of the env
      (∀ env y, dialecticaMatrix si A env (x env) y) ∧
      (∀ n ≥ am.N, ∀ env* env, MajEnv am Γ env* env → am.maj _ (tstar n env*) (x env)) ∧
      (self-majorization of tstar in its hat environment) }
```

— `termMajorizer_maj`'s statement lifted from terms to derivations. Consequences:

- **No `Term` on the bound path.** No `weaken`, no `rename`, no `Var`, no cast from a term
  index. What remains is the recursion over the derivation (`Derivable.rec ↦ 27` in the same
  profile that had `Eq.rec ↦ 16074`).
- **Evaluation of `Φ x*` is natural-number arithmetic** — `max`, `+`, `Nat.rec`, composition —
  which the kernel accelerates and `decide` closes.
- **Duplication becomes benign**: the kernel's `Expr` is a DAG with a `whnf` cache keyed on
  the expression, and `#eval` shares outright. Three mentions of a sub-majorant at the same
  argument are one computation.
- **Both engines open**: `#eval` for a number instantly with compiler trust, `decide` for the
  kernel certificate.
- **Cost**: the majorant is not syntax. Reification back to `Term F [] ρ.hat` for printing is
  a later metaprogram over a *named* combinator vocabulary (`majMax`, `majComp`, `majRec`, the
  `ConstMajorants` fields) — pattern-match on the names, as `#hilbert` does for derivations.
  Build the recursion from named combinators, not inlined lambdas, so that stays cheap.

The metatheorem's *statement* already returns `Φ : Ty.interpret X ρ.hat → Nat`, semantic. So
nothing at the theorem level weakens; only the internal object changes.

### 14.4 What the spike established (gate G0)

`Probes/MonotoneSpike.lean`, nine constructors — exactly `acFinal`'s — at the W-hyperbolic
model with `triCm M h`. **`(1709 : ℕ) = mfiU … (acSpike M h) (5, 9)` by `rfl` in ≈207 ms**,
against 200,000 heartbeats exhausted on the term route; `V` `1709`; `1708`/`1710`/`0`
refuted; `U` at `(5,1)` is `349`; the contraction-free control has no `max` in its normal
form, so the `max` is provably contraction's. Three design facts came out of it:

1. **`MaxCompat` is a genuine field of the majorizability structure.** "`max` of two majorants
   majorizes" needs `maj a c → selfMaj b b → maj (maxT a b) c` and two siblings; the abstract
   structure has no `max`, so they are not derivable from its 20 fields. True of every
   `bezem*` instance. The book has them free because its `maj` is Howard's concrete relation;
   our abstraction must state them. Per the standing check (CLAUDE.md, `EqXInterp` section):
   it is about the relation, all instances satisfy it, none for free — a field.
2. **The realizer's `∃` is hoisted outside the environment quantifier.** The per-environment
   form `∀ env* env, MajEnv → ∃ x, …` cannot close `forall_rule`: the IH supplies realizers only
   at majorized `z`, and one chosen at `z*` need not be majorized by `tstar` at another
   `z'* ≽ z`. `∃ x : env → 𝕎 A` is the book's `(+)` verbatim (`x` a functional of the free
   variables), needs no choice, and is stronger; the per-environment form is a corollary.
3. **A self-majorization conjunct is carried**, as in `termMajorizer_maj`, because
   `arrow_intro`'s second clause at `forall_rule` needs hat-monotonicity of the majorant.

### 14.5 The plan

Additive throughout; nothing existing is deleted until G3.

- **Reused verbatim**: `dialectica_soundness_ctx'` and all of `Lemmas.lean` (the existential
  `x`), `termMajorizer`/`closedMajorizer`/`ConstMajorants` (the leaf case), the `wapp_*`/
  `capp_*` lemmas of `SeqMpBoundProbe`/`CounterSideProbe`/`CombinatorLemmas` (they *are* the
  rule cases, promoted out of `Probes/`), `general_metatheorem_extract` (the semantic
  extraction half — vestigial until now because nothing could majorize semantic `U V`; MFI is
  precisely what does), `metatheorem_core_of_majorants_at` (unchanged), `extractTerm` and the
  printers (realizer syntax on demand).
- **Lane A** — `Dialectica/Monotone.lean`: `MaxCompat` promoted into `AbstractMajorizability`,
  the 27 remaining cases (leaf strategy for axioms incl. `markov`/`ip`/`ac`/`qfac`;
  composition for `importation`/`expansion`/`exist_rule`/`univ_gen`/`qfer`; `max` for
  `or_contract`/`or_perm`), `premise` via `srealizer_of_pu_val`'s default term. **Gate G1**:
  `tFinalTwice`'s `U` is a genuine `max(1709, 901)` that crosses over between `(5,9)` and
  `(5,1)`.
- **Lane B** — `induction` as the book's `t^M` (`Nat.rec` with `max`; the one case with real
  content, review by hand), and `monotone_general_metatheorem_at` = `general_metatheorem_extract`
  + MFI projections + `metatheorem_core_of_majorants_at`; the `∃`/`_at` split collapses since
  `cm` is an input. **Gate G2**: `dist_tri_chain`'s `Φ` — the first bound from a proof with
  content, and where the `pm_*` unfolding cost gets measured on the new recursion.
- **G3**: `mct_p2`'s `Φ`, named and evaluated, against `Reference/MCT.lean` via the `K := 2^k`
  bridge. Then the term-route `_at` entry points are retired.
- **Explicitly out of scope**: the classical route's ×230 from `negTrans_sound` — a fix to the
  translation, not to the interpretation (§14.1, second row).

**Status of the plan (2026-09-05, after Lanes A and B).** Lane A: `Monotone.lean`, every
constructor, G1 passed (`Probes/MonotoneLaneA.lean`). Lane B: `MonotoneMetatheorem.lean`
(`monotone_general_metatheorem_at`, `_at_gen`; `mfi_extract_core` is the extraction half over
an abstract `MRealizer`, and `general_metatheorem_extract` turned out not to be the right
reuse — it fixes the realizer, the MFI's is existential), `Probes/MonotoneLaneB.lean` (G2),
`Probes/MonotoneMCT.lean` (G3; `mct_bound_p2_at`, `mctPhi` named). **G2 and G3 both stop at
the same node, and it is neither the recursion nor the proof mode nor induction**: the
proof-mode layer reduces in the *kernel* (449-constructor derivation, counter side, ≈2 s;
Meta `rfl` is the wrong instrument at a space — no `whnf` cache with free `M`, `h`), and the
`induction` case reduces on a real `pinduction` (`V(5)=5`, `V(9)=9` through `recMaj`). What
stops is every `Eq.mpr`/`seq_cast` whose equation is a `closed_subst`/`anorm` normalisation:
the kernel's K-rule reduction must check the two formula indices definitionally equal, i.e.
compute `Term.subst` through `cauchyfy` (G2, `le_R_pu_of_le_R`'s one `canorm`, 12 GB) or
through `Term.ofNat`/`monus` per hypothesis per cast (G3, `mct_descent`). That is the
delta-expansion pathology of "Build cost" reappearing as a *cast*, one level up: the lemma
that avoided the computation produces the cast that forces it. **So the next item is not in
§14's list**: an `Eq.mpr`-commutation lemma for `monotone_soundness` (the
`syntactic_soundness_eqmpr` shape) applied by `simp` with the equation given, so casts are
rewritten and never reduced — the `wit_seq_*` programme one level up, or `canorm`-free
proof-mode lemmas. Until then the term-route `_at` entry points stay. The CLAUDE.md entry
has the numbers. Note also that this file carries **two** `## 14` headings; the second (from
"what the bound path should be") is a truncated partial duplicate of this one and ends
mid-sentence — left as found, to be resolved by the owner.

**Lane B' (2026-09-05): the `Eq.mpr` entry is written and proven** — `Dialectica/MonotoneMemo.lean`:
`MRealizer.transport` (axiom-free) plus `monotone_soundness_eqmpr`/`_eqmp`/`_subst`, the MFI
analogue of `syntactic_soundness_eqmpr`. The transport casts the majorant `tstar` by
`congrArg wTy h` — whose two sides are `Ty.interpret X (wTy B).hat`/`(wTy B').hat`, definitionally
equal for a `subst`/`rename` normalisation (`wTy` ignores a formula's terms), so it collapses
structurally with no ℚ delta; the `Prop` half goes by `subst h`. **It reduces a real ℚ cast to a
numeral where `monotone_soundness` meets `Eq.mpr`/`Eq.mp` directly** — `Probes/MonotoneLaneBp.lean`
`castU`: `U = 901` (moving to `1273` at `x* = 7`) through **two** injected `mul_Q` `Eq.mp` casts on
the premise-consuming counter path, via `simp only [monotone_soundness_eqmp (hB := …)]` + the
kernel. Measured: bare `kernel_rfl` on **one** directly-injected cast *terminates* — `mul_Q` ≈8 s,
`cauchyfy` ≈37 s: a single cast is a **linear** `Term.subst` delta, and the entry turns it O(1).
**What the entry does NOT reach**: the casts of the real ℝ lemmas (`le_R_pu_of_le_R`, `leR_tail`,
`mct_body`, …) are buried under the `pm_*`/`seq_*` layer, so `monotone_soundness` is applied to a
`pm_*` def, not to the cast; `simp` cannot fire the memo lemma without unfolding that layer, which
explodes (`le_R_of_le_R_pu` is 4167 constructors — `simp`+`kernel_rfl` OOMs at 12 GB, measured).
Reaching them needs the MRealizer analogues of `CombinatorLemmas`' `wit_seq_*` (the counter-side
commutation programme) — the entry here is that programme's missing *bridge*, not the programme.
**Part C0** (`Probes/ClassicalMfiProbe.lean`): the composed classical route under MFI type-checks
in ≈4 s (85,180 constructors, no realizer term built — unlike the term route which OOMs `#eval`
building it), but *reducing* the `U`/`V` projection through it is `std::bad_alloc` at 12 GB (≈47 s):
MFI clears the per-cast cost, not `negTrans_sound`'s ×230 per-node blowup. Lane B's "minutes, not
OOM" prediction was optimistic; the wall is the translation layer (§14.5 "out of scope"), moved
from elaboration to kernel reduction. No `main` change; headline axioms unchanged.

**Lane C (2026-09-05): the fused NT+MFI recursion — the classical route is now IN scope, and
the NT-stability condition disappears.** §14.5 listed "the classical route's ×230 from
`negTrans_sound`" as *explicitly out of scope* because it is "a fix to the translation, not to
the interpretation." Lane C makes that fix: `Dialectica/MonotoneND.lean`'s `monotone_nd_soundness`
interprets a **classical** derivation directly into `MRealizer cm Aᴺᵀ`, so the 85,180-node
`negTrans_sound` output is never built. The recursion mirrors `negTrans_sound` arm for arm: the
fixed `¬¬`-combinators it inlines per node are **hand-written monotone realizers**
(`Dialectica/MonotoneNDLeaves.lean`: `dnnIntroF`, `nnMpF`, `nnImpRevF`, `expF`, `impF`,
`expansionF`, `dnnLemF`, `nnAllNnF`; explicit hat-level majorants, `Prop` halves by the
`maj_auto` dispatcher — `leafM = ofSRealizer ∘ syntactic_soundness` remains only for axiom
terms), recursive results compose with Lane A's `MRealizer.mp`/`.syllogism`/… ,
and the eigenvariable/QF-ER/induction cases go through `MRealizer.forallRule`/`existRule`/
`univGen`/`qfer`/`induction` (`ndForallRule`/…/`ndInduction`). The consequence worth keeping:
**NT-stability vanishes.** `negTrans_sound` needs `nts : NTStableD Premises` because its premise
case is `.mp (.premise hp) (nts _ _ hp)`; here the premise case takes an `MRealizer cm Bᴺᵀ`
*directly* (`spremise_nd`), so no condition on the premise set is needed at all — and this was
the last consumer of the `isPurelyUniversal`-on-`Derivable.premise` idea (note 1). For purely
universal premise sets (every space axiom) `spremise_nd_of_pu` supplies `spremise_nd` from the
existing `spremise` through `negTrans_iff_pu`, so the space models add nothing.
`MonotoneMetatheoremClassical.lean`'s `monotone_general_metatheorem_classical_at` routes
`prenexify` → `monotone_nd_soundness` → `nn_all_nn` → the `¬¬∃u∃v` projection
(`mfi_extract_classical`, peeling the surviving `¬¬` as `extraction_of_prenex_realizer` does) →
`metatheorem_core_of_majorants_at`, SAME statement as the term-route classical metatheorem, all
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. So the classical bound no longer OOMs
at ELABORATION. **But the numeral REDUCTION still OOMs** (gate G-C1/G-C2, `Probes/ClassicalMfiProbe.lean`):
`std::bad_alloc` at 12 GB. The first pass attributed this to "`prenexify` + the `¬¬`-combinator
leaves"; hand-writing every leaf left the OOM unchanged, so that was wrong. Measured with the
leaves hand-written: `lFinalNoLem` alone through the fused recursion reduces in 37 ms;
`prenexify` alone (134 `syllogism`s) OOMs; a bare chain of k classical `syllogism`s grows ≈ ×5
per syllogism (k=2 140 ms, k=4 3.7 s, k=8 OOM). The wall is §14.2's own caveat — MFI does not
remove composition's duplication — realised as the counter-side fan-out of nested `syllogism`s
under the `¬¬`-combinators, with kernel `whnf` sharing nothing across binder depths. The
compiled evaluator (`#eval` of the hat-level ℕ) hits the same wall earlier (k ≤ 2 instant,
k=3 no result in 400 s, CPU-bound), because call-by-value shares values, not the re-evaluated
applications inside composed closures. Control: the same 12-node derivation at
`Allowed.extended` under MFI, *without* prenexify/NT, reduces to `U=0`, `V=5` in ≈17 s
(`extU5`/`extV5`, PASS). Making the classical numeral reduce needs a majorant representation
with explicit sharing (Lane D1's memo direction), the new "out of scope".

### 14.6 What this does to earlier decisions

The design table's "Dialectica realizer: Subtype, not `∃`, so the witness is extractable"
stays true and stops being the *bound's* mechanism. The realizer remains available as a term
via `extractTerm` for anyone who wants it; the bound no longer waits for it. The
`syntactic-witnesses` merge (realizers as `Term`s so `all_closed_terms_majorizable` applies)
was the right move for what it bought — majorants without a total majorizer — and MFI is the
same idea one level up: majorants from the *derivation's* syntax rather than the *term's*,
which is why `general_metatheorem`'s original shape comes back into use.

### 14.7 Status (2026-09-05, evening) — where the MFI work lives and what it has shown

The refactor was built on an integration branch `mfi` and **merged into `main` on 2026-09-06**
(as work in progress; the original gate — a bound with mathematical content reducing — was
not reached); the per-lane record is in `CLAUDE.md` ("MFI Lane A/B/B'/C/D1"). Landed: Lane A (full `monotone_soundness`, all
39 constructors, `MaxCompat` as fields, gate G1 — the `and_contract` crossover `max(1709, 901)`
by `rfl`), Lane B (`monotone_general_metatheorem_at`/`_gen`; a cast-free proof-mode derivation
at a space gives `U = V = Φ = 901` in the kernel; `pinduction` reduces through the book's
`t^M`), Lane B' (`MRealizer.transport`, the `Eq.mpr` entry; a directly reachable ℚ cast
reduces to a numeral), Lane C (the fused NT+MFI recursion `monotone_nd_soundness` on classical
derivations and `monotone_general_metatheorem_classical_at`; NT-stability is no longer needed
because the premise case takes an `MRealizer` at `Bᴺᵀ`), and Lane D1 (`mfi_memo`: the
`seq_*`-layer commutation entries — `seq_of_thm`/`seq_mp`/`seq_id`/`seq_allI`/`seq_induction`,
all Δ-generic — which push `monotone_soundness` through a whole proof-mode derivation to its
casts: `le_R_of_le_R_pu`, 4167 constructors and 180 casts, gives its counter read-out `3` in
13.5 s of kernel time). So the cast obstacle is cleared, and **one obstacle remains**, named by
measurement from both sides (Lane C on the classical route, Lane D1 on the intuitionistic):
**the composition combinators re-evaluate their sub-majorants** —
`MRealizer.syllogism` uses `hAB.val n e` three times and `hBC.val n e` twice, and neither the
kernel nor the compiled evaluator shares them, so nested syllogisms cost ×5 per level (kernel
dies at ≈8, evaluator at 3). That is the Dialectica exponential in its
last hiding place, and it applies to every route equally; §14.1's "×230 from `negTrans_sound`"
is a linear factor that fusion removed and that was invisible behind it.

**The cost is exponential in composition DEPTH, and this paragraph used to quote a COUNT.** It
said "`prenexify` has 134", against a wall at ≈8, which made the gap look hopeless. 134 is
`prenexify`'s *number* of `syllogism`s; the ×5 compounds along the longest **path** through
composition nodes, and that depth is **9** — measured 2026-09-06 by `Probes/NestingDepth.lean`
(branch `sharing`), an `Expr` DAG walk memoised on `ExprStructEq` with no `whnf`. See §14.8 for
the table and for what the measurement cost the `let`-sharing plan.

### 14.8 What the 2026-09-06 lanes measured — depth, sharing, and a second wall

Four lanes ran overnight on branches off `6abbfc4`. **As written, none is merged**; each result
below names the branch that carries its probe, and this section should be re-read when they
land. All four were verified in their own worktrees by a no-op rebuild of both targets plus
`#print axioms` by name, per the "verify before relaying" rule.

**1. Composition depth, not count (`sharing`, `Probes/NestingDepth.lean`).** The longest path
through composition nodes, memoised on `ExprStructEq`, no `whnf`:

| derivation | DAG | tree | **depth** |
|---|---|---|---|
| `prenexify` | 252 | 253 | **9** |
| `classical_to_prenex_extended` | 3434 | 3435 | 11 |
| `ConjBoundDemo.acFinal` | 13 | 13 | 4 |
| `MonotoneLaneB.pmFinal` | 202 | 527 | 4 |
| `le_R_of_le_R_pu` | 403 | 893 | 7 |
| `ProofMode.mct_p2` | 7244 | 84335 | **12** |
| `le_R_trans_core`, `dist_tri_chain`, `real_mct_p2` | ≥47938 | ≥58559 | **≥23** (budget hit) |

Against a wall at ≈8 that makes ℕ-MCT ≈5³ away and ℝ-MCT ≈5¹⁴ — a finite engineering target,
where 5¹³⁴ was not. This is the single most useful number the MFI programme has produced, and
it cost one probe; **measure depth before estimating any composition cost.**

**2. The `let`-sharing hypothesis is REFUTED (`sharing`, `Probes/SharingProbe.lean`).** Binding
each sub-majorant with `let` in `MRealizer.syllogism` changes nothing: ×3.7 per level before
and after, `std::bad_alloc` at k=6 both ways. **The kernel zeta-reduces `let` by substitution**,
so sharing at a binding site never survives to the reduction that matters; the compiled
evaluator already shared closure results by pointer. The cost is per *application* at differing
arguments, so a fix must change **what is applied**: staged evaluation with per-stage literal
reification (~12 stages for ℕ-MCT, ~23 for ℝ-MCT), or an `MRealizer` redesign whose counter
component does not call the witness component. Do not re-propose `let`-binding; it is measured.

**3. A SECOND wall, independent of depth: the VALUE (`examples`,
`Probes/ContentExampleNat.lean`).** On one fixed 145-constructor derivation, `V = 128` is
kernel-checked in ≈9 s and `V = 256` OOMs at 12 GB. `Term.add`'s majorant is a `prec`, so
`recMaj` iterates **value-many** times without sharing. So extraction is bounded from two
directions at once — composition depth and the magnitude of the number being computed — and the
second was not on any list before this. Any bound whose value is large is out of reach even
from a shallow derivation.

**4. The proof mode can itself be the wall (`examples`).** The *same theorem by the same
argument*, written in the proof mode, is **42,729** constructors against the raw derivation's
145 — a factor of 295 — and reduces only at `k = 0`. §14.7's cast story (Lane D1) clears the
`Eq.mpr` obstacle but not this one.

**5. The first bound with mathematical content (`examples`).** `∀x(∀u (f(Su) =₀ f u +ᵗ f u) →
∃v (f k =₀ v))` at `x = (k,f)`, by raw `Derivable.induction`, the witness at each step built
from the induction hypothesis's witness: `V = 2^k·f(0)`, kernel-checked at four points, moving
with **both** components, `U(k) = k−1` sharp, six refutation controls, and the term route
independently agreeing on `V`. Note what carries the content: the *theorem* `∃v (f k =₀ v)` is
trivial, and the **bound** is the mathematics — `f k ≤ 2^k f(0)`. That is the project's
"bounds are properties of proofs, not theorems" thesis with a number attached rather than the
`mct_p1`/`mct_p2` contrast.

**6. W-hyperbolic derived lemmas (`whyp`, `Metatheorems/WHyperbolicLemmas.lean`).** The four
axioms usable at arbitrary terms, then `d(x, W(x,y,λ)) ≤ λ·d(x,y)` and its mirror, the reverse
inequality, `W(x,y,0) = x`, `W(x,y,1) = y`, nonexpansiveness in each argument, (W2) as an
equality — all `[propext, Quot.sound]`, each read back in an arbitrary `WHyperbolicModel`. It
stops at a **named gap**: multiplicative monotonicity of `≤ℝ` does not exist and is not
derivable from what does, because the obvious route needs a `·ℝ`-congruence that *is* that
monotonicity. The equality forms stop one step short for that reason and say so.
