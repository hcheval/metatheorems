# Where the extraction examples are

An index of every derivation this project extracts a bound from, and every measured negative
result. Built 2026-09-08 by scanning `Metatheorems/Probes/` for numeral-asserting theorems,
not from memory.

**Every row is a theorem in the file named**, accepted by the kernel. Nothing here is a
`#eval` — see "How to read a bound" below for why that matters.

---

## How to read a bound

A number on its own means nothing. Every bound in this project should be read along five
axes, and the last one disqualifies several of them as headline material:

| axis | question |
|---|---|
| **statement** | which theorem |
| **proof** | which derivation — several statements below have two |
| **route** | term route / MFI / classical |
| **presentation** | evaluated at a point, kernel-checked symbolic form, or object-level `Term` |
| **at which point** | the majorants `x*`, spelled out |
| **denotation** | is the number a *magnitude* or a *code*? |

On that last axis: `Rounding.pairN a b = triagN (a+b) + a` is Cantor pairing, so a bound that
routes through the ℚ/ℝ encoding comes out as a **pairing code**, not a size. `901` is
`pairN(40,1) = triag(41) + 40`. Comparisons between such numbers (`1709` vs `901`) are
comparisons of encoded rationals and carry no mathematical ordering. Prefer bounds that are
magnitudes, that move with their inputs, or that are presented symbolically.

---

## 1. The examples worth showing

### 1.1 One statement, two proofs, different growth — at `ι = Empty`

The clearest demonstration that **bounds are properties of proofs, not theorems**.

Statement: `∀x (∀u (f (S u) =₀ f u +ᵗ f u) → ∃v (f k =₀ v))`, `x = (k, f)` —
*if `f` doubles at every step, then `f k` is bounded*.

| proof | `V` at `k* = 0,3,5,7` | reads as | file |
|---|---|---|---|
| raw `Derivable.induction`, witness `w ↦ w +ᵗ w` | 1, 8, 32, 128 | **`2^k · f*(0)`** | `Probes/ContentExampleNat.lean` (`V_at_0/3/5/7`) |
| same, with `f = λn.n+3` | 3 at `k*=0`, 12 at `k*=2` | `2^k · f*(0)`, moving in `f*` | `V_ys_at_0`, `V_ys_at_2` |

`U(k*) = k* − 1` and is **sharp** — the step at `k` instantiates the premise at `u := k`
(`U_at_0/1/2/3/5` = 0, 0, 1, 2, 4). So `U` is "how far into `∀u B₀` the proof reaches", a
genuine function of `x*`, not a copy of `V`.

**Why exponential.** Dialectica interprets `Derivable.induction` as primitive recursion
(`MRealizer.induction` = `cm.precM` = `recMaj`, Kohlenbach's `t^M`). The witness at step `k+1`
is built *from* the witness at `k`, so the recursion iterates and the doubling in the proof
becomes an exponential in the bound. It is **tight**: `2^k·f(0)` is exactly `f k`.

**The control that makes it a demonstration.** `Probes/MonotoneMCT.lean` (`indFinal`) uses the
*same induction rule* and gets `V(k) = k` — linear — because there the witness is the
induction variable itself, a projection, so nothing iterates.

> Same rule, two proofs. One bound linear, one exponential.

Also recorded there: the surface-recursor ban means **no hand-written witness term mentions
`Term.prec`**, so the iteration is produced by the extraction, not smuggled in.

### 1.2 The same contrast, at a space

`Probes/ContentExampleSpace.lean` — one statement, two proofs, over an arbitrary model with
`M` and `h` free:

| proof | `V` | depends on |
|---|---|---|
| `rRec` (recursive) | 1, 8, 32 at `k* = 0,3,5` | the **index** `k*` — and *not* on the first component (`Vrec3b` at `(7,5,3)` is still 8) |
| `rDir` (direct) | 901 at `(5,5,0)`, 1273 at `(7,5,0)` | the **point** `x*` — and not on `k` |

Two proofs of one statement whose bounds depend on *different inputs*. The `rDir` numbers are
pairing codes; the `rRec` ones are magnitudes.

### 1.3 A bound as syntax, not as a number

- `Probes/MonotoneLaneA.lean:177` — the symbolic normal form proved **by `rfl` inside a
  theorem**: nested `max` of `pairN` terms. Kernel-checked as an *equation*, which is stronger
  than a rendering and sidesteps the encoding objection entirely.
- `Probes/ExprBound.lean` — `Φ` displayed as arithmetic by a fuelled `Expr` reducer, with the
  model `M` and `h` absent from the body:
  `fun M h a b ↦ maxT nat (pairN (2 * ((a + b) * 2 ^ (0+1))) (2 ^ (0+1) - 1)) 0`.
  Reproduces 1709 and 349 independently. This is *output*, not an accepted equation — do not
  write it with `=` beside the proved one.
- `Probes/TermPrintDemo.lean` — the realizer as an object-level `Term`, rendered. Five
  realizers, 186–563 nodes; tree/DAG 2.76–3.21 but tree/**written** only 1.00–1.35.

---

## 2. Bounds at a space, uniform in the model

All with `M` (the model) and `h` (the reference-point bound) as free variables, so the numbers
hold of *any* model.

| file | what it adds | numbers |
|---|---|---|
| `Probes/WBoundDemo.lean` | first bound at a space; **witness exhibited outright** | `Φ = 901`, `U = 0` |
| `Probes/UPremiseDemo.lean` | premise genuinely **consumed** (`forall_ax` ⟶ `exist_ax`) | `U = V = 901 / 1273 / 1709` at `x* = 5/7/9` |
| `Probes/TriangleBoundDemo.lean` | first derivation consuming a **space axiom** (`dist_tri`, a free constructor) | `U = V = Φ = 901`; `1273` at `(7,5)` and `(5,7)` |
| `Probes/WExtBoundDemo.lean` | through a **premise** (`WHyperbolic.W2`) and through **derived** extensionality lemmas | `Vax` 901, `Vaxb` 1273; `VextD`/`VextPD` 901 |

`WBoundDemo`'s `U = 0` is *vacuous* — its proof weakens the premise away. `UPremiseDemo` is
the same statement and majorants with only the route through the implication changed, and it
is the honest control: one `ConstMajorants` value yields `0` on one derivation and `901` on
the other.

**Caveat for all of these:** the numbers are pairing codes, and the statements are shallow —
`C := B` in several. They show the *route* carries through to a numeral, not that anything was
mined.

---

## 3. Through the proof mode

| file | derivation | result |
|---|---|---|
| `Probes/MonotoneLaneB.lean` | `pmFinal` — `pforall/pintro/pinst/pexists`, 449 constructors | `U = V = 901` in ≈2 s, **counter side included** |
| | `pmFinalBig` — same over the large `triB` matrix | `U = V = 901` |
| `Probes/MonotoneMCT.lean` | `indFinal` — a real `pinduction` | `V(5) = 5`, `V(9) = 9`, `U = 0` |
| `Probes/MonotoneLaneBp.lean` | `castU` — two ℚ casts injected on a syllogism middle | `U = 901`, `1273` at `x* = 7` |

The term route never produced a counter-side numeral from any proof-mode derivation.

**But the proof mode is a liability at scale.** `ContentExampleNat` records that the
proof-mode form of its exponential argument is **42,747 nodes against 145** (295×) and reduces
only at `k* = 0`.

---

## 4. The measured negative results

These are results, not failures to hide.

| file | finding |
|---|---|
| `Probes/ConjBoundDemo.lean` | **one `and_contract` is the whole cause** of a term-route `whnf` stall. `acFinal` and `tFinalOnce` prove the *same formula*, differ by one `and_contract`/`and_weak` pair, and flip from stuck to reducible. One-sided: the witness side still gives 1709. MFI clears it (`MonotoneSpike`). |
| `Probes/LemBoundDemo.lean` | **no bound has ever come out of the classical route.** `lFinalExt` and `lFinalNoLem` are *the same derivation term at two `Allowed` values*; the extended one gives `U=0, V=5`, the classical one does not reduce. So the cost is classicality's *plumbing*, not excluded middle. |
| `Probes/ClassicalMfiProbe.lean` | the fused NT+MFI route type-checks in ≈4 s but `std::bad_alloc` at 12 GB when reduced. `prenexify` alone OOMs. |
| `Probes/SizeProbe.lean` | the classical route hands Dialectica **85,180 constructors** from a 12-constructor derivation; `negTrans_sound` is 363 → 84,905 of it. Also: the compiled evaluator preserves **no** sharing. |
| `Probes/NestingDepth.lean` | composition depth, not count. **Caveat: rows marked "budget hit" are lower bounds** — the walk is capped at 250,000 `Expr` nodes and three different declarations all report ≥23, so those are the cap, not a measurement. |
| `Probes/SharingProbe.lean` | the sub-majorant re-evaluation in `MRealizer.syllogism`, which is the blocker shared by the flagship bound and the classical route. |

Two ceilings worth knowing before a live demo:

- **The value, not the proof.** On the *same* 145-constructor derivation, `V = 128` (`k* = 7`)
  is kernel-checked in ≈9 s and `V = 256` (`k* = 8`) is a 12 GB OOM. `recMaj` iterates
  value-many times with nothing shared.
- **`whnf` cannot be measured by goal size.** `ConjBoundDemo`'s stalling and reducing goals are
  both 70/12 objects.

---

## 5. Scaffolding, not results

`P1`, `R1`, `RwBase`, `RwArrow`, `BoundProbe`, `SoundnessProbe`, `SeqMpBoundProbe`,
`CounterSideProbe`, `CombinatorLemmas`, `MonotoneMemoGates` — machinery checks and lemma
libraries. `CounterSideProbe` holds the project's only permitted `sorry`s and is deliberately
absent from the sweep.

---

## 6. Instruments

- **`kernel_rfl` is the evaluator of record**, not `#eval` and not bare `rfl`. With `M` and `h`
  free, `Meta.whnf` has no cache and times out where the kernel succeeds in a second.
- **`#eval` is never how a bound is obtained.** It is used only for measurements *about*
  extracted objects (sizes, timings). Nothing here rests on compiler trust.
- Every numeral has a **refutation control** — a theorem that the neighbouring value is *not*
  the bound (`V_at_3_ne_7`, `Udir_ne_900`, …), which is what proves the `rfl` computes rather
  than stalls.
