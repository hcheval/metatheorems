# Probes/MonotoneSpike.lean

## module header

**STATUS (2026-09-05, Lane A): the recursion has moved into the library.** What this file
used to define — `MRealizer`, `MaxCompat`, the nine combinators, `monotone_spike`, `mfiU`/
`mfiV`, `maxT_comm`, `bezemMaxCompat` — now lives in `Metatheorems/Dialectica/Monotone.lean`
(`monotone_soundness`, every constructor, no fallback), `Metatheorems/Majorizability.lean`
(`MaxCompat`'s three facts are fields of `AbstractMajorizability`, discharged in
`bezemAbstract` from a `BaseMono` hypothesis) and `Metatheorems/MajorizabilityRel.lean`
(`maxT_comm`). This file keeps its header as the record of the spike, and **re-runs its
gate against the library recursion** — same statements, same numbers, same normal forms —
so that nothing regressed in the move. The full-recursion gate G1 (`tFinalTwice`, a genuine
crossing `max`) is `Probes/MonotoneLaneA.lean`.

The header below is the spike's, kept verbatim for the record except where marked.

---

## The definition (`MRealizer`) — now `Metatheorems.MRealizer`

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

## The nine cases (the spike's), and the fallback it had

| constructor | strategy | majorant |
|---|---|---|
| `and_weak`, `forall_ax`, `exist_ax`, `refl0` | leaf (Howard, p. 142) | `termMajorizer cm (s…).val` |
| `mp` | composition (p. 144 case 5) | `t₂*.1 t₁*` |
| `syllogism` | composition | `(λx. bc.1 (ab.1 x), λx y. ab.2 x (bc.2 (ab.1 x) y))` |
| `exportation` | composition | currying of the sub-majorant |
| `forall_rule` | composition (p. 144 case 6) | `λxB z. (h*(z,e)).1 xB` …, via `arrow_intro` |
| **`and_contract`** | **p. 143 case 1** | `(λx.(x,x), λx y. maxT (cTy A) y.1 y.2)` |

The spike sent every other constructor to a fallback (the leaf strategy on the whole
sub-derivation). **The library recursion has no fallback**: see `Dialectica/Monotone.lean`'s
header for the strategy of each of the remaining constructors.

`and_contract` needs `maj ρ (maxT ρ a b) c` from `maj ρ a c` (or `b c`) plus self-majorization
of the other argument, and a `maxT` congruence for `selfMaj`, at every hat type. The abstract
`am.maj` has no `max`, so those three facts were packaged here as `MaxCompat am`; **they are
now the fields `maxT_maj_left`/`maxT_maj_right`/`maxT_selfMaj` of `AbstractMajorizability`**,
discharged in `bezemAbstract` from `maxT_bezemMaj_left` / `maxT_hatMaj` / `maxT_comm` and a
`BaseMono` hypothesis (which every instance already had).

## Gate: measured (spike, 2026-09-05; re-run against the library below)

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

Non-vacuity: `mfi_acFinal_U_ne_1708`, `_ne_1710`, `_ne_zero` are the permanent refutations; the
live `1708` control (spike, 2026-09-05) failed at `decide` with the proposition exhibited, so
the `rfl` genuinely reduces (trap 12 excluded).
