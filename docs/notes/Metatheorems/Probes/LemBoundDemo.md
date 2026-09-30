# Probes/LemBoundDemo.lean

## module header

### Why the LEM has to sit at a quantified formula

`Arithmetic.qf_lem` derives `A ∨ᶠ ¬ᶠA` for **quantifier-free** `A` with no appeal to
`Derivable.lem` at all — QF matrices are decidable in the object theory, and that is a
theorem, not an assumption. So a case distinction on the *matrix* is free, and putting one in
would produce a derivation that lives at `Allowed.extended` and tells us nothing about the
classical route.

The minimal genuinely-non-QF instance available in the metatheorem's own shape
`∀x (∀u B₀ → ∃v C₀)` is LEM at the **Π₁ premise** `∀u B₀`. That is what `lemStep` below uses,
and it is the whole difference between the two derivations in this file.

### The controlled contrast (continued)

They differ by exactly the LEM step: `lInnerLem` is `Derivable.mp lLem (or_elim_rule lCaseL
lCaseR)` where `lCaseL` is `lInner` weakened and `lCaseR` is pure ex-falso plumbing. Same
formula, same model, same majorants — so any difference in the extracted `U`/`V` is a
property of *the proof's use of excluded middle* and of nothing else.

and a third derivation, `lFinalExt`, which is **the same term as `lFinalNoLem` at a different
`Allowed` value** — `lExD`/`lInner`/`close` are all generic in `al` — so the intuitionistic
and classical *routes* are compared on literally one proof.

This is the discipline `TriangleBoundDemo`'s review established: when comparing two
extractions, hold the premise **formula** fixed, not merely the conclusion. Here it is held
fixed twice over — same formula, and for two of the three, same derivation term.

### THE RESULT — a negative one, and excluded middle is NOT the cause

The classical route **does not reduce to a numeral, on the smallest derivation that exists.**
The bound `rfl` — `(0 : Nat) = closedMajorizer lCmE lUtNoLem 5` — is a
`(deterministic) timeout at whnf`, with no limit raised. There are therefore no numeral
theorems for the classical extractors in this file; a file of `whnf` timeouts is not a green
build. The verbatim reproduction is at the bottom of this docstring.

**A measurement error, recorded because the rule it broke is this project's own.** The first
pass reported instead that `#eval lTermSize` OOMs at 12 GB and still OOMs at 20 GB, and
concluded from that. `lTermSize` is a structural tree traversal, i.e. exactly
`sizeWithoutSharing` — which CLAUDE.md's Track A item 1 bans in favour of `Expr.numObjs`,
because the measured tree/DAG ratio in this project is ≈10⁵. So that OOM is a fact about the
*tree*, which was already known to be astronomical, and it says nothing about whether the
bound reduces. The kernel's `whnf` caches where `#eval` does not, so they are different
engines and only the `rfl` is evidence. The OOM figures are kept out of the table below for
that reason.

**But `lUtNoLem` uses no LEM.** It is `close lInner`, the same term as the control. So the
cost is the *route* — `classical_to_prenex_extended` (prenexify → negative translation →
`nn_all_nn`) followed by Dialectica on the resulting `¬¬` formula — and not the excluded
middle. Putting a `Derivable.lem` in makes no observable difference because the route is
already past the ceiling without one. That is worth stating plainly: **this file set out to
measure the price of excluded middle and instead measured the price of classicality's
*plumbing*, which dominates it.**

The control in the same file, same model, same `bezemConstMajorantsEmpty`:

| route | derivation | `U` at `x*=5` | `V` at `x*=5` |
|---|---|---|---|
| extended (`…_metatheorem_at`) | `lFinalExt` | **0** (`rfl`) | **5** (`rfl`) |
| classical (`…_classical_at`) | `lFinalNoLem` | `whnf` timeout | `whnf` timeout |
| classical, with LEM | `lFinalLem` | `whnf` timeout | `whnf` timeout |

`lVtExt_at_5_ne_4` is the non-degeneracy control for the two that do reduce (trap 12: a `rfl`
where both sides stick at a common point proves nothing).

### Where the stall actually is — measured, not guessed

`set_option diagnostics true` on the stalling `rfl`. **Read this at threshold 5, not 500** —
the first pass of this analysis used 500, concluded from the resulting top-three that "nothing
from the negative translation appears at all, `whnf` never gets that far", and wrote that into
this file and into CLAUDE.md. It was false: the machinery was there, under the threshold. A
filtered view is not a small view of the truth, it is a different claim.

The full profile (threshold 5):

    Eq.rec ↦ 6312        Term.rec ↦ 1985       Term.rename ↦ 1930
    Formula.rec ↦ 138    Term.weaken ↦ 132     Formula.neg ↦ 74
    wTy ↦ 59             termMajorizer ↦ 55    cTy ↦ 43
    Formula.renameF ↦ 36 Derivable.rec ↦ 27    Derivable.castAllowed ↦ 18
    Formula.weakenBy ↦ 18  SRealizer ↦ 9       syntactic_soundness ↦ 9
    SRealizer.imp ↦ 7

**What this actually says.** `whnf` *is* inside `syntactic_soundness`'s recursion — and it has
managed **9 unfoldings of it, 27 of `Derivable.rec`**, before exhausting the entire
200,000-heartbeat budget. So the stall is not "before the translation" and not "at the
translation"; it is an enormous **per-derivation-node** cost: roughly 700 `Eq.rec` and 215
`Term.rename` for each single step of the soundness recursion. The derivation is walked at
about nine nodes per full heartbeat budget.

**`Derivable.castAllowed ↦ 18` is classicality-specific** — it is step 4 of
`classical_to_prenex_extended`, the `Allowed.classical → Allowed.extended` cast, and it
rebuilds the derivation as it goes. So the claim this file previously made, that the classical
route carries *no* classicality-specific cost, is **not supported**; that machinery is in the
profile.

**The shared-blocker guess is REFUTED, by the obvious discriminating test.** The top-three
signature does resemble the Stage-B stall of CLAUDE.md's Track A item 1
(`Eq.rec ↦ 60474`, `Term.rec ↦ 10847`, `Term.rename ↦ 10504`), and this file briefly argued
from that resemblance that one fix would unblock both. But `Eq.rec` is generic — essentially
every dependent reduction routes through it — so a shared profile is weak evidence of a
shared cause. The test that separates them is **sidedness**:

- The intuitionistic stall is **one-sided**. `ConjBoundDemo.cVtTwice_at_5_9` evaluates the
  *witness* functional `V` of the stalling two-instantiation derivation to a literal `1709`;
  only the counter side sticks. `SeqMpBoundProbe`'s three commutation lemmas are likewise
  witness-path only, and its header says so explicitly: the counter components "were not
  touched, and that is exactly where the duplication lives".
- The classical stall is **two-sided**. `(5 : Nat) = closedMajorizer lCmE lVtNoLem 5` — the
  *witness* side, LEM-free — is also a `whnf` timeout.

So the classical route costs something the counter-side debt does not explain, and paying that
debt should not be expected to unblock it. `Derivable.castAllowed ↦ 18` in the profile is a
concrete candidate for the difference, since it rebuilds the whole derivation; that is a
hypothesis and has not been tested.

The type level is **not** the explanation, and that part was checked: `tySize (wTy stmt) = 19`
against `tySize (wTy pstmt') = 93`, `cTy` 7 against 39 — a factor of ≈5, nothing.

**And note what has NOT been tried here: the technique that actually works.** A bare `rfl` is
not how this project has ever extracted a numeral from a large term. `seq_mp_11_numeral`
(`Probes/SeqMpBoundProbe.lean`) produces a kernel-checked literal from a term measured at
≈7×10¹² nodes at context depth 11 — via a **simp set of commutation lemmas**, so the term is
never materialized at all. Everything above is evidence about `rfl`, and `rfl` is known to be
the wrong instrument at this scale. Before drawing any conclusion about feasibility here, run
the simp route.

### Reproduction

The stalling theorems are necessarily not in this file. Paste into a scratch file importing
this one to re-run either half:

    set_option diagnostics true in
    set_option diagnostics.threshold 500 in
    theorem probeU : (0 : Nat) = closedMajorizer lCmE lUtNoLem (5 : Nat) := by rfl
