# Probes/ConjBoundDemo.lean

## module header

**The headline is negative, and it is sharp.** The two-instantiation `U` does **not** reduce to
a numeral: it is a `(deterministic) timeout at whnf`. Four controls localise the cause exactly,
and each rules out a hypothesis that would have been the natural guess:

| variant | premise matrix | instantiations | `U` reduces? |
|---|---|---|---|
| `cFinalOnce` | `triB ∧ triB0` (two triangle inequalities) | `s₁` | **yes**, `1709` |
| `cFinalTwice` | `triB ∧ triB0` | `s₁`, `s₂` | no — whnf timeout |
| `tFinalTwice` | `u =₀ u` (tautology) | `s₁`, `s₂` | no |
| `sFinalTwice` | `u =₀ u` | `0`, `S 0` | no |
| `acFinal` | `u =₀ u` | `s₁` only, **plus one bare `and_contract`** | no |

So the obstruction is **not** the size of the matrix (a tautology stalls too), **not** the
magnitude of the numbers (`0` and `S 0` stall too), and **not** `pair_h`'s duplicating
plumbing (`acFinal` uses none of it). It is **one `Derivable.and_contract` at the premise
formula**, whose Dialectica realizer `sAndContract` is the only rule in the system whose
*counter* component must merge two challenges into one, via
`Term.natCase (matrixTerm …) (.snd y) (.fst y)`.

And the localisation is one-sided: `cVtTwice_at_5_9` below evaluates the **witness** functional
`V` of the very same two-instantiation derivation to the literal `1709`. Witness side fine,
counter side stuck — exactly the split `SeqMpBoundProbe`/`CounterSideProbe` predicted, now
observed on a whole extraction rather than on a lemma.

## What the diagnostics say — and one correction to CLAUDE.md

`set_option diagnostics true` on the stalling `acUt_at_5_9` (run live, recorded here, option
removed) reports:

    [reduction] unfolded declarations (max: 60474, num: 16):
      Eq.rec ↦ 60474      Term.rec ↦ 10847      Term.rename ↦ 10504
      syntactic_soundness ↦ 7389                Derivable.rec ↦ 7389
      SRealizer.imp ↦ 7353                      Term.weaken ↦ 3260
      sAndWeak ↦ 2430     tInst1 ↦ 2188         sAndContract ↦ 2187
      sForallAx ↦ 2187    List.rec ↦ 1006       Term.Renaming.ext ↦ 720
      sSyllogism ↦ 513
    [reduction] unfolded reducible declarations: Eq.ndrec ↦ 60474, Term.casesOn ↦ 10847,
      Subtype.val ↦ 7389, Derivable.casesOn ↦ 7389, Ty.casesOn ↦ 2908, …

CLAUDE.md (Track A item 1) records the Stage-B stall as *"a `whnf` heartbeat timeout from
unfolding `Term.monus`/`Term.pd` under an unrestricted `termMajorizer`"*. **Neither
`Term.monus` nor `Term.pd` appears anywhere in this profile, and neither does `matrixTerm`.**
What dominates is `Eq.rec`/`Eq.ndrec` — 60,474 unfoldings, five times the next entry — with
`Term.rename`/`Term.weaken` behind it. So on this instance the cost is **dependent-cast and
renaming traffic inside `sAndContract`'s own plumbing**, and whnf never even reaches the
arithmetic constants the earlier note blames. The counts also grow steadily rather than
diverging, which suggests the stall is quantitative (a constant factor over the budget), not a
genuine non-termination — but the fix is restructuring, never a raised limit.

The `s₂` branch is *logically redundant* — it is derived and then dropped by `and_weak`. That
is deliberate and is the interesting case for proof mining: a **redundant use of the premise at
a second index still has to inflate `U`**, because the realizer's counter component cannot know
the branch was discarded. Whether it does inflate it is precisely what this file could not
measure.

## What IS established here

1. **The two numbers `U` would have to combine, and that they cross over.** `witM1_at_5_9`,
   `witM2_at_5_9`, `witM1_at_5_1`, `witM2_at_5_1`: `s₁` majorizes to `1709` at `x* = (5,9)` and
   to `349` at `(5,1)`, while `s₂` majorizes to `901` at both. So at `(5,9)` the first
   instantiation dominates and at `(5,1)` the second does — a `max` of the two is a genuinely
   different function from either. (These are majorants of the *instantiation terms*, computed
   by the same `closedMajorizer` under the same `ConstMajorants`; they are **not** `U`.)
2. **The one-instantiation `U` for this premise formula**: `1709` at `(5,9)`, `349` at `(5,1)` —
   it tracks `s₁` alone, as it must.
3. **The two-instantiation `V`**: `1709`. The witness side of the very derivation whose `U`
   stalls goes through unchanged.
4. **The extraction itself never fails.** `cUtTwice`, `tUtTwice`, `sUtTwice`, `acUt` all
   elaborate and type-check as closed `Term`s; `cBoundTwice` elaborates as a `Subtype`. Only the
   *evaluation* of the counter-side majorant stalls.

## What is NOT established

**That `U` is a `max`.** It may be; it may also be something coarser. Nothing here shows
either way, and the file deliberately does not guess. Closing this is CLAUDE.md Track A item 1's
"concrete-numeral half (Stage B)", now with a sharper profile of what has to be restructured:
`Eq.rec`/`Term.rename` traffic through `sAndContract`, not arithmetic.

## The negative result, in reproducible form (closing comment block)

Each of the four statements below was written, run, and produced a
`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached`
at the `rfl` closing the `have hval`. They are quoted rather than kept, because a file with
errors is not a green file; re-paste any one of them to reproduce. **No limit was raised.**

```lean
theorem cUtTwice_at_5_9 (M : WHyperbolicModel) (h : M.d M.ref M.zeroX ≤ ((5 : ℕ) : ℝ)) :
    (1709 : ℕ) = closedMajorizer (triCm M h) (cUtTwice M) ((5 : ℕ), (9 : ℕ)) := by
  have hval : closedMajorizer (triCm M h) (cUtTwice M) ((5 : ℕ), (9 : ℕ))
      = Nat.max (Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1))
                (Rounding.pairN (2 * ((5 + 5) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)) := rfl
  rw [hval]; decide                                                    -- ← timeout at `rfl`

theorem tUtTwice_at_5_9 … (tUtTwice M) … = Nat.max … := rfl            -- ← timeout
theorem sUtTwice_small  … (sUtTwice M) … = Nat.max 1 0 := rfl          -- ← timeout
theorem acUt_at_5_9     … (acUt M)     … = Rounding.pairN … := rfl     -- ← timeout
```

The goal at the point of reduction is small in every case: `numObjs = 70, approxDepth = 12`,
identical to the goals of the theorems that *do* reduce (also `70`/`12`). So the residual
blow-up is entirely inside `whnf`, not in the statement — which is why `numObjs` on the goal
cannot see it, and why the diagnostics profile in the module header is the measurement that
matters.

The head symbol of the stalling side is `closedMajorizer`, i.e. `termMajorizer cm t 0 ()` with
`t = extractedUTerm … `; the profile shows whnf descending through `syntactic_soundness` →
`SRealizer.imp` → `sAndContract` and then spending 60,474 steps in `Eq.rec`/`Eq.ndrec` and
10,504 in `Term.rename`.

### Design choices, and one that was rejected

**Nested existentials were rejected.** The task's ideal conclusion is
`∃v ∃w (C₁(v) ∧ C₂(w))` — one existential per instantiation term, which is still purely
existential and so still legal for `_at_gen`. It was not built, for a reason that is worth
recording because it is structural rather than a matter of effort: the two `exist_ax` steps
compose their substitutions, so the middle formula the elaborator must unify is
`C₀.substF (ext σ₁) |>.substF σ₂` against `B₁.subst0 s₁ ∧ᶠ B₂.subst0 s₂`. Unifying those forces
`Term.subst` through `Term.cauchyfy`, `Term.le_Q_dec` and `Term.sub_Q` — the delta-expansion
pathology CLAUDE.md's "Build cost" section documents at 28 s per instance, here under two
binders. `TriangleBoundDemo` escapes it only because every formula in it is a `.subst0` at a
*single* term, matched against itself; that escape is unavailable as soon as two different
terms are substituted into one formula.

The single-existential form used instead keeps the escape and still consumes the premise twice,
at the cost of making the second branch a **detour** — derived, then dropped by `and_weak`. For
the question being asked that is not a loss: the realizer's counter component has no way to know
a branch was discarded, so a detour must still be paid for in `U`. It also makes the control
sharper, since `cFinalOnce` differs from `cFinalTwice` only by the detour.

**Note on `Ty` products.** They do not help here. `∃v^(nat ×ₜ nat)` would give one binder for
two witnesses, but the two conjuncts would then read `fst v` / `snd v`, and the derivation would
need `Term.fst (Term.mkPair a b) = a` as a *derivable* equation — which the proof system does
not have (`beta_eq` covers `lam` only; `classical_to_prenex_extended`'s docstring).

### Controls actually run

* **Permanent, positive** (`decide` *refutes* in every build): `cUtOnce_ne_zero`,
  `cUtOnce_ne_1710`, `cUtOnce_ne_1708`, `cUtOnce_ne_901_at_5_1`, `witM_distinct`,
  `cBoundOnce_ne_1710`. The fourth is the informative one — it refutes, for the
  one-instantiation derivation, exactly the value a max would force at `(5,1)`.
* **Live, run as an edit and then reverted**: claiming `1708 = closedMajorizer (triCm M h)
  (cUtOnce M) ((5,9))`. The `have hval … := rfl` step **still succeeded** — so the pipeline
  genuinely reduces to a closed ℕ expression and the `rfl` is not a both-sides-stuck no-op
  (trap 12) — and then

      error: Tactic `decide` proved that the proposition
        1708 = Rounding.pairN (2 * ((5 + 9) * 2 ^ (0 + 1))) (2 ^ (0 + 1) - 1)
      is false

  Refutation, not merely "the proof did not go through".
* **Live, the four stalling variants**, quoted above with their exact error text.
* **Live, diagnostics** on `acUt_at_5_9`, quoted in the module header; the `set_option` lines
  were removed afterwards.

### Cost, measured

| goal | numObjs | approxDepth | outcome |
|---|---|---|---|
| `witM1_at_5_9` | 69 | 12 | reduces |
| `cUtOnce_at_5_9` | 70 | 12 | reduces |
| `cVtTwice_at_5_9` | 70 | 12 | reduces |
| `tUtOnce_at_5_9` | 70 | 12 | reduces |
| `cBoundOnce_at_5_9` | 154 | 23 | reduces |
| `cUtTwice` / `tUtTwice` / `sUtTwice` / `acUt` | 70 | 12 | **whnf timeout** |

Module wall clock, `lake build Metatheorems.Probes.ConjBoundDemo` with all dependencies built:
**23 s**, against `TriangleBoundDemo`'s 21.9 s — so the extra derivations and the eighteen
numeral/refutation theorems cost about a second over its nine. The stalling variants each burn
a full 200,000-heartbeat budget before failing, so a file that *keeps* them costs far more
(the exploratory version with four of them took 40 s and produced no theorems).
