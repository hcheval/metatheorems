# Probes/TinyBoundDemo.lean

## module header

### The derivation, by hand

The trick throughout is `weaken_intro_h`'s pattern (private in `PureFOLLemmas.lean`, so
reproduced inline as `Derivable.mp _ (Derivable.exportation Derivable.and_weak)`): from
`h : Derivable A`, get `Derivable (B →ᶠ A)` for *any* `B`, since `A` doesn't need `B`'s
hypothesis at all.

1. `Formula.ex Ty.nat C₀` is derivable unconditionally in context `[nat]` (i.e. with `x`
   free): `exist_ax (var vz) C₀` gives `(C₀.subst0 (var vz) →ᶠ ex nat C₀)`, and
   `C₀.subst0 (var vz)` — substituting `x` for `v` — is exactly `x =₀ x`, i.e. `refl0`.
2. Weaken that into `(∀u B₀) →ᶠ (∃v C₀)` — the antecedent is simply never used.
3. Weaken again into `(dummy) →ᶠ ((∀u B₀) →ᶠ (∃v C₀))` so `forall_rule` can generalize over
   `x` from an unconditional dummy premise `0 =₀ 0`.
4. `forall_rule` then `mp` with `refl0 : Derivable (0 =₀ 0)` closes it.

Twelve raw `Derivable` constructors total: `mp`×4, `exportation`×2, `and_weak`×2, `refl0`×2,
`exist_ax`×1, `forall_rule`×1.

## Where the pipeline stops scaling (the comment block before `## Hygiene`)

### Where the pipeline stops scaling — measured, not `#eval`-ed blind

The two `rfl`s above go through on the 12-constructor derivation `tFinal` with no trouble at
all — the realizer is 292 nodes, nowhere near the pathology `BoundProbe.lean` found for
`mct_p2`. The natural follow-up is: how much bigger can the derivation get before this stops
working? A `ulimit`-capped `#eval` of `TinyBoundDemo.termSize` on a version of the pipeline
padded with `n` extra no-op derivation layers (each layer: `Derivable.syllogism I_comb`,
i.e. 4 raw constructors — `syllogism` plus `I_comb`'s own `syllogism`+`and_contract`+
`and_weak` — composed onto `tInner` before the rest of the pipeline runs unchanged) gives:

| padding layers (×4 constructors) | extracted `U` term size |
|---|---|
| 0 (this file's `tUt`) | 302 |
| 1  | 2,297 |
| 2  | 6,287 |
| 3  | 14,267 |
| 4  | 30,227 |
| 5  | 62,147 |
| 8  | 509,027 |
| 10 | 2,041,187 |
| 12 | 8,169,827 |
| 20 | `INTERNAL PANIC: out of memory` (capped at 16 GB virtual, `ulimit -v 16000000`) |

**The growth is roughly ×2 per padding layer** (4 raw `Derivable` constructors), not linear —
each `syllogism I_comb` composition duplicates the realizer built so far, the same
no-sharing pathology CLAUDE.md's "Build cost" section documents for `Term.subst` on
`Term.add_Q`, one layer up on *proof* terms rather than *interpretations*
(`BoundProbe.lean` already noted this is the same family of blow-up). Extrapolating the
measured ×2/layer rate: 20 layers (80 extra constructors, ~92 raw constructors total) lands
around 2×10⁹ nodes, consistent with the observed OOM at a 16 GB cap.

**So the concrete calibration for this pipeline, at `ι = Empty`, on a derivation of this
particular shape:** a derivation with realizer size in the low hundreds of nodes (this file's
12-constructor `tFinal`) sails through `rfl` in seconds; by ~12 padding layers (realizer
~8×10⁶ nodes) a plain `#eval` of `termSize` alone already takes real memory, and a
`syllogism`/`I_comb`-shaped derivation becomes infeasible somewhere around 15–20 extra
layers. This is a *much* smaller derivation than `mct_p2`'s proof-mode script (which does not
even survive `#eval termSize` at all, per `BoundProbe.lean`), so the practical ceiling for
this pipeline sits well below "the size of an interesting metatheorem instance" and squarely
in "small enough to hand-derive with raw constructors, one screen of code" — exactly the
territory this file's `tFinal` occupies. Note also that the growth measured here is an
artifact of the *particular* padding construction (naive `syllogism`-composition duplicates
its argument); a derivation of the same raw constructor count built with more sharing (e.g.
reusing a `let`-bound sub-derivation via `obtain`, per CLAUDE.md rule 4) would likely scale
very differently — this measures one specific failure mode, not a universal bound on
constructor count.

## Hygiene (the comment block before the refutation controls)

Added 2026-09-07 (`docs/CLAIMS_AUDIT.md` C11). This file is cited as "the project's first
evaluated bound, full stop" and had **no `#print axioms` at all**, so the axiom list quoted for
it in `docs/RESULTS.md` rows 1–2 was prose rather than build output.

The two numerals are also the only ones in the project with **no refutation control**, which
matters here more than elsewhere: both are closed by bare `rfl`, and a `rfl` whose two sides
stall at the same unreduced point succeeds exactly like one that computes (CLAUDE.md note 12).
The controls below are what distinguish the two cases.
