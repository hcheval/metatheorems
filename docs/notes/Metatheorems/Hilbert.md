# Hilbert.lean

## module header

### Sharing

Proof terms here are DAGs, not trees: the scripts are long `let`-chains and the same
subderivation is referenced many times. Expanding naively is exponential. Every distinct
subproof is therefore numbered **once** and cited afterwards by its line number — which is
also exactly what makes a Hilbert listing readable, so sharing is a feature and not merely an
optimisation. Two mechanisms:

* `let`/`have` binders are entered with `withLetDecl`, the bound value is numbered, and the
  free variable is remembered as that line;
* a structural cache on the elaborated expression catches literal repetitions that were not
  shared through a binder.

### `depth n` — the fueled unfolding

`#hilbert foo depth 2` makes the proof-mode layer transparent, but expands each step only
**two `ProofMode` unfoldings deep**; what it has become by then is cited by name exactly as the
default does. So the listing degrades gracefully instead of not terminating, and the fuel is a
*display knob*: at depth 0 you see which proof-mode tactic each step was, at depth 1 the
`seq_*` combinator it is defined as, and so on down to raw `Derivable` constructors.

**The fuel is per step, not per path**, and this is the one thing to get right — see
`subProofs`, where it is reset. A proof-mode derivation is a chain, so a path-counted fuel is
spent entirely on the spine: measured, `depth 1` and `depth 2` on `mct_body` then differ from
`depth 0` in one line each and in nothing else.

The design is `Probes/ExprBound.lean`'s, one level up: fuel plus a name-based stop set
(`keeping g h`), with the memo keyed on the fuel as well as the expression. Keying the memo on
the fuel is forced — the same subderivation reached with two different budgets renders
differently — and it is what costs the sharing that makes depth expensive. `all` and
`unfolding` are unchanged and consume no fuel; only `ProofMode` names do.

`keeping` matters as much as the fuel, and for a reason specific to this project: a *named
sub-derivation* written in the proof mode (`ProofMode.mct_descent`) lives in the same
namespace as the tactic lemmas (`ProofMode.pm_mp`), so no name test separates "the plumbing"
from "the mathematics". `depth 1 keeping mct_descent` says expand the plumbing and cite the
mathematics, which is what a paper proof does.

Measurements (`Probes/HilbertDepth.lean`) are in that file's header.

## the object-notation printer (`#hilbert`'s formula rendering)

`→ᶠ`, `∧ᶠ`, `∨ᶠ`, `¬ᶠ`, `⊥ᶠ` and `↔ᶠ` are all declared `scoped` in `Formula`. Putting the
namespace on `Core.Context.openDecls` is *not* enough: that shortens names, but a scoped
notation's unexpander lives in a `ScopedEnvExtension` which `open` **activates in the
environment**. So both are done, and the environment change is rolled back afterwards.

`pp.fieldNotation` is switched off as well. With it on, the delaborator turns
`Formula.imp A B` into `A.imp B` before any unexpander sees it, and the notation never
fires — which is exactly how the first version of this printer produced a page of `.imp`.

## the proof-mode-layer predicate

`privateToUserName` first: a `private def` in `ProofMode/Packing.lean` is stored as
`_private.Metatheorems.ProofMode.Packing.0.Metatheorems.ProofMode.weaken_intro_h`, whose
*prefix* is `_private`, so a bare `isPrefixOf` calls it a non-proof-mode constant. That
mattered: `weaken_intro_h` is one of the two things `pintro` is built from, and it survived
into the fully-expanded listing as a cited name at every depth until this was fixed.

## `shouldUnfoldAt`

**Which constant does it, measured** (`Probes/HilbertDepth.lean`): `seq_id`, and essentially
only `seq_id` — not "every `pintro`/`prw`" collectively, as one might guess. The
discriminating test is that `keeping seq_id` — that one name, nothing else — turns
`#hilbert ProofMode.mct_descent depth 1` from a heartbeat timeout into 1766 steps in 18 s.
`seq_id` is hypothesis lookup, so it recurses on the hypothesis context through `HVar.rec`
with a dependent cast per level, and it is cited 35 times in `mct_descent`'s 112 steps; the
stalling profile is `Eq.rec ↦ 2802` with `seq_id ↦ HVar.rec ↦ List.noConfusion ↦ 442` beneath
it. Every other tactic expands without trouble.

Two escape hatches, and they are independent:

* naming a constant under `unfolding` expands it wherever it occurs, at no cost to the budget
  (this is how one proof-mode tactic at a time was expanded before `depth` existed);
* `depth n` spends one unit of budget per consecutive `ProofMode` unfolding of one step, so
  the expansion is bounded by construction rather than by luck.

Note the asymmetry, which is deliberate: a non-proof-mode constant costs nothing. The
budget is a statement about the *proof-mode layer's* depth, which is what is unbounded in
practice; ordinary library lemmas bottom out in `Derivable` constructors quickly.

**Backward compatibility is definitional, not merely tested.** At `d = 0` with `keep` empty
the body below is
`unfold.contains n || (if isProofModeName n then 0 > 0 else unfoldAll)`, i.e. exactly the old
`shouldUnfold`'s `unfold.contains n || (unfoldAll && !isProofModeName n)`. The eight listings
of `Probes/HilbertDemo.lean` are byte-identical across the change, which is the empirical half
of the same claim.

## `subProofs`

**The budget is reset here, and that is the whole meaning of `depth`.** A proof-mode
derivation is a *chain*: `pm_cut a b`'s derivation arguments are the earlier steps of the same
script, so the path from the root to a leaf passes through every step of the proof. A fuel
counted along that path is therefore spent on the spine and never reaches any definition —
measured on `mct_body`, `depth 1` and `depth 2` unfolded only the outermost one or two
tactics and were otherwise byte-identical to `depth 0`.

So the fuel counts **consecutive unfoldings of one step's head constant** and is restored when
we move to a premise. `depth n` then reads as: expand every proof-mode step `n` definition
levels, and cite whatever it has become. `depth 0` is the old opaque behaviour and an
unbounded depth is the full expansion that does not terminate.
