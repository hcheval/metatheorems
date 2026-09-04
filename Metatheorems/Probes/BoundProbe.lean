/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.MCT
import Metatheorems.Majorizability

/-!
# Probe: does the extracted realizer term reduce?

**Step 0 of the end-to-end bound extraction.** Before building any infrastructure for
"derivation → realizing term → majorant → numeral", measure the one genuine unknown: the
realizer `syntactic_soundness` produces recurses over a 36-constructor derivation, and
`mct_p2` is a proof-mode script. If the resulting term is astronomically large, the whole
pipeline plan changes shape.

Two things are already known to be favourable:

* **MCT is pure ℕ.** `mctB₀`/`mctC₀` mention only `leF`, `Term.add`, `.eq0`, `.succ` — no ℚ or
  ℝ constants — so the term-size pathology behind `Term.add_Q` (1,945 nodes written,
  1,880,329 reduced) does not apply.
* **`ι = Empty` makes every space-dependent obligation vacuous**, so `EqXInterp` and the
  premise realizer are one-liners.

NOT imported by `Metatheorems.lean`.
-/

namespace Metatheorems
namespace BoundProbe

/-- Structural node count of a term. Deliberately not in `Term.lean`: it exists to measure
this probe, not as library API. -/
def termSize {ι : Type} {F : ι → Ty ι} :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → Nat
  | _, _, .var _      => 1
  | _, _, .app f a    => 1 + termSize f + termSize a
  | _, _, .lam b      => 1 + termSize b
  | _, _, .zero       => 1
  | _, _, .succ       => 1
  | _, _, .prec _     => 1
  | _, _, .func _     => 1
  | _, _, .zeroX _    => 1
  | _, _, .dist _     => 1
  | _, _, .unitI      => 1
  | _, _, .mkPair a b => 1 + termSize a + termSize b
  | _, _, .fst p      => 1 + termSize p
  | _, _, .snd p      => 1 + termSize p

-- ============================================================================
-- The `ι = Empty` model: everything space-dependent is vacuous
-- ============================================================================

/-- The empty space interpretation. All three fields quantify over `ι = Empty`. -/
def siE : SpaceInterp XEmpty FEmpty where
  funcInterp f := f.elim
  zeroInterp i := i.elim
  distInterp i := i.elim

/-- `EqXInterp` at `ι = Empty`: every one of the four fields begins `∀ (i : ι)`, so with no
base types each is `fun i => i.elim`. This is why `ι = Empty` is the cheap setting. -/
def eqxiE : EqXInterp XEmpty FEmpty siE where
  realize             := fun i => i.elim
  extract             := fun i => i.elim
  dist_comm_holds     := fun i => i.elim
  dist_tri_holds      := fun i => i.elim

/-- No premises, so the premise realizer is vacuous. -/
def PremE : PremiseSet FEmpty := fun _ => False

def spremiseE : ∀ (Γ' : Ctx Empty) (B : Formula FEmpty Γ'), PremE ⟨Γ', B⟩ → SRealizer siE B :=
  fun _ _ h => h.elim

-- ============================================================================
-- The measurement
-- ============================================================================

/-- The MCT derivation, at `ι = Empty` with an empty premise set. -/
def mctE : @Derivable Empty Empty FEmpty Allowed.extended PremE [] mctStatement :=
  ProofMode.mct_p2 (al := Allowed.extended)

/-- Its syntactic realizer. -/
def realizerE : SRealizer siE (mctStatement (F := FEmpty)) :=
  syntactic_soundness eqxiE spremiseE mctE

/-- The two extracted functionals, as closed terms. -/
def UtE : Term FEmpty [] (mctTy Empty →ₜ Ty.nat) :=
  extractUTerm (ρ := mctTy Empty) (B₀ := mctB₀) (C₀ := mctC₀) realizerE.val

def VtE : Term FEmpty [] (mctTy Empty →ₜ Ty.nat) :=
  extractVTerm (ρ := mctTy Empty) (B₀ := mctB₀) (C₀ := mctC₀) realizerE.val

/-! ### The measurement — RESULT: naive `#eval` is not viable, even at `ι = Empty`

**Do not uncomment the `#eval`s below without a memory cap** (`ulimit -v`); on this machine
both exhausted 10 GB and one run with no cap took the whole system down (2026-09-04).

All four `def`s above — `mctE`, `realizerE`, `UtE`, `VtE` — elaborate and type-check
**instantly**, with no `#eval` in the file at all. That is consistent with the full
`lake build` being green at 8088 jobs in ~90s: the kernel never needs `syntactic_soundness
eqxiE spremiseE mctE` reduced to a value to check `mct_bound_p2`'s type, only unified up to
whnf where needed. The cost is specific to *forcing full evaluation*.

Two independent `#eval`s were tried, both capped at 10 GB, both ending in
`INTERNAL PANIC: out of memory`:

    #eval termSize UtE            -- the fully extracted, wrapped functional
    #eval termSize realizerE.val  -- the RAW realizer, before extraction wraps it at all

Since the raw realizer already blows up, **the cost is in `syntactic_soundness`'s structural
recursion over `mct_p2`'s 36-constructor derivation, not in `extractUTerm`'s wrapping**
(`weaken`/`fst`/`snd`/`app`, which only add a handful of nodes). This is the same pathology
CLAUDE.md's hard rule 3 bans `#eval`-ing `Term.interpret` for — eager reduction of a large
structurally-recursive term with no sharing — reproduced one layer up, on a *proof* term
rather than an *interpretation*.

**Conclusion for the extraction plan**: a literal evaluated bound for `mct_p2` specifically
cannot be obtained by `#eval`. If a numeral is wanted, it has to come from kernel-checked
`rfl`/`simp` with NAMED intermediate equation lemmas — the same discipline the `qval` bridge
uses (`QValBridge.lean`: one constant unfolded per lemma, citing already-proved lemmas for the
rest) — applied to `syntactic_soundness`/`extractUTerm`/`termMajorizer`. Whether that is
tractable for the full `mct_p2` script, or only for a much smaller hand-built derivation, is
untested and should be the next probe if this direction is pursued. -/

end BoundProbe
end Metatheorems
