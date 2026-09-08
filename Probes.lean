import Metatheorems.Probes.BoundLemmasP2
import Metatheorems.Probes.BoundProbe
import Metatheorems.Probes.CombinatorLemmas
import Metatheorems.Probes.ConjBoundDemo
import Metatheorems.Probes.ExtractTermDemo
import Metatheorems.Probes.GeneralMatricesDemo
import Metatheorems.Probes.HilbertDemo
import Metatheorems.Probes.P1
import Metatheorems.Probes.PapplyDemo
import Metatheorems.Probes.QComm
import Metatheorems.Probes.R1
import Metatheorems.Probes.RevTriangleDemo
import Metatheorems.Probes.WHyperbolicLemmasDemo
import Metatheorems.Probes.RwArrow
import Metatheorems.Probes.RwBase
import Metatheorems.Probes.SeqMpBoundProbe
import Metatheorems.Probes.SoundnessProbe
import Metatheorems.Probes.MonotoneSpike
import Metatheorems.Probes.SyntacticND
import Metatheorems.Probes.SizeProbe
import Metatheorems.Probes.ProductRulesDemo
import Metatheorems.Probes.MonotoneLaneA
import Metatheorems.Probes.MonotoneLaneB
import Metatheorems.Probes.MonotoneLaneBp
import Metatheorems.Probes.MonotoneMCT
import Metatheorems.Probes.MonotoneMemoGates
import Metatheorems.Probes.ClassicalMfiProbe
import Metatheorems.Probes.ContentExampleNat
import Metatheorems.Probes.ContentExampleSpace
import Metatheorems.Probes.NestingDepth
import Metatheorems.Probes.SharingProbe
import Metatheorems.Probes.ExprBound
import Metatheorems.Probes.SymbolicBound
import Metatheorems.Probes.WExtBoundDemo
-- Not a probe: `Metatheorems.Headline` is the project's `#print axioms` block for every
-- headline declaration. It is not reachable from the umbrella either, so for a long time it
-- was built by nobody and six of its names — `syntactic_general_metatheorem` and its four
-- variants, `add_Q_assoc`, `distrib_Q` — had no axiom line in any build; the lists quoted for
-- them in the docs were prose. Imported here so the sweep covers them (`docs/CLAIMS_AUDIT.md`
-- C8).
import Metatheorems.Headline
import Metatheorems.Probes.TermPrintDemo
import Metatheorems.Probes.TinyBoundDemo
import Metatheorems.Probes.TriangleBoundDemo
import Metatheorems.Probes.UPremiseDemo
import Metatheorems.Probes.WBoundDemo
-- `Demo/Walkthrough.lean`, the presenter's live-demo file, IS in this sweep — indirectly.
-- `Demo` is now a `lean_lib` in `lakefile.toml` (not in `defaultTargets`, so a plain
-- `lake build` is unaffected), and `DemoChecks` imports it, so building `Probes` builds the
-- walkthrough and re-runs every extraction §6 shows commented-out. That is the point of
-- `DemoChecks`: the walkthrough's §6 commands are commented so a presenter can run them
-- live, and commented code rots.
import Metatheorems.Probes.DemoChecks
-- `#bound` (`Metatheorems/BoundPrint.lean`) measured on the Demo derivations and on
-- `real_mct_p2`: structural depth sweeps and the capped kernel reducer.
import Metatheorems.Probes.BoundPrintDemo

/-!
# Probe sweep target

Most of `Metatheorems/Probes/` is not reachable from `Metatheorems.lean`, deliberately — the
probes are experiments and measurements, not library content, and several are expensive.
The cost of that is that `lake build` never type-checks them, so they rot silently.

**Five are the exception and ARE imported by the umbrella**: `P1`, `R1`, `RwBase`, `RwArrow`
and `GeneralMatricesDemo`. They are regression tests for the rewriting engine and for the
general-matrix metatheorem, so a break in them breaks the library itself. Read
`Metatheorems.lean`'s import list rather than trusting prose here: the sentence "`Probes/` is
not reachable from the umbrella" was stated in several documents long after it stopped being
true.

They did: the `ι`/`κ` split (`3089af9`+`f17fddc`) left **five** probe files with
`@Derivable ι F …` one argument short, and each was found by accident, weeks apart —
`BoundProbe` and `SeqMpBoundProbe` while writing `CombinatorLemmas`, `TinyBoundDemo` while
writing `WBoundDemo`, and `SoundnessProbe`/`SyntacticND` only by sweeping all sixteen by hand.

This file exists so that never happens again:

    lake build Probes

builds every probe that is *supposed* to build. It is NOT in `defaultTargets`, so a plain
`lake build` is unaffected in speed. Run it after any change to `Term`'s or `Derivable`'s
indices, and after any refactor that touches an inductive's constructors.

**`Metatheorems.Probes.CounterSideProbe` is deliberately absent.** It exhausts memory
(`INTERNAL PANIC: out of memory` even under a 12 GB cap) and holds the project's only
permitted `sorry`; it is a record of a measurement, not something to keep green. Do not add
it here — that would make this target unusable, which is how the rot started.

**Two others are absent without a stated reason, which is the rot this file exists to
prevent**: `HilbertDepth` and `WExtRung3Scratch`. Nothing type-checks either. Add them or say
here why not.

(`LemBoundDemo` is *not* in the list above but **is** covered, transitively: four listed
probes import it — `ClassicalMfiProbe`, `BoundLemmasP2`, `SizeProbe`, `NestingDepth`. Coverage
by transitive import is real but invisible; if a file is meant to stay green, listing it here
is what says so.)
-/
