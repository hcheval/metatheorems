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
import Metatheorems.Probes.WExtBoundDemo
-- Not a probe: `Metatheorems.Headline` is the project's `#print axioms` block for every
-- headline declaration. It is not reachable from the umbrella either, so until 2026-09-07 it
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
-- NOT imported here: `Demo/Walkthrough.lean`, the presenter's guided walkthrough. It must stay
-- green, and it is reachable from nothing else, but `Demo` is not a `lean_lib` in
-- `lakefile.toml`, so `import Demo.Walkthrough` fails with "unknown module prefix 'Demo'".
-- Check it with `scripts/lean.sh <repo>/Demo/Walkthrough.lean` (≈1 min, no errors expected).
-- To fold it into this sweep, add to `lakefile.toml`:  [[lean_lib]]  name = "Demo"
-- and then the import line here.

/-!
# Probe sweep target

`Metatheorems/Probes/` is **not** reachable from `Metatheorems.lean`, deliberately — the
probes are experiments and measurements, not library content, and several are expensive.
The cost of that is that `lake build` never type-checks them, so they rot silently.

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
-/
