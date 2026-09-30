# PureWEHA.lean

## module header

Before 2026-09-08 this instance existed only inside `Probes/` (`TinyBoundDemo.tXE`, `tFE`,
`tSiE`, `tEqxiE`, `tPremE`, `tSpremiseE`; `MonotoneMCT.cmE`), and `Demo/Walkthrough.lean`
imported a probe to reach it. Probes are measurements; library and demo code must not depend
on them. The probes keep their own copies — the definitions are one-liners and the copies are
definitionally equal to these, so nothing there had to move.
