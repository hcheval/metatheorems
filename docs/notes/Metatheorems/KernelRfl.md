# KernelRfl.lean

## module header

The evaluator of record for extracted bounds. `Meta.isDefEq` (what bare `rfl` runs) has no
cache on terms with free variables and recomputes `Ty.interpret` at every step; the kernel
caches by structure and consumes no heartbeats. Measured in `Probes/MonotoneLaneB.lean`: the
same `U = 901` is a 200 000-heartbeat `whnf` timeout under `rfl` and ≈2 s under `kernel_rfl`,
and every `KERNEL` run in `Probes/SymbolicBound.lean` converges where every `Meta` run aborts.

It is sound because the kernel checks the assignment when the declaration is added — the
tactic does no checking of its own, which is the whole point. Its non-vacuity control is that
the kernel **rejects** a wrong numeral: `MonotoneLaneB.e1_U_900`, "(kernel) declaration type
mismatch", 1.8 s.

Moved here from `Probes/MonotoneLaneB.lean` on 2026-09-08 so that `Demo/` and the library can
use it without importing a probe.
