# Probes/ContentExampleNat.lean

## module header

**The numbers** (`f* := λn. n+1`, so `f*(0) = 1`; kernel-checked by `kernel_rfl`, both routes):

| `x*` | `V` (witness) | `U` (premise) | `Φ = max U V` |
|---|---|---|---|
| `(3, λn.n+1)` | **8** | **2** | **8** |
| `(5, λn.n+1)` | **32** | **4** | **32** |
| `(2, λn.n+3)` | **12** | 1 | 12 |

`V(k*, f*) = 2^{k*} · f*(0)` — the doubling of the *proof* read off as an exponential in the
bound, through `MRealizer.induction` = `cm.precM` = `recMaj` (the book's `t^M`). It moves with
both components of `x*`: `8 → 32` when `k*` goes `3 → 5`, and `4 → 12` when `f*(0)` goes
`1 → 3`. `U(k*) = k* − 1` is *sharp*: the step at `k` instantiates the premise at `u := k`, for
`k = 0 … k*−1`, so `U(0) = U(1) = 0`, `U(2) = 1`, `U(3) = 2`, `U(5) = 4` — "how far into
`∀u B₀` the proof reaches", as a function of `x*`, not a copy of `V`.

## Three things this file measures that were not known

1. **The MFI route and the term route agree on `V` and disagree on `U`.**
   `closedMajorizer cmE vT (xs 3) = 8` — the *term* route (`syntactic_soundness` →
   `extractedVTerm` → `closedMajorizer`) reaches the same numeral, kernel-checked below. Its
   `U` does not: `closedMajorizer cmE uT (xs 3)` is `INTERNAL PANIC: out of memory` at the
   12 GB cap (measured; not in the file, since a file of errors is not a green build). That is
   the documented one-sidedness of the term route (`CLAUDE.md`, `ConjBoundDemo`), now seen on a
   derivation with an induction in it.
2. **Raw constructors vs the proof mode: 145 against 42,747 nodes, and only the first
   reduces.** `eFinalPm` below is *the same statement, proved by the same argument*, written
   with `pmode/pinduction/pinst/papply/pobtain/pexists/ptrans/prwby`. It elaborates fine and is
   `derivSizeA = 42,747` (295× the raw derivation, because every `pm_*` step inserts an
   `S_comb` per hypothesis in `Δ` and `prwby` a full QF-ER). Its bound reduces at `k* = 0`
   (`mfiV = 1`, after `mfi_push`, ≈8 s) and is a 12 GB `std::bad_alloc` at `k* = 1` — one step
   of the recursion. So on this example the wall is *derivation size*, i.e. the
   ×5-per-composition of `MRealizer.syllogism` (ARCHITECTURE §14.7), not the induction, not the
   premise, not the matrix.
3. **The ceiling is the VALUE, not the derivation.** On this same 145-constructor derivation
   the bound is kernel-checked at `k* = 7` (`V = 128`, ≈9 s of kernel time, `V_at_7` below) and
   is `INTERNAL PANIC: out of memory` at the 12 GB cap at `k* = 8` (`V = 256`) — measured
   2026-09-06, both by `kernel_rfl` with nothing else changed. The majorant of the object-level
   `Term.add` is a `prec` term, so `recMaj` iterates *value*-many times with nothing shared;
   that, not derivation size, is what stops the doubling at 128 here.
4. **`Φ` is a genuine recursion, not a projection.** `MonotoneMCT.indFinal` (the earlier
   `pinduction` control) has `V(k*) = k*` — the witness is the induction variable itself. Here
   the witness at `k+1` is a function *of the previous witness*, so `recMaj` iterates and the
   bound is exponential; the refutation controls below (`≠ 7`, `≠ 9`, `≠ 4`, `≠ 16`) pin it.
