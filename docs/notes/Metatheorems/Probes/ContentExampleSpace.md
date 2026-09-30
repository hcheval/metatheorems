# Probes/ContentExampleSpace.lean

## module header

| proof | how `v` is chosen | `U = V` at `x* = ((5,5),(k*,λn.n+1))` |
|---|---|---|
| `eDir` (11 constructors) | the space's own number `⌈d(x,z)⌉₀` (`forall_ax` at `D0`) | **901**, and **1273** at `x* = ((7,5),…)` |
| `eRec` (187 constructors) | the output of a **doubling induction** on `k`, using the premise's second conjunct | **1** at `k*=0`, **8** at `k*=3`, **32** at `k*=5`; unchanged at `((7,5),…)` |

So one bound is a genuine function of the **space majorants** (901 → 1273 when the majorant of
`x` goes 5 → 7 — `distMajorant` is `λn₁n₂. (n₁+n₂)∘`), and the other is a genuine
**recursion** through `MRealizer.induction` = `cm.precM` = `recMaj` (the book's `t^M`),
doubling per induction step and *provably indifferent* to the space majorants (`Vrec3` and
`Vrec3b` are both `8`). Bounds are properties of proofs, not of theorems — here at a space,
with the space axiom in the premise slot and both numbers kernel-checked.

Both numbers come out of `monotone_general_metatheorem_at` itself as well as off `mfiU`/`mfiV`
(`PhiDir = 901`, `PhiRec = 8`; `Φ = max U V`).

`U` is the index at which the **triangle inequality must be known**: `Udir = 901 = Vdir`
because the direct proof consults it at `⌈d(x,z)⌉₀`; `Urec = 2^{k*}·f*(0)` because the
recursive proof consults it at the index the recursion computed (which dominates the `k*−1` of
the ℕ conjunct).

## Method notes — what was needed to make these reduce (all measured, 2026-09-06)

* **`mfi_push` then `kernel_rfl`** (`Probes/MonotoneMemoGates.lean`, Lane D1). Bare
  `kernel_rfl` is a 12 GB `std::bad_alloc` on the recursive proof's `V` (measured on `eRec`'s
  shape before `mfi_push` was applied; the direct proof was never run bare): the casts inside
  `ex_and_left` and `forall_map` (`forall_ax_vz`, `substF_renameF_id`) are K-checked through
  `cauchyfy`/`le_Q_dec`, which is the documented delta-expansion trap. `mfi_push` rewrites them
  to `MRealizer.transportTo` at the kernel-normalised hat type and they cost nothing.
  `forall_map` is **not** among the theorems the `mfi_memo` set unfolds by itself and has to be
  passed explicitly; with it passed, no `monotone_soundness` head involving a cast survives
  (`mfi_report`: 30–60 `transportTo`, 0 cast nodes).
* **Never let the substitution reach the matrix.** The metatheorem's `B₀`/`C₀` are written
  once, in `[u, q]`, and every use is a `forall_ax`/`exist_ax` at the *same* term, so the two
  sides are the same expression and `whnf` never enters `spB`. Reducing a substitution through
  it *is* a `whnf` timeout — measured: `(Formula.all Ty.nat triK).subst0 Term.zero =
  Formula.all Ty.nat triB` by `rfl` exhausts 200 000 heartbeats. That is why the ℕ induction
  carries the *projected* premise `∀u natB` (via `forall_map`) rather than the conjunction.
* **A `Term.add` between the recursion's output and the space number does not reduce.** The
  first version of `eRec` used the witness `⌈d(x,z)⌉₀ +ᵗ w`, to have one number depending on
  both. Kernel: `std::bad_alloc` at 12 GB, in either summand order. The object-level `Term.add`
  is a `prec` term, so its majorant runs `recMaj` — and at an argument of size ≈900 that is
  what dies. The ceiling is the **value**, not the derivation: `ContentExampleNat`'s pure-ℕ `V`
  is kernel-checked at `2^7 = 128` (≈9 s) and is out of memory at `2^8 = 256`, on the same
  145-constructor derivation (measured 2026-09-06).
  The version kept here therefore reports the two dependencies as two proofs rather than as one
  sum, which is the more informative comparison anyway.

## Honest limits

The mathematics is elementary: the conclusion is an *instance of the premise*, so nothing is
proved *about* the space that the axiom did not already say. What is established is that a real
space axiom in the premise slot, consumed at an index a **recursion** computes, carries through
to a kernel-checked numeral, and that the numeral tracks whichever of (the space majorants, the
recursion) the proof actually used.
