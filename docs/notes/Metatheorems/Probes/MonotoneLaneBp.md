# Probes/MonotoneLaneBp.lean

## module header

## Gate G-B'1 — the entry reduces a real ℚ cast to a numeral (POSITIVE)

`castU` below is `UPremiseDemo`'s premise-consuming derivation
(`forall_ax s ⟶ exist_ax s`, composed by `syllogism`, so `U` is the majorant of the
instantiation term `s`), with the matrix carrying the heaviest ℚ constant, `mul_Q`
(590,955 reduced nodes, CLAUDE.md "Build cost"), and with **two `Eq.mp` casts injected on the
syllogism's middle formula** — exactly the role `le_R_pu_of_le_R`'s `canorm` cast plays, but
placed where `monotone_soundness` meets `Eq.mp` **directly**. The middle equation `mcEq`
(`mP.subst0 sMid ≡ mClean` up to a `mul_Q` `subst`) is cheap by `closed_subst` but a full
ℚ delta by kernel `rfl`.

* `monotone_soundness … (Eq.mp e d)` on the **bare** kernel forces `whnf` of the `Eq.mp`,
  i.e. `mul_Q.subst ≡ mul_Q` — the delta-expansion pathology.
* With `simp only [monotone_soundness_eqmp (hB := mcEq …)]` the cast is rewritten to
  `MRealizer.transport`, whose data cast is `congrArg wTy mcEq` — `wTy (eq0 …) = unit` on both
  sides, so it collapses structurally. `kernel_rfl` then reduces to `901`.

`castU`, `castU_at_7`, and the refutations are the evidence; **`U = 901`, moving with `x*`**.
The memo route's `kernel_rfl` is instant (the cast collapses to `cast rfl` structurally).

**Bare-kernel control, measured 2026-09-05** (run in scratch, then reverted — a control that is
not run is not a control). The same statement by `kernel_rfl` with **no** `simp` step:

    theorem castU_bare (g : ℕ → ℕ) : (901 : ℕ) = mfiU (uCm M h) (mrC M h) ((5 : ℕ), g) := by
      kernel_rfl

*terminates* — matrix `mul_Q`: **≈8 s**; matrix `cauchyfy (snd x) u`: **≈37 s**. So a *single*
directly-injected ℚ cast is a **linear** `Term.subst` delta (O(ℚ-constant size)), not the 12 GB
OOM: the kernel reduces `mul_Q.subst ≡ mul_Q` in one pass. The memo route turns that O(1). The
`std::bad_alloc` at 12 GB Lane B measured on the *real* `le_R_pu_of_le_R`
(`MonotoneLaneB.lean`, finding 3) is the **compounded** case — three casts, `cauchyfy` applied
to a *composed* real (`sub_Q (cauchyfy f …) (cauchyfy g …)`), inside the proof-mode layer — not
reproduced by one injected cast. What the entry buys is exactly the per-cast O(1); reaching the
compounded, pm-buried casts is the separate lane below.

## Gates G-B'1(literal `le_R_pu_of_le_R`), G-B'2, G-B'3 — the entry does NOT reach the
## proof-mode-buried casts (NEGATIVE, measured)

The memo lemmas fire only where `monotone_soundness` is applied *directly* to a cast. In a
proof-mode-written derivation the `Eq.mpr`/`Eq.mp`/`Eq.rec` casts sit **inside** the
`pm_*`/`seq_*` layer, so `monotone_soundness` is applied to a `pm_*`/`seq_*` def, not to the
cast. `simp` cannot fire the memo lemma without first unfolding that layer to raw `Derivable`
constructors, and:

* unfolding it explodes — `le_R_of_le_R_pu` alone is **4167** `Derivable` constructors
  (`MonotoneLaneB`), and `simp only [le_R_of_le_R_pu, le_R_pu_of_le_R, monotone_soundness,
  monotone_soundness_eqmpr] ; kernel_rfl` on the transitivity-shaped `∀q(∀n concT → ∃v concT)`
  is a `std::bad_alloc` at 12 GB (measured 2026-09-05);
* the kernel reduces the `pm_*`/`seq_*` layer *fine* on its own (Lane B finding 1: 449-node
  proof-mode derivation, 2 s) — it chokes **only** at the buried `Eq.mpr`, which is exactly
  what the memo lemma would fix if it could be reached.

Cast inventory (from a `Expr`-walk of the aux-lemma proofs, 2026-09-05):
`le_R_pu_of_le_R` 3 × `Eq.mpr`; `le_R_of_le_R_pu` 4 × `Eq.mpr`; `leR_tail` 5 × `Eq.mpr`
(+ `pm_induction`); `mct_body` 3 × `Eq.mpr`; `qfer_at_nf`/`qfer_nat_nf` 1 × `Eq.mp`;
`seq_cast` (hence `seq_induction`) 1 × `Eq.rec` (`h ▸`) — the three shapes the entry covers.

So reaching them needs the **MRealizer analogues of `Probes/CombinatorLemmas.lean`'s
`wit_seq_*`** (the counter-side commutation lemmas that push `monotone_soundness` through
`seq_of_thm`/`seq_mp`/`seq_id`/`seq_allI` so it meets the cast directly). That is a separate
lane, named by Lane B (`ARCHITECTURE.md` §14.5). The entry here is the missing *bridge* for
those lemmas' output; it is proven and demonstrated where the cast is reachable.

`derivSize` is deliberately **not** run on `le_R_pu_of_le_R`/`dist_tri_chain`/`mct_p2`: it is a
sharing-free tree count and OOMs at 12 GB even on `le_R_of_all` (a single ℚ leaf counts
2,963,450) — a ruler for raw-constructor derivations only (supervisor note, 2026-09-05).
