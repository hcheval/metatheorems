# Probes/MonotoneMCT.lean

## module header

**RESULT: NAMED AND TYPE-CHECKED; NOT EVALUATED. Localised, staged as the brief asked.**

(a) **Size.** `#eval derivSize`/`reportD` on `mct_p2`: **`INTERNAL PANIC: out of memory`
    at 12 GB while the compiled value is being built** — the same fact as for
    `le_R_trans_core` (`MonotoneLaneB.lean`): the runtime constructs every node's formula
    payload strictly. `walk` (the transitive constant walk): **170** reachable definitions;
    `pm_induction` in four (`mct_descent`, `antitone_chain`, `monus_trans`,
    `monus_succ_of_ne`); `Eq.mpr` in `mct_body`, `mct_descent`, `strict_drop`, `monus_trans`,
    `monus_succ_of_ne`, `antitone_chain`, `qfer_*_nf`, `forall_ax_inst`, `lam*_correct*`;
    raw `Derivable.induction` in the ℕ-arithmetic lemmas (`add_comm`, `monus_cancel`, …).
(b) **`Φ` named**: `mctPhi` below is a `def`; it elaborates and type-checks instantly.
(c) **Evaluation**, at `x* = λ_ _. 1` (`K = 1`, constant `g`, `a ≤ 1`): the kernel
    (`Lean.Kernel.whnf` on `mfiV`, the *witness* side) dies with **`std::bad_alloc` at
    12 GB after ≈1 min**; `Meta` `rfl` is a 200 000-heartbeat `whnf` timeout with profile
    (threshold 5, full tail read): `Ty.casesOn ↦ 1535`, **`Eq.rec ↦ 1458`**, `Term.rec 269`,
    `Term.rename 136`, `termMajorizer 133`, `List.rec 118`, `wTy 99`, `Nat.rec 85`,
    `Term.ofNat 85`, `monotone_soundness ↦ 75`, `MRealizer.syllogism 26`, `mctA/mctH 20`,
    `mtImportation 18`, `seq_mp 14`, `MRealizer.andContract 9`, `eval_h 8`, `pair_h 6`,
    `seq_of_thm 6`. Seventy-five derivation nodes reached; `Eq.rec` dominant, exactly as
    in `MonotoneLaneB`'s finding 3 — this time over the ℕ-arithmetic formulas
    (`Term.ofNat`, `mctA` unfolding), not the ℚ ones.

**What is NOT the cause — two controls, both kernel-checked below.**

* **Lane A's `induction` case is fine, on a real `pinduction`.** `indFinal`
  (`∀x (∀u (u =₀ u) → ∃v (v =₀ x))` by induction on `x`, witness `x` at every step; 368
  constructors; `pm_induction` at `Δ = []`, i.e. `seq_induction`'s `.induction base step`
  arm) evaluates through `MRealizer.induction` = `cm.precM` = `recMaj`: **`V(5) = 5`,
  `V(9) = 9`, `U(5) = 0`**, kernel ≈2 s each, refuted at `4`/`6`. So the book's `t^M`
  meets a real induction and the bound follows `x*`.
* **The proof-mode layer is fine** (`MonotoneLaneB.e1_U`/`e3_U`, 449 constructors, 2 s).

**What remains as the cause**: the `Eq.mpr`/`seq_cast` nodes. `seq_induction` at
`Δ ≠ []` casts by `Formula.subst0_weakenBy` (a theorem, not `rfl`), `pm_rw_at` and the
`qfer_*_nf` lemmas cast by `anorm`-style equations, and every such cast makes the kernel's
K-rule check the two formula indices definitionally equal — `Term.subst`/`rename` through
the closed constants (`Term.ofNat`, `monus`, `add`) at every cast, per hypothesis in `Δ`.
`mct_descent` alone has `pm_induction` under a non-empty `Δ` *and* `pm_rw_at`. The route
is the one `MonotoneLaneB` names: an `Eq.mpr`-commutation lemma for `monotone_soundness`
applied by `simp` with the equation given, so the cast is never *reduced*. Not this lane.

**The `K := 2^k` comparison with `Reference/MCT.lean`'s `Φ k g = (shift g)^[2^k+1] 0`
(CLAUDE.md Track A item 4) is therefore not made**: there is no number to compare, and
even with one the comparison would be meaningful but not literal (ℕ-MCT's `K` against
ℝ-MCT's `2^k`).

### The stalling declarations (NOT in the file)

    def rM : MRealizer cmE mctStatement := monotone_soundness tEqxiE tSpremiseE cmE mctD
    -- kernel (Lean.Kernel.whnf, witness side): std::bad_alloc at 12 GB after ≈1 min
    example : (0 : ℕ) = mfiV cmE rM xstar := by kernel_val
    -- Meta: timeout at `whnf`, profile in (c)
    set_option diagnostics true in set_option diagnostics.threshold 5 in
    example : (0 : ℕ) = mfiV cmE rM xstar := by rfl
    -- runtime: INTERNAL PANIC: out of memory (12 GB), while being built
    #eval reportD "mct_p2" mctD
