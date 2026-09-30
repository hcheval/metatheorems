# RealNumbers/Order.lean

## the forward-reference comment before `lt_add_R_inner`

`lt_trans_R` is PROVED, further down: it rests on `lt_shift`, which needs
`cauchyfy_cauchy` and the `≤ℚ`/`<ℚ` toolkit stated below.

## `<_ℝ` moves to a later index, and `lt_trans_R` (section comment before `lt_shift1`)

`lt_R f g` is `∃n. 2^{-n} ≤ℚ ĝ(n+1) −ℚ f̂(n+1)`, so transitivity has to combine two
witnesses at *different* indices (REALS_PLAN §0.4 flags this; it is why `lt_trans_R` was
never "a lift of `lt_Q_trans`"). The device is that a witness at `n` is also a witness at
every later index, **with the bound shrinking at exactly the dyadic rate**:

    2^{-n} ≤ℚ D(n)   ⟹   2^{-(n+k)} ≤ℚ D(n+k),      D(p) := ĝ(p+1) −ℚ f̂(p+1)

`lt_shift1` is one step of that and `lt_shift` iterates it. The one-step estimate is not
tight — moving from `n` to `n+1` costs `2^{-(n+2)}` on each of the two sequences, i.e.
`2^{-(n+1)}` in total, which is exactly the amount the bound is allowed to lose — but it is
*strictly* less, and that strictness is what keeps the non-strict `≤ℚ` conclusion true.

With it, transitivity needs no `max`: shifting the first witness by `n₂` and the second by
`n₁` lands both at `n₁ +ℕ n₂`, where they simply add.

## `lt_shift_at`

Doing this at the Lean level rather than with `pfrom`/`pinst` inside the proof mode is not
cosmetic: as a proof-mode hypothesis the instantiated statement has to be matched against the
goal by `pexact`, and with `Term.cauchyfy` on both sides that match runs into the
delta-expansion blow-up (measured: a heartbeat timeout). As a Lean-level implication it is fed
to `papplym … in … with …`, which never inspects the goal.

## `lt_trans_inner`

**How it is proved, and why not the obvious way** — a worked example of the display-hiding
trap family. The
first attempt ran **two nested `pobtain`s**, and `pm_exE` wraps every earlier hypothesis in
`Formula.weakenBy`, which the delaborator hides — `pexact` on the wrapped hypothesis was a
measured heartbeat timeout, not a type error. Adding `Term.subst_shift_eq_weaken` /
`Formula.substF_shift_eq_weakenBy` to `canorm` was necessary but not sufficient:
the failure moved to `canorm` itself timing out on the large packed goal. What works is
that **both `∃`-eliminations happen at the Lean level with `Derivable.exist_rule`**
(`lt_R_ex` presents the antecedent in the `le_Q` spelling, `ltBody_weakenBy` /
`lt_R_weakenBy` compute the `weakenBy` the rule's premise carries, `flip_comb` swaps the
antecedents between the two peels), so no `pobtain` ever runs and no hypothesis is ever
wrapped. `lt_trans_inner` below then sees the two witnesses as plain bound variables and is
a short forward proof over `lt_shift_at`. The same assembly closed `lt_mul_pos_R` and
`lt_add_R`.

## HISTORICAL — the nested-`pobtain` script (block comment after `lt_trans_R_core`)

HISTORICAL — the nested-`pobtain` script that could not be completed (it died at the
`pexact a` marked below: a heartbeat timeout on a `weakenBy`-wrapped hypothesis). Kept
because it is the measured failure that forced the Lean-level `exist_rule` assembly above;
its estimate steps live on inside `lt_trans_inner`.

```lean
  pmode
  pintro hyp
  pdestruct hyp with hfg hgh
  pobtain hfg with a
  canorm
  pobtain hgh with b
  -- the second `pobtain` weakens the *first* witness's hypothesis under a binder, leaving a
  -- bare `renameF (ext vs)` that `q_cons_norm` does not touch; this is `anorm_ren`'s first
  -- step, which turns that renaming into the `Subst.cons` normal form `canorm` understands
  simp only [Formula.renameF_ext_eq_substF_cons, Formula.renameF_eq_substF]
  canorm
  pexists (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))
  canorm
  phave ha2 : le_Q (.app Term.pow2neg_Q (.var (.vs .vz)))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken.weaken (.app .succ (.var (.vs .vz))))
        (Term.app2 Term.cauchyfy f.weaken.weaken (.app .succ (.var (.vs .vz)))))
  · pexact a
  papplym (lt_shift_at f.weaken.weaken g.weaken.weaken (.var (.vs .vz)) (.var .vz))
    in ha2 with hA
  papplym (lt_shift_at g.weaken.weaken h.weaken.weaken (.var .vz) (.var (.vs .vz)))
    in b with hB0
  prw (add_comm (.var .vz) (.var (.vs .vz))) in hB0 with hB
  phave hzero : le_Q Term.zero_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
  · papplym (lt_Q_imp_le_Q Term.zero_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    papplym (lt_le_Q_trans Term.zero_Q
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    psplit
    · pthm (zero_lt_pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    · pexact hB
  papplym (le_Q_congr
    (Term.app2 Term.add_Q
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))) Term.zero_Q)
    (Term.app2 Term.add_Q
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy f.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
      (Term.app2 Term.sub_Q
        (Term.app2 Term.cauchyfy h.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
        (Term.app2 Term.cauchyfy g.weaken.weaken
          (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
    (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
    (add_Q_zero_inst
      (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
    (eqQsym (sub_Q_trans_split
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))))
  papplym (le_Q_add_both
    (.app Term.pow2neg_Q (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))
    Term.zero_Q
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy f.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz)))))
    (Term.app2 Term.sub_Q
      (Term.app2 Term.cauchyfy h.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))
      (Term.app2 Term.cauchyfy g.weaken.weaken
        (.app .succ (Term.app2 Term.add (.var (.vs .vz)) (.var .vz))))))
  psplit
  · pexact hA
  · pexact hzero
```
