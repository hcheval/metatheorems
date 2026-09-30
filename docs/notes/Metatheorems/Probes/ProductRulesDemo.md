# Probes/ProductRulesDemo.lean

## module header

### Negative control

The wrong projection is **not** derivable by the new rules. Kept as a comment because a
failing declaration is not a green build; the text is the verbatim error from
`lake env lean` on the snippet (2026-09-05):

```
example : Derivable pFE al P (Formula.eq0 (Term.fst pairTerm) (Term.app Term.succ Term.zero)) :=
  .pair_fst Term.zero (Term.app Term.succ Term.zero)
```

    error: Type mismatch
      Derivable.pair_fst 0 (Term.succ ⬝ 0)
    has type
      Derivable ?m.54 ?m.33 ?m.34 (eqAtType nat (0.mkPair (Term.succ ⬝ 0)).fst 0)
    but is expected to have type
      Derivable pFE al P (Formula.eq0 pairTerm.fst (Term.succ ⬝ 0))

With the arguments left to inference (`.pair_fst _ _`):

    error: Type mismatch
      Derivable.pair_fst ?m.38 ?m.39
    has type
      Derivable ?m.32 ?m.33 ?m.34 (eqAtType ?m.36 (Term.mkPair ?m.38 ?m.39).fst ?m.38)
    but is expected to have type
      Derivable pFE al P (Formula.eq0 pairTerm.fst (Term.succ ⬝ 0))

— the rule's conclusion has the *same* `?m.38` in both the pair and the right-hand side, and
`0` and `S 0` cannot both be it. The right projection in the same shape (`hfst` below)
elaborates in the same run. Nothing else in the system can bridge it either:
`soundness` refutes the target in the standard model (`(0, 1).1 = 1` is false), so it is
underivable outright, not merely underivable *by these rules*.
