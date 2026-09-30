# QVal.lean

## module header

That whole layer is object-level `Term`s,
so there was no Lean-level function saying *which rational* a code denotes. `qval` is that
function, and it is what the phrase "`(x)◦` is a representative of `x`" needs in order to be
a statement at all.

### What this does NOT do

It does not connect `qval` to `Term.interpret` of `Term.rat_num`/`Term.lt_Q_dec`. That is a
separate bridge (evaluating the object-level `prec`-recursions `div2`, `inv_triag`, … in the
standard model) and is not attempted here. So the Cauchy condition below is stated at the
level of *actual rationals*, which is what Leuştean's (4.2) means mathematically, not at the
level of the object-level decision term `lt_Q_dec`.
