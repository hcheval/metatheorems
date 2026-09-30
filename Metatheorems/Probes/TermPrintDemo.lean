/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.TermPretty
import Metatheorems.Probes.ExtractTermDemo
import Metatheorems.Probes.TriangleBoundDemo

/-!
# Probe: printing an extracted realizer, and measuring its sharing

`Probes/ExtractTermDemo.lean` established that `extractTerm` is computable and that
`#eval tSize` on a realizer at a space produces a number. This file does the next thing that
had never been done: it **shows the term**.

Three realizers are rendered, all through `extractTerm ExtractTermDemo.wSp`:

* `UPremiseDemo.uFinal` — the premise-consuming derivation (`forall_ax` ⟶ `exist_ax`);
* `TriangleBoundDemo.triFinal` — the same route with the triangle inequality as premise;
* `TriangleBoundDemo.triUncond` — the derivation that *proves* the triangle inequality from
  `Derivable.dist_tri` instead of assuming it.

Each is rendered twice: flat, and hash-consed with repeated subterms `let`-bound.

**Result.** These terms are a few hundred nodes, so the sharing ratios are a calibration point,
not an answer. One correction: the number of distinct subterms is not the size of the
`let`-form a human would read, since an open subterm at two binder depths cannot be hoisted;
each term is therefore measured twice (naive DAG size, and the written size of the shared
form). The four correctness checks (size, scope, `expand (share t) = t`, and a negative control)
and the discussion are in the notes.

NOT imported by `Metatheorems.lean`; reachable from `Probes.lean`.
-/

namespace Metatheorems
namespace TermPrintDemo

open TermPretty

/-- One base type `X`, one function constant (`W`). -/
def N : Names MetricSpace.ι WHyperbolic.κ := Names.simple

-- The three realizers, erased

/-- `UPremiseDemo.uFinal`'s realizer — the same term `ExtractTermDemo.uRealizer` names. -/
def rU : RTerm := erase N ExtractTermDemo.uRealizer

/-- `TriangleBoundDemo.triFinal`'s realizer: premise = the triangle inequality, consumed. -/
def rTri : RTerm := erase N (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triFinal)

/-- `TriangleBoundDemo.triUncond`'s realizer: the triangle inequality *proved*, from
`Derivable.dist_tri`. -/
def rTriU : RTerm := erase N (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triUncond)

/-! Two further points, purely to see how the numbers move with size: the premise-instantiation
subderivation (smaller) and the full `triUncond` wrapped up for the metatheorem (larger). -/

/-- `UPremiseDemo.uInner`'s realizer — 186 nodes, the small end. -/
def rUInner : RTerm := erase N ExtractTermDemo.uInnerRealizer

/-- `TriangleBoundDemo.triUncondFinal`'s realizer — the large end of what is cheap here. -/
def rTriUF : RTerm := erase N (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triUncondFinal)

-- Check 1 — the printed form has the node count `tSize` reports

/-! `TermPretty.size_erase` is the general half (`(erase N t).size = Term.nodeCount t`, by
induction on `t`). These three close the gap to `ExtractTermDemo.tSize`, which is the function
whose numbers are quoted elsewhere. -/

theorem nodeCount_eq_tSize_U :
    Term.nodeCount ExtractTermDemo.uRealizer = ExtractTermDemo.tSize ExtractTermDemo.uRealizer :=
  rfl

theorem nodeCount_eq_tSize_tri :
    Term.nodeCount (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triFinal)
      = ExtractTermDemo.tSize (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triFinal) :=
  rfl

theorem nodeCount_eq_tSize_triU :
    Term.nodeCount (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triUncond)
      = ExtractTermDemo.tSize (extractTerm ExtractTermDemo.wSp TriangleBoundDemo.triUncond) :=
  rfl

/-- The printed term's node count, spelled out. `533` is `ExtractTermDemo.uRealizer_size`. -/
theorem rU_size : rU.size = 533 := by
  rw [rU, size_erase]; rfl

theorem rTri_size : rTri.size = 413 := by
  rw [rTri, size_erase]; rfl

theorem rTriU_size : rTriU.size = 431 := by
  rw [rTriU, size_erase]; rfl

/-- Non-degeneracy: the reduction really runs. -/
theorem rU_size_ne : rU.size ≠ 532 := by decide

-- Check 3 — the negative control

/-! A printer that maps distinct terms to the same string is broken in a way no size check
can see. Both control pairs below have **identical node counts**, so they are exactly the
failure a size check would miss. -/

/-- `π₁ x₀`. -/
def ctlFst : Term WHyperbolic.F [Ty.nat ×ₜ Ty.nat] Ty.nat := Term.fst (Term.var Var.vz)

/-- `π₂ x₀` — same size, different constructor. -/
def ctlSnd : Term WHyperbolic.F [Ty.nat ×ₜ Ty.nat] Ty.nat := Term.snd (Term.var Var.vz)

/-- `x₀`. -/
def ctlV0 : Term WHyperbolic.F [Ty.nat, Ty.nat] Ty.nat := Term.var Var.vz

/-- `x₁` — same size, different de Bruijn index. -/
def ctlV1 : Term WHyperbolic.F [Ty.nat, Ty.nat] Ty.nat := Term.var (Var.vs Var.vz)

theorem ctl_sizes_equal :
    Term.nodeCount ctlFst = Term.nodeCount ctlSnd ∧ Term.nodeCount ctlV0 = Term.nodeCount ctlV1 :=
  ⟨rfl, rfl⟩

/-- The erasure separates them (this is what the renderer reads). -/
theorem ctl_fst_snd_distinct : erase N ctlFst ≠ erase N ctlSnd := by decide

theorem ctl_var_distinct : erase N ctlV0 ≠ erase N ctlV1 := by decide

/-! …and so do the printed strings. -/

#eval (render (erase N ctlFst), render (erase N ctlSnd),
       render (erase N ctlFst) != render (erase N ctlSnd))
-- ("π₁ x₀", "π₂ x₀", true)

#eval (render (erase N ctlV0), render (erase N ctlV1),
       render (erase N ctlV0) != render (erase N ctlV1))
-- ("x₀", "x₁", true)

-- Check 2 — round-trip, and the measurement

/-! `summary` prints, for each term: tree size; DAG size (distinct subterms, scope ignored) and
its ratio; the number of distinct *closed* subterms; the `let`-bindings emitted; the **written
size** of the shared form and its ratio; the tree size recomputed *from* the shared form; and
whether `expand (share t) = t`. -/

/-! Non-vacuity of the round-trip check itself: corrupt the body and it must fail. Without
this, `round-trip ok` would be evidence only that `expand` and `share` agree on *something*.
-/

#eval (expand { defs := (share 2 2 rU).defs, body := .const "corrupted" } == rU,
       expand (share 2 2 rU) == rU)
-- (false, true)

#eval summary "uInner   " rUInner
#eval summary "uFinal   " rU
#eval summary "triFinal " rTri
#eval summary "triUncond" rTriU
#eval summary "triUncondFinal" rTriUF

-- The artifact

/-! Write the rendered terms to `term-print-out/realizers.md`, the way `#hilbert` writes its
listings. Re-run by rebuilding this file. -/

#eval show IO Unit from do
  let header :=
"# Extracted realizers, rendered

Generated by `Metatheorems/Probes/TermPrintDemo.lean` (`TermPretty.report`). Do not edit by
hand — rebuild `Metatheorems.Probes.TermPrintDemo` instead.

Each term is the output of `extractTerm ExtractTermDemo.wSp <derivation>`: the Dialectica
realizing term of a derivation over `WHyperbolic.Premises`, with the model deleted. `xₖ` is a
de Bruijn variable, `⋆` the inhabitant of the unit type, `⟨a, b⟩` a pair, `π₁`/`π₂` the
projections, `R[ρ]` the recursor at type `ρ`, `c` the one function constant (`W`), and
`0_X`/`d_X` the space constants. Application spines are flattened.

`DAG size` counts *distinct* subterms and ignores binder scope, so it is an **upper bound on
achievable sharing**, not the achievable sharing: de Bruijn indices are context-relative, so an
open subterm cannot be `let`-bound at top level. The hash-consed rendering therefore binds only
**closed** subterms occurring at least twice with at least two nodes, and `written size` — the
nodes actually spelled out — is the figure that says whether the term can be read.

## Summary

"
  let table :=
    summaryTable
      [ ("`UPremiseDemo.uInner`", rUInner)
      , ("`UPremiseDemo.uFinal`", rU)
      , ("`TriangleBoundDemo.triFinal`", rTri)
      , ("`TriangleBoundDemo.triUncond`", rTriU)
      , ("`TriangleBoundDemo.triUncondFinal`", rTriUF) ]
      ++ "\nThe last column is the one that matters for readability, and it grows with the "
      ++ "term: 1.00, 1.14, 1.20, 1.20, 1.35 over 186→563 nodes. Five toy points; not a trend "
      ++ "anyone should extrapolate.\n\n"
  let body :=
    report "`UPremiseDemo.uFinal`" rU
      ++ report "`TriangleBoundDemo.triFinal`" rTri
      ++ report "`TriangleBoundDemo.triUncond`" rTriU
  IO.FS.createDirAll "term-print-out"
  IO.FS.writeFile "term-print-out/realizers.md" (header ++ table ++ body)
  IO.println "wrote term-print-out/realizers.md"

#print axioms size_erase
#print axioms TermPretty.openness_erase
#print axioms rU_size
#print axioms rTri_size
#print axioms rTriU_size
#print axioms ctl_fst_snd_distinct
#print axioms ctl_var_distinct

end TermPrintDemo
end Metatheorems
