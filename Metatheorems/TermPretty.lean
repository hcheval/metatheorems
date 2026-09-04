/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Std.Data.HashMap
import Metatheorems.Term

/-!
# Printing an extracted realizer — a computable renderer for `Term`

`Metatheorems/Hilbert.lean` renders *derivations*, and does it at the `Expr` level: a
`CommandElab` that walks the elaborated proof term with `MetaM`. This file is its counterpart
for **terms**, and it is deliberately *not* a metaprogram. `extractTerm`
(`Dialectica/Syntactic.lean`) takes no model, so an extracted realizer is an ordinary
computable `Term` value; the right way to look at one is `#eval`, not the delaborator.

So everything here is a plain function. Nothing needs `MetaM`, nothing needs an `Expr`, and
the whole pipeline runs inside `#eval`.

## The shape of the pipeline

```
Term F Γ τ  --erase-->  RTerm  --share-->  Shared  --renderShared-->  String
                          |                   |
                          | size              | expand  (round-trip check)
                          v                   v
                        tree size           RTerm
```

`RTerm` is the **untyped** mirror of `Term`: the same seven node shapes with all the type
indices erased to strings. Erasing first is what makes hash-consing possible at all —
`Term F Γ τ` is indexed by its context and type, so two structurally identical subterms of one
realizer generally live at *different* Lean types and cannot be compared, let alone put in a
`HashMap`. `RTerm` has `DecidableEq` and `Hashable`, so they can.

The price of erasing is that the renderer could in principle conflate two distinct terms. That
is checked rather than assumed, in two ways: `size_erase` proves the node count is preserved
exactly (so nothing is silently dropped), and `Probes/TermPrintDemo.lean` carries a negative
control on a pair of terms differing in one constructor.

## Sharing

`share` collects every distinct subterm of the tree together with its occurrence count, binds
the repeated ones as `let`s (smallest first, so a definition only ever refers to earlier ones),
and rewrites the body against them. `expand` inverts that, and the demo checks
`expand (share t) = t` — which is the statement that the shared rendering has not lost
anything.

The number reported as **DAG size** is the count of *distinct* subterms, i.e. the number of
nodes the term has when maximally shared. Tree size is what `#eval tSize` reports.

## Names

`F : κ → Ty ι` is arbitrary, so nothing here can know what a function constant is called.
`Names ι κ` supplies the two naming functions; `Names.simple` prints every base type as `X`
and every constant as `c`, which is exactly right for the one-base-type, one-constant
signatures in this project, and `Names.ofToString` uses the indices when they have a
`ToString`.

## Totality

`RTerm`, `RTerm.size`, `Term.nodeCount`, `erase` and `size_erase` are total — that is the part
with a theorem attached. The layout and hash-consing functions are `partial`: they are driven
by `#eval` only, and making them structural would cost a termination argument for no gain.
-/

namespace Metatheorems
namespace TermPretty

open Std (Format)

-- ============================================================================
-- The untyped mirror
-- ============================================================================

/-- An erased term: `Term F Γ τ` with every type index replaced by a string.

`ref` is not produced by `erase`; it is the placeholder for a `let`-bound shared subterm and
appears only in the output of `share`. -/
inductive RTerm where
  /-- de Bruijn variable, by index. -/
  | var   : Nat → RTerm
  /-- A constant: `0`, `S`, `R[ρ]`, a function constant, `0_X`, `d_X`, `⋆`. -/
  | const : String → RTerm
  /-- Application. -/
  | app   : RTerm → RTerm → RTerm
  /-- Lambda, carrying the *printed* binder type. -/
  | lam   : String → RTerm → RTerm
  /-- Pairing. -/
  | pair  : RTerm → RTerm → RTerm
  /-- First projection. -/
  | fst   : RTerm → RTerm
  /-- Second projection. -/
  | snd   : RTerm → RTerm
  /-- Reference to the `n`-th shared binding. Only `share` produces these. -/
  | ref   : Nat → RTerm
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace RTerm

/-- Number of nodes, counting every occurrence: the **tree** size. -/
def size : RTerm → Nat
  | .var _    => 1
  | .const _  => 1
  | .ref _    => 1
  | .app f a  => 1 + f.size + a.size
  | .lam _ b  => 1 + b.size
  | .pair a b => 1 + a.size + b.size
  | .fst p    => 1 + p.size
  | .snd p    => 1 + p.size

/-- How many enclosing binders the term needs: `0` iff it is closed, otherwise one more than
the largest free de Bruijn index.

**This is what makes hash-consing correct.** De Bruijn indices are context-relative, so two
*syntactically identical* subterms occurring at different binder depths do not denote the same
thing, and an open subterm cannot be hoisted into a top-level `let` at all. `share` therefore
binds only subterms with `openness = 0`. Dropping this check produces a `let`-listing that
looks fine, round-trips fine as a tree, and is mathematically wrong. -/
def openness : RTerm → Nat
  | .var n    => n + 1
  | .const _  => 0
  -- a reference always stands for a closed binding
  | .ref _    => 0
  | .app f a  => max f.openness a.openness
  | .pair a b => max a.openness b.openness
  | .lam _ b  => b.openness - 1
  | .fst p    => p.openness
  | .snd p    => p.openness

/-- No free variables, hence safe to bind at top level. -/
def isClosed (t : RTerm) : Bool := t.openness == 0

end RTerm

-- ============================================================================
-- Naming
-- ============================================================================

/-- How to spell the two families of indices a signature is parameterised by. -/
structure Names (ι κ : Type) where
  /-- Name of the base type `X_i`. -/
  base : ι → String
  /-- Name of the function constant `f_χ`. -/
  func : κ → String

/-- The default: one base type `X`, one constant `c`. Correct for every signature in this
project (`ι = Unit`, `κ` a small enumeration), and honest for any other — it does not pretend
to know indices it cannot see. -/
def Names.simple {ι κ : Type} : Names ι κ := ⟨fun _ => "X", fun _ => "c"⟩

/-- Names from the indices themselves, when they can be printed. -/
def Names.ofToString {ι κ : Type} [ToString ι] [ToString κ] : Names ι κ :=
  ⟨fun i => "X" ++ toString i, fun f => "c" ++ toString f⟩

-- ============================================================================
-- Types
-- ============================================================================

/-- `n` as a subscript, for de Bruijn indices and shared-binding names. -/
def subscript (n : Nat) : String :=
  String.ofList ((Nat.toDigits 10 n).map fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080))

private def parenIf (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- Render a type. Arrows are right-associative at level 25, products at level 35, matching the
`→ₜ` / `×ₜ` notations. -/
def tyString {ι : Type} (nb : ι → String) : Nat → Ty ι → String
  | _, .nat      => "ℕ"
  | _, .base i   => nb i
  | _, .unit     => "𝟙"
  | p, .arr a b  => parenIf (p > 25) (tyString nb 26 a ++ " → " ++ tyString nb 25 b)
  | p, .prod a b => parenIf (p > 35) (tyString nb 36 a ++ " × " ++ tyString nb 35 b)

-- ============================================================================
-- Erasure
-- ============================================================================

variable {ι κ : Type} {F : κ → Ty ι}

/-- A de Bruijn variable as its index. -/
def varIndex : {Γ : Ctx ι} → {τ : Ty ι} → Var Γ τ → Nat
  | _, _, .vz   => 0
  | _, _, .vs v => varIndex v + 1

/-- Node count of a `Term`: the same recursion as `Probes/ExtractTermDemo.tSize`, restated
here so that `size_erase` can be proved where the printer lives. -/
def _root_.Metatheorems.Term.nodeCount :
    {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → Nat
  | _, _, .var _      => 1
  | _, _, .app f a    => 1 + Term.nodeCount f + Term.nodeCount a
  | _, _, .lam b      => 1 + Term.nodeCount b
  | _, _, .zero       => 1
  | _, _, .succ       => 1
  | _, _, .prec _     => 1
  | _, _, .func _     => 1
  | _, _, .zeroX _    => 1
  | _, _, .dist _     => 1
  | _, _, .unitI      => 1
  | _, _, .mkPair a b => 1 + Term.nodeCount a + Term.nodeCount b
  | _, _, .fst p      => 1 + Term.nodeCount p
  | _, _, .snd p      => 1 + Term.nodeCount p

/-- Erase a term to its untyped mirror. The `lam` case reads its binder type off the *type
index* (`τ = ρ →ₜ σ`), which is the only place it is available. -/
def erase (N : Names ι κ) : {Γ : Ctx ι} → {τ : Ty ι} → Term F Γ τ → RTerm
  | _, _, .var v            => .var (varIndex v)
  | _, _, .app f a          => .app (erase N f) (erase N a)
  | _, _, .zero             => .const "0"
  | _, _, .succ             => .const "S"
  | _, _, .prec ρ           => .const ("R[" ++ tyString N.base 0 ρ ++ "]")
  | _, .arr ρ _, .lam b     => .lam (tyString N.base 0 ρ) (erase N b)
  | _, _, .func f           => .const (N.func f)
  | _, _, .zeroX i          => .const ("0_" ++ N.base i)
  | _, _, .dist i           => .const ("d_" ++ N.base i)
  | _, _, .unitI            => .const "⋆"
  | _, _, .mkPair a b       => .pair (erase N a) (erase N b)
  | _, _, .fst p            => .fst (erase N p)
  | _, _, .snd p            => .snd (erase N p)

/-- **Erasure preserves the node count exactly.** This is the correctness statement that
matters for the printer: whatever it does to the *display*, it does not drop or duplicate
structure. Combined with the demo's `Term.nodeCount t = tSize t`, it says the printed form
has as many nodes as `#eval tSize` reports. -/
theorem size_erase (N : Names ι κ) :
    ∀ {Γ : Ctx ι} {τ : Ty ι} (t : Term F Γ τ), (erase N t).size = Term.nodeCount t
  | _, _, .var _      => rfl
  | _, _, .app f a    => by
      simp only [erase, RTerm.size, Term.nodeCount, size_erase N f, size_erase N a]
  | _, _, .zero       => rfl
  | _, _, .succ       => rfl
  | _, _, .prec _     => rfl
  | _, .arr _ _, .lam b => by
      simp only [erase, RTerm.size, Term.nodeCount, size_erase N b]
  | _, _, .func _     => rfl
  | _, _, .zeroX _    => rfl
  | _, _, .dist _     => rfl
  | _, _, .unitI      => rfl
  | _, _, .mkPair a b => by
      simp only [erase, RTerm.size, Term.nodeCount, size_erase N a, size_erase N b]
  | _, _, .fst p      => by simp only [erase, RTerm.size, Term.nodeCount, size_erase N p]
  | _, _, .snd p      => by simp only [erase, RTerm.size, Term.nodeCount, size_erase N p]

/-- A well-typed variable's index is inside its context. -/
theorem varIndex_lt : ∀ {Γ : Ctx ι} {τ : Ty ι} (v : Var Γ τ), varIndex v < Γ.length
  | _, _, .vz   => Nat.succ_pos _
  | _, _, .vs v => Nat.succ_lt_succ (varIndex_lt v)

/-- **Erasure respects scope.** A term in context `Γ` erases to something needing at most
`Γ.length` enclosing binders — in particular a closed term erases to a closed `RTerm`. This is
what licenses `share`'s `isClosed` test, and it is the statement an off-by-one in `varIndex`
or a mishandled `lam` would break. -/
theorem openness_erase (N : Names ι κ) :
    ∀ {Γ : Ctx ι} {τ : Ty ι} (t : Term F Γ τ), (erase N t).openness ≤ Γ.length
  | _, _, .var v   => varIndex_lt v
  | _, _, .app f a => by
      simp only [erase, RTerm.openness]
      exact Nat.max_le.2 ⟨openness_erase N f, openness_erase N a⟩
  | _, _, .zero    => Nat.zero_le _
  | _, _, .succ    => Nat.zero_le _
  | _, _, .prec _  => Nat.zero_le _
  | _, .arr _ _, .lam b => by
      simp only [erase, RTerm.openness]
      exact Nat.sub_le_sub_right (openness_erase N b) 1
  | _, _, .func _  => Nat.zero_le _
  | _, _, .zeroX _ => Nat.zero_le _
  | _, _, .dist _  => Nat.zero_le _
  | _, _, .unitI   => Nat.zero_le _
  | _, _, .mkPair a b => by
      simp only [erase, RTerm.openness]
      exact Nat.max_le.2 ⟨openness_erase N a, openness_erase N b⟩
  | _, _, .fst p   => by simp only [erase, RTerm.openness]; exact openness_erase N p
  | _, _, .snd p   => by simp only [erase, RTerm.openness]; exact openness_erase N p

-- ============================================================================
-- Layout
-- ============================================================================

/-! Application spines are flattened — `f a b c`, not `((f a) b) c` — which is the single
biggest difference between a readable realizer and an unreadable one. Everything else is
ordinary precedence-driven parenthesisation:

| level | what needs parentheses at it |
|---|---|
| 0 | nothing (top level, a `λ` body, inside `⟨…⟩`) |
| 1 | `λ` |
| 2 | `λ`, application spines, `π₁`/`π₂` |
-/

private def fparen (b : Bool) (f : Format) : Format :=
  if b then Format.paren f else f

mutual

/-- Lay out a term at precedence `p`. -/
partial def fmt (p : Nat) : RTerm → Format
  | .var n    => Format.text ("x" ++ subscript n)
  | .ref n    => Format.text ("s" ++ subscript n)
  | .const s  => Format.text s
  | .pair a b => Format.group (Format.nest 1
      ("⟨" ++ fmt 0 a ++ "," ++ Format.line ++ fmt 0 b ++ "⟩"))
  | .fst t    => fparen (p ≥ 2) (Format.group (Format.nest 2 ("π₁" ++ Format.line ++ fmt 2 t)))
  | .snd t    => fparen (p ≥ 2) (Format.group (Format.nest 2 ("π₂" ++ Format.line ++ fmt 2 t)))
  | .lam ty b => fparen (p ≥ 1) (Format.group (Format.nest 2
      ("λ:" ++ Format.text ty ++ "." ++ Format.line ++ fmt 0 b)))
  | .app f a  => fparen (p ≥ 2) (Format.group (Format.nest 2 (fmtSpine f [fmt 2 a])))

/-- Flatten `((h a) b) c` into `h a b c`. -/
partial def fmtSpine : RTerm → List Format → Format
  | .app f a, acc => fmtSpine f (fmt 2 a :: acc)
  | h,        acc => Format.joinSep (fmt 2 h :: acc) Format.line

end

/-- Width the renderings are laid out at. -/
def width : Nat := 100

/-- A term as text, spines flattened, de Bruijn variables as `xₖ`. -/
def render (t : RTerm) : String := (fmt 0 t).pretty width

-- ============================================================================
-- Hash-consing
-- ============================================================================

/-- A term with its repeated subterms named. `defs[i]` may mention `.ref j` only for `j < i`,
so the bindings can be read top to bottom. -/
structure Shared where
  /-- The `let`-bound subterms, smallest first. -/
  defs : Array RTerm
  /-- The term itself, with references substituted in. -/
  body : RTerm
  deriving Inhabited

/-- Occurrence counts of every distinct subterm, over the whole tree. -/
partial def counts (t : RTerm) : Std.HashMap RTerm Nat :=
  go t {}
where
  go (t : RTerm) (m : Std.HashMap RTerm Nat) : Std.HashMap RTerm Nat :=
    let m := m.insert t ((m.getD t 0) + 1)
    match t with
    | .app f a  => go a (go f m)
    | .pair a b => go b (go a m)
    | .lam _ b  => go b m
    | .fst p    => go p m
    | .snd p    => go p m
    | _         => m

/-- Number of **distinct** subterms: the size of the term as a maximally shared DAG.

This is the naive structural number, and it is an **upper bound on achievable sharing, not the
achievable sharing**: it counts open subterms, which cannot be `let`-bound (see
`RTerm.openness`). `writtenSize` is the honest figure. -/
def dagSize (t : RTerm) : Nat := (counts t).size

/-- Number of distinct **closed** subterms — the ones that can actually be named. -/
def closedDagSize (t : RTerm) : Nat :=
  ((counts t).toList.filter fun p => p.1.isClosed).length

/-- Replace every subterm carrying a reference number, except at the root. -/
partial def abstract (idx : Std.HashMap RTerm Nat) (t : RTerm) : RTerm :=
  match t with
  | .app f a  => .app (sub f) (sub a)
  | .pair a b => .pair (sub a) (sub b)
  | .lam ty b => .lam ty (sub b)
  | .fst p    => .fst (sub p)
  | .snd p    => .snd (sub p)
  | _         => t
where
  sub (u : RTerm) : RTerm :=
    match idx[u]? with
    | some n => .ref n
    | none   => abstract idx u

/-- Bind every **closed** subterm that occurs at least `minCount` times and has at least
`minSize` nodes.

Three filters, each load-bearing:

* `isClosed` — **correctness**. An open subterm's de Bruijn indices mean different things at
  different binder depths; hoisting one out is simply wrong. See `RTerm.openness`.
* `minCount` — sharing something that occurs once makes the output longer.
* `minSize` — binding a leaf is pointless: `x₀` is not shortened by calling it `s₃`. -/
partial def share (minCount : Nat := 2) (minSize : Nat := 2) (t : RTerm) : Shared :=
  let cand : Array RTerm :=
    ((counts t).toList.filter fun p =>
      p.2 ≥ minCount && p.1.size ≥ minSize && p.1.isClosed).toArray.map (·.1)
  -- smallest first, so every definition only ever refers to earlier ones
  let sorted := cand.qsort fun a b => a.size < b.size
  let idx : Std.HashMap RTerm Nat :=
    sorted.zipIdx.foldl (fun m (u, i) => m.insert u i) {}
  { defs := sorted.map (abstract idx)
    body := abstract idx t }

/-- Undo the sharing: substitute every reference back in. -/
partial def substRefs (full : Array RTerm) : RTerm → RTerm
  | .ref n    => full[n]!
  | .app f a  => .app (substRefs full f) (substRefs full a)
  | .pair a b => .pair (substRefs full a) (substRefs full b)
  | .lam ty b => .lam ty (substRefs full b)
  | .fst p    => .fst (substRefs full p)
  | .snd p    => .snd (substRefs full p)
  | t         => t

/-- Expand a shared form back to a tree. `expand (share t) = t` is the round-trip check. -/
def expand (s : Shared) : RTerm :=
  let full := s.defs.foldl (fun acc d => acc.push (substRefs acc d)) #[]
  substRefs full s.body

/-- Tree size of a shared form, i.e. the size of its expansion — computed *without* expanding,
by weighting each reference by the size of what it stands for. Agreement with `RTerm.size` of
the original is a second, independent check on `share`. -/
def expandedSize (s : Shared) : Nat :=
  let sizes := s.defs.foldl (fun acc d => acc.push (weigh acc d)) (#[] : Array Nat)
  weigh sizes s.body
where
  weigh (sizes : Array Nat) : RTerm → Nat
    | .ref n    => sizes[n]!
    | .app f a  => 1 + weigh sizes f + weigh sizes a
    | .pair a b => 1 + weigh sizes a + weigh sizes b
    | .lam _ b  => 1 + weigh sizes b
    | .fst p    => 1 + weigh sizes p
    | .snd p    => 1 + weigh sizes p
    | _         => 1

/-- **The number that decides whether a human can read it**: how many nodes the shared form
actually spells out — every `let`-bound definition plus the body, counting each reference as
one node. Compare `RTerm.size` of the original. -/
def writtenSize (s : Shared) : Nat :=
  s.defs.foldl (fun acc d => acc + d.size) 0 + s.body.size

-- ============================================================================
-- Reports
-- ============================================================================

/-- The shared form, as `let`-bindings followed by the body. -/
def renderShared (s : Shared) : String := Id.run do
  let mut out := ""
  for (d, i) in s.defs.zipIdx do
    out := out ++ "let s" ++ subscript i ++ " =\n  " ++ (fmt 0 d).pretty width ++ "\n"
  out := out ++ "in\n  " ++ (fmt 0 s.body).pretty width ++ "\n"
  return out

/-- `a / b` to two decimal places, without floats. -/
def ratio2 (a b : Nat) : String :=
  if b == 0 then "-" else
    let q := (a * 100) / b
    toString (q / 100) ++ "." ++ (if q % 100 < 10 then "0" else "") ++ toString (q % 100)

/-- Everything measured about one term, as a Markdown section: the two sizes, the sharing
ratio, both renderings, and the two self-checks. -/
def report (title : String) (t : RTerm) : String := Id.run do
  let s := share 2 2 t
  let tree := t.size
  let dag := dagSize t
  let cdag := closedDagSize t
  let written := writtenSize s
  let ok := decide (expand s = t)
  let mut out := "## " ++ title ++ "\n\n"
  out := out ++ "| measure | value |\n|---|---:|\n"
  out := out ++ "| tree size (nodes, every occurrence) | " ++ toString tree ++ " |\n"
  out := out ++ "| DAG size (distinct subterms, scope ignored) | " ++ toString dag ++ " |\n"
  out := out ++ "| distinct **closed** subterms | " ++ toString cdag ++ " |\n"
  out := out ++ "| `let`-bindings emitted (closed, repeated, ≥2 nodes) | "
    ++ toString s.defs.size ++ " |\n"
  out := out ++ "| **written size** (nodes actually spelled out) | " ++ toString written
    ++ " |\n"
  out := out ++ "| structural sharing ratio (tree / DAG) | " ++ ratio2 tree dag ++ " |\n"
  out := out ++ "| realizable compression (tree / written) | " ++ ratio2 tree written ++ " |\n"
  out := out ++ "| expanded size of shared form | " ++ toString (expandedSize s) ++ " |\n"
  out := out ++ "| round-trip `expand (share t) = t` | " ++ (if ok then "ok" else "FAILED")
    ++ " |\n\n"
  out := out ++ "### Flat\n\n```\n" ++ render t ++ "\n```\n\n"
  out := out ++ "### Hash-consed\n\n```\n" ++ renderShared s ++ "```\n\n"
  return out

/-- All the numbers for several terms at once, as one Markdown table. -/
def summaryTable (rows : List (String × RTerm)) : String := Id.run do
  let mut out :=
    "| term | tree | DAG | tree/DAG | closed subterms | `let`s | written | tree/written |\n"
      ++ "|---|---:|---:|---:|---:|---:|---:|---:|\n"
  for (name, t) in rows do
    let s := share 2 2 t
    let w := writtenSize s
    out := out ++ "| " ++ name ++ " | " ++ toString t.size ++ " | " ++ toString (dagSize t)
      ++ " | " ++ ratio2 t.size (dagSize t) ++ " | " ++ toString (closedDagSize t)
      ++ " | " ++ toString s.defs.size ++ " | " ++ toString w
      ++ " | " ++ ratio2 t.size w ++ " |\n"
  return out

/-- One line of numbers, for `#eval` at the console. -/
def summary (title : String) (t : RTerm) : String :=
  let s := share 2 2 t
  title ++ ": tree " ++ toString t.size
    ++ ", DAG " ++ toString (dagSize t) ++ " (ratio " ++ ratio2 t.size (dagSize t) ++ ")"
    ++ ", closed-DAG " ++ toString (closedDagSize t)
    ++ ", lets " ++ toString s.defs.size
    ++ ", written " ++ toString (writtenSize s)
      ++ " (ratio " ++ ratio2 t.size (writtenSize s) ++ ")"
    ++ ", expanded " ++ toString (expandedSize s)
    ++ ", round-trip " ++ (if expand s = t then "ok" else "FAILED")

end TermPretty
end Metatheorems
