/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems

/-!
# `#hilbert` — printing a `Derivable` proof term as a Hilbert derivation

`Derivable` is `Type`-valued, so every proof in this development *is* a term whose head
constructors are exactly the inference rules of Appendix 9. This file walks such a term and
emits the numbered, line-by-line listing a Hilbert-style proof is normally written as:

```
 1.  A ∧ᶠ A →ᶠ A                                     ∧-weakening
 2.  A →ᶠ A ∧ᶠ A                                     ∧-contraction
 3.  A →ᶠ A                                          syllogism 2, 1
```

## Sharing

Proof terms here are DAGs, not trees: the scripts are long `let`-chains and the same
subderivation is referenced many times. Expanding naively is exponential. Every distinct
subproof is therefore numbered **once** and cited afterwards by its line number — which is
also exactly what makes a Hilbert listing readable, so sharing is a feature and not merely an
optimisation. Two mechanisms:

* `let`/`have` binders are entered with `withLetDecl`, the bound value is numbered, and the
  free variable is remembered as that line;
* a structural cache on the elaborated expression catches literal repetitions that were not
  shared through a binder.

## Opaqueness

The default is that **only `Derivable`'s own constructors are transparent**. Any other
constant — `PropositionalLemmas.I_comb`, an `Arithmetic` lemma, a `ProofMode` tactic lemma —
is printed as a *single* line citing that constant by name, with its `Derivable`-typed
arguments numbered as its own premises. That is what a paper proof does when it says "by
Lemma 3.2", and it is the only tenable default for the proof-mode layer: `ProofMode` is
definitionally `Derivable`, so a proof-mode proof *will* traverse — into thousands of lines,
because every `pintro`/`prw` is itself a derivation.

`#hilbert foo unfolding bar baz` makes the named constants transparent (delta-unfolded and
walked). `#hilbert foo all` makes everything transparent **except the proof-mode layer**,
which is what you want on a combinator and never what you want on `mct_p2`.

There is **no** `unfolding *`: the parser takes `ident+` and resolves each through
`realizeGlobalConstNoOverloadWithInfo`, so `*` does not even parse. This paragraph claimed
otherwise until 2026-09-07. To expand a proof-mode constant, name it under `unfolding`, one
at a time — and see `shouldUnfoldAt` for why `all` stops where it does.

## `depth n` — the fueled unfolding (2026-09-07)

`#hilbert foo depth 2` makes the proof-mode layer transparent, but only **two `ProofMode`
unfoldings deep along any path**; below that a proof-mode constant is cited by name exactly as
the default does. So the listing degrades gracefully instead of not terminating, and the fuel
is a *display knob*: at depth 1 you see which proof-mode tactic each step was, at depth 2 you
see the `seq_*` combinators it is built from, and so on down to raw `Derivable` constructors.

The design is `Probes/ExprBound.lean`'s, one level up: fuel plus a name-based stop set
(`keeping g h`), with the memo keyed on the fuel as well as the expression. Keying the memo on
the fuel is forced — the same subderivation reached with two different budgets renders
differently — and it is what costs the sharing that makes depth expensive. `all` and
`unfolding` are unchanged and consume no fuel; only `ProofMode` names do.

`keeping` matters as much as the fuel, and for a reason specific to this project: a *named
sub-derivation* written in the proof mode (`ProofMode.mct_descent`) lives in the same
namespace as the tactic lemmas (`ProofMode.pm_mp`), so no name test separates "the plumbing"
from "the mathematics". `depth 1 keeping mct_descent` says expand the plumbing and cite the
mathematics, which is what a paper proof does.

Measurements (`Probes/HilbertDepth.lean`) are in that file's header.

## Output

Both a Markdown table and a LaTeX `longtable` are written. Formulas are rendered by the
existing object-language delaborators in `ProofMode/Pretty.lean` — `→ᶠ`, `∧ᶠ`, `∀ᶠ x₀ : nat`,
`xₖ` variable tokens — and the LaTeX form is a token-level rewrite of that same rendering
(`→ᶠ ↦ \to`, `x₀ ↦ x_0`, …), so the two never drift apart.
-/

namespace Metatheorems
namespace Hilbert

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

-- ============================================================================
-- Rule names
-- ============================================================================

/-- Display name for a `Derivable` constructor, following `axioms.tex`, `rules.tex` and
`intuitionistic-rules.tex`. `none` means "not a constructor of `Derivable`". -/
def ctorRuleName : Name → Option String
  | ``Derivable.premise      => some "premise"
  | ``Derivable.or_contract  => some "∨-contraction"
  | ``Derivable.and_contract => some "∧-contraction"
  | ``Derivable.or_weak      => some "∨-weakening"
  | ``Derivable.and_weak     => some "∧-weakening"
  | ``Derivable.or_perm      => some "∨-permutation"
  | ``Derivable.and_perm     => some "∧-permutation"
  | ``Derivable.exfalso      => some "ex falso quodlibet"
  | ``Derivable.forall_ax    => some "∀-axiom"
  | ``Derivable.exist_ax     => some "∃-axiom"
  | ``Derivable.mp           => some "modus ponens"
  | ``Derivable.syllogism    => some "syllogism"
  | ``Derivable.exportation  => some "exportation"
  | ``Derivable.importation  => some "importation"
  | ``Derivable.expansion    => some "expansion"
  | ``Derivable.forall_rule  => some "∀-rule"
  | ``Derivable.exist_rule   => some "∃-rule"
  | ``Derivable.univ_gen     => some "generalisation"
  | ``Derivable.succ_ne_zero => some "successor axiom (S x ≠ 0)"
  | ``Derivable.succ_inj     => some "successor axiom (S injective)"
  | ``Derivable.beta_eq      => some "β-equality"
  | ``Derivable.pair_fst     => some "β×₁ (fst of pair)"
  | ``Derivable.pair_snd     => some "β×₂ (snd of pair)"
  | ``Derivable.pair_eta     => some "η× (pair of projections)"
  | ``Derivable.rec_zero     => some "recursor (zero)"
  | ``Derivable.rec_succ     => some "recursor (successor)"
  | ``Derivable.refl0        => some "reflexivity"
  | ``Derivable.sym0         => some "symmetry"
  | ``Derivable.trans0       => some "transitivity"
  | ``Derivable.qfer         => some "QF-ER"
  | ``Derivable.induction    => some "induction"
  | ``Derivable.lem          => some "LEM"
  | ``Derivable.markov       => some "Markov (Mω)"
  | ``Derivable.ip           => some "IP^ω_∀"
  | ``Derivable.ac           => some "AC"
  | ``Derivable.qfac         => some "QF-AC"
  | _ => none

/-- Standard combinator names for the library lemmas that have one. Cosmetic: it only
changes how an opaque citation is spelled. -/
def libRuleName : Name → Option String
  | ``I_comb => some "I (identity)"
  | ``K_comb => some "K"
  | ``S_comb => some "S"
  | ``flip_comb => some "C (flip)"
  | ``contract => some "W (contraction)"
  | ``mp_form => some "MP as a formula"
  | _ => none

/-- Constants that are pure re-typings and carry no proof content of their own. They are
walked through silently rather than getting a line. -/
def isTransparentWrapper : Name → Bool
  | ``Derivable.castAllowed  => true
  | ``ProofMode.SeqD.toSeq   => true
  | ``ProofMode.SeqD.ofSeq   => true
  -- `nf ▸ h` and friends: a retyping of `h` along a normalisation equation.
  | ``Eq.mpr                 => true
  | ``Eq.mp                  => true
  | ``Eq.ndrec               => true
  | ``Eq.rec                 => true
  | ``cast                   => true
  | ``id                     => true
  | _ => false

-- ============================================================================
-- Lines
-- ============================================================================

/-- One line of the listing. `formula` is kept twice, already rendered: once in the object
notation of `ProofMode/Pretty.lean` and once in LaTeX. -/
structure Line where
  num : Nat
  uni : String
  tex : String
  rule : String
  premises : List Nat
  deriving Inhabited

structure Config where
  /-- Constants to delta-unfold and walk instead of citing. -/
  unfold : NameSet := {}
  /-- Constants **never** unfolded, whatever `all` or `depth` say.

  This is the stop set, and per `Probes/ExprBound.lean`'s finding it is at least as much of
  the design as the fuel is: what you refuse to unfold is the vocabulary the listing gets
  written in. On a proof-mode derivation the thing you want to keep is usually a *named
  sub-derivation* — `mct_descent` inside `mct_body` — which lives in the same `ProofMode`
  namespace as the tactic lemmas and is therefore indistinguishable from them by name alone.
  `keeping mct_descent` is how you say "expand the tactics, cite the mathematics". -/
  keep : NameSet := {}
  /-- Unfold *every* constant. Useful on combinators, disastrous on proof-mode proofs. -/
  unfoldAll : Bool := false
  /-- How many `ProofMode` unfoldings deep to go along any one path. `0` — the default — is
  the historical behaviour: the proof-mode layer is opaque and every tactic gets one cited
  line. Only `ProofMode` names draw on this budget. -/
  pmDepth : Nat := 0
  /-- Hard cap; a runaway traversal stops rather than hanging. -/
  maxLines : Nat := 20000

structure State where
  lines : Array Line := #[]
  /-- Keyed on the remaining proof-mode budget as well as the expression: the same
  subderivation reached with different budgets left renders differently (expanded here, cited
  there), so a fuel-blind key would report the first rendering for both. At `pmDepth = 0` —
  every pre-2026-09-07 invocation — the key is constantly `(0, e)` and this is the old cache
  exactly. -/
  cache : Std.HashMap (Nat × ExprStructEq) Nat := {}
  fvars : Std.HashMap (Nat × FVarId) Nat := {}

abbrev M := ReaderT Config (StateRefT State MetaM)

-- ============================================================================
-- Rendering a formula
-- ============================================================================

/-- Digits `₀`–`₉` as ordinary characters, for the LaTeX pass. -/
private def subDigit? (c : Char) : Option Char :=
  let n := c.toNat
  if 0x2080 ≤ n && n ≤ 0x2089 then some (Char.ofNat (n - 0x2080 + '0'.toNat)) else none

/-- Longest-match token table for **math mode**, applied left to right. Order matters: `→ᶠ`
must be tried before `→`, and `⊥ᶠ` before `⊥`. -/
private def texTokens : List (String × String) :=
  [ ("→ᶠ", " \\to "), ("∧ᶠ", " \\land "), ("∨ᶠ", " \\lor "), ("↔ᶠ", " \\leftrightarrow ")
  , ("¬ᶠ", "\\lnot "), ("⊥ᶠ", "\\bot "), ("∀ᶠ", "\\forall "), ("∃ᶠ", "\\exists ")
  , ("λᶠ", "\\lambda "), ("=₀", " =_0 "), ("→ₜ", " \\to ")
    -- object-level application and the arithmetic notations of `ProofMode/Arith.lean`
  , ("⬝", "\\,"), ("+ᵗ", " + "), ("*ᵗ", " \\cdot "), ("∸ᵗ", " \\mathbin{\\dot-} ")
  , ("pdᵗ ", "\\mathrm{pd}\\,")
    -- words that are words, not products of single-letter variables
  , (": nat", ": \\mathrm{nat}"), ("hypotheses", "\\text{hypotheses}")
  , ("↑ᶜ", "{\\uparrow}"), ("⟨", "\\langle "), ("⟩", "\\rangle "), ("·", "\\cdot")
  , ("⊢", " \\vdash "), ("⊥", "\\bot "), ("→", " \\to ")
  , ("∀", "\\forall "), ("∃", "\\exists "), ("¬", "\\lnot "), ("∧", " \\land ")
  , ("∨", " \\lor "), ("λ", "\\lambda "), ("≠", " \\neq "), ("≤", " \\le ")
  , ("_", "\\_"), ("#", "\\#"), ("%", "\\%"), ("&", "\\&"), ("$", "\\$") ]

/-- The same symbols for **text mode**: a justification like `∧-contraction` sits outside
`$…$`, so each symbol has to bring its own math shift. -/
private def texJustTokens : List (String × String) :=
  [ ("∧", "$\\land$"), ("∨", "$\\lor$"), ("→", "$\\to$"), ("∀", "$\\forall$")
  , ("∃", "$\\exists$"), ("¬", "$\\lnot$"), ("⊥", "$\\bot$"), ("ω", "$\\omega$")
  , ("β", "$\\beta$"), ("≠", "$\\neq$"), ("_", "\\_"), ("#", "\\#"), ("%", "\\%")
  , ("&", "\\&"), ("$", "\\$") ]

/-- Rewrite a rendering in object notation into LaTeX, against the given token table. A
subscript run becomes one `_{…}` group, so `x₁₂` is `x_{12}` and not `x_1_2`. -/
partial def toTexWith (table : List (String × String)) (s : String) : String :=
  go s.toList ""
where
  go : List Char → String → String
    | [], acc => acc
    | c :: cs, acc =>
      match subDigit? c with
      | some _ =>
        let (run, rest) := span (c :: cs)
        go rest (acc ++ "_{" ++ run ++ "}")
      | none =>
        match matchToken (c :: cs) with
        | some (repl, rest) => go rest (acc ++ repl)
        | none => go cs (acc.push c)
  span : List Char → String × List Char
    | [] => ("", [])
    | c :: cs =>
      match subDigit? c with
      | some d => let (r, rest) := span cs; (String.singleton d ++ r, rest)
      | none => ("", c :: cs)
  matchToken (cs : List Char) : Option (String × List Char) :=
    table.findSome? fun (tok, repl) =>
      let tl := tok.toList
      if tl.isPrefixOf cs then some (repl, cs.drop tl.length) else none

/-- A formula, for inside `$…$`. -/
def toTex (s : String) : String := toTexWith texTokens s

/-- A justification, for outside `$…$`. -/
def toTexJust (s : String) : String := toTexWith texJustTokens s

/-- A listing row must not be broken across lines, so everything is laid out at this width. -/
def rowWidth : Nat := 400

/-- Print in object notation, whatever the caller's file happens to have opened.

`→ᶠ`, `∧ᶠ`, `∨ᶠ`, `¬ᶠ`, `⊥ᶠ` and `↔ᶠ` are all declared `scoped` in `Formula`. Putting the
namespace on `Core.Context.openDecls` is *not* enough: that shortens names, but a scoped
notation's unexpander lives in a `ScopedEnvExtension` which `open` **activates in the
environment**. So both are done, and the environment change is rolled back afterwards.

`pp.fieldNotation` is switched off as well. With it on, the delaborator turns
`Formula.imp A B` into `A.imp B` before any unexpander sees it, and the notation never
fires — which is exactly how the first version of this printer produced a page of `.imp`. -/
def withObjNotation {α : Type} (x : MetaM α) : MetaM α :=
  withOptions (fun o =>
      ((o.setBool `pp.fieldNotation false).setBool `pp.fieldNotation.generalized false).setBool
        `pp.notation true) <|
    withoutModifyingEnv do
      Lean.activateScoped ``Metatheorems.Formula
      withTheReader Lean.Core.Context
        (fun ctx => { ctx with
          openDecls := Lean.OpenDecl.simple ``Metatheorems.Formula [] :: ctx.openDecls }) x

/-- `Derivable` applied to seven arguments (`ι κ F a Premises Γ A`) has its conclusion last. -/
def derivConcl? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let ty ← whnfR ty
  match ty.getAppFnArgs with
  | (``Derivable, args) => return if args.size == 7 then some args[6]! else none
  | _ => return none

/-- Is this expression a proof of something derivable? -/
def isDerivProof (e : Expr) : MetaM Bool := do
  return (← derivConcl? (← inferType e)).isSome

/-- A literal `List String` read back out of its expression, if it is one. -/
partial def decodeStrList? (e : Expr) : Option (List String) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, hd, tl]) => do
      let .lit (.strVal s) := hd | none
      let rest ← decodeStrList? tl
      return s :: rest
  | _ => none

/-- The length of a literal list, if the spine is explicit. -/
partial def listLength? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some 0
  | (``List.cons, #[_, _, tl]) => (listLength? tl).map (· + 1)
  | _ => none

/-- What to display as the conclusion of `e`. A proof-mode goal is shown as the sequent
`Δ ⊢ B` rather than as its packing `pack Δ B`, which is unreadable. -/
def conclusionOf (e : Expr) : MetaM Format := withObjNotation do
  let ty ← instantiateMVars (← inferType e)
  let render (x : Expr) : MetaM Format := Lean.PrettyPrinter.ppExpr x
  -- `Δ ⊢ B` from the hypothesis-context and goal arguments at positions `i` and `i+1`,
  -- naming the hypotheses from `names?` when the judgment carries them.
  --
  -- Printing `Δ` in full is what a naive version does, and it makes a proof-mode listing
  -- unreadable: every row then repeats the entire context, which for `mct_body` is four
  -- nested quantified formulas. The context is *shared state*, not the content of the step,
  -- so it is named rather than spelled out — exactly what the proof-mode goal display does.
  let sequent (args : Array Expr) (i : Nat) (names? : Option (List String)) : MetaM Format := do
    -- The list is often a `List.map (weakenBy …) []` left over from a `pallI`; reduce it so
    -- an empty context shows as one dot rather than as its own computation.
    let Δ ← whnf args[i]!
    let hyps : Format ←
      match names? with
      | some [] => pure (format "·")
      | some ns => pure (format (String.intercalate ", " ns))
      | none =>
        if Δ.isAppOfArity ``List.nil 1 then pure (format "·")
        else match listLength? Δ with
          | some 0 => pure (format "·")
          | some k => pure (format s!"⟨{k} hypotheses⟩")
          | none => render Δ
    return hyps ++ " ⊢ " ++ (← render args[i + 1]!)
  match ty.getAppFnArgs with
  -- `SeqD names F a Premises {Γ} Δ B`, plus the implicit `ι` and `κ`.
  | (``ProofMode.SeqD, args) =>
    if args.size == 9 then sequent args 7 (decodeStrList? args[2]!) else render ty
  -- `Seq F a Premises {Γ} Δ B`, plus the implicit `ι` and `κ`.
  | (``ProofMode.Seq, args) => if args.size == 8 then sequent args 6 none else render ty
  | _ =>
    match ← derivConcl? ty with
    | some c => render c
    | none => render ty

-- ============================================================================
-- The traversal
-- ============================================================================

/-- Record a line and hand back its number. -/
def push (concl : Expr) (rule : String) (prems : List Nat) : M Nat := do
  let f ← conclusionOf concl
  let s := f.pretty rowWidth
  let n := (← get).lines.size + 1
  let line : Line := { num := n, uni := s, tex := toTex s, rule := rule, premises := prems }
  modify fun st => { st with lines := st.lines.push line }
  return n

/-- Short display name of a constant: everything is inside `Metatheorems`, so that prefix
carries no information and is dropped. -/
def shortName (n : Name) : String :=
  match n.components with
  | `Metatheorems :: rest => String.intercalate "." (rest.map toString)
  | _ => toString n

/-- Does this constant belong to the proof-mode layer? -/
def isProofModeName (n : Name) : Bool := (`Metatheorems.ProofMode).isPrefixOf n

/-- Should this constant be walked into rather than cited, with `d` of the proof-mode budget
left?

`all` deliberately stops at the proof-mode layer. Expanding it without a bound is not merely
verbose: on `mct_body` it does not finish at all — every `pintro`/`prw` is a derivation over a
packed hypothesis context, and unfolding them exhausts the heartbeat budget inside `whnf`
before producing a line. Two escape hatches, and they are independent:

* naming a constant under `unfolding` expands it wherever it occurs, at no cost to the budget
  (this is how one proof-mode tactic at a time was expanded before `depth` existed);
* `depth n` spends one unit of budget per `ProofMode` unfolding along a path, so the expansion
  is bounded by construction rather than by luck.

Note the asymmetry, which is deliberate: a non-proof-mode constant costs nothing. The
budget is a statement about the *proof-mode layer's* depth, which is what is unbounded in
practice; ordinary library lemmas bottom out in `Derivable` constructors quickly. -/
def shouldUnfoldAt (cfg : Config) (d : Nat) (n : Name) : Bool :=
  !cfg.keep.contains n
    && (cfg.unfold.contains n || (if isProofModeName n then d > 0 else cfg.unfoldAll))

mutual

/-- Number the `Derivable`-typed explicit arguments of an application, in order. -/
partial def subProofs (d : Nat) (args : Array Expr) : M (List Nat) := do
  let mut out := #[]
  for a in args do
    if ← isDerivProof a then
      out := out.push (← go d a)
  return out.toList

/-- The instantiating term, for the two rules where it is the whole content of the step and
cannot be read off the conclusion alone. Everywhere else the terms are already visible in the
formula and repeating them is noise. -/
partial def termAnnotation (c : Name) (args : Array Expr) : MetaM String := do
  unless c == ``Derivable.forall_ax || c == ``Derivable.exist_ax do return ""
  let mut parts := #[]
  for a in args do
    let ty ← instantiateMVars (← inferType a)
    if ty.isAppOf ``Term then
      let s ← withObjNotation <| Lean.PrettyPrinter.ppExpr a
      parts := parts.push (s.pretty rowWidth)
  if parts.isEmpty then return "" else return s!" [{String.intercalate ", " parts.toList}]"

partial def go (d : Nat) (e₀ : Expr) : M Nat := do
  let cfg ← read
  if (← get).lines.size > cfg.maxLines then
    throwError "#hilbert: exceeded {cfg.maxLines} lines; the proof is too large to list \
      (or an `unfolding`/`depth` made it so)"
  let e ← instantiateMVars e₀
  if let some n := (← get).cache[(d, ExprStructEq.mk e)]? then return n
  let n ← step d e
  modify fun st => { st with cache := st.cache.insert (d, ExprStructEq.mk e) n }
  return n

/-- One node of the DAG, with `d` of the proof-mode budget left. -/
partial def step (d : Nat) (e : Expr) : M Nat := do
  let cfg ← read
  match e with
  | .mdata _ b => go d b
  | .fvar id =>
    if let some n := (← get).fvars[(d, id)]? then return n
    let decl ← id.getDecl
    match decl.value? with
    | some v =>
      let n ← go d v
      modify fun st => { st with fvars := st.fvars.insert (d, id) n }
      return n
    | none => push e s!"hypothesis {decl.userName}" []
  | .letE nm t v b _ =>
    -- A `let` whose value is not itself a derivation — `let xw := x.weaken`, or a
    -- normalisation equation proved by `simp` — carries no step. Bind it and move on.
    withLetDecl nm t v fun x => do
      if ← isDerivProof v then
        let k ← go d v
        modify fun st => { st with fvars := st.fvars.insert (d, x.fvarId!) k }
      go d (b.instantiate1 x)
  | _ =>
    -- `have`/`let_fun` survives elaboration as `letFun v (fun x => body)`.
    if e.isAppOfArity ``letFun 4 then
      let args := e.getAppArgs
      let isProof ← isDerivProof args[2]!
      let f ← whnf args[3]!
      match f with
      | .lam nm t body _ =>
        return ← withLocalDeclD nm t fun x => do
          if isProof then
            let k ← go d args[2]!
            modify fun st => { st with fvars := st.fvars.insert (d, x.fvarId!) k }
          go d (body.instantiate1 x)
      | _ => return ← go d (mkApp args[3]! args[2]!)
    let fn := e.getAppFn
    match fn with
    | .const c _ =>
      if isTransparentWrapper c then
        -- No content: walk straight through to the single derivation argument.
        let subs ← subProofs d e.getAppArgs
        match subs with
        | [k] => return k
        | _   => return ← push e (shortName c) subs
      if let some r := ctorRuleName c then
        let args := e.getAppArgs
        let subs ← subProofs d args
        let ann ← termAnnotation c args
        return ← push e (r ++ ann) subs
      if shouldUnfoldAt cfg d c then
        if let some u ← unfoldDefinition? e then
          -- Only the proof-mode layer draws on the budget; see `shouldUnfoldAt`.
          return ← go (if isProofModeName c then d - 1 else d) u
      let subs ← subProofs d e.getAppArgs
      let r := (libRuleName c).getD (shortName c)
      return ← push e r subs
    | _ =>
      -- A lambda- or projection-headed proof: no name to cite, so show it as a leaf.
      let subs ← subProofs d e.getAppArgs
      return ← push e "(term)" subs

end

-- ============================================================================
-- Emitting
-- ============================================================================

def escapeMd (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

def renderMd (name : Name) (lines : Array Line) (note : String := "") : String := Id.run do
  let mut out := s!"# `{name}`\n\n"
  out := out ++ s!"{lines.size} steps{note}.\n\n"
  out := out ++ "| # | Formula | Justification |\n|---:|---|---|\n"
  for l in lines do
    let just :=
      if l.premises.isEmpty then l.rule
      else s!"{l.rule} {String.intercalate ", " (l.premises.map toString)}"
    out := out ++ s!"| {l.num} | `{escapeMd l.uni}` | {escapeMd just} |\n"
  return out

def renderTex (name : Name) (lines : Array Line) (note : String := "") : String := Id.run do
  let nm := (toString name).replace "_" "\\_"
  let mut out := "% Generated by #hilbert. Requires \\usepackage{longtable,amssymb,amsmath}.\n"
  out := out ++ "\\section*{\\texttt{" ++ nm ++ "}}\n"
  out := out ++ s!"{lines.size} steps{note}.\n\n"
  out := out ++ "\\begin{longtable}{r l l}\n"
  out := out ++ "\\hline\n\\# & Formula & Justification \\\\\n\\hline\n\\endhead\n"
  for l in lines do
    let just :=
      if l.premises.isEmpty then l.rule
      else s!"{l.rule} {String.intercalate ", " (l.premises.map toString)}"
    out := out ++ toString l.num ++ " & $" ++ l.tex ++ "$ & \\textit{" ++ toTexJust just
      ++ "} \\\\\n"
  out := out ++ "\\hline\n\\end{longtable}\n"
  return out

/-- Walk `name`'s value and produce the listing. Section variables become named free
variables first, so `A →ᶠ A` prints with the user's own names. -/
def hilbertLines (name : Name) (cfg : Config) : MetaM (Array Line) := do
  let ci ← getConstInfo name
  let some val := ci.value? | throwError "#hilbert: `{name}` has no value (opaque or axiom)"
  lambdaTelescope val fun _ body => do
    let some _ ← derivConcl? (← inferType body)
      | throwError "#hilbert: `{name}` does not conclude in `Derivable`"
    let (_, st) ← ((go cfg.pmDepth body).run cfg).run {}
    return st.lines

end Hilbert

-- ============================================================================
-- The command
-- ============================================================================

namespace Hilbert
open Lean Lean.Elab Lean.Elab.Command

/-- `#hilbert f` cites every non-constructor by name; `#hilbert f all` expands everything
outside the proof-mode layer; `#hilbert f unfolding g h` expands just `g` and `h`;
`#hilbert f depth n` expands the proof-mode layer `n` levels deep and cites it below that;
`#hilbert f keeping g` never expands `g`, whatever the rest says;
`to "path"` sets the output base name (no extension — `.md` and `.tex` are both written).

They are independent and compose: `#hilbert f all unfolding g keeping h depth 2 to "…"` is
legal and means all five things at once. `keeping` wins over `unfolding` and over both
`all` and `depth`. -/
syntax (name := hilbertCmd)
  "#hilbert " ident (" all")? (" unfolding " ident+)? (" keeping " ident+)?
    (" depth " num)? (" to " str)? : command

@[command_elab hilbertCmd]
def elabHilbert : CommandElab := fun stx => do
  match stx with
  | `(command| #hilbert $id:ident $[all%$a?]? $[unfolding $us*]? $[keeping $ks*]?
        $[depth $dp?:num]? $[to $out?:str]?) => do
    liftTermElabM do
      let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
      let mut cfg : Config :=
        { unfoldAll := a?.isSome, pmDepth := (dp?.map (·.getNat)).getD 0 }
      if let some us := us then
        for u in us do
          let n ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo u
          cfg := { cfg with unfold := cfg.unfold.insert n }
      if let some ks := ks then
        for k in ks do
          let n ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo k
          cfg := { cfg with keep := cfg.keep.insert n }
      let t0 ← IO.monoMsNow
      let lines ← hilbertLines name cfg
      let t1 ← IO.monoMsNow
      let base := match out? with
        | some s => s.getString
        | none =>
          let stem := "hilbert-out/" ++ (toString name).replace "." "_"
          if cfg.pmDepth = 0 then stem else stem ++ s!"_d{cfg.pmDepth}"
      if let some dir := (System.FilePath.mk base).parent then
        IO.FS.createDirAll dir
      let note :=
        (if cfg.unfoldAll then ", `all`" else "")
          ++ (if cfg.pmDepth = 0 then "" else s!", proof-mode depth {cfg.pmDepth}")
      IO.FS.writeFile (base ++ ".md") (renderMd name lines note)
      IO.FS.writeFile (base ++ ".tex") (renderTex name lines note)
      logInfo m!"#hilbert {name}: {lines.size} steps in {t1 - t0}ms → {base}.md, {base}.tex"
  | _ => throwUnsupportedSyntax

end Hilbert
end Metatheorems
