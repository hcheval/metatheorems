/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.Majorizability

/-!
# `theory … endtheory` — a declarative front end for a proof-mining theory

Every space in the tower (`MetricSpaces.lean`, `WHyperbolic.lean`, `CAT0.lean`,
`Normed.lean`) opens with the same boilerplate: an index type `κ`, a signature
`F : κ → Ty ι`, one `abbrev` per constant, the axioms as de Bruijn `Formula`s, a `Premises`
predicate, the `premises_pu` / `premises_vf` theorems, and one `.premise`-accessor per axiom.
None of that is mathematics.  This command generates it.

## What it does NOT do

It **proves nothing about a space**, and it **does not invent a majorization relation**.
Those are exactly the parts of a space instantiation that carry content — `zeroX_maj`'s
parameter `n₀`, `distMajorant = λn₁n₂.(n₁+n₂)◦`, `WMajorant = λn₁n₂_.max n₁ n₂`, and the
lesson of `Normed.lean`'s header that a *defined* operation inherits its definiens' majorant
(which is why `−` was made a primitive constant).  What the command does instead is **emit
the obligations**: a field per axiom (its truth in the model) and a majorant-plus-proof pair
per constant, so the user discharges named goals in ordinary Lean and gets `spremise` free.

## Syntax

```
/-- A doc comment here is allowed, and ignored. -/
theory Foo
  index MetricSpace.ι                        -- optional; see "Two modes" below
  types X := xTy
  types R := realTy MetricSpace.ι
  abbrev d := Term.dist ()                   -- a syntactic alias for axiom bodies
  constants W : X →ₜ X →ₜ R →ₜ X
  axioms W1 (z x y : X) (l : R) : <body>
  axioms W2 (x y : X)           : <body>
endtheory
```

One keyword per item; items may appear in any order, except that `index`, `types` and
`abbrev` must precede anything that mentions them.  The three keywords `index`, `types` and
`constants` become parser tokens in every file that imports this module, so they cannot be
used as identifiers there; `abbrev` and `axioms` reuse tokens Lean already has.  **This is
why `Theory.lean` is deliberately not imported by `Metatheorems.lean`** — putting it in the
umbrella would make those three words keywords for the whole project.

### `abbrev` items

`abbrev n := e` is a *syntactic* alias, not a declaration: `n` is replaced by `(e)` wherever
it occurs in a later axiom body (parenthesised, so a multi-token right-hand side is safe in
an application spine).  It exists for the things an axiom body wants short that are not
function constants — above all the structural metric `Term.dist i` and the base points
`Term.zeroX i`, which are `Term` constructors rather than elements of the signature and so
get no generated `abbrev`.

### Two modes for the index type `ι`

* **No `index` clause** — `Foo.ι` is *generated* as an inductive with one constructor per
  `types` item that has no `:=`, and each such item also gets
  `abbrev Foo.X : Ty Foo.ι := Ty.base Foo.ι.X`.
* **`index e`** — `Foo.ι` is `abbrev`-ed to `e`, and every `types` item **must** carry a
  `:= <Ty expression>`.  This is what lets a theory sit over `MetricSpace.ι` and inherit
  `MetricTransfer.lean`, `MetricModel`, and the whole ℝ layer.

A `types n := e` item is a plain abbreviation in either mode; it is how non-base types
(`R`, function types) get short names.

### Axiom bodies

The body is an ordinary Lean term of type `Formula Foo.F Γ'`, elaborated in the **innermost**
context `Γ' = τₖ :: … :: τ₁ :: Γ`.  Before elaboration the command substitutes, at the level
of syntax:

* each binder name by its de Bruijn variable (`z ↦ Term.var (Var.vs (Var.vs Var.vz))`, …),
* each declared type name by `Foo.<name>`,
* each declared constant name by `Foo.<name>`,
* each `abbrev` alias by its parenthesised right-hand side.

So the body reads with **named variables**, and the index arithmetic — the single largest
source of mistakes in the hand-written space files — is done by the command.  Binder names
shadow type and constant names.  The substitution is purely textual over identifiers, so a
`fun x => …` inside a body whose bound name collides with a theory binder is rewritten too;
do not do that.

## What is generated, for `theory Foo` with constants `cᵢ` and axioms `aⱼ`

| declaration | what it is |
|---|---|
| `Foo.ι` | the index type (generated inductive, or the `index` expression) |
| `Foo.X` | `Ty Foo.ι` abbreviations, one per `types` item |
| `Foo.κ` | inductive with one constructor per constant (`Empty` if there are none) |
| `Foo.F : Foo.κ → Ty Foo.ι` | the signature |
| `Foo.cᵢ` | `Term.func Foo.κ.cᵢ`, at any context |
| `Foo.ax_aⱼ` | the axiom, as a closed context-polymorphic `Formula` |
| `Foo.ax_aⱼ_pu`, `_vf` | purely universal / ∨-free, by `rfl` |
| `Foo.Premises` | the `PremiseSet` — the disjunction of the axioms |
| `Foo.premises_pu`, `Foo.premises_vf` | the two facts every metatheorem asks for |
| `Foo.aⱼ` | `Derivable Foo.F al Foo.Premises Foo.ax_aⱼ`, the axiom as a proof |
| `Foo.Obligations si` | structure: one field `aⱼ` per axiom, its truth in the model |
| `Foo.axiomsHold` | `Obligations → ` the `hprem` shape `soundness_gen` wants |
| `Foo.spremise` | `Obligations → ` premise realizers, via `srealizer_of_pu` |
| `Foo.Majorants am` | structure: one majorant and one proof per constant |
| `Foo.Majorants.funcM`, `.funcM_maj` | those two, in the shape `ConstMajorants` asks for |
| `Foo.metatheorem` | `syntactic_general_metatheorem` at this premise set |
| `Foo.metatheorem_classical` | `syntactic_general_metatheorem_classical`, ditto |

The last two are the reason to read the list as a **contract**.  Their hypotheses are exactly
`EqXInterp`, `Foo.Obligations`, `AbstractMajorizability`, and the derivation — the two
premise-set side conditions the metatheorems ask for (`premises_pu`, `premises_vf`) are
generated *and discharged*.  So "what does a model of this theory still owe?" has a
mechanical answer: those three things and nothing else.

## Admissibility

Before emitting the `_pu` / `_vf` theorems the command **evaluates**
`Formula.isPurelyUniversal` and `Formula.isVFree` on each axiom and fails, naming the
offending axiom, if either is `false`.  Those are precisely the two conditions
`syntactic_general_metatheorem` imposes on a premise set, so an axiom that gets past this
command is one the metatheorems will accept.  There is nothing else to check: `Premises` is
otherwise an arbitrary predicate, and the remaining obligations (truth in the model,
majorants) are emitted rather than checked because they are not decidable properties of
syntax.
-/

-- The `theory` block is written with blank lines between its items, and the elaborator below
-- with blank lines between its phases; Mathlib's style linter objects to both.
set_option linter.style.emptyLine false

namespace Metatheorems

open Lean Elab Command Meta

/-- Local abbreviation: a piece of `term` syntax.  Written out because `Term` names this
project's object-language terms. -/
abbrev TSTerm := TSyntax `term

/-! ## Syntax -/

declare_syntax_cat thyItem

/-- `(x y z : τ)` — a group of theory-axiom binders sharing a type. -/
syntax thyBinderGroup := "(" ident+ " : " term ")"

/-- Reuse an existing index type instead of generating one. -/
syntax "index " term : thyItem
/-- Declare a base type (no `:=`) or a type abbreviation (with `:=`). -/
syntax "types " ident (" := " term)? : thyItem
/-- Declare a function constant of the signature. -/
syntax "constants " ident " : " term : thyItem
/-- A *syntactic* alias usable in axiom bodies: `abbrev d := Term.dist ()`.  The right-hand
side is substituted (parenthesised) wherever the name occurs in a later axiom body.  It
generates no declaration, so it can name anything an axiom body wants short — the structural
metric above all, which is not a function constant and so has no generated `abbrev`. -/
syntax "abbrev " ident " := " term : thyItem
/-- Declare an axiom, with named binders. -/
syntax "axioms " ident thyBinderGroup* " : " term : thyItem

/-- Declare a proof-mining theory: index type, signature, axioms, and the obligations a model
of it owes.  See the module docstring for the full grammar. -/
syntax (name := theoryCmd) (docComment)? "theory " ident thyItem* "endtheory" : command

/-! ## Collected data -/

namespace TheoryDSL

/-- A `types` item. -/
structure TypeDecl where
  id : Ident
  /-- `none` for a base type (generated-`ι` mode only); `some e` for an abbreviation. -/
  defn? : Option TSTerm
  deriving Inhabited

/-- A `constants` item. -/
structure ConstDecl where
  id : Ident
  ty : TSTerm
  deriving Inhabited

/-- An `axioms` item, with its binder groups flattened. -/
structure AxiomDecl where
  id : Ident
  /-- Binders, outermost first. -/
  binders : Array (Ident × TSTerm)
  body : TSTerm
  deriving Inhabited

/-- Substitute identifiers, by simple name, throughout a piece of syntax.  Used to turn the
user's named variables into de Bruijn `Term.var`s and their short type/constant names into
the theory-qualified ones. -/
partial def substIdents (m : Std.HashMap Name Syntax) : Syntax → Syntax
  | s@(.ident _ _ n _) => match m[n]? with
      | some t => t
      | none   => s
  | .node i k args => .node i k (args.map (substIdents m))
  | s => s

/-- Apply `substIdents` to a `term`. -/
def substT (m : Std.HashMap Name Syntax) (t : TSTerm) : TSTerm := ⟨substIdents m t.raw⟩

/-- `Term.var (Var.vs^[k] Var.vz)`, the de Bruijn variable at index `k`. -/
def mkVar (k : Nat) : CommandElabM TSTerm := do
  let mut v ← `(Var.vz)
  for _ in [0:k] do
    v ← `(Var.vs $v)
  `(Term.var $v)

/-- `p₁ ∨ p₂ ∨ … ∨ pₙ`, right-nested; `False` when the array is empty. -/
def mkOrChain (ps : Array TSTerm) : CommandElabM TSTerm := do
  if ps.isEmpty then `(False) else
  let mut acc := ps[ps.size - 1]!
  for i in [0 : ps.size - 1] do
    let p := ps[ps.size - 2 - i]!
    acc ← `($p ∨ $acc)
  return acc

/-- Given `leaves[j] : (B = aⱼ) → G`, build a proof of `(B = a₁ ∨ … ∨ B = aₙ) → G`.
With no axioms the disjunction is `False` and the eliminator is `False.elim`. -/
def mkOrElim (leaves : Array TSTerm) : CommandElabM TSTerm := do
  if leaves.isEmpty then `(fun h => h.elim) else
  let mut acc := leaves[leaves.size - 1]!
  for i in [0 : leaves.size - 1] do
    let l := leaves[leaves.size - 2 - i]!
    acc ← `(fun h => Or.elim h $l $acc)
  return acc

/-- The `j`-th injection into an `n`-fold right-nested `Or`, applied to `rfl`. -/
def mkOrIntro (j n : Nat) : CommandElabM TSTerm := do
  let base ← if j + 1 == n then `(rfl) else `(Or.inl rfl)
  let mut acc := base
  for _ in [0:j] do
    acc ← `(Or.inr $acc)
  return acc

end TheoryDSL

open TheoryDSL

/-! ## The elaborator -/

/-- Evaluate a closed `Bool`-valued piece of syntax to a constructor. -/
private def evalBoolStx (stx : TSTerm) : CommandElabM Bool := do
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTerm stx (some (mkConst ``Bool))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let r ← whnf (← instantiateMVars e)
    if r.isConstOf ``Bool.true then return true
    else if r.isConstOf ``Bool.false then return false
    else throwError "theory: the admissibility check did not reduce to a Boolean:{indentExpr r}"

@[command_elab theoryCmd]
def elabTheory : CommandElab := fun stx => do
  let `(command| $[$_doc:docComment]? theory $thy:ident $items:thyItem* endtheory) := stx
    | throwUnsupportedSyntax
  let thyName := thy.getId

  -- ---------------------------------------------------------------- collect
  let mut idxClause : Option TSTerm := none
  -- NOTE: `types`, `constants`, `axioms` and `index` are now parser tokens (declared above),
  -- so they cannot be used as local names anywhere below this point in this file.
  let mut tyDecls : Array TypeDecl := #[]
  let mut consts : Array ConstDecl := #[]
  let mut aliases : Array (Ident × TSTerm) := #[]
  let mut axs : Array AxiomDecl := #[]
  for it in items do
    match it with
    | `(thyItem| index $e:term) =>
        if idxClause.isSome then throwErrorAt it "theory: duplicate `index` clause"
        idxClause := some e
    | `(thyItem| types $n:ident $[:= $e?:term]?) =>
        tyDecls := tyDecls.push { id := n, defn? := e? }
    | `(thyItem| constants $n:ident : $t:term) =>
        consts := consts.push { id := n, ty := t }
    | `(thyItem| abbrev $n:ident := $e:term) =>
        aliases := aliases.push (n, e)
    | `(thyItem| axioms $n:ident $gs:thyBinderGroup* : $b:term) =>
        let mut bs : Array (Ident × TSTerm) := #[]
        for g in gs do
          match g with
          | `(thyBinderGroup| ($ns:ident* : $t:term)) =>
              for nm in ns do bs := bs.push (nm, t)
          | _ => throwErrorAt g "theory: malformed binder group"
        axs := axs.push { id := n, binders := bs, body := b }
    | _ => throwErrorAt it "theory: unrecognised item"

  let qid : Name → Ident := fun n => mkIdent (thyName ++ n)
  let sub : String → Ident := fun s => mkIdent (thyName ++ Name.mkSimple s)
  let iotaId := qid `ι
  let kappaId := qid `κ
  let fId := qid `F

  -- ------------------------------------------------------- the index type ι
  match idxClause with
  | some e =>
      for t in tyDecls do
        if t.defn?.isNone then
          throwErrorAt t.id
            "theory: with an `index` clause every `types` item needs `:= <Ty expression>` \
             (there is no generated inductive to add a constructor to)"
      elabCommand (← `(command| abbrev $iotaId : Type := $e))
  | none =>
      let baseNames := (tyDecls.filter (·.defn?.isNone)).map (·.id)
      if baseNames.isEmpty then
        throwErrorAt thy
          "theory: no base types.  Declare at least one `types X` (without `:=`), or give an \
           `index` clause naming an existing index type."
      elabCommand (← `(command| inductive $iotaId where $[| $baseNames:ident]*))

  -- ------------------------------------ the type abbreviations, in declaration order
  let mut typeSubst : Std.HashMap Name Syntax := {}
  for t in tyDecls do
    let tid := qid t.id.getId
    let rhs ← match t.defn? with
      | some e => pure (substT typeSubst e)
      | none   => do
          let ctor := mkIdent (thyName ++ `ι ++ t.id.getId)
          `(Ty.base $ctor)
    elabCommand (← `(command| abbrev $tid : Ty $iotaId := $rhs))
    typeSubst := typeSubst.insert t.id.getId tid.raw

  -- ------------------------------------------------------------ κ and F
  let constNames := consts.map (·.id)
  let constTys : Array TSTerm := consts.map fun c => substT typeSubst c.ty
  let ctorIds : Array Ident := consts.map fun c => mkIdent (thyName ++ `κ ++ c.id.getId)
  let ctorPats : Array TSTerm ← ctorIds.mapM fun c => `($c)
  if consts.isEmpty then
    elabCommand (← `(command| abbrev $kappaId : Type := Empty))
    elabCommand (← `(command| def $fId : $kappaId → Ty $iotaId := fun c => c.elim))
  else
    elabCommand (← `(command| inductive $kappaId where $[| $constNames:ident]*))
    elabCommand (← `(command|
      def $fId : $kappaId → Ty $iotaId := fun c => match c with
        $[| $ctorPats:term => $constTys:term]*))

  -- --------------------------------------------------- one abbrev per constant
  let gammaId := mkIdent `Γ
  let mut constSubst : Std.HashMap Name Syntax := {}
  for i in [0 : consts.size] do
    let c := consts[i]!
    let cid := qid c.id.getId
    let ctor := ctorIds[i]!
    let ty := constTys[i]!
    elabCommand (← `(command|
      abbrev $cid {$gammaId : Ctx $iotaId} : Term $fId $gammaId $ty := Term.func $ctor))
    constSubst := constSubst.insert c.id.getId cid.raw

  -- ------------------------------------------------------------- the axioms
  let mut baseSubst := typeSubst
  for (k, v) in constSubst.toList do baseSubst := baseSubst.insert k v
  -- `abbrev` aliases, in declaration order, each seeing the ones before it.  Parenthesised,
  -- so that a multi-token right-hand side is safe in an application spine.
  for (n, e) in aliases do
    let rhs ← `(($(substT baseSubst e)))
    baseSubst := baseSubst.insert n.getId rhs.raw

  let mut axIds : Array Ident := #[]
  for a in axs do
    let k := a.binders.size
    let mut s := baseSubst
    for i in [0:k] do
      -- binder `i` (outermost is 0) sits at de Bruijn index `k - 1 - i`
      s := s.insert (a.binders[i]!.1).getId (← mkVar (k - 1 - i)).raw
    let mut f := substT s a.body
    -- wrap: the last binder is the innermost `Formula.all`
    for i in [0:k] do
      let τ := substT typeSubst (a.binders[k - 1 - i]!).2
      f ← `(Formula.all $τ $f)
    let axId := sub s!"ax_{a.id.getId}"
    elabCommand (← `(command|
      def $axId {$gammaId : Ctx $iotaId} : Formula $fId $gammaId := $f))
    axIds := axIds.push axId

    -- admissibility, checked here so the error can name the axiom
    let puOK ← evalBoolStx (← `(Formula.isPurelyUniversal ($axId (Γ := ([] : Ctx $iotaId)))))
    if !puOK then
      throwErrorAt a.id
        "theory: axiom `{a.id.getId}` is NOT purely universal, so the metatheorems cannot \
         take it as a premise.\n\
         A premise must be a block of `∀` (and `∧`) over a quantifier-free matrix: no `∃`, \
         and no `→` or `∨` above a quantifier.  Checked by evaluating \
         `Formula.isPurelyUniversal {axId.getId}`, which is `false`."
    let vfOK ← evalBoolStx (← `(Formula.isVFree ($axId (Γ := ([] : Ctx $iotaId)))))
    if !vfOK then
      throwErrorAt a.id
        "theory: axiom `{a.id.getId}` is NOT ∨-free, so the metatheorems cannot take it as a \
         premise.\n\
         The Dialectica interpretation of a disjunction carries a decision, so premises must \
         be ∨-free.  Replace the `∨ᶠ` by a quantifier-free decision term, or split the two \
         cases into separate axioms.  Checked by evaluating \
         `Formula.isVFree {axId.getId}`, which is `false`."

    elabCommand (← `(command|
      theorem $(sub s!"ax_{a.id.getId}_pu") {$gammaId : Ctx $iotaId} :
          ($axId (Γ := $gammaId)).isPurelyUniversal = true := by rfl))
    elabCommand (← `(command|
      theorem $(sub s!"ax_{a.id.getId}_vf") {$gammaId : Ctx $iotaId} :
          ($axId (Γ := $gammaId)).isVFree = true := by rfl))

  -- ---------------------------------------------------------- the premise set
  let premId := qid `Premises
  let bId := mkIdent `B
  let eqs : Array TSTerm ← axIds.mapM fun ax => `($bId = $ax)
  let orChain ← mkOrChain eqs
  elabCommand (← `(command|
    def $premId : PremiseSet $fId
      | ⟨_, $bId⟩ => $orChain))

  let leafRfl ← `(fun e => by subst e; rfl)
  let puElim ← mkOrElim (axIds.map fun _ => leafRfl)
  elabCommand (← `(command|
    theorem $(qid `premises_pu) : ∀ (Γ' : Ctx $iotaId) (B : Formula $fId Γ'),
        $premId ⟨Γ', B⟩ → B.isPurelyUniversal = true :=
      fun _ B h => $puElim h))
  let vfElim ← mkOrElim (axIds.map fun _ => leafRfl)
  elabCommand (← `(command|
    theorem $(qid `premises_vf) : ∀ (Γ' : Ctx $iotaId) (B : Formula $fId Γ'),
        $premId ⟨Γ', B⟩ → B.isVFree = true :=
      fun _ B h => $vfElim h))

  -- ------------------------------------------- one `Derivable` accessor per axiom
  let alId := mkIdent `al
  for i in [0 : axs.size] do
    let a := axs[i]!
    let axId := axIds[i]!
    let intro ← mkOrIntro i axs.size
    elabCommand (← `(command|
      def $(qid a.id.getId) {$gammaId : Ctx $iotaId} {$alId : Allowed} :
          Derivable $fId $alId $premId ($axId (Γ := $gammaId)) :=
        Derivable.premise $intro))

  -- ------------------------------------------------------------- obligations
  let xId := mkIdent `X
  let siId := mkIdent `si
  let envId := mkIdent `env
  let oId := mkIdent `o
  if axs.isEmpty then
    elabCommand (← `(command|
      abbrev $(qid `Obligations) {$xId : $iotaId → Type}
          (_si : SpaceInterp $xId $fId) : Prop := True))
  else
    let fieldNames := axs.map (·.id)
    let fieldTys : Array TSTerm ← axIds.mapM fun ax =>
      `(∀ {$gammaId : Ctx $iotaId} ($envId : Ctx.interpret $xId $gammaId),
          Formula.interpret $siId ($ax (Γ := $gammaId)) $envId)
    elabCommand (← `(command|
      structure $(qid `Obligations) {$xId : $iotaId → Type}
          ($siId : SpaceInterp $xId $fId) : Prop where
        $[$fieldNames:ident : $fieldTys:term]*))

  let axHoldLeaves : Array TSTerm ← axs.mapM fun a => do
    let fld := mkIdent a.id.getId
    `(fun e => by subst e; exact $(oId).$(fld) $envId)
  let axHoldElim ← mkOrElim axHoldLeaves
  elabCommand (← `(command|
    theorem $(qid `axiomsHold) {$xId : $iotaId → Type} {$siId : SpaceInterp $xId $fId}
        ($oId : $(qid `Obligations) $siId) :
        ∀ {Γ' : Ctx $iotaId} (B : Formula $fId Γ'), $premId ⟨Γ', B⟩ →
          ∀ $envId : Ctx.interpret $xId Γ', Formula.interpret $siId B $envId :=
      fun B h $envId => $axHoldElim h))

  elabCommand (← `(command|
    def $(qid `spremise) {$xId : $iotaId → Type} {$siId : SpaceInterp $xId $fId}
        ($oId : $(qid `Obligations) $siId) :
        ∀ (Γ' : Ctx $iotaId) (B : Formula $fId Γ'), $premId ⟨Γ', B⟩ → SRealizer $siId B :=
      fun Γ' B hp =>
        srealizer_of_pu B ($(qid `premises_pu) Γ' B hp) ($(qid `premises_vf) Γ' B hp)
          ($(qid `axiomsHold) $oId B hp)))

  -- ------------------------------------------------- the theory's metatheorems
  -- The point of emitting these is that they name, in one signature, *everything* a model of
  -- the theory still owes: an `EqXInterp`, the axioms' truth (`Obligations`), and a
  -- majorizability relation.  Nothing else — the two premise-set side conditions the
  -- metatheorems ask for are generated and discharged above.
  elabCommand (← `(command|
    theorem $(qid `metatheorem) {$xId : $iotaId → Type} {$siId : SpaceInterp $xId $fId}
        (eqxi : EqXInterp $xId $fId $siId) ($oId : $(qid `Obligations) $siId)
        (am : AbstractMajorizability $siId)
        {ρ : Ty $iotaId} {B₀ C₀ : Formula $fId [Ty.nat, ρ]}
        (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
        (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
        (prf : @Derivable $iotaId $kappaId $fId Allowed.extended $premId []
          (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀) (Formula.ex Ty.nat C₀)))) :
        ∃ Φ : Ty.interpret $xId ρ.hat → Nat,
          ∀ (x : Ty.interpret $xId ρ) (x_star : Ty.interpret $xId ρ.hat),
            am.toRel.maj ρ x_star x →
            (∀ u : Nat, u ≤ Φ x_star → Formula.interpret $siId B₀ (u, (x, ()))) →
            ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret $siId C₀ (v, (x, ())) :=
      syntactic_general_metatheorem eqxi ($(qid `spremise) $oId) am
        hB_qf hB_vf hC_qf hC_vf prf))

  elabCommand (← `(command|
    theorem $(qid `metatheorem_classical) {$xId : $iotaId → Type}
        {$siId : SpaceInterp $xId $fId}
        (eqxi : EqXInterp $xId $fId $siId) ($oId : $(qid `Obligations) $siId)
        (am : AbstractMajorizability $siId)
        {ρ : Ty $iotaId} {B₀ C₀ : Formula $fId [Ty.nat, ρ]}
        (hB_qf : B₀.isQF = true) (hB_vf : B₀.isVFree = true)
        (hC_qf : C₀.isQF = true) (hC_vf : C₀.isVFree = true)
        (prf : @Derivable $iotaId $kappaId $fId Allowed.classical $premId []
          (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀) (Formula.ex Ty.nat C₀)))) :
        ∃ Φ : Ty.interpret $xId ρ.hat → Nat,
          ∀ (x : Ty.interpret $xId ρ) (x_star : Ty.interpret $xId ρ.hat),
            am.toRel.maj ρ x_star x →
            (∀ u : Nat, u ≤ Φ x_star → Formula.interpret $siId B₀ (u, (x, ()))) →
            ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret $siId C₀ (v, (x, ())) :=
      syntactic_general_metatheorem_classical eqxi
        (ntStable_of_pu $(qid `premises_pu)) ($(qid `spremise) $oId) am
        hB_qf hB_vf hC_qf hC_vf prf))

  -- ------------------------------------------------------ majorant obligations
  let amId := mkIdent `am
  let nId := mkIdent `n
  let mId := mkIdent `m
  if consts.isEmpty then
    elabCommand (← `(command|
      abbrev $(qid `Majorants) {$xId : $iotaId → Type} {$siId : SpaceInterp $xId $fId}
          (_am : AbstractMajorizability $siId) : Type := PUnit))
    elabCommand (← `(command|
      def $(qid `Majorants.funcM) {$xId : $iotaId → Type}
          {$siId : SpaceInterp $xId $fId} {$amId : AbstractMajorizability $siId}
          (_m : $(qid `Majorants) $amId) :
          (f : $kappaId) → Nat → Ty.interpret $xId ($fId f).hat := fun c => c.elim))
    elabCommand (← `(command|
      theorem $(qid `Majorants.funcM_maj) {$xId : $iotaId → Type}
          {$siId : SpaceInterp $xId $fId} {$amId : AbstractMajorizability $siId}
          ($mId : $(qid `Majorants) $amId) :
          ∀ (f : $kappaId), ∀ ($nId : Nat), $nId ≥ $(amId).N →
            $(amId).maj ($fId f) ($(qid `Majorants.funcM) $mId f $nId)
              ($(siId).funcInterp f) :=
        fun c => c.elim))
  else
    let mut fieldNames : Array Ident := #[]
    let mut fieldTys : Array TSTerm := #[]
    for i in [0 : consts.size] do
      let c := consts[i]!
      let ctor := ctorIds[i]!
      let ty := constTys[i]!
      fieldNames := fieldNames.push c.id
      fieldTys := fieldTys.push (← `(Nat → Ty.interpret $xId (Ty.hat $ty)))
      fieldNames := fieldNames.push (mkIdent (Name.mkSimple s!"{c.id.getId}_maj"))
      fieldTys := fieldTys.push (← `(∀ ($nId : Nat), $nId ≥ $(amId).N →
        $(amId).maj ($fId $ctor) ($(mkIdent c.id.getId) $nId) ($(siId).funcInterp $ctor)))
    elabCommand (← `(command|
      structure $(qid `Majorants) {$xId : $iotaId → Type} {$siId : SpaceInterp $xId $fId}
          ($amId : AbstractMajorizability $siId) : Type where
        $[$fieldNames:ident : $fieldTys:term]*))
    let vals : Array TSTerm ← consts.mapM fun c => do
      let f := mkIdent c.id.getId; `($(mId).$(f))
    elabCommand (← `(command|
      def $(qid `Majorants.funcM) {$xId : $iotaId → Type}
          {$siId : SpaceInterp $xId $fId} {$amId : AbstractMajorizability $siId}
          ($mId : $(qid `Majorants) $amId) :
          (f : $kappaId) → Nat → Ty.interpret $xId ($fId f).hat := fun c => match c with
        $[| $ctorPats:term => $vals:term]*))
    let majVals : Array TSTerm ← consts.mapM fun c => do
      let f := mkIdent (Name.mkSimple s!"{c.id.getId}_maj"); `($(mId).$(f))
    elabCommand (← `(command|
      theorem $(qid `Majorants.funcM_maj) {$xId : $iotaId → Type}
          {$siId : SpaceInterp $xId $fId} {$amId : AbstractMajorizability $siId}
          ($mId : $(qid `Majorants) $amId) :
          ∀ (f : $kappaId), ∀ ($nId : Nat), $nId ≥ $(amId).N →
            $(amId).maj ($fId f) ($(qid `Majorants.funcM) $mId f $nId)
              ($(siId).funcInterp f) :=
        fun c => match c with
        $[| $ctorPats:term => $majVals:term]*))

end Metatheorems
