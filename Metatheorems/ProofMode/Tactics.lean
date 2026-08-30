/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.ProofMode.Display
import Metatheorems.ProofMode.Induction
import Metatheorems.ProofMode.Linter

/-!
# The tactic layer

Each move is a *lemma* stated on `SeqD` — the name-carrying wrapper — and a *macro* that
applies it. Splitting it that way is the point of this file: the lemma is where the name
list is kept in step with `Δ`, so the bookkeeping is checked by the elaborator rather than
by tactic code manipulating `Expr`s.

Consequently there is exactly one tactic here that inspects the goal at all, `pexact`, and
it does so only to turn a *name* into a de Bruijn index. Everything else is a macro.

## Naming

Tactics are prefixed `p`, since they operate on the object logic and must not be confused
with Lean's own `intro`, `cases`, … . A tactic never touches the kernel: it emits a `refine`
against a lemma from this file, which is built from `Packing.lean`, which is built from
`Derivable`.

## Where side conditions go

The rules of the extended system carry side conditions — an `allowed` flag, an `isQF` or
`isVFree` check. These cannot be passed as `(by …)` arguments, because at the time such an
argument is elaborated the matrix is still a metavariable: it is fixed only when `refine`
unifies the lemma's conclusion with the goal. They are therefore left as *named holes* and
discharged afterwards by `pside`, which computes when everything is concrete and otherwise
looks in the Lean context.

The one exception is a rule whose matrix comes from a *hypothesis* rather than from the
goal — QF-AC. There the hypothesis argument must be elaborated inline, since nothing else
determines the matrix.
-/

namespace Metatheorems
namespace ProofMode

open Lean Formula

variable {ι : Type} {F : ι → Ty ι}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {ns : List String}

-- ============================================================================
-- The moves, as name-aware lemmas
-- ============================================================================

/-- Introduce an implication, naming the new hypothesis. -/
def pm_intro (n : String) {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD (n :: ns) F EqX a Premises (A :: Δ) B) :
    SeqD ns F EqX a Premises Δ (A →ᶠ B) :=
  seq_intro h

/-- Split a conjunctive goal. -/
def pm_split {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h₁ : SeqD ns F EqX a Premises Δ A) (h₂ : SeqD ns F EqX a Premises Δ B) :
    SeqD ns F EqX a Premises Δ (A ∧ᶠ B) :=
  seq_andI h₁ h₂

/-- Take the left disjunct. -/
def pm_left {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ A) : SeqD ns F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_orI₁ h

/-- Take the right disjunct. -/
def pm_right {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ B) : SeqD ns F EqX a Premises Δ (A ∨ᶠ B) :=
  seq_orI₂ h

/-- Case analysis on a disjunction, naming the hypothesis in each branch. -/
def pm_cases (n m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F EqX a Premises Δ (A ∨ᶠ B))
    (h₁ : SeqD (n :: ns) F EqX a Premises (A :: Δ) C)
    (h₂ : SeqD (m :: ns) F EqX a Premises (B :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_orE hAB h₁ h₂

/-- Project out of a conjunctive hypothesis-shaped goal (left). -/
def pm_andE₁ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A ∧ᶠ B)) : SeqD ns F EqX a Premises Δ A :=
  seq_andE₁ h

/-- Project out of a conjunctive hypothesis-shaped goal (right). -/
def pm_andE₂ {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A ∧ᶠ B)) : SeqD ns F EqX a Premises Δ B :=
  seq_andE₂ h

/-- Destructure a conjunction into two named hypotheses.

Stated as a *cut* rather than as an in-place rewrite of one position, so it does not care
where the conjunction sits in `Δ`: the caller proves `A ∧ᶠ B` however it likes (typically
`pexact`), and the two components arrive on top of the context. -/
def pm_andcut (n m : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hAB : SeqD ns F EqX a Premises Δ (A ∧ᶠ B))
    (k : SeqD (n :: m :: ns) F EqX a Premises (A :: B :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_andE₂ hAB) (seq_cut (seq_andE₁ (seq_weaken hAB)) k)

/-- `⊥` eliminates to anything. -/
def pm_exfalso {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ ⊥ᶠ) : SeqD ns F EqX a Premises Δ A :=
  seq_exfalso h

/-- Conjoin two hypotheses into one. -/
def pm_conj (n : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (hA : SeqD ns F EqX a Premises Δ A) (hB : SeqD ns F EqX a Premises Δ B)
    (k : SeqD (n :: ns) F EqX a Premises ((A ∧ᶠ B) :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_andI hA hB) k

/-- Case split on `A ∨ᶠ ¬ᶠA`. Needs LEM, so it is not available in the base system. -/
def pm_classic (n m : String) (hlem : a.lem = true) (A : Formula F Γ)
    {Δ : HCtx F Γ} {C : Formula F Γ}
    (h₁ : SeqD (n :: ns) F EqX a Premises (A :: Δ) C)
    (h₂ : SeqD (m :: ns) F EqX a Premises ((¬ᶠA) :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_orE (seq_of_thm (.lem hlem)) h₁ h₂

/-- Use an implicational hypothesis, proving its antecedent, and keep the conclusion. -/
def pm_impcut (n : String) {Δ : HCtx F Γ} {A B C : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A →ᶠ B))
    (hA : SeqD ns F EqX a Premises Δ A)
    (k : SeqD (n :: ns) F EqX a Premises (B :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_mp h hA) k

/-- Rename a hypothesis. Names are display data, so this is the identity. -/
def pm_rename {ns' : List String} {Δ : HCtx F Γ} {B : Formula F Γ}
    (h : SeqD ns' F EqX a Premises Δ B) : SeqD ns F EqX a Premises Δ B := h

/-- Revert the most recent hypothesis into the goal. Definitionally the identity — the
packing is arranged so that it is (see `Packing.lean`). -/
def pm_revert {n : String} {Δ : HCtx F Γ} {A B : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (A →ᶠ B)) :
    SeqD (n :: ns) F EqX a Premises (A :: Δ) B := h

/-- Prove the goal in a *weaker* system. The counterpart of `use <reasoning> in H`: since
`Allowed` is a flag rather than a constraint system, weakening is a plain cast. -/
def pm_in_system {a' : Allowed} (h_le : Allowed.le a' a) {Δ : HCtx F Γ} {B : Formula F Γ}
    (h : SeqD ns F EqX a' Premises Δ B) : SeqD ns F EqX a Premises Δ B :=
  Derivable.castAllowed h_le h

/-- **Enter the proof mode** from an ordinary kernel goal.

`Seq` with an empty hypothesis context *is* `Derivable`, so this is the identity — but a
script has to say so, or the goal stays a kernel derivation and none of the tactics apply. -/
def pm_enter {Γ : Ctx ι} {A : Formula F Γ}
    (h : SeqD [] F EqX a Premises [] A) : Derivable F EqX a Premises A := h

/-- Introduce a `∀`. The whole hypothesis context weakens; the *names* do not change, which
is why the name list can be reused verbatim. -/
def pm_allI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F EqX a Premises (Δ.map (Formula.weakenBy ρ)) A) :
    SeqD ns F EqX a Premises Δ (Formula.all ρ A) :=
  seq_allI h

/-- Instantiate a weakened `∀`-hypothesis at the bound variable. -/
def pm_allE_here {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)} {A : Formula F (ρ :: Γ)}
    (h : SeqD ns F EqX a Premises Δ (Formula.weakenBy ρ (Formula.all ρ A))) :
    SeqD ns F EqX a Premises Δ A :=
  seq_allE_here h

/-- Supply a witness for an `∃` goal. -/
def pm_exI {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F EqX a Premises Δ (A.subst0 t)) :
    SeqD ns F EqX a Premises Δ (Formula.ex ρ A) :=
  seq_exI t h

/-- Supply a witness at a *headline* `∃`. The recursor ban is enforced by the `pbound`
tactic, not by this lemma — see `ProofMode/Linter.lean`. -/
def pm_bound {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} (t : Term F Γ ρ)
    (h : SeqD ns F EqX a Premises Δ (A.subst0 t)) :
    SeqD ns F EqX a Premises Δ (Formula.ex ρ A) :=
  seq_bound t h

/-- Consume an `∃`, naming the body. -/
def pm_exE (n : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} {B : Formula F Γ}
    (hex : SeqD ns F EqX a Premises Δ (Formula.ex ρ A))
    (hbody : SeqD (n :: ns) F EqX a Premises
      (A :: Δ.map (Formula.weakenBy ρ)) (Formula.weakenBy ρ B)) :
    SeqD ns F EqX a Premises Δ B :=
  seq_exE hex hbody

/-- Use a theorem of the kernel — the escape hatch into `Derivable`. -/
def pm_have {Δ : HCtx F Γ} {A : Formula F Γ}
    (h : Derivable F EqX a Premises A) : SeqD ns F EqX a Premises Δ A :=
  seq_of_thm h

/-- Modus ponens against a hypothesis. -/
def pm_mp {Δ : HCtx F Γ} {A B : Formula F Γ}
    (hAB : SeqD ns F EqX a Premises Δ (A →ᶠ B)) (hA : SeqD ns F EqX a Premises Δ A) :
    SeqD ns F EqX a Premises Δ B :=
  seq_mp hAB hA

/-- Forward reasoning: prove something, then keep it as a named hypothesis. -/
def pm_cut (n : String) {Δ : HCtx F Γ} {A C : Formula F Γ}
    (hA : SeqD ns F EqX a Premises Δ A)
    (k : SeqD (n :: ns) F EqX a Premises (A :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut hA k

-- ============================================================================
-- Equational reasoning
-- ============================================================================

/-- Reflexivity of `=₀`. -/
def pm_refl {Δ : HCtx F Γ} {t : Term F Γ Ty.nat} :
    SeqD ns F EqX a Premises Δ (Formula.eq0 t t) :=
  seq_of_thm .refl0

/-- Symmetry of `=₀`. -/
def pm_sym {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat}
    (h : SeqD ns F EqX a Premises Δ (Formula.eq0 t s)) :
    SeqD ns F EqX a Premises Δ (Formula.eq0 s t) :=
  seq_mono .sym0 h

/-- Transitivity of `=₀`, as a *step*: name the midpoint and get the two halves as goals.

The kernel gives transitivity in `∧`-form; this is the curried form a script wants, and it
is the closest thing to a `calc` step the object logic has — there is no rewriting, because
there is no extensionality. -/
def pm_trans {Δ : HCtx F Γ} {s u : Term F Γ Ty.nat} (t : Term F Γ Ty.nat)
    (h₁ : SeqD ns F EqX a Premises Δ (Formula.eq0 s t))
    (h₂ : SeqD ns F EqX a Premises Δ (Formula.eq0 t u)) :
    SeqD ns F EqX a Premises Δ (Formula.eq0 s u) :=
  seq_mp (seq_of_thm .trans0) (seq_andI h₁ h₂)

/-- Flip an equational hypothesis, keeping the flipped form under a new name. -/
def pm_sym_at (n : String) {Δ : HCtx F Γ} {s t : Term F Γ Ty.nat} {C : Formula F Γ}
    (h : SeqD ns F EqX a Premises Δ (Formula.eq0 s t))
    (k : SeqD (n :: ns) F EqX a Premises (Formula.eq0 t s :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (pm_sym h) k

-- ============================================================================
-- Moves specific to this logic
-- ============================================================================

/-- Induction on `ℕ`, with the hypothesis context carried through. See
`ProofMode/Induction.lean` for why the context is not free here. -/
def pm_induction {Δ : HCtx F Γ} {A : Formula F (Ty.nat :: Γ)}
    (base : SeqD ns F EqX a Premises Δ (A.subst0 Term.zero))
    (step : SeqD ns F EqX a Premises Δ
      (Formula.all Ty.nat (A →ᶠ Formula.substVar0 A succVar0))) :
    SeqD ns F EqX a Premises Δ (Formula.all Ty.nat A) :=
  seq_induction base step

/-- Markov's principle: a `∃` over a QF ∨-free matrix may be proved by contradiction. -/
def pm_markov {Δ : HCtx F Γ} {ρ : Ty ι} {A₀ : Formula F (ρ :: Γ)}
    (hm : a.markov = true) (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : SeqD ns F EqX a Premises Δ (¬ᶠ¬ᶠ(Formula.ex ρ A₀))) :
    SeqD ns F EqX a Premises Δ (Formula.ex ρ A₀) :=
  seq_mono (.markov hm hqf hvf) h

/-- Instantiate a weakened `∀`-hypothesis at the bound variable, keeping the result as a
named hypothesis. The forward counterpart of `pm_allE_here`, and the move you need after
`pm_allI` to *use* a `∀`-hypothesis rather than to prove a `∀`-goal. -/
def pm_allE_here_cut (n : String) {ρ : Ty ι} {Δ : HCtx F (ρ :: Γ)}
    {A C : Formula F (ρ :: Γ)}
    (h : SeqD ns F EqX a Premises Δ (Formula.weakenBy ρ (Formula.all ρ A)))
    (k : SeqD (n :: ns) F EqX a Premises (A :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_allE_here h) k

/-- Instantiate a `∀`-hypothesis at a term, keeping the result as a named hypothesis. -/
def pm_inst (n : String) {ρ : Ty ι} {Δ : HCtx F Γ} {A : Formula F (ρ :: Γ)} {C : Formula F Γ}
    (t : Term F Γ ρ)
    (h : SeqD ns F EqX a Premises Δ (Formula.all ρ A))
    (k : SeqD (n :: ns) F EqX a Premises (A.subst0 t :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_allE h t) k

/-- QF-AC, forwards: from `∀x ∃y A₀` obtain the choice function. -/
def pm_qfac (n : String) {ρ τ : Ty ι} {Δ : HCtx F Γ} {A₀ : Formula F (τ :: ρ :: Γ)}
    {C : Formula F Γ}
    (hq : a.qfac = true) (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : SeqD ns F EqX a Premises Δ (Formula.all ρ (Formula.ex τ A₀)))
    (k : SeqD (n :: ns) F EqX a Premises
      (Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A₀)) :: Δ) C) :
    SeqD ns F EqX a Premises Δ C :=
  seq_cut (seq_mono (.qfac hq hqf hvf) h) k

-- ============================================================================
-- Tactics
-- ============================================================================

section Tactics
open Lean.Elab.Tactic Lean.Meta

/-- `pexact h` closes the goal with the hypothesis named `h`.

This is the only tactic that reads the goal: it turns the *name* `h` into the de Bruijn
index that `HVar` wants. Names and `Δ` are aligned positionally, so the index is just the
position of `h` in the name list. It comes first because the elimination tactics below
discharge their major premise with `by pexact …`. -/
elab "pexact " h:ident : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let args := ty.getAppArgs
  unless ty.isAppOf ``SeqD && args.size == 9 do
    throwError "pexact: the goal is not a proof-mode sequent{indentExpr ty}"
  let some namesE := listLit? args[1]! |
    throwError "pexact: the hypothesis names are not a literal list"
  let names := namesE.filterMap strLit?
  let n := h.getId.toString
  let some i := names.findIdx? (· == n) |
    throwError "pexact: no hypothesis named `{n}` (have: {names})"
  let mut v ← `(HVar.hz)
  for _ in [0:i] do v ← `(HVar.hs $v)
  evalTactic (← `(tactic| exact seq_id $v))

/-- `pmode` enters the proof mode from a kernel goal, so a theorem can be *stated* as an
ordinary `Derivable` and *proved* as a script. -/
macro "pmode" : tactic => `(tactic| refine pm_enter ?_)

/-- `passumption` closes the goal with whichever hypothesis matches, without naming it. -/
elab "passumption" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let args := ty.getAppArgs
  unless ty.isAppOf ``SeqD && args.size == 9 do
    throwError "passumption: the goal is not a proof-mode sequent{indentExpr ty}"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  for n in names do
    let stx := mkIdent (Name.mkSimple n)
    try
      evalTactic (← `(tactic| pexact $stx))
      return
    catch _ => pure ()
  throwError "passumption: no hypothesis matches the goal (have: {names})"

/-- `pfail "…"` fails with exactly this message. Unlike `fail` it does not append the goal
state, which matters here: the interesting failures are about the *shape* of the goal, and
the shape is what the message already says. -/
elab "pfail " s:str : tactic => throwError s.getString

/-- Side conditions of the object-logic rules — `allowed` flags and `isQF`/`isVFree`
checks — are settled by computation when everything is concrete, and otherwise looked for
in the Lean context. -/
macro "pside" : tactic => `(tactic| first | rfl | assumption | decide)

/-- Reduce a `Bool`-valued side condition. `some b` if it settles, `none` if it is stuck on
an abstract formula — in which case the tactic should try to *prove* the side condition
rather than refuse. -/
private def evalBoolCheck (e : Expr) : TacticM (Option Bool) := do
  match (← whnfD e) with
  | .const ``Bool.true  _ => return some true
  | .const ``Bool.false _ => return some false
  | _ => return none

/-- The `SeqD` goal, split into its arguments: `ι, names, F, EqX, a, Premises, Γ, Δ, B`. -/
def seqDGoalArgs (who : String) : TacticM (Array Expr) := do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let args := ty.getAppArgs
  unless ty.isAppOf ``SeqD && args.size == 9 do
    throwError "{who}: the goal is not a proof-mode sequent{indentExpr ty}"
  return args

/-- The formula at position `n` of the hypothesis context of the current goal. -/
private def hypFormula (who : String) (n : String) : TacticM Expr := do
  let args ← seqDGoalArgs who
  let some namesE := listLit? args[1]! |
    throwError "{who}: the hypothesis names are not a literal list"
  let names := namesE.filterMap strLit?
  let some i := names.findIdx? (· == n) |
    throwError "{who}: no hypothesis named `{n}` (have: {names})"
  let some hyps ← whnfListLit? args[7]! |
    throwError "{who}: the hypothesis context is not a literal list"
  let some A := hyps[i]? | throwError "{who}: `{n}` names position {i}, which is not there"
  return A

/-- Does this expression *apply the recursor itself*, as opposed to using a constant of the
language that happens to be defined by recursion?

The traversal deliberately does not unfold constants: `Term.add` is built from `Term.prec`,
as every primitive-recursive constant must be, and `x + y` is not a smuggled bound. Only an
occurrence the user typed is refused. See `ProofMode/Linter.lean` for why this is the right
reading of "surface", and for the limit of it. -/
private def mentionsPrec (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Term.prec)).isSome

private partial def unparen (s : Syntax) : Syntax :=
  if s.getKind == ``Lean.Parser.Term.paren then unparen s[1] else s

/-- Elaborate a kernel theorem with its context pinned to the goal's.

Pinning by the *expected type* alone does not work: Lean fixes a theorem's `Γ` from its first
explicit argument, before unifying the result type. So the goal's context is injected as a
named argument at the head of the application — which is what lets a theorem mention `x₀`
next to a term from the outer context, the latter then weakening by coercion.

Theorems that are not applications, or whose context implicit is not called `Γ`, fall back to
plain elaboration against the expected type. -/
def elabRuleInCtx (eStx : TSyntax `term) (Γ expected : Expr) : TacticM Expr := do
  let bare := unparen eStx.raw
  if bare.getKind == ``Lean.Parser.Term.app then
    let ΓStx ← Lean.Elab.Term.exprToSyntax Γ
    let named ← `(Lean.Parser.Term.namedArgument| (Γ := $ΓStx))
    let pinned : TSyntax `term := ⟨Syntax.node2 .none ``Lean.Parser.Term.app bare[0]
      (Syntax.node .none `null (#[named.raw] ++ bare[1].getArgs))⟩
    try
      return ← Lean.Elab.Term.withoutErrToSorry (elabTerm pinned (some expected))
    catch _ => pure ()
  Lean.Elab.Term.withoutErrToSorry (elabTerm eStx (some expected))

/-- The type `Derivable F EqX a Premises Γ ?A` for the goal's parameters — the expected type
a kernel theorem is elaborated against. -/
def derivableInGoal (args : Array Expr) : TacticM Expr := do
  let A ← mkFreshExprMVar (mkAppN (.const ``Formula []) #[args[0]!, args[2]!, args[6]!])
  return mkAppN (.const ``Derivable [])
    #[args[0]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, A]

/-- Elaborate a term the *user wrote* at a surface position, and enforce the recursor ban.

`HANDOFF` D-2 puts the ban on the surface language as a whole — "instantiation witnesses,
`bound` instantiations, `split` precisions, `ind` motives" — not only on headline `∃`
witnesses. That is deliberately stronger than a headline-only check and is what makes the
non-triviality claim a statement about *expressiveness*: the input language cannot write the
bound, so no enumeration of smuggling routes is needed. R4's attempt C reached the extracted
term through an *instantiation*, never touching an `∃`, which is exactly why the check has
to live here rather than at `∃`-introduction. -/
private def elabSurfaceTerm (who : String) (ι F Γ ρ : Expr) (tStx : TSyntax `term) :
    TacticM Expr := do
  let t ← elabTerm tStx (some (mkAppN (.const ``Term []) #[ι, F, Γ, ρ]))
  if mentionsPrec (← instantiateMVars t) then
    throwError "{who}: the term applies the primitive recursor directly.\n\
      Iteration is what extraction produces, so a hand-written iterating term makes the\n\
      extraction vacuous (HANDOFF D-2, surface-recursor ban). If this really is auxiliary, \
      say so\nexplicitly with `pexists!`."
  return t

/-- `pintro h k …` introduces implications, naming the hypotheses. -/
syntax (name := pintro) "pintro" (ppSpace colGt ident)+ : tactic

macro_rules
  | `(tactic| pintro $h:ident $hs:ident*) =>
      let n := Lean.quote h.getId.toString
      if hs.isEmpty then
        `(tactic| refine pm_intro $n ?_)
      else
        `(tactic| (refine pm_intro $n ?_; pintro $hs*))

/-- `psplit` splits a conjunctive goal into two. -/
macro "psplit" : tactic => `(tactic| refine pm_split ?_ ?_)

/-- `pleft` / `pright` choose a disjunct. -/
macro "pleft" : tactic => `(tactic| refine pm_left ?_)
macro "pright" : tactic => `(tactic| refine pm_right ?_)

/-- `pcases h with hl | hr` does case analysis on the disjunction proved by hypothesis `h`. -/
macro "pcases " h:ident " with " l:ident " | " r:ident : tactic =>
  `(tactic| refine pm_cases $(Lean.quote l.getId.toString) $(Lean.quote r.getId.toString)
      (by pexact $h) ?_ ?_)

/-- `pand_left` / `pand_right` weaken the goal to a conjunction containing it. The other
conjunct is left as a metavariable, to be fixed by whatever closes the branch. -/
macro "pand_left" : tactic => `(tactic| apply pm_andE₁)
macro "pand_right" : tactic => `(tactic| apply pm_andE₂)

/-- `pexfalso` replaces the goal by `⊥ᶠ`. -/
macro "pexfalso" : tactic => `(tactic| refine pm_exfalso ?_)

/-- `prefl` / `psym` / `ptrans t` — equational reasoning on `=₀`. `ptrans` names the
midpoint and leaves the two halves as goals; the midpoint is a surface term, so the
recursor ban applies to it. -/
macro "prefl" : tactic => `(tactic| exact pm_refl)
macro "psym" : tactic => `(tactic| refine pm_sym ?_)

elab "ptrans " tStx:term : tactic => do
  let args ← seqDGoalArgs "ptrans"
  let target ← whnfD args[8]!
  let targs := target.getAppArgs
  unless target.isAppOf ``Formula.eq0 && targs.size == 5 do
    throwError "ptrans: the goal is not an equation."
  let natTy := mkApp (.const ``Ty.nat []) targs[0]!
  let _ ← elabSurfaceTerm "ptrans" targs[0]! targs[1]! targs[2]! natTy tStx
  evalTactic (← `(tactic| refine pm_trans $tStx ?_ ?_))

/-- `pnorm` clears the de Bruijn bookkeeping a goal accumulates when a weakening meets a
substitution — most often after supplying a just-obtained witness back to an `∃`. -/
macro "pnorm" : tactic =>
  `(tactic| simp only [Formula.subst0_weakenUnder, Formula.subst0_weakenBy,
      Formula.substVar0_weakenBy])

/-- `pforall` introduces a `∀`, weakening the hypothesis context. -/
macro "pforall" : tactic => `(tactic| refine pm_allI ?_)

/-- `pspecialize` instantiates a weakened `∀`-*goal* at the bound variable;
`pspecialize h as k` instantiates a weakened `∀`-*hypothesis*, which is how a `∀`-hypothesis
is used after `pforall`.

The `colGt` matters: without it the bare form would swallow the next line's tactic name as
its `h`. -/
syntax "pspecialize" (ppSpace colGt ident " with " ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| pspecialize) => `(tactic| refine pm_allE_here ?_)
  | `(tactic| pspecialize $h:ident with $k:ident) =>
      `(tactic| refine pm_allE_here_cut $(Lean.quote k.getId.toString) (by pexact $h) ?_)

/-- The `Formula.ex` the goal is, split into `ι, F, Γ, ρ, A`. -/
private def exGoalArgs (who : String) : TacticM (Array Expr) := do
  let args ← seqDGoalArgs who
  let target ← whnfD args[8]!
  let targs := target.getAppArgs
  unless target.isAppOf ``Formula.ex && targs.size == 5 do
    throwError "{who}: the goal is not an ∃, so there is no witness to supply."
  return targs

/-- `pexists t` supplies a witness for an `∃` goal, subject to the surface-recursor ban. -/
elab "pexists " tStx:term : tactic => do
  let g ← exGoalArgs "pexists"
  let _ ← elabSurfaceTerm "pexists" g[0]! g[1]! g[2]! g[3]! tStx
  evalTactic (← `(tactic| refine pm_exI $tStx ?_))

/-- `pexists! t` supplies a witness **without** the recursor ban.

The escape hatch exists so that a bypass is visible in the source and greppable, rather than
being the silent default. Using it at a headline `∃` invalidates the extraction claim. -/
macro "pexists! " t:term : tactic => `(tactic| refine pm_exI $t ?_)

/-- `pbound t` supplies a witness at a *headline* `∃`.

This is `bound` v0: a certificate **checker**, not a prover. The user writes the bound; the
tactic checks that it is a bound the extraction could have produced rather than one smuggled
in by hand. It differs from `pexists` only in recording, at the call site, that this is the
headline position — the check itself is the same, because D-2 puts the ban on the surface
language rather than on headline positions specifically.

Like `pby_contra`, the check runs *before* anything is applied to the goal. -/
elab "pbound " tStx:term : tactic => do
  let g ← exGoalArgs "pbound"
  let _ ← elabSurfaceTerm "pbound" g[0]! g[1]! g[2]! g[3]! tStx
  evalTactic (← `(tactic| refine pm_bound $tStx ?_))

/-- `pobtain h with x` consumes the `∃` proved by hypothesis `h`, naming the body `x`. -/
macro "pobtain " h:ident " with " x:ident : tactic =>
  `(tactic| refine pm_exE $(Lean.quote x.getId.toString) (by pexact $h) ?_)

/-- `pdestruct h with x y` splits the conjunction proved by hypothesis `h`. -/
macro "pdestruct " h:ident " with " x:ident ppSpace y:ident : tactic =>
  `(tactic| refine pm_andcut $(Lean.quote x.getId.toString) $(Lean.quote y.getId.toString)
      (by pexact $h) ?_)

/-- `pthm e` discharges the goal with a kernel theorem. -/
elab "pthm " eStx:term : tactic => do
  let args ← seqDGoalArgs "pthm"
  let e ← elabRuleInCtx eStx args[6]! (← derivableInGoal args)
  let eS ← Lean.Elab.Term.exprToSyntax (← instantiateMVars e)
  evalTactic (← `(tactic| exact pm_have $eS))

/-- `papply h` uses the implicational hypothesis `h`, leaving its antecedents as goals.

It peels as many arrows as it takes to reach the goal, so a hypothesis with several premises
produces several subgoals, in order — the same way Lean's own `apply` does. -/
elab "papply " h:ident : tactic => do
  let args ← seqDGoalArgs "papply"
  let goalF := args[8]!
  let hyp ← hypFormula "papply" h.getId.toString
  -- How many antecedents lie between `h` and the goal? Probed without committing to any
  -- unification the probe happens to make.
  let k? ← withoutModifyingState do
    let mut cur ← whnfD hyp
    for i in [0:16] do
      if (← isDefEq cur goalF) then return some i
      let cargs := cur.getAppArgs
      unless cur.isAppOf ``Formula.imp && cargs.size == 5 do return none
      cur ← whnfD cargs[4]!
    return none
  let some k := k? |
    throwError "papply: `{h.getId}` does not conclude the goal.\n\
      It is{indentExpr hyp}\nand the goal is{indentExpr goalF}"
  if k == 0 then
    evalTactic (← `(tactic| pexact $h))
  else
    let mut e ← `(by pexact $h)
    for _ in [0:k] do e ← `(pm_mp $e ?_)
    evalTactic (← `(tactic| refine $e))

/-- `papply h in k with m` applies the implicational hypothesis `h` to the hypothesis `k`,
adding the conclusion under the name `m`. Forward reasoning, the counterpart of `papply`. -/
macro "papply " h:ident " in " k:ident " with " m:ident : tactic =>
  `(tactic| refine pm_cut $(Lean.quote m.getId.toString)
      (pm_mp (by pexact $h) (by pexact $k)) ?_)

/-- `papplym e` applies a *kernel theorem* to the goal, leaving its antecedents as goals —
the escape hatch's `apply`, next to `pthm`'s `exact`. -/
elab "papplym " eStx:term : tactic => do
  let args ← seqDGoalArgs "papplym"
  let goalF := args[8]!
  let e ← elabRuleInCtx eStx args[6]! (← derivableInGoal args)
  let ety ← instantiateMVars (← inferType e)
  let etyArgs := ety.getAppArgs
  unless ety.isAppOf ``Derivable && etyArgs.size == 7 do
    throwError "papplym: not a kernel derivation{indentExpr ety}"
  let k? ← withoutModifyingState do
    let mut cur ← whnfD etyArgs[6]!
    for i in [0:16] do
      if (← isDefEq cur goalF) then return some i
      let cargs := cur.getAppArgs
      unless cur.isAppOf ``Formula.imp && cargs.size == 5 do return none
      cur ← whnfD cargs[4]!
    return none
  let some k := k? | throwError "papplym: this theorem does not conclude the goal.\n\
      It proves{indentExpr etyArgs[6]!}\nand the goal is{indentExpr goalF}"
  if k == 0 then
    evalTactic (← `(tactic| pthm $eStx))
  else
    let mut t ← `(pm_have $eStx)
    for _ in [0:k] do t ← `(pm_mp $t ?_)
    evalTactic (← `(tactic| refine $t))

/-- `papplym e in h with k` applies a kernel theorem to a hypothesis. -/
macro "papplym " e:term " in " h:ident " with " k:ident : tactic =>
  `(tactic| refine pm_cut $(Lean.quote k.getId.toString)
      (pm_mp (pm_have $e) (by pexact $h)) ?_)

/-- `pdestruct_imp h with k` uses an implicational hypothesis: prove its antecedent in the
first goal, continue with its conclusion named `k` in the second. -/
macro "pdestruct_imp " h:ident " with " k:ident : tactic =>
  `(tactic| refine pm_impcut $(Lean.quote k.getId.toString) (by pexact $h) ?_ ?_)

/-- `pconj h k with m` conjoins two hypotheses. -/
macro "pconj " h:ident ppSpace k:ident " with " m:ident : tactic =>
  `(tactic| refine pm_conj $(Lean.quote m.getId.toString) (by pexact $h) (by pexact $k) ?_)

/-- `pcontradiction h` finishes the proof from a hypothesis `h : ⊥ᶠ`. -/
macro "pcontradiction " h:ident : tactic => `(tactic| (pexfalso; pexact $h))

/-- `pclassic A with h k` splits on `A ∨ᶠ ¬ᶠA`. Refused — before anything is applied to the
goal — unless LEM is available. -/
elab "pclassic " A:term " with " h:ident ppSpace k:ident : tactic => do
  let args ← seqDGoalArgs "pclassic"
  if (← evalBoolCheck (mkAppN (.const ``Allowed.lem []) #[args[4]!])) == some false then
    throwError "pclassic: excluded middle is not available here — \
      `allowed.lem` is not `true`."
  evalTactic (← `(tactic|
    (refine pm_classic $(Lean.quote h.getId.toString) $(Lean.quote k.getId.toString)
        ?hlem $A ?pos ?neg
     case hlem => pside)))

/-- The pieces a context-surgery tactic needs: the goal's arguments, the hypothesis names,
the hypothesis formulas, the position of `n`, and the `Formula F Γ` type to build lists at. -/
private def hypSplit (who : String) (n : String) :
    TacticM (Array Expr × List String × List Expr × Nat × Expr) := do
  let args ← seqDGoalArgs who
  let some namesE := listLit? args[1]! |
    throwError "{who}: the hypothesis names are not a literal list"
  let names := namesE.filterMap strLit?
  let some i := names.findIdx? (· == n) |
    throwError "{who}: no hypothesis named `{n}` (have: {names})"
  let some hyps ← whnfListLit? args[7]! |
    throwError "{who}: the hypothesis context is not a literal list"
  let fTy := mkAppN (.const ``Formula []) #[args[0]!, args[2]!, args[6]!]
  return (args, names, hyps, i, fTy)

/-- Replace the goal by `newTy`, justified by `proof newGoal`. -/
private def replaceGoalWith (newTy : Expr) (proof : Expr → Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let m ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar newTy
  goal.assign (proof m)
  replaceMainGoal [m.mvarId!]

/-- Rebuild a `SeqD` goal with new names and a new hypothesis context. -/
private def mkSeqD (args : Array Expr) (namesE ΔE : Expr) : Expr :=
  mkAppN (.const ``SeqD []) #[args[0]!, namesE, args[2]!, args[3]!, args[4]!,
    args[5]!, args[6]!, ΔE, args[8]!]

private def mkStrListLit (xs : List String) : MetaM Expr :=
  Lean.Meta.mkListLit (.const ``String []) (xs.map (Expr.lit <| .strVal ·))

/-- `pclear h` drops a hypothesis, wherever it sits in the context. -/
elab "pclear " h:ident : tactic => do
  let (args, names, hyps, i, fTy) ← hypSplit "pclear" h.getId.toString
  let Δ₁ ← Lean.Meta.mkListLit fTy (hyps.take i)
  let Δ₂ ← Lean.Meta.mkListLit fTy (hyps.drop (i + 1))
  let namesE ← mkStrListLit (names.take i ++ names.drop (i + 1))
  let ΔE ← Lean.Meta.mkListLit fTy (hyps.take i ++ hyps.drop (i + 1))
  replaceGoalWith (mkSeqD args namesE ΔE) fun m =>
    mkAppN (.const ``seq_clear []) #[args[0]!, args[2]!, args[3]!, args[4]!, args[5]!,
      args[6]!, Δ₁, hyps[i]!, Δ₂, args[8]!, m]

/-- `pswap h with k` exchanges two *adjacent* hypotheses. Non-adjacent swaps compose from
these; the kit rule is the adjacent one. -/
elab "pswap " h:ident " with " k:ident : tactic => do
  let (args, names, hyps, i, fTy) ← hypSplit "pswap" h.getId.toString
  let n2 := k.getId.toString
  let some j := names.findIdx? (· == n2) |
    throwError "pswap: no hypothesis named `{n2}` (have: {names})"
  unless j == i + 1 do
    throwError "pswap: `{h.getId}` and `{k.getId}` are at positions {i} and {j}; \
      only adjacent hypotheses can be exchanged directly."
  let Δ₁ ← Lean.Meta.mkListLit fTy (hyps.take i)
  let Δ₂ ← Lean.Meta.mkListLit fTy (hyps.drop (i + 2))
  let namesE ← mkStrListLit
    (names.take i ++ [names[j]!, names[i]!] ++ names.drop (i + 2))
  let ΔE ← Lean.Meta.mkListLit fTy
    (hyps.take i ++ [hyps[j]!, hyps[i]!] ++ hyps.drop (i + 2))
  replaceGoalWith (mkSeqD args namesE ΔE) fun m =>
    mkAppN (.const ``seq_swap []) #[args[0]!, args[2]!, args[3]!, args[4]!, args[5]!,
      args[6]!, Δ₁, hyps[j]!, hyps[i]!, Δ₂, args[8]!, m]

/-- `prevert` moves the most recent hypothesis back into the goal;
`prevert h` moves a named one, walking it to the top with adjacent exchanges first. -/
syntax "prevert" (ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| prevert) => `(tactic| refine pm_revert ?_)

elab_rules : tactic
  | `(tactic| prevert $h:ident) => do
    let n := h.getId.toString
    -- Each exchange moves `h` one place towards the top; re-read the names each time,
    -- since the tactic that did the exchange rewrote them.
    for _ in [0:64] do
      let args ← seqDGoalArgs "prevert"
      let names := ((listLit? args[1]!).getD []).filterMap strLit?
      let some i := names.findIdx? (· == n) |
        throwError "prevert: no hypothesis named `{n}` (have: {names})"
      if i == 0 then
        evalTactic (← `(tactic| refine pm_revert ?_))
        return
      let above := mkIdent (Name.mkSimple names[i - 1]!)
      evalTactic (← `(tactic| pswap $above with $h))
    throwError "prevert: gave up walking `{n}` to the top of the context"

/-- `pin_system h` proves the goal in the weaker system justified by `h : Allowed.le a' a`. -/
macro "pin_system " h:term : tactic => `(tactic| refine pm_in_system $h ?_)

/-- `prename h into k` renames a hypothesis. Names are display data, so nothing is proved. -/
elab "prename " h:ident " into " k:ident : tactic => do
  let args ← seqDGoalArgs "prename"
  let names := ((listLit? args[1]!).getD []).filterMap strLit?
  let n := h.getId.toString
  let some i := names.findIdx? (· == n) |
    throwError "prename: no hypothesis named `{n}` (have: {names})"
  let names' := names.set i k.getId.toString
  let lst ← `([$(names'.toArray.map (Syntax.mkStrLit ·)),*])
  evalTactic (← `(tactic| refine pm_rename (ns' := $lst) ?_))

/-- `psym in h with k` flips an equational hypothesis. -/
macro "psym " " in " h:ident " with " k:ident : tactic =>
  `(tactic| refine pm_sym_at $(Lean.quote k.getId.toString) (by pexact $h) ?_)

/-- `phave h : A` proves `A` in a side goal and keeps it as the hypothesis `h`.

The formula is user-written, so the recursor ban applies to the terms inside it: a cut on
`A` contributes `A`'s witness and counter types to the interpretation, which is the same
route to the extracted content that `pinst` has. -/
elab "phave " h:ident " : " AStx:term : tactic => do
  let args ← seqDGoalArgs "phave"
  let A ← elabTerm AStx (some (mkAppN (.const ``Formula []) #[args[0]!, args[2]!, args[6]!]))
  if mentionsPrec (← instantiateMVars A) then
    throwError "phave: the formula applies the primitive recursor directly.\n\
      Iteration is what extraction produces, so writing it by hand makes the extraction\n\
      vacuous (HANDOFF D-2, surface-recursor ban)."
  evalTactic (← `(tactic| refine pm_cut (A := $AStx) $(Lean.quote h.getId.toString) ?_ ?_))

/-- `pfrom h := e` adds a kernel theorem to the context under the name `h`. -/
macro "pfrom " h:ident " := " e:term : tactic =>
  `(tactic| refine pm_cut $(Lean.quote h.getId.toString) (pm_have $e) ?_)

/-- `pinduction` starts an induction on `ℕ`: base case first, then the step. -/
macro "pinduction" : tactic => `(tactic| refine pm_induction ?_ ?_)

/-- `pby_contra h` proves an `∃` over a QF ∨-free matrix by contradiction, via Markov. The
goal becomes `⊥ᶠ` with `h` the negated `∃`.

**The shape check comes first, and the tactic is atomic.** `HANDOFF` D-4 makes `by_contra`
*be* the Markov rule, and D-1 makes "is this proof translated?" the question a refusal
should provoke. Both require that a wrong-shaped goal be refused before anything is applied
to it — a tactic that half-applies and then complains leaves the user reading errors about a
goal they did not write. -/
elab "pby_contra " h:ident : tactic => do
  let args ← seqDGoalArgs "pby_contra"
  -- `Formula.ex` : {ι} {F} {Γ} (ρ) (A)
  let target ← whnfD args[8]!
  let targs := target.getAppArgs
  unless target.isAppOf ``Formula.ex && targs.size == 5 do
    throwError "pby_contra: the goal is not an ∃ — not a Markov shape.\n\
      Is this proof translated? (HANDOFF D-1: the classical content of a hand-translated \
      proof is\nexactly `¬¬∃n(qf) → ∃n(qf)`.)"
  let A₀ := targs[4]!
  -- `Formula F Γ'` : the three arguments needed to say `isQF A₀` / `isVFree A₀`
  let fargs := (← instantiateMVars (← inferType A₀)).getAppArgs
  let check (fn : Name) : TacticM (Option Bool) :=
    evalBoolCheck (mkAppN (.const fn []) #[fargs[0]!, fargs[1]!, fargs[2]!, A₀])
  if (← evalBoolCheck (mkAppN (.const ``Allowed.markov []) #[args[4]!])) == some false then
    throwError "pby_contra: Markov is not available here — `allowed.markov` is not `true`."
  if (← check ``Formula.isQF) == some false then
    throwError "pby_contra: the matrix is not quantifier-free — not a Markov shape.\n\
      Is this proof translated?"
  if (← check ``Formula.isVFree) == some false then
    throwError "pby_contra: the matrix contains ∨ — not a Markov shape.\n\
      Is this proof translated?"
  evalTactic (← `(tactic| (refine pm_markov ?hm ?hqf ?hvf ?main
                           case hm => pside
                           case hqf => pside
                           case hvf => pside
                           pintro $h)))

/-- `pinst h t as k` instantiates the `∀`-hypothesis `h` at `t`, naming the result `k`.

The instantiation term is a surface term, so the recursor ban applies. This is the route
R4's attempt C used: a `∀`-premise instantiated at a hand-written iterating term contributes
that term to the Dialectica challenge side, and thence to the extracted bound, without ever
introducing an `∃` for a headline-scoped linter to notice. -/
elab "pinst " h:ident ppSpace tStx:term " with " k:ident : tactic => do
  let A ← whnfD (← hypFormula "pinst" h.getId.toString)
  let aargs := A.getAppArgs
  unless A.isAppOf ``Formula.all && aargs.size == 5 do
    throwError "pinst: `{h.getId}` is not a ∀, so there is nothing to instantiate."
  let _ ← elabSurfaceTerm "pinst" aargs[0]! aargs[1]! aargs[2]! aargs[3]! tStx
  evalTactic (← `(tactic| refine pm_inst $(Lean.quote k.getId.toString) $tStx
    (by pexact $h) ?_))

/-- `pqfac h as k` applies QF-AC to the `∀∃`-hypothesis `h`, naming the choice function
statement `k`. -/
macro "pqfac " h:ident " with " k:ident : tactic =>
  -- Unlike Markov, the matrix here is fixed by the *hypothesis*, not by the goal, so that
  -- argument has to be elaborated inline; only the side conditions can be deferred.
  `(tactic| (refine pm_qfac $(Lean.quote k.getId.toString) ?hq ?hqf ?hvf (by pexact $h) ?main
             case hq => pside
             case hqf => pside
             case hvf => pside))

end Tactics

end ProofMode
end Metatheorems
