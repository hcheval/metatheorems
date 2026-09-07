import Metatheorems.Arithmetic
import Metatheorems.Metatheorem

/-!
# Probe P2: is the ℕ-level MCT statement expressible in the shape the metatheorem wants?

Every entry point — `syntactic_general_metatheorem`, its classical and `_at`/`_gen`
variants, and the MFI ones — consumes a derivation of

    all ρ (imp (all .nat B₀) (ex .nat C₀))     with  B₀ C₀ : Formula F [Ty.nat, ρ]

and demands `isQF` and `isVFree` on both matrices.

Three parameters have to travel in one `ρ`, and `Ty` has no products. They don't need any:
take `ρ = nat →ₜ nat →ₜ nat` and read the parameters off as subterms,

    a := h ⌜0⌝        the sequence
    g := h ⌜1⌝        the counterfunction
    K := h ⌜2⌝ ⌜0⌝    the bound

so a majorant for `h` is simultaneously a majorant for all three.

Only ONE universal variable is available in `all .nat B₀`, so antitonicity has to be
stated in one-step form; the two-variable version is derived inside.
-/

namespace Metatheorems
open Formula

variable {ι κ : Type} {F : κ → Ty ι}

/-- The parameter type: `a`, `g`, `K` fused into a single functional. -/
abbrev mctTy (ι : Type) : Ty ι := Ty.nat →ₜ Ty.nat →ₜ Ty.nat

/-- The working context: `.var .vz` is the quantified ℕ, `.var (.vs .vz)` is the parameter. -/
abbrev mctCtx (ι : Type) : Ctx ι := [Ty.nat, mctTy ι]

/-- `h`, the fused parameter. -/
def mctH : Term F (mctCtx ι) (mctTy ι) := .var (.vs .vz)

/-- `a n` -/
def mctA (n : Term F (mctCtx ι) Ty.nat) : Term F (mctCtx ι) Ty.nat :=
  Term.app2 mctH (Term.ofNat 0) n

/-- `g n` -/
def mctG (n : Term F (mctCtx ι) Ty.nat) : Term F (mctCtx ι) Ty.nat :=
  Term.app2 mctH (Term.ofNat 1) n

/-- `K` -/
def mctK : Term F (mctCtx ι) Ty.nat :=
  Term.app2 mctH (Term.ofNat 2) (Term.ofNat 0)

/-- The quantified ℕ variable of the ambient binder. -/
abbrev mctVar : Term F (mctCtx ι) Ty.nat := .var .vz

/-- `x ∸ y =₀ 0`, i.e. `x ≤ y`. -/
abbrev leF (x y : Term F (mctCtx ι) Ty.nat) : Formula F (mctCtx ι) :=
  .eq0 (Term.app2 Term.monus x y) Term.zero

/-- **The premise matrix.**  `a(u+1) ≤ a u  ∧  a u ≤ K`.
One-step antitonicity plus boundedness. -/
def mctB₀ : Formula F (mctCtx ι) :=
  leF (mctA (.app .succ (mctVar))) (mctA mctVar)
    ∧ᶠ leF (mctA mctVar) mctK

/-- **The conclusion matrix.**  `a v =₀ a (v + g v)` — the window `[v, v + g v]` is flat. -/
def mctC₀ : Formula F (mctCtx ι) :=
  .eq0 (mctA mctVar) (mctA (Term.app2 Term.add mctVar (mctG mctVar)))

/-- **The full statement**, in exactly the shape the metatheorem consumes. -/
def mctStatement : Formula F [] :=
  .all (mctTy ι) (.all Ty.nat mctB₀ →ᶠ .ex Ty.nat mctC₀)

/-- **Variant.** Boundedness stated at `0` only, as `a 0 ≤ K`.
`all .nat B₀` puts every conjunct under the `∀u`, so this is expressible only by
duplicating the closed conjunct under the binder. Legal, QF, ∨-free — but the pointwise
`a u ≤ K` of `mctB₀` is equivalent given antitonicity and reads better, so `mctB₀` is what
the derivations use. -/
def mctB₀' : Formula F (mctCtx ι) :=
  leF (mctA (.app .succ (mctVar))) (mctA mctVar)
    ∧ᶠ leF (mctA Term.zero) mctK

example : (mctB₀' (F := F) (ι := ι)).isQF = true := rfl
example : (mctB₀' (F := F) (ι := ι)).isVFree = true := rfl

/-! ## The side conditions -/

example : (mctB₀ (F := F) (ι := ι)).isQF = true := rfl
example : (mctB₀ (F := F) (ι := ι)).isVFree = true := rfl
example : (mctC₀ (F := F) (ι := ι)).isQF = true := rfl
example : (mctC₀ (F := F) (ι := ι)).isVFree = true := rfl

/-! ## Does it actually fit a metatheorem entry point?

An `example` used to sit here applying `general_metatheorem` to `mctStatement`, as the shape
check: if it elaborates, the only remaining input is the derivation. It went with
`general_metatheorem` itself, whose `Majorizability` argument is uninhabitable
(`MajorizabilityRel.lean`), so no instantiation of it could ever have been run.

Nothing is lost, because the check is made twice over further down and both times against a
live entry point: **Probe P2d** (`mctExtract` / `mct_bound`, below) composes
`general_metatheorem_extract` with `metatheorem_core_of_majorants` over a `MajorizabilityRel`,
and `mct_bound_p1` / `mct_bound_p2` (`ProofMode/MCT.lean`, `ProofMode/MCTLazy.lean`) apply
`syntactic_general_metatheorem` to the real derivations. `mct_bound_p2_at` and `mctPhi` are
the MFI versions. -/

/-!
## Probe P2b: does the derivation plumbing compute?

The statement lives at `Γ = []`. `forall_rule` is the only ∀-introduction that lets the
conclusion mention the bound variable, and it carries a side hypothesis:

    (weakenBy ρ B →ᶠ A)  ⟹  (B →ᶠ all ρ A)

so every line of the derivation has the shape `H →ᶠ …` with `H` the accumulated hypothesis.
That is the Iris-style display, forced by the system rather than chosen.

The question is whether `subst0` and `weakenBy` reduce on *these* formulas — the ones with
`h ⌜0⌝ n` subterms — so that instantiating the premise lands on the formula one expects,
definitionally. Each `rfl`-shaped proof below that elaborates means no rewriting is needed.
-/

section Plumbing

variable {al : Allowed} {Premises : PremiseSet F}

/-- The context after introducing the parameter binder. -/
abbrev mctCtx1 (ι : Type) : Ctx ι := [mctTy ι]

/-- `h` in that context. -/
abbrev mctH1 : Term F (mctCtx1 ι) (mctTy ι) := .var .vz

/-- `a n`, `g n`, `K` there. -/
abbrev mctA1 (n : Term F (mctCtx1 ι) Ty.nat) : Term F (mctCtx1 ι) Ty.nat :=
  Term.app2 mctH1 (Term.ofNat 0) n
abbrev mctG1 (n : Term F (mctCtx1 ι) Ty.nat) : Term F (mctCtx1 ι) Ty.nat :=
  Term.app2 mctH1 (Term.ofNat 1) n
abbrev mctK1 : Term F (mctCtx1 ι) Ty.nat :=
  Term.app2 mctH1 (Term.ofNat 2) (Term.ofNat 0)

/-- **P2b-i.** Instantiate the premise at `t` and project out one-step antitonicity.
If `subst0` did not compute through `app2`/`ofNat`, this would not typecheck. -/
def mct_anti_step (t : Term F (mctCtx1 ι) Ty.nat) :
    Derivable F al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        .eq0 (Term.app2 Term.monus (mctA1 (.app .succ t)) (mctA1 t)) Term.zero) :=
  .syllogism (.forall_ax t) .and_weak

/-- **P2b-ii.** … and boundedness. -/
def mct_bounded (t : Term F (mctCtx1 ι) Ty.nat) :
    Derivable F al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        .eq0 (Term.app2 Term.monus (mctA1 t) mctK1) Term.zero) :=
  .syllogism (.forall_ax t) and_proj2

/-- **P2b-iii.** ∃-introduction at a witness `t`: the goal the derivation must eventually hit. -/
def mct_ex_intro (t : Term F (mctCtx1 ι) Ty.nat) :
    Derivable F al Premises
      (Formula.eq0 (mctA1 t) (mctA1 (Term.app2 Term.add t (mctG1 t)))
        →ᶠ Formula.ex Ty.nat mctC₀) :=
  .exist_ax t mctC₀

/-- **P2b-iv.** The ∀-introduction that closes the outer binder, given the body.
`B := ⊥ᶠ →ᶠ ⊥ᶠ` is the "no hypothesis yet" placeholder; `mp` discharges it. -/
def mct_close
    (body : Derivable F al Premises
      (Formula.weakenBy (mctTy ι) (⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ
        (Formula.all Ty.nat mctB₀ →ᶠ Formula.ex Ty.nat mctC₀))) :
    Derivable F al Premises (mctStatement (ι := ι) (F := F)) :=
  .mp I_comb (.forall_rule body)

/-! ### The step that consumes the induction hypothesis

The IH gives `H →ᶠ ex nat C`. To use the witness while keeping `H` available, the hypothesis
has to be pushed under the existential first. That lemma now lives in `PureFOLLemmas`. -/

-- `ex_and_left` now lives in `PureFOLLemmas`; the local copy was removed.

/-! ### Probe P2c: the induction formula, at the real depth

`induction` consumes `A.subst0 zero` and `all nat (A →ᶠ substVar0 A (succ (var vz)))`.
`A` here is the actual induction formula of the MCT proof — the hypothesis `H` carried as an
antecedent, then a `∀m`, then an `∃n`, so the innermost matrix sits four binders deep.

Each `rfl` below says that the constructor's index reduces, at that depth, to the formula
written out by hand. If de Bruijn bookkeeping were going to hurt, it would hurt here. -/

section Depth

/-- `a n`, `g n`, `K` relative to an arbitrary `h` in an arbitrary context. -/
abbrev aAt {Γ : Ctx ι} (h : Term F Γ (mctTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app2 h (Term.ofNat 0) n
abbrev gAt {Γ : Ctx ι} (h : Term F Γ (mctTy ι)) (n : Term F Γ Ty.nat) : Term F Γ Ty.nat :=
  Term.app2 h (Term.ofNat 1) n

/-- `x ≤ y` in an arbitrary context. -/
abbrev leAt {Γ : Ctx ι} (x y : Term F Γ Ty.nat) : Formula F Γ :=
  .eq0 (Term.app2 Term.monus x y) Term.zero

/-- The flat-window conclusion `∃n (a n =₀ a (n + g n))`, over a given `h`. -/
abbrev flatEx {Γ : Ctx ι} (h : Term F Γ (mctTy ι)) : Formula F Γ :=
  Formula.ex Ty.nat
    (.eq0 (aAt (Term.weaken h) (.var .vz))
          (aAt (Term.weaken h) (Term.app2 Term.add (.var .vz) (gAt (Term.weaken h) (.var .vz)))))

/-- **The induction formula**, in context `[nat, mctTy ι]`: `k` is `.vz`, `h` is `.vs .vz`.

    A(k)  ≡  H  →  ∀m (a m ≤ k → ∃n (a n =₀ a (n + g n))) -/
def mctIndF : Formula F (mctCtx ι) :=
  Formula.weakenBy Ty.nat (Formula.all Ty.nat mctB₀) →ᶠ
    Formula.all Ty.nat
      (leAt (aAt (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))
        →ᶠ flatEx (.var (.vs (.vs .vz))))

/-- **P2c-i.** The base index `A(0)`, written by hand. -/
example :
    (mctIndF (F := F) (ι := ι)).subst0 Term.zero
      = (Formula.all Ty.nat mctB₀ →ᶠ
          Formula.all Ty.nat
            (leAt (aAt (.var (.vs .vz)) (.var .vz)) Term.zero
              →ᶠ flatEx (.var (.vs .vz)))) := rfl

/-- **P2c-ii.** The step index `A(Sk)`, written by hand. -/
example :
    Formula.substVar0 (mctIndF (F := F) (ι := ι)) (.app .succ (.var .vz))
      = (Formula.weakenBy Ty.nat (Formula.all Ty.nat mctB₀) →ᶠ
          Formula.all Ty.nat
            (leAt (aAt (.var (.vs (.vs .vz))) (.var .vz))
                  (.app .succ (.var (.vs .vz)))
              →ᶠ flatEx (.var (.vs (.vs .vz))))) := rfl

/-- **P2c-iii.** The `induction` constructor accepts those two shapes and yields `∀k A(k)`. -/
def mctInduction
    (base : Derivable F al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        Formula.all Ty.nat
          (leAt (aAt (.var (.vs .vz)) (.var .vz)) Term.zero →ᶠ flatEx (.var (.vs .vz)))))
    (step : Derivable F al Premises
      (Formula.all Ty.nat (mctIndF →ᶠ
        (Formula.weakenBy Ty.nat (Formula.all Ty.nat mctB₀) →ᶠ
          Formula.all Ty.nat
            (leAt (aAt (.var (.vs (.vs .vz))) (.var .vz)) (.app .succ (.var (.vs .vz)))
              →ᶠ flatEx (.var (.vs (.vs .vz)))))))) :
    Derivable F al Premises (Formula.all Ty.nat (mctIndF (ι := ι) (F := F))) :=
  .induction base step

/-- **P2c-iv.** Instantiating the induction at `k := K` gives the goal the outer proof needs.
`K` is a term over the parameter, not a numeral, so this exercises `subst0` at a compound term. -/
def mctInstK
    (h : Derivable F al Premises (Formula.all Ty.nat (mctIndF (ι := ι) (F := F)))) :
    Derivable F al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        Formula.all Ty.nat
          (leAt (aAt (.var (.vs .vz)) (.var .vz))
                (Term.app2 (.var (.vs .vz)) (Term.ofNat 2) (Term.ofNat 0))
            →ᶠ flatEx (.var (.vs .vz)))) :=
  .mp h (.forall_ax (Term.app2 (.var .vz) (Term.ofNat 2) (Term.ofNat 0)))

end Depth

end Plumbing

/-! ## Probe P2d: does the extraction/bounding split compose for this statement?

The document's Def. 6.0.1 route needs a *total* majorizer, and no instance of that exists
(nor can one, non-degenerately, at the type level this statement needs — see
`MajorizabilityRel.lean`'s closing section).
`general_metatheorem_extract` plus `metatheorem_core_of_majorants` needs only a
`MajorizabilityRel`, which `bezemRel` provides, together with majorants for the two
extracted functionals. This checks the two halves actually fit together here. -/

section Compose


/-- The two functionals the derivation yields: `U` says where to test the premise,
`V` is the witness. Both compute. -/
def mctExtract
    {X : ι → Type} (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (prf : @Derivable ι κ F Allowed.extended Premises [] mctStatement) :=
  general_metatheorem_extract si eqxi premise_realizer rfl rfl rfl rfl prf

/-- **The bound**, from the extraction plus majorants for `U` and `V`.

**Superseded and no longer called.** `mct_bound_p1`/`mct_bound_p2` go through
`syntactic_general_metatheorem`, which produces the two majorants itself from
`all_closed_terms_majorizable` — so the `mj`, `U_star`, `V_star`, `hU`, `hV` arguments below
are all unnecessary. It is kept as the record of an early probe, written before the Dialectica
witness types became object-level, which established that the extraction/bounding split
composes — at a time when the only alternative was the total-majorizer route, which turned out
to be uninhabitable and was deleted. -/
theorem mct_bound
    {X : ι → Type} (si : SpaceInterp X F) (eqxi : EqXInterp X F si)
    (mj : MajorizabilityRel si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (prf : @Derivable ι κ F Allowed.extended Premises [] mctStatement)
    (U_star V_star : Ty.interpret X (mctTy ι →ₜ Ty.nat).hat)
    (hU : mj.maj (mctTy ι →ₜ Ty.nat) U_star
      (mctExtract si eqxi premise_realizer prf).val.1)
    (hV : mj.maj (mctTy ι →ₜ Ty.nat) V_star
      (mctExtract si eqxi premise_realizer prf).val.2) :
    ∃ Φ : Ty.interpret X (mctTy ι).hat → Nat,
      ∀ (x : Ty.interpret X (mctTy ι)) (x_star : Ty.interpret X (mctTy ι).hat),
        mj.maj (mctTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si mctB₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si mctC₀ (v, (x, ())) :=
  let e := mctExtract si eqxi premise_realizer prf
  metatheorem_core_of_majorants mj
    (fun x u => Formula.interpret si mctB₀ (u, (x, ())))
    (fun x v => Formula.interpret si mctC₀ (v, (x, ())))
    e.val.1 e.val.2 U_star V_star hU hV e.property

end Compose

end Metatheorems
