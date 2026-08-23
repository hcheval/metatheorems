import Metatheorems.Arithmetic
import Metatheorems.Metatheorem

/-!
# Probe P2: is the ℕ-level MCT statement expressible in the shape `general_metatheorem` wants?

`general_metatheorem` consumes a derivation of

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

variable {ι : Type} {F : ι → Ty ι}

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

/-- **The full statement**, in exactly the shape `general_metatheorem` consumes. -/
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

/-! ## Does it actually fit `general_metatheorem`?

If this elaborates, the shape is right: the only remaining input is the derivation. -/

example
    {X : ι → Type} (si : SpaceInterp X F)
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    (mj : Majorizability si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (prf : @Derivable ι F EqX Allowed.extended Premises [] mctStatement) :
    { Φ : Ty.interpret X (mctTy ι).hat → Nat //
      ∀ (x : Ty.interpret X (mctTy ι)) (x_star : Ty.interpret X (mctTy ι).hat),
        mj.maj (mctTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si mctB₀ (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si mctC₀ (v, (x, ())) } :=
  general_metatheorem si eqxi mj premise_realizer rfl rfl rfl rfl prf


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

variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    {al : Allowed} {Premises : PremiseSet F}

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
    Derivable F EqX al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        .eq0 (Term.app2 Term.monus (mctA1 (.app .succ t)) (mctA1 t)) Term.zero) :=
  .syllogism (.forall_ax t) .and_weak

/-- **P2b-ii.** … and boundedness. -/
def mct_bounded (t : Term F (mctCtx1 ι) Ty.nat) :
    Derivable F EqX al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        .eq0 (Term.app2 Term.monus (mctA1 t) mctK1) Term.zero) :=
  .syllogism (.forall_ax t) and_proj2

/-- **P2b-iii.** ∃-introduction at a witness `t`: the goal the derivation must eventually hit. -/
def mct_ex_intro (t : Term F (mctCtx1 ι) Ty.nat) :
    Derivable F EqX al Premises
      (Formula.eq0 (mctA1 t) (mctA1 (Term.app2 Term.add t (mctG1 t)))
        →ᶠ Formula.ex Ty.nat mctC₀) :=
  .exist_ax t mctC₀

/-- **P2b-iv.** The ∀-introduction that closes the outer binder, given the body.
`B := ⊥ᶠ →ᶠ ⊥ᶠ` is the "no hypothesis yet" placeholder; `mp` discharges it. -/
def mct_close
    (body : Derivable F EqX al Premises
      (Formula.weakenBy (mctTy ι) (⊥ᶠ →ᶠ ⊥ᶠ) →ᶠ
        (Formula.all Ty.nat mctB₀ →ᶠ Formula.ex Ty.nat mctC₀))) :
    Derivable F EqX al Premises (mctStatement (ι := ι) (F := F)) :=
  .mp I_comb (.forall_rule body)

/-! ### The step that consumes the induction hypothesis

The IH gives `H →ᶠ ex nat C`. To use the witness while keeping `H` available, the hypothesis
has to be pushed under the existential first. That lemma is not in `PureFOLLemmas`. -/

def ex_and_left {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)} {B : Formula F Γ} :
    Derivable F EqX al Premises
      (Formula.ex ρ A ∧ᶠ B →ᶠ Formula.ex ρ (A ∧ᶠ Formula.weakenBy ρ B)) :=
  -- Under the binder, re-introduce the existential at the bound variable itself.
  have key : Derivable F EqX al Premises
      ((A ∧ᶠ Formula.weakenBy ρ B) →ᶠ
        Formula.weakenBy ρ (Formula.ex ρ (A ∧ᶠ Formula.weakenBy ρ B))) := by
    have h := Derivable.exist_ax (F := F) (EqX := EqX) (allowed := al) (Premises := Premises)
      (Term.var .vz)
      (Formula.renameF (Term.Renaming.ext Term.Renaming.shift) (A ∧ᶠ Formula.weakenBy ρ B))
    simp only [Formula.subst0] at h
    rwa [Formula.substF_renameF_id _ _ (fun {_} v => by cases v <;> rfl)] at h
  .importation (.exist_rule (.exportation key))

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
    (base : Derivable F EqX al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        Formula.all Ty.nat
          (leAt (aAt (.var (.vs .vz)) (.var .vz)) Term.zero →ᶠ flatEx (.var (.vs .vz)))))
    (step : Derivable F EqX al Premises
      (Formula.all Ty.nat (mctIndF →ᶠ
        (Formula.weakenBy Ty.nat (Formula.all Ty.nat mctB₀) →ᶠ
          Formula.all Ty.nat
            (leAt (aAt (.var (.vs (.vs .vz))) (.var .vz)) (.app .succ (.var (.vs .vz)))
              →ᶠ flatEx (.var (.vs (.vs .vz)))))))) :
    Derivable F EqX al Premises (Formula.all Ty.nat (mctIndF (ι := ι) (F := F))) :=
  .induction base step

/-- **P2c-iv.** Instantiating the induction at `k := K` gives the goal the outer proof needs.
`K` is a term over the parameter, not a numeral, so this exercises `subst0` at a compound term. -/
def mctInstK
    (h : Derivable F EqX al Premises (Formula.all Ty.nat (mctIndF (ι := ι) (F := F)))) :
    Derivable F EqX al Premises
      (Formula.all Ty.nat mctB₀ →ᶠ
        Formula.all Ty.nat
          (leAt (aAt (.var (.vs .vz)) (.var .vz))
                (Term.app2 (.var (.vs .vz)) (Term.ofNat 2) (Term.ofNat 0))
            →ᶠ flatEx (.var (.vs .vz)))) :=
  .mp h (.forall_ax (Term.app2 (.var .vz) (Term.ofNat 2) (Term.ofNat 0)))

end Depth

end Plumbing

/-! ## Probe P2d: does the extraction/bounding split compose for this statement?

`general_metatheorem` needs a `Majorizability` — a *total* majorizer — and no instance of
that exists (nor can one, non-degenerately, at the type level this statement needs).
`general_metatheorem_extract` plus `metatheorem_core_of_majorants` needs only a
`MajorizabilityRel`, which `bezemRel` provides, together with majorants for the two
extracted functionals. This checks the two halves actually fit together here. -/

section Compose

variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}

/-- The two functionals the derivation yields: `U` says where to test the premise,
`V` is the witness. Both compute. -/
def mctExtract
    {X : ι → Type} (si : SpaceInterp X F) (eqxi : EqXInterp X F si EqX)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (prf : @Derivable ι F EqX Allowed.extended Premises [] mctStatement) :=
  general_metatheorem_extract si eqxi premise_realizer rfl rfl rfl rfl prf

/-- **The bound**, from the extraction plus majorants for `U` and `V`. -/
theorem mct_bound
    {X : ι → Type} (si : SpaceInterp X F) (eqxi : EqXInterp X F si EqX)
    (mj : MajorizabilityRel si)
    {Premises : PremiseSet F}
    (premise_realizer : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ →
      ∀ env : Ctx.interpret X Γ', dialecticaRealizerCtx si B env)
    (prf : @Derivable ι F EqX Allowed.extended Premises [] mctStatement)
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
