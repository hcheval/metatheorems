import Metatheorems.Metatheorem
import Metatheorems.Arithmetic

/-!
# Probe R1 — is the witness/counter type assignment coherent on the MCT corpus?

Risk R1: if `W-ty` (here: `dialecticaWitness` / `dialecticaCounter`) has a design flaw on the
formulas that actually occur — the MCT statement, its negative translation — everything
downstream is rework.

Method: hand-compute the types, then assert the hand computation against the machine by `rfl`.
Every `example` below that elaborates is one hand computation confirmed.

Ground instance: `ι = Empty` (no abstract space), so `⟦mctTy⟧ = ℕ → ℕ → ℕ`.
The MCT statement is the one from `MCTStatement.lean`, repeated here so the probe is
self-contained and disposable.
-/

namespace Metatheorems
namespace ProbeR1

open Formula

abbrev ι₀ : Type := Empty
abbrev F₀ : ι₀ → Ty ι₀ := fun e => e.elim
abbrev X₀ : ι₀ → Type := fun e => e.elim

/-- The parameter type: `a`, `g`, `K` fused into one functional. -/
abbrev mctTy : Ty ι₀ := Ty.nat →ₜ Ty.nat →ₜ Ty.nat
abbrev mctCtx : Ctx ι₀ := [Ty.nat, mctTy]

abbrev mctH : Term F₀ mctCtx mctTy := .var (.vs .vz)
abbrev mctA (n : Term F₀ mctCtx Ty.nat) : Term F₀ mctCtx Ty.nat := Term.app2 mctH (Term.ofNat 0) n
abbrev mctG (n : Term F₀ mctCtx Ty.nat) : Term F₀ mctCtx Ty.nat := Term.app2 mctH (Term.ofNat 1) n
abbrev mctK : Term F₀ mctCtx Ty.nat := Term.app2 mctH (Term.ofNat 2) (Term.ofNat 0)
abbrev mctVar : Term F₀ mctCtx Ty.nat := .var .vz

abbrev leF (x y : Term F₀ mctCtx Ty.nat) : Formula F₀ mctCtx :=
  .eq0 (Term.app2 Term.monus x y) Term.zero

/-- `a(u+1) ≤ a u  ∧  a u ≤ K` -/
abbrev mctB₀ : Formula F₀ mctCtx :=
  leF (mctA (.app .succ mctVar)) (mctA mctVar) ∧ᶠ leF (mctA mctVar) mctK

/-- `a v =₀ a (v + g v)` -/
abbrev mctC₀ : Formula F₀ mctCtx :=
  .eq0 (mctA mctVar) (mctA (Term.app2 Term.add mctVar (mctG mctVar)))

/-- `∀h (∀u B₀ → ∃v C₀)` -/
abbrev mctStatement : Formula F₀ [] :=
  .all mctTy (.all Ty.nat mctB₀ →ᶠ .ex Ty.nat mctC₀)

/-- The semantic parameter type. -/
abbrev R : Type := Nat → Nat → Nat

example : Ty.interpret X₀ mctTy = R := rfl
/-- The hat of the parameter type has the same shape — so `Φ : R → ℕ`. -/
example : Ty.interpret X₀ mctTy.hat = R := rfl

/-! ## 1. The matrices are singletons

`B₀` and `C₀` are QF and ∨-free, so their witness and counter types carry no information.
This is what makes extraction possible at all. -/

example : 𝕎 X₀ mctB₀ = (Unit × Unit) := rfl
example : ℂ X₀ mctB₀ = (Unit × Unit) := rfl
example : 𝕎 X₀ mctC₀ = Unit := rfl
example : ℂ X₀ mctC₀ = Unit := rfl

/-! ## 2. The extended-system statement

    𝕎(∀u B₀) = ℕ → 1        ℂ(∀u B₀) = ℕ × 1
    𝕎(∃v C₀) = ℕ × 1        ℂ(∃v C₀) = 1
    𝕎(P → Q) = (𝕎P → 𝕎Q) × (𝕎P → ℂQ → ℂP)
    𝕎(S)     = R → ((ℕ→1) → ℕ×1) × ((ℕ→1) → 1 → ℕ×1)

The two components of the pair are exactly the `V` and `U` that `general_metatheorem`
projects out. -/

example :
    𝕎 X₀ mctStatement
      = (R → (((Nat → Unit × Unit) → Nat × Unit) ×
              ((Nat → Unit × Unit) → Unit → Nat × (Unit × Unit)))) := rfl

example :
    ℂ X₀ mctStatement = (R × ((Nat → Unit × Unit) × Unit)) := rfl

/-! ## 3. The negatively translated statement

`NT(S) = ¬¬ nt(S)`, `nt(S) = ∀h ¬¬(∀u ¬¬B₀ → ∃v C₀)`.

Layer by layer, writing `1` for anything built only from `Unit`:

    𝕎(¬A) ≅ 𝕎A → ℂA          ℂ(¬A) ≅ 𝕎A
    ¬¬B₀ over a QF matrix stays a singleton — no blow-up at the matrix.
    P' = ∀u ¬¬B₀ :  𝕎 ≅ 1,      ℂ ≅ ℕ
    Q' = ∃v C₀   :  𝕎 ≅ ℕ,      ℂ ≅ 1
    I  = P' → Q' :  𝕎 ≅ ℕ × ℕ,  ℂ ≅ 1        (the V-part and the U-part)
    ¬¬I          :  𝕎 ≅ ℕ × ℕ,  ℂ ≅ 1
    ∀h ¬¬I       :  𝕎 ≅ R → ℕ × ℕ,   ℂ ≅ R
    NT(S)        :  𝕎 ≅ ((R → ℕ×ℕ) → R) → (R → ℕ×ℕ)

The last line is the finding: the witness for `NT(S)` is not a solution function
`R → ℕ × ℕ`.  It is a functional that yields one only when handed a *challenge*
`(R → ℕ×ℕ) → R` — a Herbrand-style counterexample selector, one exponential above `Ψ`. -/

abbrev ntS : Formula F₀ [] := mctStatement.negTrans

/-- The literal machine type, `Unit`s and all.  Read off the definitions, asserted by `rfl`.
Abbreviations used below to keep it legible:
  `WB := Unit × Unit`      the (singleton) witness/counter type of `B₀`
  `WnB := (WB → Unit) × (WB → Unit → WB)`    witness of `¬B₀`
  `WnnB := (WnB → Unit) × (WnB → Unit → WB × Unit)`  witness of `¬¬B₀` -/
abbrev WB : Type := Unit × Unit
abbrev WnB : Type := (WB → Unit) × (WB → Unit → WB)
abbrev CnB : Type := WB × Unit
abbrev WnnB : Type := (WnB → Unit) × (WnB → Unit → CnB)
abbrev CnnB : Type := WnB × Unit

/-- `P' = ∀u ¬¬B₀` -/
example : 𝕎 X₀ (Formula.all Ty.nat mctB₀).kurodaInner = (Nat → WnnB) := rfl
example : ℂ X₀ (Formula.all Ty.nat mctB₀).kurodaInner = (Nat × CnnB) := rfl

/-- `Q' = ∃v C₀` — the negative translation leaves it alone. -/
example : (Formula.ex Ty.nat mctC₀).kurodaInner = Formula.ex Ty.nat mctC₀ := rfl

/-- `I = P' → Q'`: the witness is (V-part, U-part), as at the extended level. -/
abbrev WI : Type := ((Nat → WnnB) → Nat × Unit) × ((Nat → WnnB) → Unit → Nat × CnnB)
abbrev CI : Type := (Nat → WnnB) × Unit

example :
    𝕎 X₀ ((Formula.all Ty.nat mctB₀ →ᶠ Formula.ex Ty.nat mctC₀).kurodaInner) = WI := rfl
example :
    ℂ X₀ ((Formula.all Ty.nat mctB₀ →ᶠ Formula.ex Ty.nat mctC₀).kurodaInner) = CI := rfl

/-- `¬¬I` — the doubled negation around the implication. -/
abbrev WnI : Type := (WI → Unit) × (WI → Unit → CI)
abbrev CnI : Type := WI × Unit
abbrev WnnI : Type := (WnI → Unit) × (WnI → Unit → CnI)
abbrev CnnI : Type := WnI × Unit

/-- `nt(S) = ∀h ¬¬I`. -/
abbrev Wnt : Type := R → WnnI
abbrev Cnt : Type := R × CnnI

example : 𝕎 X₀ mctStatement.kurodaInner = Wnt := rfl
example : ℂ X₀ mctStatement.kurodaInner = Cnt := rfl

/-- **The R1 result for the classical route.**  `𝕎(NT(S))` is a functional taking a
challenge `Wnt → Cnt` — not a solution `Wnt`. -/
example :
    𝕎 X₀ ntS = ((((Wnt → Unit) × (Wnt → Unit → Cnt)) → Unit) ×
                (((Wnt → Unit) × (Wnt → Unit → Cnt)) → Unit → Wnt × Unit)) := rfl

example :
    ℂ X₀ ntS = ((((Wnt → Unit) × (Wnt → Unit → Cnt))) × Unit) := rfl

/-! ## 4. What the extraction in `general_metatheorem_classical` actually does

It builds `ki_w := (w.2 (default 𝕎(¬nt(S))) ()).1 : Wnt` — i.e. it supplies the *default*
challenge.  The soundness property of `w` then only says the resulting `Wnt` answers that
one junk challenge.  The junk challenge's `Wnt → Cnt` component picks a *fixed* `h`
(`Ty.interpret_default`), not the `h` the theorem is being proved for.

So the `sorry` at `Metatheorem.lean:340` is not a missing lemma; it is a place where the
proof needs a challenge depending on `x`, and none is available from `dialecticaDefaultWitness`.
-/

/-- The default challenge really does ignore its argument: it is `fun _ => (default h, …)`. -/
example (si : SpaceInterp X₀ F₀) (f : Wnt) :
    ((dialecticaDefaultWitness si (¬ᶠ mctStatement.kurodaInner)).2 f ()).1
      = Ty.interpret_default si mctTy := rfl

end ProbeR1
end Metatheorems
