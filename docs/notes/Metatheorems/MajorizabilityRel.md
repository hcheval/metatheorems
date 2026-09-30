# MajorizabilityRel.lean

## module header

**Nothing here mentions `Term`** — that is the boundary against
`Majorizability.lean`, which holds the recursion over terms (`termMajorizer`,
`all_terms_majorizable`, `closedMajorizer`) and the per-constant data
(`AbstractMajorizability`, `ConstMajorants`). This file is what that one is stated in
terms of; it imports `Semantics` and nothing else.

### History, at the bottom of this file

The file was `StrongMajorizability.lean` and held a `Majorizability` structure — the
total majorizer of the document's Def. 6.0.1, which is **uninhabitable**. Both the name and
the structure are gone; the closing section records why, since the argument is a finding
about that presentation and is worth more than the dead code was.

## `MajorizabilityRel`

This is everything `metatheorem_core_of_majorants` needs apart from the majorants
themselves, and unlike `Majorizability` at the bottom of this file it is inhabited — see
`bezemRel`. Conditions 1–2 of the document's Def. 6.0.1.

## `hatMaj`

Both arguments live in `Ty.interpret X ρ.hat`, which is legitimate because `Ty.hat` is
idempotent (`Ty.hat_idempotent`) — the "star side" of `≽ᵃ_ρ̂` is `ρ̂̂ = ρ̂`. Indexing by `ρ`
rather than by `ρ̂` is what keeps the definition **cast-free**: `ρ̂.hat = ρ̂` is a propositional
equality, not a definitional one, so a literal `bezemMaj base ρ.hat` would need a transport
at every use.

## `bezemMaj`

**Two clauses, not one** — it carried only the first conjunct (Howard majorizability) at
first. The self-majorization clause is what makes `bezem_prec_maj` provable:
the document's induction (`.tex:82–96`) gives `R n y* z* ≽ R n y z` at *equal* `n`, while
`maj` at `nat →ₜ ρ` demands `n* ≥ n → …`, and the bridge is `hatMaj_of_bezemMaj` plus
`bezemMaj_of_hatMaj`.

## `bezemRel`

`bezemMaj` satisfies the two properties the metatheorem uses. Both come from the *first*
conjunct, which is why the widening left the vestigial `general_metatheorem` untouched.

## `maxT_comm`

Promoted here from `Probes/MonotoneSpike.lean`.

## Removed: `Majorizability`, the total majorizer (the file's closing section)

A `Majorizability` structure used to sit here — `MajorizabilityRel` extended with

    majorizer     : {ρ : Ty ι} → Ty.interpret X ρ → Ty.interpret X ρ.hat
    majorizer_maj : ∀ {ρ} (x : Ty.interpret X ρ), maj ρ (majorizer x) x

the faithful transcription of the reference document's Def. 6.0.1, matching the Lean 3
formalization. It was deleted along with its only consumers — `metatheorem_core`,
`general_metatheorem`, `general_metatheorem_classical` (`MetatheoremPrereqs.lean`) and the shape
probe in `MCTStatement.lean`. **The reason is recorded here rather than in code, because it
is a finding about that presentation and the code could never do anything.**

**It has no instances and cannot have any.** `majorizer` quantifies over
`Ty.interpret X ρ`, the *full set-theoretic* type structure — uncountable, containing
non-definable functionals. At `(nat →ₜ nat) →ₜ nat` take `f* = id`; the `f` that `f*`
majorizes then range over all `f` with `f n ≤ n`, and on that set

    Φ f := the least n ≥ 1 with f n = 0, else 0

is unbounded, witnessed by `fₖ n := if n = k then 0 else n`. So no single `Φ*` majorizes
`Φ`. Degenerate choices (`maj := Eq` where `ρ.hat = ρ`) do satisfy the field, but then the
bound depends on `x` itself and carries no uniformity — which is the entire point of a
metatheorem. Turning this argument into a `no_total_majorizer` theorem is about 30 lines and
has not been done.

**This is not a defect of the semantic route as such, and that contrast is the resolution.**
`all_terms_majorizable` quantifies over `Term F Γ ρ` — countable syntax, every element
definable — and goes through. Its docstring writes this out. The monotone functional
interpretation reaches the same place a third way: it carries no witness at all, only a
majorant with its condition.

**What replaced it.** The Dialectica witness/counter *types* are object-level `Ty ι`, so
realizers are closed `Term`s and
`all_closed_terms_majorizable` produces their majorants outright. That needs only
`AbstractMajorizability` (inhabited by `bezemAbstract`) and no total majorizer at all. The
live entry points are `syntactic_general_metatheorem{,_classical,_at,_gen}` and the MFI
`monotone_general_metatheorem{_at,_classical_at}`; every bound in the project comes through
`MajorizabilityRel` plus explicit majorants, via `metatheorem_core_of_majorants_at`.
