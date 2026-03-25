# Proof Rules for WE-HA^{ω,X}

This file documents the Hilbert-style proof system defined in
`Metatheorems/Derivable.lean`. It is intended as a reference for writing
Lean 4 proofs that produce terms of type `Derivable F EqX φ`.

---

## The Derivable Type

```lean
inductive Derivable {ι : Type} (F : ι → Ty ι)
    (EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ) :
    {Γ : Ctx ι} → Formula F Γ → Type
```

- **`Derivable F EqX φ`** is a `Type` (not `Prop`) — large elimination is allowed.
- Constructors of `Derivable` are exactly the axioms and rules.
- Use **term-mode** proofs wherever possible (e.g., `.syllogism .and_contract .and_weak`).
- Use `by exact ...` or `by apply ...` only when needed for unification.
- **Never** use `by induction h with` on a `Derivable` value — the code generator
  does not support it. Use `match h with` instead.

---

## Notations

```
⊥ᶠ           Formula.bot
A ∧ᶠ B       Formula.and A B      (infixl, precedence 35)
A ∨ᶠ B       Formula.or  A B      (infixl, precedence 30)
A →ᶠ B       Formula.imp A B      (infixr, precedence 25)
¬ᶠA          Formula.neg A  =  A →ᶠ ⊥ᶠ     (prefix, precedence 40)
A ↔ᶠ B       (A →ᶠ B) ∧ᶠ (B →ᶠ A)
```

**Precedence warning**: `¬ᶠ` binds tighter than `→ᶠ` but looser than `=`.
Write `(¬ᶠ¬ᶠA) = (¬ᶠ¬ᶠB)` not `¬ᶠ¬ᶠA = ¬ᶠ¬ᶠB` (the latter means `¬ᶠ(¬ᶠ(A = B))`).

---

## Propositional Axioms (§9.1)

All are nullary constructors; Lean infers `A`, `B`, `C` from context.

| Constructor | Type | Meaning |
|---|---|---|
| `.or_contract` | `A ∨ᶠ A →ᶠ A` | ∨-contraction |
| `.and_contract` | `A →ᶠ A ∧ᶠ A` | ∧-contraction |
| `.or_weak` | `A →ᶠ A ∨ᶠ B` | ∨-weakening |
| `.and_weak` | `A ∧ᶠ B →ᶠ A` | ∧-weakening (left projection) |
| `.or_perm` | `A ∨ᶠ B →ᶠ B ∨ᶠ A` | ∨-permutation |
| `.and_perm` | `A ∧ᶠ B →ᶠ B ∧ᶠ A` | ∧-permutation |
| `.exfalso` | `⊥ᶠ →ᶠ A` | ex falso quodlibet |

Note: `and_weak` gives the **left** component. For the right component, use
`.syllogism .and_perm .and_weak` (permute first, then project).

---

## Quantifier Axioms (§9.1)

```lean
-- Universal instantiation: ∀x.A → A[t/x]
.forall_ax (t : Term F Γ ρ) : Derivable F EqX (Formula.all ρ A →ᶠ A.subst0 t)

-- Existential introduction: A[t/x] → ∃x.A
.exist_ax (t : Term F Γ ρ) (A : Formula F (ρ :: Γ)) :
    Derivable F EqX (A.subst0 t →ᶠ Formula.ex ρ A)
```

---

## Rules (§9.2)

```lean
-- Modus ponens: from ⊢ A and ⊢ A → B, derive ⊢ B
.mp (ha : Derivable F EqX A) (hab : Derivable F EqX (A →ᶠ B)) : Derivable F EqX B

-- Syllogism (→-transitivity): from ⊢ A → B and ⊢ B → C, derive ⊢ A → C
.syllogism (hab : Derivable F EqX (A →ᶠ B)) (hbc : Derivable F EqX (B →ᶠ C)) :
    Derivable F EqX (A →ᶠ C)

-- Exportation: from ⊢ A ∧ B → C, derive ⊢ A → B → C
.exportation (h : Derivable F EqX (A ∧ᶠ B →ᶠ C)) : Derivable F EqX (A →ᶠ B →ᶠ C)

-- Importation: from ⊢ A → B → C, derive ⊢ A ∧ B → C
.importation (h : Derivable F EqX (A →ᶠ B →ᶠ C)) : Derivable F EqX (A ∧ᶠ B →ᶠ C)

-- Expansion: from ⊢ A → B, derive ⊢ C ∨ A → C ∨ B
.expansion (h : Derivable F EqX (A →ᶠ B)) : Derivable F EqX (C ∨ᶠ A →ᶠ C ∨ᶠ B)

-- ∀-rule: from ⊢ B.weakenBy ρ → A (where x:ρ is not free in B),
--         derive ⊢ B → ∀x.A
.forall_rule (h : Derivable F EqX (B.weakenBy ρ →ᶠ A)) :
    Derivable F EqX (B →ᶠ Formula.all ρ A)

-- ∃-rule: from ⊢ A → B.weakenBy ρ (where x:ρ is not free in B),
--         derive ⊢ ∃x.A → B
.exist_rule (h : Derivable F EqX (A →ᶠ B.weakenBy ρ)) :
    Derivable F EqX (Formula.ex ρ A →ᶠ B)

-- Universal generalization: from ⊢ A, derive ⊢ ∀x. A.weakenBy ρ
.univ_gen (h : Derivable F EqX A) :
    Derivable F EqX (Formula.all ρ (A.weakenBy ρ))
```

---

## Arithmetic Axioms (§9.5–9.8)

```lean
-- Successor ≠ 0: ∀n. S(n) =₀ 0 → ⊥
.succ_ne_zero : Derivable F EqX
    (Formula.all Ty.nat (Formula.eq0 (Term.app Term.succ (.var .vz)) Term.zero →ᶠ ⊥ᶠ))

-- Successor injectivity: ∀m n. S(m) =₀ S(n) → m =₀ n
.succ_inj : Derivable F EqX
    (Formula.all Ty.nat (Formula.all Ty.nat (
      Formula.eq0 (Term.app Term.succ (.var (.vs .vz)))
                  (Term.app Term.succ (.var .vz))
      →ᶠ Formula.eq0 (.var (.vs .vz)) (.var .vz))))

-- Equality reflexivity: s =₀ s
.refl0 : Derivable F EqX (Formula.eq0 t t)

-- Equality symmetry: s =₀ t → t =₀ s
.sym0 : Derivable F EqX (Formula.eq0 s t →ᶠ Formula.eq0 t s)

-- Equality transitivity: s =₀ t ∧ t =₀ u → s =₀ u
.trans0 : Derivable F EqX (Formula.eq0 s t ∧ᶠ Formula.eq0 t u →ᶠ Formula.eq0 s u)
```

---

## Combinator and Recursor Axioms (§9.6)

```lean
-- Π (proj): Π_{ρ,τ} s t =_ρ s
.proj_ax : Derivable F EqX (eqAtType EqX ρ (Term.app2 (Term.proj ρ τ) s t) s)

-- Σ (comb): Σ_{δ,ρ,τ} f g x =_τ f x (g x)
.comb_ax : Derivable F EqX
    (eqAtType EqX τ (Term.app3 (Term.comb δ ρ τ) f g x)
                    (Term.app (Term.app f x) (Term.app g x)))

-- Recursor base: R_ρ y z 0 =_ρ y
.rec_zero : Derivable F EqX
    (eqAtType EqX ρ (Term.app3 (Term.prec ρ) y z Term.zero) y)

-- Recursor step: R_ρ y z (S x) =_ρ z (R_ρ y z x) x
.rec_succ : Derivable F EqX
    (eqAtType EqX ρ (Term.app3 (Term.prec ρ) y z (Term.app Term.succ x))
                    (Term.app2 z (Term.app3 (Term.prec ρ) y z x) x))
```

---

## QF-ER Rule (§9.7)

```lean
-- If A₀ is QF and ∨-free, and ⊢ A₀ → s =_ρ t,
-- then ⊢ A₀ → r[s/x] =_σ r[t/x]   for any r : Term F (ρ :: Γ) σ
.qfer (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
      (h : Derivable F EqX (A₀ →ᶠ eqAtType EqX ρ s t)) :
    Derivable F EqX (A₀ →ᶠ eqAtType EqX σ (Term.subst0 r s) (Term.subst0 r t))
```

---

## Induction (§9.8)

```lean
-- From ⊢ A[0/x] and ⊢ ∀x. A → A[S(x)/x], derive ⊢ ∀x. A
.induction
    (h_zero : Derivable F EqX (A.subst0 Term.zero))
    (h_step : Derivable F EqX (Formula.all Ty.nat
                (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz))))) :
    Derivable F EqX (Formula.all Ty.nat A)
```

---

## Already-Proved Building Blocks (in NegTrans.lean)

These are `private` helpers, but their proofs serve as examples:

```lean
-- A → A
self_imp : Derivable F EqX (A →ᶠ A)
  := .syllogism .and_contract .and_weak

-- ⊢ A  implies  ⊢ B → A
weaken_intro (h : Derivable F EqX A) : Derivable F EqX (B →ᶠ A)
  := .mp h (.exportation .and_weak)

-- A → B → A ∧ B
and_intro : Derivable F EqX (A →ᶠ B →ᶠ A ∧ᶠ B)
  := .exportation self_imp
```

---

## Key Derived Patterns

These are not axioms but standard derivable facts. Useful for sketching proofs:

**Modus ponens in hypothetical context** (`A, A → B ⊢ B`):
- Have `ha : Derivable F EqX A` and `hab : Derivable F EqX (A →ᶠ B)`
- Produce: `.mp ha hab`

**Right ∧-projection** (`A ∧ B → B`):
- `.syllogism .and_perm .and_weak`

**Hypothetical syllogism chain** (`A → B`, `B → C`, `C → D` gives `A → D`):
- `.syllogism (.syllogism h1 h2) h3`

**Introduce double negation** (`A → ¬¬A`):
- Informal: given `a : A` and `na : ¬A = A →ᶠ ⊥ᶠ`, apply `na` to `a`
- In Hilbert system: `.importation` of `A ∧ ¬A → ⊥`:
  the latter is `A ∧ (A →ᶠ ⊥ᶠ) → ⊥`, i.e., apply the second component to the first

**Contrapositive** (`A → B` gives `¬B → ¬A`):
- `¬B → ¬A` is `(B →ᶠ ⊥ᶠ) →ᶠ (A →ᶠ ⊥ᶠ)`
- Derivation: `.importation (.syllogism .and_perm (.importation (.syllogism h .and_weak)))`
  where `h : Derivable (A →ᶠ B)`

---

## Common Proof Strategies

### To prove `⊢ P →ᶠ Q`:
Use `.exportation`, `.forall_rule`, `.syllogism`, or `.mp` with an axiom.

### To prove `⊢ ¬ᶠP` (i.e., `P →ᶠ ⊥ᶠ`):
This is an implication; use the rules for `→ᶠ`.

### To prove `⊢ ¬ᶠ¬ᶠP`:
Expand to `(P →ᶠ ⊥ᶠ) →ᶠ ⊥ᶠ`. Usually proved via `dnn_intro` (once available):
`dnn_intro : Derivable F EqX (A →ᶠ ¬ᶠ¬ᶠA)`.

### To prove `⊢ ∀x. φ(x)`:
Use `.induction` (if arithmetic) or `.forall_rule` + `.univ_gen`.

### To eliminate `¬ᶠ¬ᶠ` from a hypothesis:
Not possible in intuitionistic logic in general. Use Markov's principle
(`DerivableExt.markov`) if the formula is QF ∨-free.

---

## Extended System (DerivableExt)

```lean
inductive DerivableExt F EqX : {Γ : Ctx ι} → Formula F Γ → Type where
  | base   : Derivable F EqX A → DerivableExt F EqX A
  | markov : A₀.isQF = true → A₀.isVFree = true →
             DerivableExt F EqX (¬ᶠ(¬ᶠ(Formula.ex ρ A₀)) →ᶠ Formula.ex ρ A₀)
  | ip     : A₀.isQF = true → A₀.isVFree = true →
             DerivableExt F EqX
               ((Formula.all σ A₀ →ᶠ Formula.ex ρ B) →ᶠ
                Formula.ex ρ ((Formula.all σ A₀).weakenBy ρ →ᶠ B))
  | ac     : DerivableExt F EqX
               ((Formula.all ρ (Formula.ex τ A)) →ᶠ
                Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A)))
  | mp     : DerivableExt F EqX A → DerivableExt F EqX (A →ᶠ B) → DerivableExt F EqX B
```

To lift a `Derivable` proof to `DerivableExt`, wrap it in `.base`.

---

## Classical System (DerivableClass)

```lean
inductive DerivableClass F EqX : {Γ : Ctx ι} → Formula F Γ → Type where
  | base  : Derivable F EqX A → DerivableClass F EqX A
  | lem   : DerivableClass F EqX (A ∨ᶠ ¬ᶠA)
  | qf_ac : DerivableClass F EqX
              ((Formula.all ρ (Formula.ex τ A)) →ᶠ
               Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A)))
  | mp    : DerivableClass F EqX A → DerivableClass F EqX (A →ᶠ B) → DerivableClass F EqX B
```

---

## Tips for Agents

1. **Term mode is preferred**: Write `.syllogism .and_contract .and_weak` not `by exact ...`.
2. **Lean infers `A`, `B`, `C`**: Don't supply them unless unification fails. If needed,
   use named argument syntax: `.and_weak (A := foo) (B := bar)`.
3. **Expand negation**: `¬ᶠA` is definitionally `A →ᶠ ⊥ᶠ`. When stuck, `show` the
   expanded form: `show Derivable F EqX (A →ᶠ ⊥ᶠ)`.
4. **`and_weak` gives the left conjunct**. For the right, prepend `.syllogism .and_perm`.
5. **`mp` argument order**: `.mp ha hab` where `ha : ⊢ A` and `hab : ⊢ A → B`.
6. **`syllogism` argument order**: `.syllogism h_AB h_BC` where `h_AB : ⊢ A → B`.
7. **`importation`/`exportation` pair**: use to move between `A ∧ B → C` and `A → B → C`.
8. **Sketch first in natural deduction**, then translate to Hilbert combinators.
   Each ND rule has a standard Hilbert encoding.
