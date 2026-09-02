/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Derivable


namespace Metatheorems

/-!
# Propositional Lemmas for WE-HA^{ω,X}

A comprehensive library of derived propositional rules, organized in tiers:

  Tier 1 — Implication combinators (K, S, flip, contract, mp_form)
  Tier 2 — Conjunction
  Tier 3 — Disjunction
  Tier 4 — Negation and double negation

These lemmas form the infrastructure needed for the negative translation
and other metatheorems. They are all provable in the base intuitionistic
system `Derivable` (no LEM, Markov, or AC required).
-/

open Formula

section PropositionalLemmas

variable {ι : Type} {F : ι → Ty ι}
    {a : Allowed} {Premises : PremiseSet F} {Γ : Ctx ι} {A B C D : Formula F Γ}

/-- Meta-level pairing: from `H→X` and `H→Y`, derive `H→X∧Y`. -/
def pair_h {H X Y : Formula F Γ}
    (f : Derivable F a Premises (H →ᶠ X)) (g : Derivable F a Premises (H →ᶠ Y)) :
    Derivable F a Premises (H →ᶠ X ∧ᶠ Y) :=
  -- and_intro[Y,H] : Y → H → Y∧H; syllogism g: H → H → Y∧H; import: H∧H→Y∧H
  -- and_contract: H→H∧H; compose: H→Y∧H; and_perm: H→H∧Y
  -- and_intro[X,Y] : X → Y → X∧Y; syllogism f: H → Y → X∧Y; import: H∧Y→X∧Y
  -- compose: H→X∧Y
  let and_intro_YH : Derivable F a Premises (Y →ᶠ H →ᶠ Y ∧ᶠ H) :=
    .exportation (.syllogism .and_contract .and_weak)
  let and_intro_XY : Derivable F a Premises (X →ᶠ Y →ᶠ X ∧ᶠ Y) :=
    .exportation (.syllogism .and_contract .and_weak)
  let s1 := .syllogism g and_intro_YH
  let s2 := Derivable.importation s1
  let s3 := Derivable.syllogism .and_contract s2
  let s4 := Derivable.syllogism s3 .and_perm
  let s5 := .syllogism f and_intro_XY
  let s6 := Derivable.importation s5
  Derivable.syllogism s4 s6

/-- Meta-level eval: from `H→(A→B)` and `H→A`, derive `H→B`. -/
def eval_h {H : Formula F Γ}
    (f : Derivable F a Premises (H →ᶠ (A →ᶠ B))) (x : Derivable F a Premises (H →ᶠ A)) :
    Derivable F a Premises (H →ᶠ B) :=
  -- importation(I_comb at A→B) : (A→B)∧A → B
  let eval_AB : Derivable F a Premises ((A →ᶠ B) ∧ᶠ A →ᶠ B) :=
    .importation (.syllogism .and_contract .and_weak)
  .syllogism (pair_h f x) eval_AB

-- ============================================================================
-- Tier 1 — Implication combinators
-- ============================================================================

/-- Identity: `A → A`. -/
def I_comb : Derivable F a Premises (A →ᶠ A) :=
  .syllogism .and_contract .and_weak

/-- K-combinator: `A → B → A`. -/
def K_comb : Derivable F a Premises (A →ᶠ B →ᶠ A) :=
  .exportation .and_weak

/-- S-combinator: `(A → B → C) → (A → B) → A → C`. -/
def S_comb : Derivable F a Premises ((A →ᶠ B →ᶠ C) →ᶠ (A →ᶠ B) →ᶠ A →ᶠ C) :=
  let get_f : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) ∧ᶠ A →ᶠ A →ᶠ B →ᶠ C) := .syllogism .and_weak .and_weak
  let get_g : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) ∧ᶠ A →ᶠ A →ᶠ B) := .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let get_a : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ (A →ᶠ B) ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let get_b := eval_h get_g get_a
  let get_bc := eval_h get_f get_a
  let get_c := eval_h get_bc get_b
  Derivable.exportation (Derivable.exportation get_c)

/-- Flip / commutativity of premises: `(A → B → C) → B → A → C`. -/
def flip_comb : Derivable F a Premises ((A →ᶠ B →ᶠ C) →ᶠ B →ᶠ A →ᶠ C) :=
  let get_f : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ B ∧ᶠ A →ᶠ A →ᶠ B →ᶠ C) := .syllogism .and_weak .and_weak
  let get_b : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ B ∧ᶠ A →ᶠ B) := .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let get_a : Derivable F a Premises ((A →ᶠ B →ᶠ C) ∧ᶠ B ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let get_bc := eval_h get_f get_a
  let get_c := eval_h get_bc get_b
  Derivable.exportation (Derivable.exportation get_c)

/-- Contraction / W-combinator: `(A → A → B) → A → B`.

Derivation (C abbreviates `(A →ᶠ A →ᶠ B) ∧ᶠ A`):
| #  | Formula                   | Justification                       |
|----|---------------------------|-------------------------------------|
| 1  | (A→A→B) → (A→A→B)        | I_comb at A→A→B                     |
| 2  | (A→A→B)∧A → (A→B)        | importation 1                       |
| 3  | C∧A → B                   | importation 2                       |
| 4  | C → A                     | syllogism and_perm and_weak         |
| 5  | A∧C → A∧C                 | I_comb at A∧C                       |
| 6  | A → C → A∧C               | exportation 5                       |
| 7  | C → C → A∧C               | syllogism 4 6                       |
| 8  | C∧C → A∧C                 | importation 7                       |
| 9  | C∧C → C∧A                 | syllogism 8 and_perm                |
| 10 | C → C∧C                   | and_contract                        |
| 11 | C → C∧A                   | syllogism 10 9                      |
| 12 | C → B                     | syllogism 11 3                      |
| 13 | (A→A→B) → A → B           | exportation 12                      |
-/
def contract : Derivable F a Premises ((A →ᶠ A →ᶠ B) →ᶠ A →ᶠ B) :=
  let h1 := @I_comb ι F a Premises Γ (A →ᶠ A →ᶠ B)
  let h2 := Derivable.importation h1
  let h3 := Derivable.importation h2
  let h4 : Derivable F a Premises ((A →ᶠ A →ᶠ B) ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let h5 := @I_comb ι F a Premises Γ (A ∧ᶠ ((A →ᶠ A →ᶠ B) ∧ᶠ A))
  let h6 := Derivable.exportation h5
  let h7 := Derivable.syllogism h4 h6
  let h8 := Derivable.importation h7
  let h9 := Derivable.syllogism h8 .and_perm
  let h10 : Derivable F a Premises ((A →ᶠ A →ᶠ B) ∧ᶠ A →ᶠ
      ((A →ᶠ A →ᶠ B) ∧ᶠ A) ∧ᶠ ((A →ᶠ A →ᶠ B) ∧ᶠ A)) := .and_contract
  let h11 := Derivable.syllogism h10 h9
  let h12 := Derivable.syllogism h11 h3
  Derivable.exportation h12

/-- MP as a formula: `(A → B) → A → B`.
    (Function application; the `→` of the formula language IS application.) -/
def mp_form : Derivable F a Premises ((A →ᶠ B) →ᶠ A →ᶠ B) :=
  I_comb

-- ============================================================================
-- Tier 2 — Conjunction
-- ============================================================================

/-- Conjunction introduction: `A → B → A ∧ B`. -/
def and_intro : Derivable F a Premises (A →ᶠ B →ᶠ A ∧ᶠ B) :=
  .exportation I_comb

/-- Left projection: `A ∧ B → A`. -/
def and_proj1 : Derivable F a Premises (A ∧ᶠ B →ᶠ A) :=
  .and_weak

/-- Right projection: `A ∧ B → B`. -/
def and_proj2 : Derivable F a Premises (A ∧ᶠ B →ᶠ B) :=
  .syllogism .and_perm .and_weak

/-- Left associativity: `A ∧ (B ∧ C) → (A ∧ B) ∧ C`.

Pairing trick: to build `H → X∧Y` from `H→X` and `H→Y`:
  1. syllogism(H→Y)(and_intro[Y,H]) : H → H → Y∧H
  2. importation → H∧H → Y∧H; compose with and_contract: H → Y∧H
  3. and_perm → H → H∧Y
  4. syllogism(H→X)(and_intro[X,Y]) : H → Y → X∧Y; importation → H∧Y → X∧Y
  5. compose 3 and 4: H → X∧Y
-/
def and_assocl : Derivable F a Premises (A ∧ᶠ (B ∧ᶠ C) →ᶠ (A ∧ᶠ B) ∧ᶠ C) :=
  let get_B : Derivable F a Premises (A ∧ᶠ (B ∧ᶠ C) →ᶠ B) := .syllogism and_proj2 .and_weak
  let get_C : Derivable F a Premises (A ∧ᶠ (B ∧ᶠ C) →ᶠ C) := .syllogism and_proj2 and_proj2
  -- Get H→A∧B from and_weak(H→A) and get_B(H→B)
  let s1 := .syllogism get_B (@and_intro ι F a Premises Γ B (A ∧ᶠ (B ∧ᶠ C)))
  let s2 := Derivable.importation s1
  let s3 := Derivable.syllogism .and_contract s2
  let s4 := Derivable.syllogism s3 .and_perm
  let s5 := .syllogism .and_weak (@and_intro ι F a Premises Γ A B)
  let s6 := Derivable.importation s5
  let get_AB := Derivable.syllogism s4 s6
  -- Get H→(A∧B)∧C from get_AB and get_C
  let t1 := .syllogism get_C (@and_intro ι F a Premises Γ C (A ∧ᶠ (B ∧ᶠ C)))
  let t2 := Derivable.importation t1
  let t3 := Derivable.syllogism .and_contract t2
  let t4 := Derivable.syllogism t3 .and_perm
  let t5 := .syllogism get_AB (@and_intro ι F a Premises Γ (A ∧ᶠ B) C)
  let t6 := Derivable.importation t5
  Derivable.syllogism t4 t6

/-- Right associativity: `(A ∧ B) ∧ C → A ∧ (B ∧ C)`. -/
def and_assocr : Derivable F a Premises ((A ∧ᶠ B) ∧ᶠ C →ᶠ A ∧ᶠ (B ∧ᶠ C)) :=
  let get_A : Derivable F a Premises ((A ∧ᶠ B) ∧ᶠ C →ᶠ A) := .syllogism .and_weak .and_weak
  let get_B : Derivable F a Premises ((A ∧ᶠ B) ∧ᶠ C →ᶠ B) := .syllogism .and_weak and_proj2
  let get_C : Derivable F a Premises ((A ∧ᶠ B) ∧ᶠ C →ᶠ C) := and_proj2
  -- Get H→B∧C from get_B and get_C
  let s1 := .syllogism get_B (@and_intro ι F a Premises Γ B C)
  let s2 := Derivable.importation s1
  let s3 := .syllogism get_C (@and_intro ι F a Premises Γ C ((A ∧ᶠ B) ∧ᶠ C))
  let s4 := Derivable.importation s3
  let s5 := Derivable.syllogism .and_contract s4
  let s6 := Derivable.syllogism s5 .and_perm
  let get_BC := Derivable.syllogism s6 s2
  -- Get H→A∧(B∧C) from get_A and get_BC
  let t1 := .syllogism get_A (@and_intro ι F a Premises Γ A (B ∧ᶠ C))
  let t2 := Derivable.importation t1
  let t3 := .syllogism get_BC (@and_intro ι F a Premises Γ (B ∧ᶠ C) ((A ∧ᶠ B) ∧ᶠ C))
  let t4 := Derivable.importation t3
  let t5 := Derivable.syllogism .and_contract t4
  let t6 := Derivable.syllogism t5 .and_perm
  Derivable.syllogism t6 t2

-- ============================================================================
-- Tier 3 — Disjunction
-- ============================================================================

/-- Right injection: `B → A ∨ B`. -/
def or_inr : Derivable F a Premises (B →ᶠ A ∨ᶠ B) :=
  .syllogism .or_weak .or_perm

/-- Disjunction elimination as a rule: `(A → C) → (B → C) → (A ∨ B → C)`.

Note: `or_elim` as a *formula* `(A→C)→(B→C)→A∨B→C` is not derivable from the given
primitives because `expansion` requires a closed proof, not a formula hypothesis.
This meta-level function is used instead for building further results. -/
def or_elim_rule (f : Derivable F a Premises (A →ᶠ C)) (g : Derivable F a Premises (B →ᶠ C)) :
    Derivable F a Premises (A ∨ᶠ B →ᶠ C) :=
  -- A∨B → B∨A → B∨C → C∨B → C∨C → C
  .syllogism (.syllogism (.syllogism (.syllogism .or_perm (.expansion f)) .or_perm)
    (.expansion g)) .or_contract

/-- Left associativity for ∨: `A ∨ (B ∨ C) → (A ∨ B) ∨ C`. -/
def or_assocl : Derivable F a Premises (A ∨ᶠ (B ∨ᶠ C) →ᶠ (A ∨ᶠ B) ∨ᶠ C) :=
  -- A → (A∨B)∨C  via  or_weak then or_weak
  let step_A : Derivable F a Premises (A →ᶠ (A ∨ᶠ B) ∨ᶠ C) := .syllogism .or_weak .or_weak
  -- B → (A∨B)∨C  via  or_inr then or_weak
  let step_B : Derivable F a Premises (B →ᶠ (A ∨ᶠ B) ∨ᶠ C) := .syllogism or_inr .or_weak
  -- C → (A∨B)∨C  via  or_inr
  let step_C : Derivable F a Premises (C →ᶠ (A ∨ᶠ B) ∨ᶠ C) := or_inr
  -- B∨C → (A∨B)∨C
  let step_BC := or_elim_rule step_B step_C
  -- A∨(B∨C) → (A∨B)∨C
  or_elim_rule step_A step_BC

/-- Right associativity for ∨: `(A ∨ B) ∨ C → A ∨ (B ∨ C)`. -/
def or_assocr : Derivable F a Premises ((A ∨ᶠ B) ∨ᶠ C →ᶠ A ∨ᶠ (B ∨ᶠ C)) :=
  -- A → A∨(B∨C)
  let step_A : Derivable F a Premises (A →ᶠ A ∨ᶠ (B ∨ᶠ C)) := .or_weak
  -- B → B∨C → A∨(B∨C)
  let step_B : Derivable F a Premises (B →ᶠ A ∨ᶠ (B ∨ᶠ C)) := .syllogism .or_weak or_inr
  -- C → B∨C → A∨(B∨C)
  let step_C : Derivable F a Premises (C →ᶠ A ∨ᶠ (B ∨ᶠ C)) := .syllogism or_inr or_inr
  -- A∨B → A∨(B∨C)
  let step_AB := or_elim_rule step_A step_B
  -- (A∨B)∨C → A∨(B∨C)
  or_elim_rule step_AB step_C

-- ============================================================================
-- Tier 4 — Negation and double negation
-- ============================================================================

/-- Double-negation introduction: `A → ¬¬A`. -/
def dnn_intro : Derivable F a Premises (A →ᶠ ¬ᶠ¬ᶠA) :=
  .exportation (.syllogism .and_perm (.importation I_comb))

/-- Contrapositive: `(A → B) → ¬B → ¬A`. -/
def contrapositive (h : Derivable F a Premises (A →ᶠ B)) : Derivable F a Premises (¬ᶠB →ᶠ ¬ᶠA) :=
  .exportation (.syllogism .and_perm (.importation (.syllogism h dnn_intro)))

/-- Triple negation elimination: `¬¬¬A → ¬A`. -/
def triple_neg_elim : Derivable F a Premises (¬ᶠ¬ᶠ¬ᶠA →ᶠ ¬ᶠA) :=
  contrapositive dnn_intro

/-- `¬¬` distributes over `→` (forward): `¬¬(A → B) → ¬¬A → ¬¬B`. -/
def neg_neg_mp : Derivable F a Premises (¬ᶠ¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) :=
  -- comp_neg : (A→B)∧¬B → ¬A  (derived from the sub-antecedent (A→B)∧¬B∧A)
  let cn1 : Derivable F a Premises ((A →ᶠ B) ∧ᶠ ¬ᶠB ∧ᶠ A →ᶠ (A →ᶠ B)) := .syllogism .and_weak .and_weak
  let cn2 : Derivable F a Premises ((A →ᶠ B) ∧ᶠ ¬ᶠB ∧ᶠ A →ᶠ ¬ᶠB) := .syllogism .and_weak and_proj2
  let cn3 : Derivable F a Premises ((A →ᶠ B) ∧ᶠ ¬ᶠB ∧ᶠ A →ᶠ A) := and_proj2
  let cn4 := eval_h cn1 cn3
  let cn5 := eval_h cn2 cn4
  let comp_neg : Derivable F a Premises ((A →ᶠ B) ∧ᶠ ¬ᶠB →ᶠ ¬ᶠA) := Derivable.exportation cn5
  -- Main: from (¬¬(A→B) ∧ ¬¬A ∧ ¬B) ∧ (A→B), derive ⊥, then curry twice
  let get_f : Derivable F a Premises ((¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ¬ᶠA ∧ᶠ ¬ᶠB) ∧ᶠ (A →ᶠ B) →ᶠ (A →ᶠ B)) := and_proj2
  let get_nb : Derivable F a Premises ((¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ¬ᶠA ∧ᶠ ¬ᶠB) ∧ᶠ (A →ᶠ B) →ᶠ ¬ᶠB) :=
    .syllogism .and_weak and_proj2
  let get_nnA : Derivable F a Premises ((¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ¬ᶠA ∧ᶠ ¬ᶠB) ∧ᶠ (A →ᶠ B) →ᶠ ¬ᶠ¬ᶠA) :=
    .syllogism (.syllogism .and_weak .and_weak) and_proj2
  let get_fb := pair_h get_f get_nb
  let get_nA := .syllogism get_fb comp_neg
  let eval_nnA : Derivable F a Premises (¬ᶠ¬ᶠA ∧ᶠ ¬ᶠA →ᶠ ⊥ᶠ) := .importation (.syllogism .and_contract .and_weak)
  let get_bot_U := .syllogism (pair_h get_nnA get_nA) eval_nnA
  let nAB : Derivable F a Premises (¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ¬ᶠA ∧ᶠ ¬ᶠB →ᶠ ¬ᶠ(A →ᶠ B)) :=
    Derivable.exportation get_bot_U
  let get_nnAB : Derivable F a Premises (¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ¬ᶠA ∧ᶠ ¬ᶠB →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
    .syllogism .and_weak .and_weak
  let eval_nnAB : Derivable F a Premises (¬ᶠ¬ᶠ(A →ᶠ B) ∧ᶠ ¬ᶠ(A →ᶠ B) →ᶠ ⊥ᶠ) :=
    .importation (.syllogism .and_contract .and_weak)
  Derivable.exportation (Derivable.exportation (.syllogism (pair_h get_nnAB nAB) eval_nnAB))

/-- `¬¬` distributes over `→` (reverse): `(A → ¬¬B) → ¬¬(A → B)`. -/
def neg_neg_imp_rev : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
  -- H = (A→¬¬B)∧¬(A→B); K_BA: B→A→B, contrapositive: ¬(A→B)→¬B
  let K_BA : Derivable F a Premises (B →ᶠ A →ᶠ B) := .exportation .and_weak
  let cp_K_BA : Derivable F a Premises (¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠB) := contrapositive K_BA
  let get_h : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) →ᶠ A →ᶠ ¬ᶠ¬ᶠB) := .and_weak
  let get_k : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠ(A →ᶠ B)) :=
    .syllogism .and_perm .and_weak
  let neg_B  := .syllogism get_k cp_K_BA
  let neg_nB := .syllogism neg_B dnn_intro
  -- sub: (A→¬¬B)∧¬¬¬B∧A → ⊥; export: (A→¬¬B)∧¬¬¬B → ¬A
  let h2   : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ¬ᶠ¬ᶠB ∧ᶠ A →ᶠ A →ᶠ ¬ᶠ¬ᶠB) := .syllogism .and_weak .and_weak
  let nnnB : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ¬ᶠ¬ᶠB ∧ᶠ A →ᶠ ¬ᶠ¬ᶠ¬ᶠB) := .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let a2   : Derivable F a Premises ((A →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ¬ᶠ¬ᶠB ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let eval_nnnB_nnB : Derivable F a Premises (¬ᶠ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ¬ᶠB →ᶠ ⊥ᶠ) := .importation (.syllogism .and_contract .and_weak)
  let neg_A_closed := Derivable.exportation (.syllogism (pair_h nnnB (eval_h h2 a2)) eval_nnnB_nnB)
  let neg_A := .syllogism (pair_h get_h neg_nB) neg_A_closed
  let hab   := Derivable.exportation (.syllogism (Derivable.importation neg_A) .exfalso)
  Derivable.exportation (eval_h get_k hab)

/-- `¬¬` distributes over `→` (reverse, double-neg premises):
    `(¬¬A → ¬¬B) → ¬¬(A → B)`. -/
def neg_neg_imp_rev2 : Derivable F a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) →ᶠ ¬ᶠ¬ᶠ(A →ᶠ B)) :=
  -- H = (¬¬A→¬¬B)∧¬(A→B); from H∧A: ¬¬A → ¬¬B, ¬B; get ⊥ → ¬A → A→B via exfalso
  let K_BA : Derivable F a Premises (B →ᶠ A →ᶠ B) := .exportation .and_weak
  let cp_K_BA : Derivable F a Premises (¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠB) := contrapositive K_BA
  let get_k : Derivable F a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) →ᶠ ¬ᶠ(A →ᶠ B)) :=
    .syllogism .and_perm .and_weak
  let get_h2 : Derivable F a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) ∧ᶠ A →ᶠ ¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) := .syllogism .and_weak .and_weak
  let get_k2 : Derivable F a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) ∧ᶠ A →ᶠ ¬ᶠ(A →ᶠ B)) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let get_a : Derivable F a Premises ((¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB) ∧ᶠ ¬ᶠ(A →ᶠ B) ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let neg_B2 := .syllogism get_k2 cp_K_BA
  let nnB    := eval_h get_h2 (.syllogism get_a dnn_intro)
  let eval_nnB_nB : Derivable F a Premises (¬ᶠ¬ᶠB ∧ᶠ ¬ᶠB →ᶠ ⊥ᶠ) := .importation (.syllogism .and_contract .and_weak)
  let neg_A  := Derivable.exportation (.syllogism (pair_h nnB neg_B2) eval_nnB_nB)
  let hab    := Derivable.exportation (.syllogism (Derivable.importation neg_A) .exfalso)
  Derivable.exportation (eval_h get_k hab)

/-- `¬¬` introduction under `∧` (left): `¬¬(A ∧ B) → ¬¬A`. -/
def neg_neg_and_left : Derivable F a Premises (¬ᶠ¬ᶠ(A ∧ᶠ B) →ᶠ ¬ᶠ¬ᶠA) :=
  let cp := fun {X Y : Formula F Γ} (h : Derivable F a Premises (X →ᶠ Y)) =>
    Derivable.exportation (.syllogism .and_perm (.importation (.syllogism h dnn_intro)))
  cp (cp .and_weak)

/-- `¬¬` introduction under `∧` (right): `¬¬(A ∧ B) → ¬¬B`. -/
def neg_neg_and_right : Derivable F a Premises (¬ᶠ¬ᶠ(A ∧ᶠ B) →ᶠ ¬ᶠ¬ᶠB) :=
  let cp := fun {X Y : Formula F Γ} (h : Derivable F a Premises (X →ᶠ Y)) =>
    Derivable.exportation (.syllogism .and_perm (.importation (.syllogism h dnn_intro)))
  cp (cp (.syllogism .and_perm .and_weak))

/-- `¬¬A → ¬¬B → ¬¬(A ∧ B)`. -/
def neg_neg_and_intro : Derivable F a Premises (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠB →ᶠ ¬ᶠ¬ᶠ(A ∧ᶠ B)) :=
  -- H = (¬¬A∧¬¬B)∧¬(A∧B); H' = H∧A; H'' = H'∧B
  -- From H'': get A, B, ¬(A∧B); pair A∧B; contradiction with ¬(A∧B) → ¬B from H'
  let get_a : Derivable F a Premises ((¬ᶠ¬ᶠA ∧ᶠ ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ(A ∧ᶠ B) ∧ᶠ A) ∧ᶠ B →ᶠ A) :=
    .syllogism .and_weak (.syllogism .and_perm .and_weak)
  let get_b : Derivable F a Premises ((¬ᶠ¬ᶠA ∧ᶠ ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ(A ∧ᶠ B) ∧ᶠ A) ∧ᶠ B →ᶠ B) :=
    .syllogism .and_perm .and_weak
  let get_nAB : Derivable F a Premises ((¬ᶠ¬ᶠA ∧ᶠ ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ(A ∧ᶠ B) ∧ᶠ A) ∧ᶠ B →ᶠ A ∧ᶠ B →ᶠ ⊥ᶠ) :=
    .syllogism (.syllogism .and_weak .and_weak) (.syllogism .and_perm .and_weak)
  let get_bot'' := eval_h get_nAB (pair_h get_a get_b)
  let neg_B := Derivable.exportation get_bot''
  -- From H': get ¬¬B; combine with ¬B to get ⊥ → ¬A from H
  let get_nnB : Derivable F a Premises (¬ᶠ¬ᶠA ∧ᶠ ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ(A ∧ᶠ B) ∧ᶠ A →ᶠ ¬ᶠ¬ᶠB) :=
    .syllogism (.syllogism .and_weak .and_weak) (.syllogism .and_perm .and_weak)
  let eval_nnB : Derivable F a Premises (¬ᶠ¬ᶠB ∧ᶠ ¬ᶠB →ᶠ ⊥ᶠ) := .importation (.syllogism .and_contract .and_weak)
  let neg_A := Derivable.exportation (.syllogism (pair_h get_nnB neg_B) eval_nnB)
  -- From H: get ¬¬A; combine with ¬A to get ⊥
  let get_nnA : Derivable F a Premises (¬ᶠ¬ᶠA ∧ᶠ ¬ᶠ¬ᶠB ∧ᶠ ¬ᶠ(A ∧ᶠ B) →ᶠ ¬ᶠ¬ᶠA) := .syllogism .and_weak .and_weak
  let eval_nnA : Derivable F a Premises (¬ᶠ¬ᶠA ∧ᶠ ¬ᶠA →ᶠ ⊥ᶠ) := .importation (.syllogism .and_contract .and_weak)
  Derivable.exportation (Derivable.exportation (.syllogism (pair_h get_nnA neg_A) eval_nnA))

/-- `¬¬A ∨ ¬¬B → ¬¬(A ∨ B)`. -/
def neg_neg_or_intro : Derivable F a Premises (¬ᶠ¬ᶠA ∨ᶠ ¬ᶠ¬ᶠB →ᶠ ¬ᶠ¬ᶠ(A ∨ᶠ B)) :=
  let step_A : Derivable F a Premises (¬ᶠ¬ᶠA →ᶠ ¬ᶠ¬ᶠ(A ∨ᶠ B)) :=
    contrapositive (contrapositive .or_weak)
  let step_B : Derivable F a Premises (¬ᶠ¬ᶠB →ᶠ ¬ᶠ¬ᶠ(A ∨ᶠ B)) :=
    contrapositive (contrapositive or_inr)
  or_elim_rule step_A step_B

/-- Double-negated LEM: `¬¬(A ∨ ¬A)`. -/
def dnn_lem : Derivable F a Premises (¬ᶠ¬ᶠ(A ∨ᶠ ¬ᶠA)) :=
  -- K = ¬(A∨¬A); from K∧A → K∧(A∨¬A) → ⊥, get K→¬A, then K→A∨¬A via or_inr, then K→⊥
  let eval_K : Derivable F a Premises (¬ᶠ(A ∨ᶠ ¬ᶠA) ∧ᶠ (A ∨ᶠ ¬ᶠA) →ᶠ ⊥ᶠ) :=
    .importation (.syllogism .and_contract .and_weak)
  let get_K1 : Derivable F a Premises (¬ᶠ(A ∨ᶠ ¬ᶠA) ∧ᶠ A →ᶠ ¬ᶠ(A ∨ᶠ ¬ᶠA)) := .and_weak
  let get_a  : Derivable F a Premises (¬ᶠ(A ∨ᶠ ¬ᶠA) ∧ᶠ A →ᶠ A) := .syllogism .and_perm .and_weak
  let bot1 := .syllogism (pair_h get_K1 (.syllogism get_a .or_weak)) eval_K
  let neg_A := Derivable.exportation bot1
  let or_inr_A : Derivable F a Premises (¬ᶠ(A ∨ᶠ ¬ᶠA) →ᶠ A ∨ᶠ ¬ᶠA) :=
    .syllogism neg_A (@or_inr ι F a Premises Γ A (¬ᶠA))
  Derivable.syllogism (pair_h I_comb or_inr_A) eval_K

/-- Distribute a conjunct over a disjunction. -/
def and_or_dist : Derivable F a Premises (Γ := Γ)
    (A ∧ᶠ (B ∨ᶠ C) →ᶠ (A ∧ᶠ B) ∨ᶠ (A ∧ᶠ C)) :=
  .syllogism .and_perm
    (.importation (or_elim_rule
      (.exportation (.syllogism .and_perm .or_weak))
      (.exportation (.syllogism .and_perm or_inr))))

end PropositionalLemmas

end Metatheorems
