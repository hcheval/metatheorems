/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.SyntacticMetatheorem
import Metatheorems.RealNumbers
import Metatheorems.CodeRealOps

/-!
# ℝ-MCT: the real-number monotone convergence theorem, in the metatheorem's shape

The *statement only* — design, side conditions, the semantic reading, and the plumbing that
shows it fits `syntactic_general_metatheorem_at_gen` / `_classical_gen`. No derivation is
built here — it is `ProofMode/RealMCT.lean`, and `docs/REAL_MCT.md` describes it.

This file is ℝ-MCT *inside the object logic*, over the encoded reals (`realTy ι = nat →ₜ nat`,
Cauchy sequences of ℚ-codes with the fixed modulus `2^{-n}`).

## The statement

    ∀ x^ρ ( ∀u B(u, x)  →  ∃v C(v, x) )          ρ := (ℕ → ℝ) ×ₜ ((ℕ → ℕ) ×ₜ ℕ)

* **`x` packs the three parameters with `Ty.prod`**: `a := fst x : ℕ → ℝ` the sequence,
  `g := fst (snd x) : ℕ → ℕ` the counterfunction, `k := snd (snd x) : ℕ` the precision.
  The hat type is `ρ.hat = (ℕ → ℕ → ℕ) ×ₜ ((ℕ → ℕ) ×ₜ ℕ)`, so `x* = (a*, (g*, k*))`.

* **The premise `∀u B` says `a` is antitone and lies in `[0,1]`, with `u` the Cauchy
  index**, `B` being

      B(u, x)  :=  ∀n ( leIdx (a(n+1)) (a n) u  ∧  leIdx 0ℝ (a n) u  ∧  leIdx (a n) 1ℝ u )

  `B` is purely universal and ∨-free. Consequently the extracted `U` bounds **the precision
  to which antitonicity and `0 ≤ a ≤ 1` must be known**.

* **The conclusion `∃v C` is the metastability statement with explicit slack at a fixed
  index**:

      C(v, x)  :=  leIdx  |a v −ℝ a (v + g v)|ℝ   ⟨2^{-(k+1)}⟩ℝ   (k+2)

  i.e. `D̂(k+3) <ℚ 3·2^{-(k+2)}` for the cauchyfied window difference `D`. It is QF, so
  `isPurelyExistential` and ∨-free hold trivially, and the metatheorem's own `∃v` is the
  only existential.

## Plumbing checked here

* `all_leIdx_eq : Formula.all Ty.nat (leIdx f.weaken g.weaken (.var .vz)) = le_R_pu f g` by
  `rfl` — the premise conjuncts and the conclusion really are `≤ℝ` bodies.
* The four side conditions by `rfl`.
* Two `example`s applying `syntactic_general_metatheorem_at_gen` and
  `syntactic_general_metatheorem_classical_gen` with the derivation as a binder — the shape
  is on the nose.
* The semantic reading: `rmB_all_iff` (the premise holds in a model **iff** `codeReal ∘ a`
  is antitone and in `[0,1]`), `rmC_implies` (the conclusion gives `|a v − a(v+g v)| < 2^{-k}`),
  and `real_mct_of_bound`, which composes them with the metatheorem: from any derivation, a
  `Φ` such that every antitone `[0,1]`-sequence majorized by `x*` has a `2^{-k}`-good window
  starting below `Φ x*`. That is `Reference/MCT.lean`'s `metastable`, with `Φ` extracted.
-/

namespace Metatheorems
namespace RealMCT

open Formula Rounding QBridge

variable {ι κ : Type} {F : κ → Ty ι}

-- Types and the packed parameter

/-- Sequences of encoded reals, `ℕ → ℝ`. -/
abbrev seqTy (ι : Type) : Ty ι := Ty.nat →ₜ realTy ι

/-- **The quantified type**: `a : ℕ → ℝ`, `g : ℕ → ℕ`, `k : ℕ`, packed with `Ty.prod`. -/
abbrev rmTy (ι : Type) : Ty ι := seqTy ι ×ₜ ((Ty.nat →ₜ Ty.nat) ×ₜ Ty.nat)

/-- The metatheorem's working context `[u/v : ℕ, x : rmTy]`. -/
abbrev rmCtx (ι : Type) : Ctx ι := [Ty.nat, rmTy ι]

/-- The context inside `B`'s own quantifier: `[n : ℕ, u : ℕ, x : rmTy]`. -/
abbrev rmCtx3 (ι : Type) : Ctx ι := [Ty.nat, Ty.nat, rmTy ι]

section Projections
variable {Γ : Ctx ι}

/-- `a := fst x`. -/
abbrev aOf (x : Term F Γ (rmTy ι)) : Term F Γ (seqTy ι) := Term.fst x
/-- `g := fst (snd x)`. -/
abbrev gOf (x : Term F Γ (rmTy ι)) : Term F Γ (Ty.nat →ₜ Ty.nat) := Term.fst (Term.snd x)
/-- `k := snd (snd x)`. -/
abbrev kOf (x : Term F Γ (rmTy ι)) : Term F Γ Ty.nat := Term.snd (Term.snd x)

-- `≤ℝ` at a fixed Cauchy index

/-- **`f ≤ℝ g` read at the single Cauchy index `m`**: the quantifier-free body of
`le_R_pu f g` with its bound variable replaced by `m`,

    ¬( 2^{-m} ≤ℚ f̂(m+1) −ℚ ĝ(m+1) ),   i.e.   f̂(m+1) −ℚ ĝ(m+1) <ℚ 2^{-m}.

`le_R_pu f g` is `Formula.all Ty.nat (leIdx f.weaken g.weaken (.var .vz))` on the nose
(`all_leIdx_eq`). -/
def leIdx (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) : Formula F Γ :=
  Formula.imp
    (Formula.eq0
      (Term.app2 Term.le_Q_dec
        (Term.app Term.pow2neg_Q m)
        (Term.app2 Term.sub_Q
          (Term.app (Term.app Term.cauchyfy f) (Term.app .succ m))
          (Term.app (Term.app Term.cauchyfy g) (Term.app .succ m))))
      Term.zero)
    ⊥ᶠ

/-- `le_R_pu` *is* `∀m leIdx`. -/
theorem all_leIdx_eq (f g : Term F Γ (realTy ι)) :
    Formula.all Ty.nat (leIdx f.weaken g.weaken (.var .vz)) = le_R_pu f g := rfl

theorem leIdx_qf (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    (leIdx f g m).isQF = true := rfl

theorem leIdx_vf (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat) :
    (leIdx f g m).isVFree = true := rfl

end Projections

-- The premise matrix `B`

/-- `n`, the sequence index bound by `B`'s inner `∀`. -/
abbrev nV : Term F (rmCtx3 ι) Ty.nat := .var .vz
/-- `u`, the metatheorem's premise variable = the shared Cauchy index. -/
abbrev uV : Term F (rmCtx3 ι) Ty.nat := .var (.vs .vz)
/-- `x`, seen from inside `B`. -/
abbrev xV3 : Term F (rmCtx3 ι) (rmTy ι) := .var (.vs (.vs .vz))

/-- **The premise matrix**, in context `[u : ℕ, x : rmTy]`:

    B(u, x)  :=  ∀n ( a(n+1) ≤ℝ a n  ∧  0ℝ ≤ℝ a n  ∧  a n ≤ℝ 1ℝ )   — each read at index u.

Purely universal, ∨-free. `∀u B` is antitonicity plus `a ∈ [0,1]`, as three `le_R_pu`
statements with their `∀`-blocks swapped past `∀n` and their Cauchy indices identified. -/
def rmB : Formula F (rmCtx ι) :=
  Formula.all Ty.nat
    (leIdx (Term.app (aOf xV3) (Term.app .succ nV)) (Term.app (aOf xV3) nV) uV
      ∧ᶠ leIdx Term.zero_R (Term.app (aOf xV3) nV) uV
      ∧ᶠ leIdx (Term.app (aOf xV3) nV) Term.one_R uV)

theorem rmB_pu : (rmB (F := F) (ι := ι)).isPurelyUniversal = true := rfl
theorem rmB_vf : (rmB (F := F) (ι := ι)).isVFree = true := rfl
/-- …and it is **not** quantifier-free, so the QF metatheorem cannot take it. -/
theorem rmB_not_qf : (rmB (F := F) (ι := ι)).isQF = false := rfl

-- The conclusion matrix `C`

/-- `v`, the metatheorem's witness variable = the left end of the window. -/
abbrev vV : Term F (rmCtx ι) Ty.nat := .var .vz
/-- `x`, seen from `[v, x]`. -/
abbrev xV : Term F (rmCtx ι) (rmTy ι) := .var (.vs .vz)

/-- The window difference `D := |a v −ℝ a (v + g v)|ℝ`. -/
def winDiff : Term F (rmCtx ι) (realTy ι) :=
  Term.app Term.abs_R
    (Term.app2 Term.sub_R
      (Term.app (aOf xV) vV)
      (Term.app (aOf xV) (Term.app2 Term.add vV (Term.app (gOf xV) vV))))

/-- `k + 1`, the exponent of the slack constant. -/
def kIdx1 : Term F (rmCtx ι) Ty.nat := Term.app .succ (kOf xV)

/-- The index at which the conclusion is read: `k + 2`. -/
def kIdx : Term F (rmCtx ι) Ty.nat := Term.app .succ kIdx1

/-- The constant real `⟨2^{-(k+1)}⟩ℝ`. -/
def slackR : Term F (rmCtx ι) (realTy ι) := const_R (Term.app Term.pow2neg_Q kIdx1)

/-- **The conclusion matrix**, in context `[v : ℕ, x : rmTy]`:

    C(v, x)  :=  leIdx |a v −ℝ a(v + g v)|ℝ  ⟨2^{-(k+1)}⟩ℝ  (k+2)
              ≡  ¬( 2^{-(k+2)} ≤ℚ D̂(k+3) −ℚ 2^{-(k+1)} )
              ≡  D̂(k+3) <ℚ 3·2^{-(k+2)}.

Quantifier-free; the body of `le_R_pu D ⟨2^{-(k+1)}⟩ℝ` at its index `k+2`, so a derivation
of `D ≤ℝ 2^{-(k+1)}` yields it by `le_R_pu_of_le_R` and one `forall_ax`. It implies
`|codeReal (a v) − codeReal (a (v + g v))| < 2^{-k}` in every model (`rmC_implies`): the
denoted difference is below `3·2^{-(k+2)} + 2^{-(k+3)} = 7·2^{-(k+3)}`. -/
def rmC : Formula F (rmCtx ι) := leIdx winDiff slackR kIdx

theorem rmC_pe : (rmC (F := F) (ι := ι)).isPurelyExistential = true := rfl
theorem rmC_vf : (rmC (F := F) (ι := ι)).isVFree = true := rfl
theorem rmC_qf : (rmC (F := F) (ι := ι)).isQF = true := rfl

/-- `C` is the body of a `le_R_pu`, spelled out: `∀m leIdx D c m` is `D ≤ℝ c` in Π⁰₁ form. -/
theorem rmC_is_le_R_pu_body :
    Formula.all Ty.nat (leIdx (winDiff (F := F) (ι := ι)).weaken slackR.weaken (.var .vz))
      = le_R_pu winDiff slackR := rfl

-- The statement

/-- **ℝ-MCT, metastable form, in the metatheorem's shape.**

    ∀ x^{(ℕ→ℝ) ×ₜ ((ℕ→ℕ) ×ₜ ℕ)} ( ∀u B(u,x) → ∃v C(v,x) ). -/
def rmStatement : Formula F [] :=
  Formula.all (rmTy ι) (Formula.all Ty.nat rmB →ᶠ Formula.ex Ty.nat rmC)

-- Does it fit the metatheorem? (derivation as a hypothesis)

section Fit
variable {X : ι → Type} {si : SpaceInterp X F} {Premises : PremiseSet F}

/-- **The bound as data**, from any extended derivation of `rmStatement`. Elaborating is the
check: the four side conditions and the `∀x(∀u B → ∃v C)` shape are exactly what
`syntactic_general_metatheorem_at_gen` wants. -/
def rmBound
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
    (prf : @Derivable ι κ F Allowed.extended Premises [] rmStatement) :
    { Φ : Ty.interpret X (rmTy ι).hat → Nat //
      ∀ (x : Ty.interpret X (rmTy ι)) (x_star : Ty.interpret X (rmTy ι).hat),
        am.toRel.maj (rmTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si rmB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si rmC (v, (x, ())) } :=
  syntactic_general_metatheorem_at_gen eqxi spremise cm rmB_pu rmB_vf rmC_pe rmC_vf prf

/-- The `∃`-valued extended version. -/
example
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    (prf : @Derivable ι κ F Allowed.extended Premises [] rmStatement) :
    ∃ Φ : Ty.interpret X (rmTy ι).hat → Nat,
      ∀ (x : Ty.interpret X (rmTy ι)) (x_star : Ty.interpret X (rmTy ι).hat),
        am.toRel.maj (rmTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si rmB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si rmC (v, (x, ())) :=
  syntactic_general_metatheorem_gen eqxi spremise am rmB_pu rmB_vf rmC_pe rmC_vf prf

/-- **The classical version**, for a derivation that does use classical logic. -/
example
    (eqxi : EqXInterp X F si)
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (am : AbstractMajorizability si)
    (prf : @Derivable ι κ F Allowed.classical Premises [] rmStatement) :
    ∃ Φ : Ty.interpret X (rmTy ι).hat → Nat,
      ∀ (x : Ty.interpret X (rmTy ι)) (x_star : Ty.interpret X (rmTy ι).hat),
        am.toRel.maj (rmTy ι) x_star x →
        (∀ u : Nat, u ≤ Φ x_star → Formula.interpret si rmB (u, (x, ()))) →
        ∃ v : Nat, v ≤ Φ x_star ∧ Formula.interpret si rmC (v, (x, ())) :=
  syntactic_general_metatheorem_classical_gen eqxi nts spremise am
    rmB_pu rmB_vf rmC_pe rmC_vf prf

end Fit

-- Semantic side, part 1: `neg_R` on a RAW code

/-! `CodeRealOps.codeReal_negR_of_isCauchyCode` handles `neg_R` only on check-passing codes,
which is all the space axioms needed. The window difference `a v −ℝ a(v + g v)` subtracts a
raw code, so the general fact is needed: `cauchyfy` commutes with pointwise negation for
**every** code — the semantic mirror of `RealNumbers/Negation.lean`'s `cauchyState_neg`. The
check is `neg_Q`-invariant (`|−a − (−b)| = |a − b|`), so the flag never differs and the value
is negated. -/

/-- The Cauchy check is invariant under pointwise negation: `|−a − (−b)| = |a − b|`. -/
theorem checkN_neg_iff (g : ℕ → ℕ) (n : ℕ) :
    checkN (fun k => negQN (g k)) n = 0 ↔ checkN g n = 0 := by
  rw [checkN_eq_zero_iff, checkN_eq_zero_iff]
  simp only [qval_negQN]
  rw [neg_sub_neg, abs_sub_comm]

theorem cauchyStateN_neg (g : ℕ → ℕ) : ∀ n : ℕ,
    cauchyStateN (fun k => negQN (g k)) n
      = pairN (negQN (fstN (cauchyStateN g n))) (sndN (cauchyStateN g n))
  | 0 => by simp [cauchyStateN]
  | n + 1 => by
      have ih := cauchyStateN_neg g n
      rw [cauchyStateN_succ, cauchyStateN_succ, ih]
      rcases cauchyStateN_inv g n with ⟨hf, _⟩ | hf
      · by_cases hc : checkN g n = 0
        · have hc' : checkN (fun k => negQN (g k)) n = 0 := (checkN_neg_iff g n).mpr hc
          simp [cstep, hf, iteN, sgBarN, hc, hc']
        · have hc' : checkN (fun k => negQN (g k)) n ≠ 0 :=
            fun h => hc ((checkN_neg_iff g n).mp h)
          have hs : sgBarN (checkN g n) = 0 := by unfold sgBarN; omega
          have hs' : sgBarN (checkN (fun k => negQN (g k)) n) = 0 := by unfold sgBarN; omega
          simp [cstep, hf, iteN, hs, hs']
      · simp [cstep, hf, iteN]

theorem cauchyfyN_neg (g : ℕ → ℕ) (n : ℕ) :
    cauchyfyN (fun k => negQN (g k)) n = negQN (cauchyfyN g n) := by
  simp only [cauchyfyN, cauchyStateN_neg, fstN_pairN]

/-- **`neg_R` denotes the negation for every code**, Cauchy or not. -/
theorem codeReal_negR (g : ℕ → ℕ) : codeReal (fun n => negQN (g n)) = - codeReal g := by
  refine tendsto_nhds_unique (codeReal_tendsto _) ?_
  refine ((codeReal_tendsto g).neg).congr ?_
  intro n
  simp only [cauchyfyN_neg, qval_negQN, Rat.cast_neg]

/-- The sequence `sub_R` builds, for **all** `f g` (no side condition, unlike
`codeReal_subR`). -/
theorem codeReal_subR_all (f g : ℕ → ℕ) :
    codeReal (fun n => addQN (cauchyfyN f (n + 1)) (cauchyfyN (fun k => negQN (g k)) (n + 1)))
      = codeReal f - codeReal g := by
  rw [codeReal_addR, codeReal_negR]; ring

section Interp
variable {X : ι → Type} {si : SpaceInterp X F} {Γ : Ctx ι}

theorem codeReal_interp_sub_R_all (f g : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ) :
    codeReal (Term.interpret si (Term.app2 Term.sub_R f g) env)
      = codeReal (Term.interpret si f env) - codeReal (Term.interpret si g env) := by
  simp only [Term.app2, Term.interpret, interpret_sub_R_fun]
  exact codeReal_subR_all _ _

-- Semantic side, part 2: `leIdx` in a model

/-- `leIdx f g m` holds in a model iff, as rationals, `f̂(m+1) − ĝ(m+1) < 2^{-m}`. -/
theorem interpret_leIdx (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat)
    (env : Ctx.interpret X Γ) :
    Formula.interpret si (leIdx f g m) env ↔
      qval (cauchyfyN (Term.interpret si f env) (Term.interpret si m env + 1))
        - qval (cauchyfyN (Term.interpret si g env) (Term.interpret si m env + 1))
        < 1 / 2 ^ (Term.interpret si m env) := by
  simp only [leIdx, Formula.interpret, Term.app2, Term.interpret, interpret_le_Q_dec_fun,
    interpret_sub_Q_fun, interpret_cauchyfy_fun, interpret_pow2neg_Q_fun,
    Nat.succ_eq_add_one, imp_false]
  rw [leQdecN_eq_zero_iff, qval_subQN, qval_pow2neg_code, not_le]

/-- `≤` on the denoted reals gives the single-index bound at every index — the one-index
half of `interpret_le_R_pu_of_codeReal_le`, same budget: `2·2^{-(m+1)} = 2^{-m}`, consumed
exactly. -/
theorem lt_of_codeReal_le (f g : ℕ → ℕ) (m : ℕ) (h : codeReal f ≤ codeReal g) :
    qval (cauchyfyN f (m + 1)) - qval (cauchyfyN g (m + 1)) < 1 / 2 ^ m := by
  have h1 := abs_qval_cauchyfyN_sub_codeReal_lt f (m + 1)
  have h2 := abs_qval_cauchyfyN_sub_codeReal_lt g (m + 1)
  rw [abs_lt] at h1 h2
  have hh := two_halves_R m
  refine (Rat.cast_lt (K := ℝ)).mp ?_
  push_cast
  linarith [h1.2, h2.1]

/-- …so `≤` on the denoted reals makes `leIdx` true at every index. -/
theorem interpret_leIdx_of_codeReal_le (f g : Term F Γ (realTy ι)) (m : Term F Γ Ty.nat)
    (env : Ctx.interpret X Γ)
    (h : codeReal (Term.interpret si f env) ≤ codeReal (Term.interpret si g env)) :
    Formula.interpret si (leIdx f g m) env := by
  rw [interpret_leIdx]
  exact lt_of_codeReal_le _ _ _ h

/-- The converse, in the limit: `leIdx f g` at **every** index gives `≤` on the denoted
reals. (`Probes/RevTriangleDemo.codeReal_le_of_interpret_le_R_pu` is this for `le_R_pu`; it
lives in a probe, so it is re-proved here on the index form.) -/
theorem codeReal_le_of_forall_lt (f g : ℕ → ℕ)
    (h : ∀ n : ℕ, qval (cauchyfyN f (n + 1)) - qval (cauchyfyN g (n + 1)) < 1 / 2 ^ n) :
    codeReal f ≤ codeReal g := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1:ℝ)/2 < 1)
  have hpow : (1:ℝ) / 2 ^ n < ε / 2 := by
    rw [div_pow] at hn; simpa using hn
  have h1 := abs_qval_cauchyfyN_sub_codeReal_lt f (n + 1)
  have h2 := abs_qval_cauchyfyN_sub_codeReal_lt g (n + 1)
  rw [abs_lt] at h1 h2
  have hq := h n
  have hr : ((qval (cauchyfyN f (n + 1)) : ℚ) : ℝ) - ((qval (cauchyfyN g (n + 1)) : ℚ) : ℝ)
      < 1 / 2 ^ n := by
    have hc : (((qval (cauchyfyN f (n + 1)) - qval (cauchyfyN g (n + 1)) : ℚ)) : ℝ)
        < ((1 / 2 ^ n : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at hc
    exact hc
  have hh := two_halves_R n
  linarith [h1.1, h1.2, h2.1, h2.2]

end Interp

-- Semantic side, part 3: what the premise and the conclusion SAY

section Meaning
variable {X : ι → Type} (si : SpaceInterp X F)

/-! The semantic value of `x : Ty.interpret X (rmTy ι)` is, reducibly, a triple
`(a, (g, k)) : (ℕ → ℕ → ℕ) × ((ℕ → ℕ) × ℕ)`. The lemmas below take it destructured, with
`k : ℕ` *syntactically* — `2 ^ x.2.2` with an exponent of type `Ty.interpret X Ty.nat` is
opaque to `norm_cast`/`omega` (CLAUDE.md, bridge section). -/

/-! The three variable terms of `rmB`, evaluated. Stated as `rfl` facts and used by `rw`,
never by unification against `codeReal (…)`: `codeReal` is a `limUnder`, and letting
`isDefEq` unfold it is a `whnf` timeout with no error to point at. -/

theorem interp_aSucc (n u : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (Term.app (aOf (xV3 (F := F))) (Term.app .succ nV))
      (n, (u, ((a, (g, k)), ()))) = a (n + 1) := rfl

theorem interp_aN (n u : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (Term.app (aOf (xV3 (F := F))) nV) (n, (u, ((a, (g, k)), ()))) = a n :=
  rfl

theorem interp_uV (n u : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (uV (F := F)) (n, (u, ((a, (g, k)), ()))) = u := rfl

/-- `B(u, x)` in a model, as three rational bounds at index `u`. -/
theorem interpret_rmB (u : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Formula.interpret si rmB (u, ((a, (g, k)), ())) ↔
      ∀ n : ℕ,
        ((qval (cauchyfyN (a (n + 1)) (u + 1)) - qval (cauchyfyN (a n) (u + 1)) < 1 / 2 ^ u)
          ∧ (qval (cauchyfyN (fun _ => pairN 0 0) (u + 1)) - qval (cauchyfyN (a n) (u + 1))
              < 1 / 2 ^ u))
        ∧ (qval (cauchyfyN (a n) (u + 1)) - qval (cauchyfyN (fun _ => pairN 2 0) (u + 1))
            < 1 / 2 ^ u) := by
  simp only [rmB, Formula.interpret, interpret_leIdx, interpret_zero_R, interpret_one_R]
  -- the variable terms evaluate by `rfl` (`interp_aSucc`, `interp_aN`, `interp_uV`), so the
  -- two sides are definitionally equal once the quantifier is instantiated
  constructor <;> intro h n <;> exact h n

/-- **The premise, read in a model**: `∀u B(u,x)` holds iff `codeReal ∘ a` is antitone and
lies in `[0,1]`. So the object-level premise is exactly `Reference/MCT.lean`'s three
hypotheses `hanti`, `hlb`, `hub` (with `hub` pointwise, which antitonicity makes equivalent). -/
theorem rmB_all_iff (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    (∀ u : ℕ, Formula.interpret si rmB (u, ((a, (g, k)), ()))) ↔
      ((∀ n, codeReal (a (n + 1)) ≤ codeReal (a n))
        ∧ (∀ n, 0 ≤ codeReal (a n))
        ∧ (∀ n, codeReal (a n) ≤ 1)) := by
  simp only [interpret_rmB si]
  have hz : codeReal (fun _ => pairN 0 0) = 0 := by
    rw [codeReal_const, qval_zero_code, Rat.cast_zero]
  have ho : codeReal (fun _ => pairN 2 0) = 1 := by
    rw [codeReal_const, qval_one_code, Rat.cast_one]
  constructor
  · intro h
    refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
    · exact codeReal_le_of_forall_lt _ _ (fun u => (h u n).1.1)
    · have := codeReal_le_of_forall_lt _ _ (fun u => (h u n).1.2)
      rwa [hz] at this
    · have := codeReal_le_of_forall_lt _ _ (fun u => (h u n).2)
      rwa [ho] at this
  · rintro ⟨hanti, h0, h1⟩ u n
    refine ⟨⟨lt_of_codeReal_le _ _ _ (hanti n), lt_of_codeReal_le _ _ _ ?_⟩,
      lt_of_codeReal_le _ _ _ ?_⟩
    · rw [hz]; exact h0 n
    · rw [ho]; exact h1 n

/-- A constant code is its own cauchyfication. -/
theorem cauchyfyN_const (q n : ℕ) : cauchyfyN (fun _ => q) n = q :=
  cauchyfyN_id_of_cauchy _ (isCauchyCode_const q) n

/-- `k+1`, `k+2`, `⟨2^{-(k+1)}⟩ℝ` and `D` evaluated. -/
theorem interp_kIdx1 (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (kIdx1 (F := F)) (v, ((a, (g, k)), ())) = k + 1 := rfl

theorem interp_kIdx (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (kIdx (F := F)) (v, ((a, (g, k)), ())) = k + 2 := rfl

theorem interp_slackR (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (slackR (F := F)) (v, ((a, (g, k)), ())) = fun _ => pow2negQN (k + 1) := by
  funext j
  -- `const_R q = Term.lam q.weaken`; a folded `weaken` is invisible under `⬝`, so it is
  -- exposed by `show` and removed by `rw`, not by `simp`.
  show Term.interpret si (Term.app Term.pow2neg_Q (kIdx1 (F := F))).weaken
    (j, (v, ((a, (g, k)), ()))) = _
  rw [Term.interpret_weaken]
  show Term.interpret si Term.pow2neg_Q _ (Term.interpret si (kIdx1 (F := F)) _) = _
  rw [interpret_pow2neg_Q_fun, interp_kIdx1]
  rfl

theorem interp_aV (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (Term.app (aOf (xV (F := F))) vV) (v, ((a, (g, k)), ())) = a v := rfl

theorem interp_aShift (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Term.interpret si (Term.app (aOf (xV (F := F))) (Term.app2 Term.add vV (Term.app (gOf xV) vV)))
      (v, ((a, (g, k)), ())) = a (v + g v) := by
  simp only [Term.app2, Term.interpret, interpret_add_fun]
  rfl

theorem codeReal_interp_winDiff (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    codeReal (Term.interpret si (winDiff (F := F)) (v, ((a, (g, k)), ())))
      = |codeReal (a v) - codeReal (a (v + g v))| := by
  rw [winDiff, codeReal_interp_abs_R, codeReal_interp_sub_R_all, interp_aV, interp_aShift]

/-- **The conclusion, read in a model**: `C(v,x)` gives `|a v − a(v + g v)| < 2^{-k}` on the
denoted reals — strictly: the difference is below `7·2^{-(k+3)}`. -/
theorem rmC_implies (v : ℕ) (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ)
    (h : Formula.interpret si rmC (v, ((a, (g, k)), ()))) :
    |codeReal (a v) - codeReal (a (v + g v))| < 1 / 2 ^ k := by
  simp only [rmC] at h
  rw [interpret_leIdx, interp_kIdx, interp_slackR] at h
  simp only [cauchyfyN_const, qval_pow2negQN] at h
  set D := Term.interpret si (winDiff (F := F)) (v, ((a, (g, k)), ())) with hD
  have hb := abs_qval_cauchyfyN_sub_codeReal_lt D (k + 2 + 1)
  rw [codeReal_interp_winDiff, abs_lt] at hb
  have h' : ((qval (cauchyfyN D (k + 2 + 1)) : ℚ) : ℝ) - 1 / 2 ^ (k + 1) < 1 / 2 ^ (k + 2) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at hc
    simpa using hc
  have e1 : (1 : ℝ) / 2 ^ (k + 2) + 1 / 2 ^ (k + 2) = 1 / 2 ^ (k + 1) := by
    rw [pow_succ]; field_simp; ring
  have e2 : (1 : ℝ) / 2 ^ (k + 1) + 1 / 2 ^ (k + 1) = 1 / 2 ^ k := two_halves_R k
  have e3 : (1 : ℝ) / 2 ^ (k + 2 + 1) < 1 / 2 ^ (k + 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith [hb.1, hb.2, h', e1, e2, e3]

end Meaning

-- The assembled reading: Reference/MCT.lean's `metastable`, with Φ extracted

section Assembled
variable {X : ι → Type} {si : SpaceInterp X F} {Premises : PremiseSet F}

/-- **ℝ-MCT with its bound, from any derivation of `rmStatement`.** For every model, every
`x = (a, (g, k))` majorized by `x*`, if `codeReal ∘ a` is antitone and in `[0,1]` then some
`v ≤ Φ(x*)` has `|a v − a(v + g v)| < 2^{-k}`. This is `Reference/MCT.lean`'s `metastable`
(strict, and with `Φ` the *extracted* bound rather than the hand-computed
`(shift g)^[2^k+1] 0`), obtained by composing the metatheorem with the two semantic readings. -/
theorem real_mct_of_bound
    (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {am : AbstractMajorizability si} (cm : ConstMajorants am)
    (prf : @Derivable ι κ F Allowed.extended Premises [] rmStatement)
    (a : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) (x_star : Ty.interpret X (rmTy ι).hat)
    (hmaj : am.toRel.maj (rmTy ι) x_star (a, (g, k)))
    (hanti : ∀ n, codeReal (a (n + 1)) ≤ codeReal (a n))
    (h0 : ∀ n, 0 ≤ codeReal (a n))
    (h1 : ∀ n, codeReal (a n) ≤ 1) :
    ∃ v : ℕ, v ≤ (rmBound eqxi spremise cm prf).val x_star ∧
      |codeReal (a v) - codeReal (a (v + g v))| < 1 / 2 ^ k := by
  obtain ⟨v, hv, hC⟩ := (rmBound eqxi spremise cm prf).property (a, (g, k)) x_star hmaj
    (fun u _ => ((rmB_all_iff si a g k).mpr ⟨hanti, h0, h1⟩) u)
  exact ⟨v, hv, rmC_implies si v a g k hC⟩

end Assembled

-- Why `a*` is not `λn.1`: codes of a real in `[0,1]` are unbounded as naturals

/-- **There is no uniform majorant for the codes of `[0,1]`**: `0` has codes with `f 0` as
large as you like (`pairN 0 d` encodes `0/(d+1)`). So the bound `Φ(a*, g*, k*)` genuinely
depends on `a*`, and a `λ`-independent bound needs the rounded representative `(·)◦`
(`Rounding.roundR_le₁_Mmaj`), which has no object-level term yet — see the header. -/
theorem codeReal_zero_code_unbounded (N : ℕ) :
    ∃ f : ℕ → ℕ, codeReal f = 0 ∧ N < f 0 := by
  refine ⟨fun _ => pairN (2 * 0) (N + 1), ?_, ?_⟩
  · rw [codeReal_const, qval_pairN_even]; simp
  · show N < pairN (2 * 0) (N + 1)
    have := le_pairN (2 * 0) (N + 1); omega

-- Axiom hygiene — verify by name after a completed `lake build`

#print axioms all_leIdx_eq
#print axioms rmB_pu
#print axioms rmB_vf
#print axioms rmB_not_qf
#print axioms rmC_pe
#print axioms rmC_vf
#print axioms rmC_qf
#print axioms rmC_is_le_R_pu_body
#print axioms rmStatement
#print axioms rmBound
#print axioms checkN_neg_iff
#print axioms cauchyStateN_neg
#print axioms cauchyfyN_neg
#print axioms codeReal_negR
#print axioms codeReal_subR_all
#print axioms codeReal_interp_sub_R_all
#print axioms interpret_leIdx
#print axioms lt_of_codeReal_le
#print axioms interpret_leIdx_of_codeReal_le
#print axioms codeReal_le_of_forall_lt
#print axioms interp_aSucc
#print axioms interp_aN
#print axioms interp_uV
#print axioms interpret_rmB
#print axioms rmB_all_iff
#print axioms cauchyfyN_const
#print axioms interp_kIdx1
#print axioms interp_kIdx
#print axioms interp_slackR
#print axioms interp_aV
#print axioms interp_aShift
#print axioms codeReal_interp_winDiff
#print axioms rmC_implies
#print axioms real_mct_of_bound
#print axioms codeReal_zero_code_unbounded

end RealMCT
end Metatheorems
