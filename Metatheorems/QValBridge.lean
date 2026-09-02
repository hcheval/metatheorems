/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.QVal
import Metatheorems.Terms.Rational

namespace Metatheorems

/-!
# The evaluation bridge: object-level `ℚ` terms ↦ Lean-level mirrors

`QVal.lean` defines `qval : ℕ → ℚ`, the rational denoted by a code, and its header says
explicitly that it does **not** connect `qval` to `Term.interpret` of `Term.rat_num`,
`Term.lt_Q_dec`, … This file is that connection, bottom-up.

## Method

For each **closed** constant `C : Term F Γ (nat →ₜ … →ₜ nat)` we prove a *function-level*
lemma

    Term.interpret si (Term.C (F := F) (Γ := Δ)) env = <Lean mirror>

— not an application-level one. Three reasons:

* the constants are closed, so the statement is environment-independent and is proved once;
* each proof unfolds **exactly one** constant and cites the already-proved lemmas for the
  rest. Never compose two unfoldings in one `simp`: `Term.add_Q` is 1,945 nodes as written
  and 1,880,329 fully reduced, so a `simp` that unfolds two layers at once will blow
  heartbeats;
* they chain: a function-level lemma fires as a rewrite on the *head* of an application
  spine, at any context and any environment, which is what lets the next stratum up unfold
  one level and finish.

The template is `interpret_pd_fun` in `Dialectica/Syntactic.lean`.

## Mirrors

Every mirror is chosen to be `omega`-friendly (truncated subtraction, `%`, `min`) rather
than a Lean `if`, so that the arithmetic side conditions of the strata above are discharged
automatically.

## Dependency order

    sg_bar, pd, add, mul, monus, abs_diff        (Terms/Arith.lean)
      → sg, isEven, isOdd, geq, ite_nat, max, min
        → triag, exp2
          → pair, inv_triag, fst_pair, snd_pair
            → div2
              → rat_num, rat_den, rat_sign, rat_encode

`inv_triag` is the only step with real mathematical content: the object-level recursion has
to be shown to compute `Rounding.invTriagN`, which is a `Nat.findGreatest`.
-/

namespace QBridge

open Rounding

variable {ι : Type} {F : ι → Ty ι} {X : ι → Type}

-- ============================================================================
-- Section 0: the Lean mirrors that are not already in Mathlib or `Rounding`
-- ============================================================================

/-- Mirror of `Term.sg_bar`: `1` at `0`, `0` elsewhere. Written as truncated subtraction so
that `omega` sees through it. -/
abbrev sgBarN (n : ℕ) : ℕ := 1 - n

/-- Mirror of `Term.sg`: `0` at `0`, `1` elsewhere. -/
abbrev sgN (n : ℕ) : ℕ := min n 1

/-- Mirror of `Term.isEven`: `1` on evens, `0` on odds. -/
abbrev isEvenN (n : ℕ) : ℕ := 1 - n % 2

/-- Mirror of `Term.isOdd`. -/
abbrev isOddN (n : ℕ) : ℕ := n % 2

/-- Mirror of `Term.geq`: `1` when `a ≥ b`, else `0`. -/
abbrev geqN (a b : ℕ) : ℕ := 1 - (b - a)

/-- Mirror of `Term.ite_nat`: `b·x + (1−b)·y`, which is `x` at `b = 1` and `y` at `b = 0`.
This *is* what the object term computes; it is not an idealisation of it. -/
abbrev iteN (b x y : ℕ) : ℕ := b * x + (1 - b) * y

/-- Mirror of `Term.rat_num`: the unsigned numerator `⌈j₁(n)/2⌉`. -/
def ratNumN (n : ℕ) : ℕ := (fstN n + 1) / 2

/-- Mirror of `Term.rat_den`: the denominator `j₂(n) + 1`. -/
def ratDenN (n : ℕ) : ℕ := sndN n + 1

/-- Mirror of `Term.rat_sign`: `1` for non-negative, `0` for negative. -/
def ratSignN (n : ℕ) : ℕ := isEvenN (fstN n)

/-- Mirror of `Term.rat_encode`. -/
def ratEncodeN (s p d : ℕ) : ℕ := pairN (2 * p - isEvenN s) d

-- ============================================================================
-- Section 1: what the object-level `prec`-recursions compute
--
-- Each is a plain Lean induction, stated on the `Nat.rec` that
-- `Term.interpret si (.prec _)` unfolds to.
-- ============================================================================

private theorem rec_succ_eq_add (x : ℕ) :
    ∀ n : ℕ, (Nat.rec x (fun _ ih => Nat.succ ih) n : ℕ) = x + n
  | 0 => rfl
  | m + 1 => by
      change Nat.succ (Nat.rec x (fun _ ih => Nat.succ ih) m : ℕ) = x + (m + 1)
      rw [rec_succ_eq_add x m]
      rfl

private theorem rec_add_eq_mul (x : ℕ) :
    ∀ n : ℕ, (Nat.rec 0 (fun _ ih => ih + x) n : ℕ) = x * n
  | 0 => rfl
  | m + 1 => by
      change (Nat.rec 0 (fun _ ih => ih + x) m : ℕ) + x = x * (m + 1)
      rw [rec_add_eq_mul x m]; ring

private theorem rec_pred_eq_sub (x : ℕ) :
    ∀ n : ℕ, (Nat.rec x (fun _ ih => Nat.pred ih) n : ℕ) = x - n
  | 0 => rfl
  | m + 1 => by
      change Nat.pred (Nat.rec x (fun _ ih => Nat.pred ih) m : ℕ) = x - (m + 1)
      rw [rec_pred_eq_sub x m, Nat.sub_succ]

private theorem rec_const_zero_eq_sgBar :
    ∀ n : ℕ, (Nat.rec 1 (fun _ _ => 0) n : ℕ) = sgBarN n
  | 0 => rfl
  | m + 1 => by change (0 : ℕ) = 1 - (m + 1); omega

private theorem rec_const_one_eq_sg :
    ∀ n : ℕ, (Nat.rec 0 (fun _ _ => 1) n : ℕ) = sgN n
  | 0 => rfl
  | m + 1 => by
      change (1 : ℕ) = min (m + 1) 1
      omega

private theorem rec_eq_isEven :
    ∀ n : ℕ, (Nat.rec 1 (fun _ ih => 1 - ih) n : ℕ) = isEvenN n
  | 0 => rfl
  | m + 1 => by
      change 1 - (Nat.rec 1 (fun _ ih => 1 - ih) m : ℕ) = isEvenN (m + 1)
      rw [rec_eq_isEven m]
      simp only [isEvenN]
      omega

private theorem rec_eq_triagN :
    ∀ n : ℕ, (Nat.rec 0 (fun k ih => ih + (k + 1)) n : ℕ) = triagN n
  | 0 => rfl
  | m + 1 => by
      change (Nat.rec 0 (fun k ih => ih + (k + 1)) m : ℕ) + (m + 1) = triagN (m + 1)
      rw [rec_eq_triagN m]; rfl

private theorem rec_eq_exp2 :
    ∀ n : ℕ, (Nat.rec 1 (fun _ ih => ih + ih) n : ℕ) = 2 ^ n
  | 0 => rfl
  | m + 1 => by
      change (Nat.rec 1 (fun _ ih => ih + ih) m : ℕ) + (Nat.rec 1 (fun _ ih => ih + ih) m : ℕ)
            = 2 ^ (m + 1)
      rw [rec_eq_exp2 m]; ring

-- ============================================================================
-- Section 2: the arithmetic constants of `Terms/Arith.lean`
-- ============================================================================

theorem interpret_sg_bar_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.sg_bar (F := F) (Γ := Δ)) env = sgBarN := by
  funext n
  simp only [Term.sg_bar, Term.app3, Term.interpret]
  exact rec_const_zero_eq_sgBar n

theorem interpret_pd_fun' {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.pd (F := F) (Γ := Δ)) env = Nat.pred := by
  funext n
  simp only [Term.pd, Term.app3, Term.interpret]
  cases n <;> rfl

theorem interpret_add_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.add (F := F) (Γ := Δ)) env = fun x n => x + n := by
  funext x n
  simp only [Term.add, Term.app3, Term.interpret]
  exact rec_succ_eq_add x n

theorem interpret_mul_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.mul (F := F) (Γ := Δ)) env = fun x n => x * n := by
  funext x n
  simp only [Term.mul, Term.app3, Term.app2, Term.interpret, interpret_add_fun]
  exact rec_add_eq_mul x n

theorem interpret_monus_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.monus (F := F) (Γ := Δ)) env = fun x n => x - n := by
  funext x n
  simp only [Term.monus, Term.app3, Term.interpret, interpret_pd_fun']
  exact rec_pred_eq_sub x n

theorem interpret_abs_diff_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.abs_diff (F := F) (Γ := Δ)) env = fun x y => (x - y) + (y - x) := by
  funext x y
  simp only [Term.abs_diff, Term.app2, Term.interpret,
    interpret_add_fun, interpret_monus_fun]
  rfl

theorem interpret_ofNat {si : SpaceInterp X F} {Δ : Ctx ι} (n : ℕ) (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.ofNat (F := F) (Γ := Δ) n) env = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [Term.ofNat, Term.interpret, ih]

-- ============================================================================
-- Section 3: the auxiliary constants of `Terms/Rational.lean` §1
-- ============================================================================

theorem interpret_max_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.max (F := F) (Γ := Δ)) env = fun x y => max x y := by
  funext x y
  simp only [Term.max, Term.app2, Term.interpret,
    interpret_add_fun, interpret_monus_fun]
  exact (by omega : ∀ a b : ℕ, a + (b - a) = max a b) x y

theorem interpret_min_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.min (F := F) (Γ := Δ)) env = fun x y => min x y := by
  funext x y
  simp only [Term.min, Term.app2, Term.interpret, interpret_monus_fun]
  exact (by omega : ∀ a b : ℕ, a - (a - b) = min a b) x y

theorem interpret_sg_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.sg (F := F) (Γ := Δ)) env = sgN := by
  funext n
  simp only [Term.sg, Term.app3, Term.interpret]
  exact rec_const_one_eq_sg n

theorem interpret_isEven_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.isEven (F := F) (Γ := Δ)) env = isEvenN := by
  funext n
  simp only [Term.isEven, Term.app3, Term.interpret, interpret_sg_bar_fun]
  exact rec_eq_isEven n

theorem interpret_isOdd_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.isOdd (F := F) (Γ := Δ)) env = isOddN := by
  funext n
  simp only [Term.isOdd, Term.app2, Term.interpret,
    interpret_monus_fun, interpret_isEven_fun]
  change (1 : ℕ) - (1 - n % 2) = n % 2
  omega

theorem interpret_geq_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.geq (F := F) (Γ := Δ)) env = geqN := by
  funext a b
  simp only [Term.geq, Term.app2, Term.interpret,
    interpret_sg_bar_fun, interpret_monus_fun]
  rfl

theorem interpret_ite_nat_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.ite_nat (F := F) (Γ := Δ)) env = iteN := by
  funext b x y
  simp only [Term.ite_nat, Term.app2, Term.interpret,
    interpret_add_fun, interpret_mul_fun, interpret_monus_fun]
  rfl

theorem interpret_triag_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.triag (F := F) (Γ := Δ)) env = triagN := by
  funext n
  simp only [Term.triag, Term.app3, Term.app2, Term.interpret, interpret_add_fun]
  exact rec_eq_triagN n

theorem interpret_exp2_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.exp2 (F := F) (Γ := Δ)) env = fun n => 2 ^ n := by
  funext n
  simp only [Term.exp2, Term.app3, Term.app2, Term.interpret, interpret_add_fun]
  exact rec_eq_exp2 n

-- ============================================================================
-- Section 4: the Cantor pairing
--
-- `inv_triag` is the one step with mathematical content: the object-level
-- recursion has to be identified with `Rounding.invTriagN`, a `Nat.findGreatest`.
-- ============================================================================

theorem interpret_pair_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.pair (F := F) (Γ := Δ)) env = pairN := by
  funext a b
  simp only [Term.pair, Term.app2, Term.interpret, interpret_add_fun, interpret_triag_fun]
  rfl

/-- The Lean-side transcription of the object recursion in `Term.inv_triag`. -/
private def itr : ℕ → ℕ
  | 0 => 0
  | n + 1 => itr n + (1 - (triagN (itr n + 1) - (n + 1)))

/-- The defining property of `itr`: it brackets its argument between consecutive
triangular numbers. -/
private theorem itr_spec : ∀ n : ℕ, triagN (itr n) ≤ n ∧ n < triagN (itr n + 1)
  | 0 => ⟨Nat.le_refl 0, by decide⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := itr_spec n
      have hstep : triagN (itr n + 1 + 1) = triagN (itr n + 1) + (itr n + 1 + 1) := rfl
      by_cases hc : triagN (itr n + 1) ≤ n + 1
      · have hval : itr (n + 1) = itr n + 1 := by
          change itr n + (1 - (triagN (itr n + 1) - (n + 1))) = itr n + 1
          omega
        rw [hval]
        exact ⟨hc, by omega⟩
      · have hval : itr (n + 1) = itr n := by
          change itr n + (1 - (triagN (itr n + 1) - (n + 1))) = itr n
          omega
        rw [hval]
        exact ⟨by omega, by omega⟩

/-- `Nat.findGreatest` agrees with any function satisfying the bracketing property. -/
private theorem invTriagN_eq_of_spec {n w : ℕ} (h1 : triagN w ≤ n) (h2 : n < triagN (w + 1)) :
    invTriagN n = w := by
  refine Nat.findGreatest_eq_iff.2 ⟨Nat.le_trans (le_triagN w) h1, ?_, ?_⟩
  · intro _; exact h1
  · intro k hk _ hkle
    have : triagN (w + 1) ≤ triagN k := triagN_strictMono.monotone (by omega)
    omega

private theorem itr_eq_invTriagN (n : ℕ) : itr n = invTriagN n :=
  (invTriagN_eq_of_spec (itr_spec n).1 (itr_spec n).2).symm

private theorem rec_eq_invTriagN :
    ∀ n : ℕ,
      (Nat.rec 0 (fun k ih => ih + (1 - (triagN (ih + 1) - (k + 1)))) n : ℕ) = invTriagN n
  | 0 => (itr_eq_invTriagN 0).symm ▸ rfl
  | m + 1 => by
      change (Nat.rec 0 (fun k ih => ih + (1 - (triagN (ih + 1) - (k + 1)))) m : ℕ)
          + (1 - (triagN ((Nat.rec 0 (fun k ih => ih + (1 - (triagN (ih + 1) - (k + 1)))) m : ℕ)
              + 1) - (m + 1))) = invTriagN (m + 1)
      rw [rec_eq_invTriagN m, ← itr_eq_invTriagN m, ← itr_eq_invTriagN (m + 1)]
      rfl

theorem interpret_inv_triag_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.inv_triag (F := F) (Γ := Δ)) env = invTriagN := by
  funext n
  simp only [Term.inv_triag, Term.app3, Term.app2, Term.interpret,
    interpret_add_fun, interpret_sg_bar_fun, interpret_monus_fun, interpret_triag_fun]
  exact rec_eq_invTriagN n

theorem interpret_fst_pair_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.fst_pair (F := F) (Γ := Δ)) env = fstN := by
  funext n
  simp only [Term.fst_pair, Term.app2, Term.interpret,
    interpret_monus_fun, interpret_triag_fun, interpret_inv_triag_fun]
  rfl

theorem interpret_snd_pair_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.snd_pair (F := F) (Γ := Δ)) env = sndN := by
  funext n
  simp only [Term.snd_pair, Term.app2, Term.interpret,
    interpret_monus_fun, interpret_inv_triag_fun, interpret_fst_pair_fun]
  rfl

end QBridge

end Metatheorems
