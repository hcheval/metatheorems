/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.QVal
import Metatheorems.Terms.Real

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

-- ============================================================================
-- Section 5: division by two
--
-- `Term.div2` runs a `prec` whose state is the *code* `pair(⌈k/2⌉, isEven k)`.
-- The content is the invariant `state k = pairN ((k + 1) / 2) (1 - k % 2)`, which
-- is where `fstN_pairN` / `sndN_pairN` earn their keep.
--
-- **`Term.div2` is misnamed**: it computes the ceiling `⌈n/2⌉ = (n+1)/2`, not the
-- floor. Its own docstring claims the state is `pair(div2 k, isEven k)`, but the
-- step adds `snd` *before* flipping the parity flag, so `div2 1 = 1`. Nothing
-- downstream is wrong — `Term.rat_num` is `div2 (j + isOdd j)`, and that is
-- `⌈j/2⌉` on the nose either way, which is what the encoding wants — but the
-- mirror below states the ceiling, because that is what the term computes.
-- ============================================================================

private theorem rec_div2_state :
    ∀ n : ℕ,
      (Nat.rec (pairN 0 1) (fun _ ih => pairN (fstN ih + sndN ih) (1 - sndN ih)) n : ℕ)
        = pairN ((n + 1) / 2) (1 - n % 2)
  | 0 => rfl
  | m + 1 => by
      change pairN (fstN (Nat.rec (pairN 0 1)
                (fun _ ih => pairN (fstN ih + sndN ih) (1 - sndN ih)) m : ℕ)
              + sndN (Nat.rec (pairN 0 1)
                (fun _ ih => pairN (fstN ih + sndN ih) (1 - sndN ih)) m : ℕ))
            (1 - sndN (Nat.rec (pairN 0 1)
                (fun _ ih => pairN (fstN ih + sndN ih) (1 - sndN ih)) m : ℕ))
          = pairN ((m + 1 + 1) / 2) (1 - (m + 1) % 2)
      rw [rec_div2_state m, fstN_pairN, sndN_pairN]
      congr 1 <;> omega

theorem interpret_div2_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.div2 (F := F) (Γ := Δ)) env = fun n => (n + 1) / 2 := by
  funext n
  simp only [Term.div2, Term.app3, Term.app2, Term.interpret,
    interpret_add_fun, interpret_pair_fun, interpret_sg_bar_fun,
    interpret_fst_pair_fun, interpret_snd_pair_fun]
  -- the residual `Ctx.lookup`s are definitional; `change` clears them in one step
  change fstN (Nat.rec (pairN 0 1) (fun _ ih => pairN (fstN ih + sndN ih) (1 - sndN ih)) n)
      = (n + 1) / 2
  rw [rec_div2_state n, fstN_pairN]

-- ============================================================================
-- Section 6: the rational accessors — the checkpoint
--
-- These sit on top of the whole pairing + `div2` layer, so if they compose the
-- method scales.
-- ============================================================================

theorem interpret_rat_num_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.rat_num (F := F) (Γ := Δ)) env = ratNumN := by
  funext n
  simp only [Term.rat_num, Term.app2, Term.interpret,
    interpret_add_fun, interpret_div2_fun, interpret_isOdd_fun, interpret_fst_pair_fun]
  change (fstN n + fstN n % 2 + 1) / 2 = ratNumN n
  simp only [ratNumN]
  omega

theorem interpret_rat_den_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.rat_den (F := F) (Γ := Δ)) env = ratDenN := by
  funext n
  simp only [Term.rat_den, Term.interpret, interpret_snd_pair_fun]
  rfl

theorem interpret_rat_sign_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.rat_sign (F := F) (Γ := Δ)) env = ratSignN := by
  funext n
  simp only [Term.rat_sign, Term.interpret, interpret_isEven_fun, interpret_fst_pair_fun]
  rfl

theorem interpret_rat_encode_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.rat_encode (F := F) (Γ := Δ)) env = ratEncodeN := by
  funext s p d
  simp only [Term.rat_encode, Term.app2, Term.interpret,
    interpret_pair_fun, interpret_mul_fun, interpret_monus_fun,
    interpret_isEven_fun, interpret_ofNat]
  rfl

-- ============================================================================
-- Section 7: the accessors against `qval`
--
-- The point of the mirrors: they really are the sign/numerator/denominator of
-- the rational `qval` names.
-- ============================================================================

theorem qval_eq_of_parts (n : ℕ) :
    qval n = (if ratSignN n = 1 then (ratNumN n : ℚ) else -(ratNumN n)) / (ratDenN n : ℚ) := by
  have hden : ((ratDenN n : ℕ) : ℚ) = (sndN n : ℚ) + 1 := by
    simp only [ratDenN]; push_cast; ring
  rw [qval, hden]
  congr 1
  simp only [ratSignN, ratNumN, isEvenN, qnumZ]
  rcases Nat.even_or_odd (fstN n) with he | ho
  · obtain ⟨k, hk⟩ := he
    have h2 : fstN n % 2 = 0 := by omega
    rw [if_pos h2, if_pos (by omega : 1 - fstN n % 2 = 1),
      (by omega : (fstN n + 1) / 2 = fstN n / 2)]
    norm_cast
  · obtain ⟨k, hk⟩ := ho
    have h2 : fstN n % 2 = 1 := by omega
    rw [if_neg (by omega : ¬ fstN n % 2 = 0), if_neg (by omega : ¬ 1 - fstN n % 2 = 1)]
    simp only [Int.cast_neg, Int.cast_natCast]

-- ============================================================================
-- Section 8: the S1 tail — the constants that are one unfold over the above
--
-- `neg_Q`, `abs_Q`, `pow2neg_Q`, `zero_Q`, `one_Q` introduce no new recursion:
-- each is `rat_encode` or `pair` applied to already-interpreted pieces. The real
-- ℚ arithmetic — `add_Q`, `sub_Q`, `lt_Q_dec` — is *not* here; that is S2.
-- ============================================================================

theorem interpret_neg_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.neg_Q (F := F) (Γ := Δ)) env
      = fun n => ratEncodeN (1 - ratSignN n) (ratNumN n) (sndN n) := by
  funext n
  simp only [Term.neg_Q, Term.app3, Term.app2, Term.interpret,
    interpret_rat_encode_fun, interpret_monus_fun, interpret_rat_sign_fun,
    interpret_rat_num_fun, interpret_snd_pair_fun]
  rfl

theorem interpret_abs_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.abs_Q (F := F) (Γ := Δ)) env
      = fun n => pairN (2 * ratNumN n) (sndN n) := by
  funext n
  simp only [Term.abs_Q, Term.app3, Term.interpret,
    interpret_rat_encode_fun, interpret_rat_num_fun, interpret_snd_pair_fun]
  change ratEncodeN 1 (ratNumN n) (sndN n) = _
  simp only [ratEncodeN, isEvenN]
  norm_num

theorem interpret_pow2neg_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.pow2neg_Q (F := F) (Γ := Δ)) env
      = fun n => pairN 2 (2 ^ n - 1) := by
  funext n
  simp only [Term.pow2neg_Q, Term.app2, Term.interpret,
    interpret_pair_fun, interpret_pd_fun', interpret_exp2_fun, interpret_ofNat]
  change pairN 2 (Nat.pred (2 ^ n)) = pairN 2 (2 ^ n - 1)
  rfl

theorem interpret_zero_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.zero_Q (F := F) (Γ := Δ)) env = pairN 0 0 := by
  simp only [Term.zero_Q, Term.app2, Term.interpret, interpret_pair_fun]

theorem interpret_one_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.one_Q (F := F) (Γ := Δ)) env = pairN 2 0 := by
  simp only [Term.one_Q, Term.app2, Term.interpret, interpret_pair_fun, interpret_ofNat]

-- ============================================================================
-- Section 9: the payoff — object-level constants denote the right rationals
--
-- These are the first statements in the project relating `Term.interpret` of a
-- ℚ-constant to `qval`. They are exactly what `QVal.lean`'s header said it did
-- not do.
-- ============================================================================

theorem qval_interpret_zero_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    qval (Term.interpret si (Term.zero_Q (F := F) (Γ := Δ)) env) = 0 := by
  rw [interpret_zero_Q]; exact qval_zero_code

theorem qval_interpret_one_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    qval (Term.interpret si (Term.one_Q (F := F) (Γ := Δ)) env) = 1 := by
  rw [interpret_one_Q]; exact qval_one_code

theorem qval_interpret_pow2neg_Q {si : SpaceInterp X F} {Δ : Ctx ι} (n : ℕ)
    (env : Ctx.interpret X Δ) :
    qval (Term.interpret si (Term.pow2neg_Q (F := F) (Γ := Δ)) env n) = 1 / 2 ^ n := by
  rw [interpret_pow2neg_Q_fun]; exact qval_pow2neg_code n

/-- `Term.abs_Q` really denotes `|·|` on the rationals. -/
theorem qval_interpret_abs_Q {si : SpaceInterp X F} {Δ : Ctx ι} (n : ℕ)
    (env : Ctx.interpret X Δ) :
    qval (Term.interpret si (Term.abs_Q (F := F) (Γ := Δ)) env n) = |qval n| := by
  rw [interpret_abs_Q_fun, qval_pairN_even, qval_eq_of_parts]
  have hden : (0 : ℚ) < (ratDenN n : ℚ) := by
    have : 0 < ratDenN n := by simp only [ratDenN]; omega
    exact_mod_cast this
  rw [abs_div, abs_of_pos hden]
  congr 1
  · split <;> simp
  · simp only [ratDenN]; push_cast; ring

-- ============================================================================
-- Section 10: interpretation congruence for `eq_R` / `le_R_pu`
--
-- The eventual target of this file is `Formula.interpret` of `eq_R` and
-- `le_R_pu`, and both mention their arguments only as `.weaken`ed terms under a
-- single `∀n`. So their interpretation factors through the *values* of those
-- terms, which is what lets a bridge lemma about the ℕ-level be transported to
-- the formula level.
--
-- These were developed in `Probes/SoundnessProbe.lean` and are hoisted here (not
-- into `Semantics.lean`) so that the core semantics file does not have to import
-- the whole ℚ/ℝ term layer. The probe keeps its own copies; it is not built.
-- ============================================================================

theorem eq_R_interp_congr (si : SpaceInterp X F) {Γ : Ctx ι}
    (f f' g g' : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hf : Term.interpret si f env = Term.interpret si f' env)
    (hg : Term.interpret si g env = Term.interpret si g' env) :
    Formula.interpret si (eq_R f g) env ↔ Formula.interpret si (eq_R f' g') env := by
  have hfw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si f.weaken (n, env) = Term.interpret si f'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hf
  have hgw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si g.weaken (n, env) = Term.interpret si g'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hg
  simp only [eq_R, Formula.interpret, Term.app2, Term.interpret, hfw, hgw]

theorem le_R_pu_interp_congr (si : SpaceInterp X F) {Γ : Ctx ι}
    (f f' g g' : Term F Γ (realTy ι)) (env : Ctx.interpret X Γ)
    (hf : Term.interpret si f env = Term.interpret si f' env)
    (hg : Term.interpret si g env = Term.interpret si g' env) :
    Formula.interpret si (le_R_pu f g) env ↔ Formula.interpret si (le_R_pu f' g') env := by
  have hfw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si f.weaken (n, env) = Term.interpret si f'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hf
  have hgw : ∀ n : Ty.interpret X Ty.nat,
      Term.interpret si g.weaken (n, env) = Term.interpret si g'.weaken (n, env) := by
    intro n; rw [Term.interpret_weaken, Term.interpret_weaken]; exact hg
  simp only [le_R_pu, Formula.interpret, Term.app2, Term.interpret, hfw, hgw]

-- ============================================================================
-- Section 11: S2 — the `qval` semantics of `add_Q`, `sub_Q`, `lt_Q_dec`
--
-- Method unchanged: one constant per unfold, S1 lemmas for the rest. The new
-- ingredient is the round trip through `ratEncodeN`, which is where the
-- encoding's non-injectivity (the sign bit is ignored at numerator `0`) is
-- paid, once, in `qval_ratEncodeN`.
-- ============================================================================

-- ---- Round trips through the encoder ----

@[simp] theorem sndN_ratEncodeN (s p d : ℕ) : sndN (ratEncodeN s p d) = d := by
  simp only [ratEncodeN, sndN_pairN]

@[simp] theorem ratDenN_ratEncodeN (s p d : ℕ) : ratDenN (ratEncodeN s p d) = d + 1 := by
  simp only [ratDenN, ratEncodeN, sndN_pairN]

/-- The numerator round-trips unconditionally — including at `p = 0`, where the truncated
`2·0 − 1 = 0` happens to decode to `0` again. -/
@[simp] theorem ratNumN_ratEncodeN (s p d : ℕ) : ratNumN (ratEncodeN s p d) = p := by
  simp only [ratNumN, ratEncodeN, fstN_pairN, isEvenN]
  omega

/-- The sign round-trips only away from `0` (and only mod 2): `rat_encode` ignores the sign
bit when the numerator is `0`, which is exactly what makes the encoding non-injective. -/
theorem ratSignN_ratEncodeN (s p d : ℕ) (hp : 0 < p) :
    ratSignN (ratEncodeN s p d) = s % 2 := by
  simp only [ratSignN, ratEncodeN, fstN_pairN, isEvenN]
  omega

/-- The degenerate case: an encoded `0` is always non-negative, whatever sign was requested. -/
theorem ratSignN_ratEncodeN_zero (s d : ℕ) : ratSignN (ratEncodeN s 0 d) = 1 := by
  simp only [ratSignN, ratEncodeN, fstN_pairN, isEvenN]
  omega

/-- What the encoder denotes. Unconditional: at `p = 0` both sides are `0`, so the
degenerate sign does not surface at the `qval` level. -/
theorem qval_ratEncodeN (s p d : ℕ) :
    qval (ratEncodeN s p d)
      = (if s % 2 = 1 then (p : ℚ) else -(p : ℚ)) / ((d : ℚ) + 1) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have h0 : 2 * 0 - isEvenN s = 2 * 0 := by simp only [isEvenN]; omega
    simp only [ratEncodeN]
    rw [h0, qval_pairN_even]
    split_ifs <;> norm_num
  · rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · -- sign bit even: the first component is odd, the value negative
      obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      have h0 : 2 * p - isEvenN s = 2 * k + 1 := by simp only [isEvenN]; omega
      simp only [ratEncodeN]
      rw [h0, qval_pairN_odd, if_neg (by omega), hk]
      push_cast
      ring
    · have h0 : 2 * p - isEvenN s = 2 * p := by simp only [isEvenN]; omega
      simp only [ratEncodeN]
      rw [h0, qval_pairN_even, if_pos hs]

-- ---- Small facts about the accessors ----

theorem ratDenN_pos (k : ℕ) : 0 < ratDenN k := Nat.succ_pos _

theorem ratSignN_cases (k : ℕ) : ratSignN k = 0 ∨ ratSignN k = 1 := by
  simp only [ratSignN, isEvenN]; omega

private theorem qval_of_sign_one {k : ℕ} (h : ratSignN k = 1) :
    qval k = (ratNumN k : ℚ) / (ratDenN k : ℚ) := by
  rw [qval_eq_of_parts, if_pos h]

private theorem qval_of_sign_zero {k : ℕ} (h : ratSignN k = 0) :
    qval k = -(ratNumN k : ℚ) / (ratDenN k : ℚ) := by
  rw [qval_eq_of_parts, if_neg (by omega)]

/-- Positivity of the denoted rational, through the parts. This is what turns the
object-level decision `lt_Q_dec` into a statement about `<` on `ℚ`. -/
theorem qval_pos_iff (k : ℕ) : 0 < qval k ↔ ratSignN k = 1 ∧ 0 < ratNumN k := by
  have hden : (0:ℚ) < (ratDenN k : ℚ) := by exact_mod_cast ratDenN_pos k
  rcases ratSignN_cases k with h | h
  · rw [qval_of_sign_zero h]
    constructor
    · intro hpos
      rw [neg_div, lt_neg] at hpos
      have h1 : (0:ℚ) ≤ (ratNumN k : ℚ) / (ratDenN k : ℚ) :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
      exfalso; linarith
    · rintro ⟨h1, -⟩
      omega
  · rw [qval_of_sign_one h]
    constructor
    · intro hpos
      refine ⟨h, ?_⟩
      by_contra h0
      have hz : ratNumN k = 0 := by omega
      rw [hz] at hpos
      norm_num at hpos
    · rintro ⟨-, hp⟩
      exact div_pos (by exact_mod_cast hp) hden

-- ---- The mirror of `Term.add_Q` and its four-branch semantics ----

/-- Mirror of `Term.add_Q`, transcribed clause for clause (`a = p₁·d₂`, `b = p₂·d₁`,
`same = sg_bar |s₁ − s₂|`, `num = ite(same, a+b, |a−b|)`,
`sign = ite(same, s₁, ite(geq(a,b), s₁, s₂))`, `den−1 = d₁·d₂ − 1`). Kept in the exact
shape the interpretation residual takes, so `interpret_add_Q_fun` closes by `rfl`. -/
def addQN (m n : ℕ) : ℕ :=
  ratEncodeN
    (iteN (sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)))
      (ratSignN m)
      (iteN (geqN (ratNumN m * ratDenN n) (ratNumN n * ratDenN m))
        (ratSignN m) (ratSignN n)))
    (iteN (sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)))
      (ratNumN m * ratDenN n + ratNumN n * ratDenN m)
      ((ratNumN m * ratDenN n - ratNumN n * ratDenN m)
        + (ratNumN n * ratDenN m - ratNumN m * ratDenN n)))
    (ratDenN m * ratDenN n - 1)

theorem interpret_add_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.add_Q (F := F) (Γ := Δ)) env = addQN := by
  funext m n
  simp only [Term.add_Q, Term.app2, Term.app3, Term.interpret,
    interpret_rat_sign_fun, interpret_rat_num_fun, interpret_rat_den_fun,
    interpret_mul_fun, interpret_add_fun, interpret_sg_bar_fun,
    interpret_abs_diff_fun, interpret_ite_nat_fun, interpret_geq_fun,
    interpret_rat_encode_fun, interpret_pd_fun']
  rfl

-- The four shapes `addQN` collapses to, one per (sign agreement, magnitude order) branch.

private theorem addQN_same_sign {m n : ℕ} (h : ratSignN m = ratSignN n) :
    addQN m n = ratEncodeN (ratSignN m)
      (ratNumN m * ratDenN n + ratNumN n * ratDenN m) (ratDenN m * ratDenN n - 1) := by
  have h1 : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 1 := by
    simp only [sgBarN]; omega
  simp only [addQN, h1, iteN]
  norm_num

private theorem addQN_pos_neg_ge {m n : ℕ} (h₁ : ratSignN m = 1) (h₂ : ratSignN n = 0)
    (hge : ratNumN n * ratDenN m ≤ ratNumN m * ratDenN n) :
    addQN m n = ratEncodeN 1
      (ratNumN m * ratDenN n - ratNumN n * ratDenN m) (ratDenN m * ratDenN n - 1) := by
  have h1 : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
    simp only [sgBarN]; omega
  have h2 : geqN (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) = 1 := by
    simp only [geqN]; omega
  have h3 : (ratNumN m * ratDenN n - ratNumN n * ratDenN m)
      + (ratNumN n * ratDenN m - ratNumN m * ratDenN n)
      = ratNumN m * ratDenN n - ratNumN n * ratDenN m := by omega
  simp only [addQN, h1, h2, h3, iteN]
  norm_num [h₁]

private theorem addQN_pos_neg_lt {m n : ℕ} (h₁ : ratSignN m = 1) (h₂ : ratSignN n = 0)
    (hlt : ratNumN m * ratDenN n < ratNumN n * ratDenN m) :
    addQN m n = ratEncodeN 0
      (ratNumN n * ratDenN m - ratNumN m * ratDenN n) (ratDenN m * ratDenN n - 1) := by
  have h1 : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
    simp only [sgBarN]; omega
  have h2 : geqN (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) = 0 := by
    simp only [geqN]; omega
  have h3 : (ratNumN m * ratDenN n - ratNumN n * ratDenN m)
      + (ratNumN n * ratDenN m - ratNumN m * ratDenN n)
      = ratNumN n * ratDenN m - ratNumN m * ratDenN n := by omega
  simp only [addQN, h1, h2, h3, iteN]
  norm_num [h₂]

private theorem addQN_neg_pos_ge {m n : ℕ} (h₁ : ratSignN m = 0) (h₂ : ratSignN n = 1)
    (hge : ratNumN n * ratDenN m ≤ ratNumN m * ratDenN n) :
    addQN m n = ratEncodeN 0
      (ratNumN m * ratDenN n - ratNumN n * ratDenN m) (ratDenN m * ratDenN n - 1) := by
  have h1 : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
    simp only [sgBarN]; omega
  have h2 : geqN (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) = 1 := by
    simp only [geqN]; omega
  have h3 : (ratNumN m * ratDenN n - ratNumN n * ratDenN m)
      + (ratNumN n * ratDenN m - ratNumN m * ratDenN n)
      = ratNumN m * ratDenN n - ratNumN n * ratDenN m := by omega
  simp only [addQN, h1, h2, h3, iteN]
  norm_num [h₁]

private theorem addQN_neg_pos_lt {m n : ℕ} (h₁ : ratSignN m = 0) (h₂ : ratSignN n = 1)
    (hlt : ratNumN m * ratDenN n < ratNumN n * ratDenN m) :
    addQN m n = ratEncodeN 1
      (ratNumN n * ratDenN m - ratNumN m * ratDenN n) (ratDenN m * ratDenN n - 1) := by
  have h1 : sgBarN ((ratSignN m - ratSignN n) + (ratSignN n - ratSignN m)) = 0 := by
    simp only [sgBarN]; omega
  have h2 : geqN (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) = 0 := by
    simp only [geqN]; omega
  have h3 : (ratNumN m * ratDenN n - ratNumN n * ratDenN m)
      + (ratNumN n * ratDenN m - ratNumN m * ratDenN n)
      = ratNumN n * ratDenN m - ratNumN m * ratDenN n := by omega
  simp only [addQN, h1, h2, h3, iteN]
  norm_num [h₂]

/-- **The S2 lemma**: `Term.add_Q` really denotes `+` on the rationals. -/
theorem qval_addQN (m n : ℕ) : qval (addQN m n) = qval m + qval n := by
  have hd₁ : 0 < ratDenN m := ratDenN_pos m
  have hd₂ : 0 < ratDenN n := ratDenN_pos n
  have hq₁ : (ratDenN m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq₂ : (ratDenN n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdd : 1 ≤ ratDenN m * ratDenN n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hden : ((ratDenN m * ratDenN n - 1 : ℕ) : ℚ) + 1
      = (ratDenN m : ℚ) * (ratDenN n : ℚ) := by
    push_cast [Nat.cast_sub hdd]
    ring
  rcases ratSignN_cases m with h₁ | h₁ <;> rcases ratSignN_cases n with h₂ | h₂
  · -- both negative
    rw [addQN_same_sign (h₁.trans h₂.symm), h₁, qval_ratEncodeN, hden,
      qval_of_sign_zero h₁, qval_of_sign_zero h₂, if_neg (by norm_num)]
    push_cast
    field_simp
    ring
  · -- m negative, n positive
    rcases Nat.lt_or_ge (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) with hlt | hge
    · rw [addQN_neg_pos_lt h₁ h₂ hlt, qval_ratEncodeN, hden, Nat.cast_sub (le_of_lt hlt),
        qval_of_sign_zero h₁, qval_of_sign_one h₂, if_pos (by norm_num)]
      push_cast
      field_simp
      ring
    · rw [addQN_neg_pos_ge h₁ h₂ hge, qval_ratEncodeN, hden, Nat.cast_sub hge,
        qval_of_sign_zero h₁, qval_of_sign_one h₂, if_neg (by norm_num)]
      push_cast
      field_simp
      ring
  · -- m positive, n negative
    rcases Nat.lt_or_ge (ratNumN m * ratDenN n) (ratNumN n * ratDenN m) with hlt | hge
    · rw [addQN_pos_neg_lt h₁ h₂ hlt, qval_ratEncodeN, hden, Nat.cast_sub (le_of_lt hlt),
        qval_of_sign_one h₁, qval_of_sign_zero h₂, if_neg (by norm_num)]
      push_cast
      field_simp
      ring
    · rw [addQN_pos_neg_ge h₁ h₂ hge, qval_ratEncodeN, hden, Nat.cast_sub hge,
        qval_of_sign_one h₁, qval_of_sign_zero h₂, if_pos (by norm_num)]
      push_cast
      field_simp
      ring
  · -- both positive
    rw [addQN_same_sign (h₁.trans h₂.symm), h₁, qval_ratEncodeN, hden,
      qval_of_sign_one h₁, qval_of_sign_one h₂, if_pos (by norm_num)]
    push_cast
    field_simp

theorem qval_interpret_add_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ)
    (a b : ℕ) :
    qval (Term.interpret si (Term.add_Q (F := F) (Γ := Δ)) env a b) = qval a + qval b := by
  rw [interpret_add_Q_fun]
  exact qval_addQN a b

-- ---- `sub_Q`, by assembly ----

/-- Mirror of `Term.neg_Q` (the RHS of `interpret_neg_Q_fun`, named). -/
def negQN (k : ℕ) : ℕ := ratEncodeN (1 - ratSignN k) (ratNumN k) (sndN k)

theorem interpret_neg_Q_fun' {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.neg_Q (F := F) (Γ := Δ)) env = negQN := by
  rw [interpret_neg_Q_fun]
  rfl

theorem qval_negQN (k : ℕ) : qval (negQN k) = - qval k := by
  have hden : ((sndN k : ℚ) + 1) = (ratDenN k : ℚ) := by
    simp only [ratDenN]; push_cast; ring
  simp only [negQN]
  rw [qval_ratEncodeN, hden]
  rcases ratSignN_cases k with h | h
  · rw [h, qval_of_sign_zero h, if_pos (by norm_num)]
    ring
  · rw [h, qval_of_sign_one h, if_neg (by norm_num)]
    ring

/-- Mirror of `Term.sub_Q`. -/
def subQN (m n : ℕ) : ℕ := addQN m (negQN n)

theorem interpret_sub_Q_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.sub_Q (F := F) (Γ := Δ)) env = subQN := by
  funext m n
  simp only [Term.sub_Q, Term.app2, Term.interpret,
    interpret_add_Q_fun, interpret_neg_Q_fun]
  rfl

theorem qval_subQN (m n : ℕ) : qval (subQN m n) = qval m - qval n := by
  simp only [subQN]
  rw [qval_addQN, qval_negQN]
  ring

theorem qval_interpret_sub_Q {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ)
    (a b : ℕ) :
    qval (Term.interpret si (Term.sub_Q (F := F) (Γ := Δ)) env a b) = qval a - qval b := by
  rw [interpret_sub_Q_fun]
  exact qval_subQN a b

-- ---- `lt_Q_dec`, the payoff ----

/-- Mirror of `Term.lt_Q_dec`: `|sign(d) − 1| + sg_bar(num(d))` with `d = sub_Q n m`. -/
def ltQdecN (m n : ℕ) : ℕ :=
  ((ratSignN (subQN n m) - 1) + (1 - ratSignN (subQN n m)))
    + (1 - ratNumN (subQN n m))

theorem interpret_lt_Q_dec_fun {si : SpaceInterp X F} {Δ : Ctx ι} (env : Ctx.interpret X Δ) :
    Term.interpret si (Term.lt_Q_dec (F := F) (Γ := Δ)) env = ltQdecN := by
  funext m n
  simp only [Term.lt_Q_dec, Term.app2, Term.interpret,
    interpret_add_fun, interpret_abs_diff_fun, interpret_sg_bar_fun,
    interpret_rat_sign_fun, interpret_rat_num_fun, interpret_sub_Q_fun]
  rfl

/-- **The S2 payoff**: the object-level decision term `lt_Q_dec` decides `<` on `ℚ` —
its value is `0` exactly when the first code denotes a rational strictly below the
second's. -/
theorem interpret_lt_Q_dec_eq_zero_iff {si : SpaceInterp X F} {Δ : Ctx ι}
    (env : Ctx.interpret X Δ) (m n : ℕ) :
    Term.interpret si (Term.lt_Q_dec (F := F) (Γ := Δ)) env m n = 0 ↔ qval m < qval n := by
  rw [interpret_lt_Q_dec_fun]
  have hkey : ltQdecN m n = 0
      ↔ (ratSignN (subQN n m) = 1 ∧ 0 < ratNumN (subQN n m)) := by
    simp only [ltQdecN]; omega
  rw [hkey, ← qval_pos_iff, qval_subQN]
  constructor <;> intro h <;> linarith

-- ============================================================================
-- Axiom audit. `Classical.choice` is expected: `invTriagN` is a
-- `Nat.findGreatest`, and `qval` lands in Mathlib's `ℚ`. What matters is the
-- absence of `sorryAx`.
-- ============================================================================

#print axioms interpret_add_fun
#print axioms interpret_monus_fun
#print axioms interpret_triag_fun
#print axioms interpret_inv_triag_fun
#print axioms interpret_fst_pair_fun
#print axioms interpret_snd_pair_fun
#print axioms interpret_div2_fun
#print axioms interpret_rat_num_fun
#print axioms interpret_rat_den_fun
#print axioms interpret_rat_sign_fun
#print axioms interpret_rat_encode_fun
#print axioms qval_eq_of_parts
#print axioms qval_interpret_pow2neg_Q
#print axioms qval_interpret_abs_Q
#print axioms qval_ratEncodeN
#print axioms ratNumN_ratEncodeN
#print axioms ratSignN_ratEncodeN
#print axioms interpret_add_Q_fun
#print axioms qval_addQN
#print axioms qval_interpret_add_Q
#print axioms interpret_sub_Q_fun
#print axioms qval_interpret_sub_Q
#print axioms interpret_lt_Q_dec_fun
#print axioms interpret_lt_Q_dec_eq_zero_iff
#print axioms eq_R_interp_congr
#print axioms le_R_pu_interp_congr
#print axioms Formula.interpret_substF
#print axioms Formula.interpret_subst0

end QBridge

end Metatheorems
