import Mathlib

/-!
# The bridge between ℕ-MCT and ℝ-MCT: `K := 2^k`, and exactly where the off-by-one is

`Reference/MCT.lean` proves the metastable ℝ-MCT with the hand-computed bound
`Φ k g = (shift g)^[2^k + 1] 0`. `Metatheorems/MCTStatement.lean` + `ProofMode/MCT.lean`
prove ℕ-MCT — an antitone `b : ℕ → ℕ` with `b 0 ≤ K` has a flat window `b n = b (n + g n)` —
by a budget descent on `K`. CLAUDE.md (Track A item 4) records the gap: "same combinatorics
with `K` where the real version has `2^k`", meaningful but not literal. This file makes it
literal, at the Mathlib level (not built by `lake build`; check with `lake env lean`).

## What is proved

1. **ℕ-MCT, with its bound** (`nat_mct`, `nat_mct_window`): among the iterates
   `it g 0, …, it g (K+1)` some window `[it g i, it g (i+1)]`, `i ≤ K`, is flat, so the flat
   `n` is `≤ Φℕ K g := it g K = (shift g)^[K] 0`. This is exactly `mct_p2`'s descent
   (`ProofMode/MCT.lean`): `A(k) ≡ b m ≤ k → ∃ flat n`, induction on the budget. **The bound
   is attained** (`nat_mct_attained`): `b n := K − n` with `g ≡ 1` has its first flat window
   at `n = K = Φℕ K (fun _ => 1)`.

2. **The coarsening** (`floorSeq`): `b n := ⌊a n · 2^k⌋₊`. For `a` antitone in `[0,1]` it is
   antitone with `b 0 ≤ 2^k`, and equal floors mean `|a i − a j| < 2^{-k}` — *strictly*.

3. **ℝ-MCT from ℕ-MCT** (`metastable_via_nat`): apply (1) to (2) with **`K := 2^k`**. The
   bound is `Φℕ (2^k) g = it g (2^k)`, and the window is `2^{-k}`-good in the strict sense.

4. **The off-by-one, exactly** (`Φℕ_le_Φ`, `Φℕ_lt_Φ_const_one`): the bridge's bound is one
   iterate *below* the reference's, `it g (2^k) ≤ it g (2^k + 1) = Φ k g`, strictly for
   `g ≡ 1` (`2^k` against `2^k + 1`). So the literal claim "`Φ k g` is ℕ-MCT's bound at
   `K := 2^k`" is **false by one iterate**; the correct identity is `Φℕ (2^k) g = it g (2^k)`,
   and `Reference/MCT.lean`'s `2^k + 1` is slack in *its* proof (its `descent` lemma is
   non-strict, so it needs one extra window to contradict `a ∈ [0,1]`).

5. **Where the slack really is** (`descent_strict`, `metastable_le_sharp`,
   `strict_bound_attained`): the real argument with a strict descent needs only `2^k` windows,
   giving the bound `it g (2^k − 1)` for the **non-strict** conclusion `|a i − a j| ≤ 2^{-k}`.
   For the **strict** conclusion `< 2^{-k}` — which is what the object-level `RealMCT.rmC`
   delivers (`rmC_implies`) — the sharp bound is `it g (2^k)`, attained by
   `a n := (2^k − n)/2^k`, `g ≡ 1`. So the ℕ-bridge bound is *exactly* the sharp bound for
   the strict statement, and the reference's `Φ` is one iterate above both.

Summary, as bounds on the first good `n` for `g ≡ 1` (so `it g m = m`):

| statement | sharp bound | via |
|---|---|---|
| ℕ-MCT, budget `K` | `K` | `nat_mct` / `nat_mct_attained` |
| ℝ-MCT, `\|a i − a j\| < 2^{-k}` | `2^k` | `metastable_via_nat` / `strict_bound_attained` |
| ℝ-MCT, `\|a i − a j\| ≤ 2^{-k}` | `2^k − 1` | `metastable_le_sharp` |
| `Reference/MCT.lean`'s `Φ k g` | `2^k + 1` | one extra window, non-strict `descent` |

`shift`, `it`, `Φ` and the iterate bookkeeping are copied verbatim from `Reference/MCT.lean`
(that file is not importable from here — `Reference/` is not a Lake target).
-/

namespace MCTBridge

open Function

/-- `g̃ n = n + g n` (verbatim `MCT.shift`). -/
def shift (g : ℕ → ℕ) (n : ℕ) : ℕ := n + g n

/-- The iterates `it g i = g̃^i 0` (verbatim `MCT.it`). -/
def it (g : ℕ → ℕ) (i : ℕ) : ℕ := (shift g)^[i] 0

/-- `Reference/MCT.lean`'s bound (verbatim `MCT.Φ`). -/
def Φ (k : ℕ) (g : ℕ → ℕ) : ℕ := (shift g)^[2 ^ k + 1] 0

/-- **The ℕ-MCT bound at budget `K`**: `it g K = (shift g)^[K] 0`. -/
def Φℕ (K : ℕ) (g : ℕ → ℕ) : ℕ := it g K

theorem self_le_shift (g : ℕ → ℕ) (n : ℕ) : n ≤ shift g n := Nat.le_add_right _ _

theorem le_iterate (g : ℕ → ℕ) (m x : ℕ) : x ≤ (shift g)^[m] x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iterate_succ_apply']
      exact ih.trans (self_le_shift g _)

theorem it_mono (g : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) : it g i ≤ it g j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [it, it, Nat.add_comm i d, iterate_add_apply]
  exact le_iterate g d _

theorem it_succ (g : ℕ → ℕ) (i : ℕ) : it g (i + 1) = it g i + g (it g i) := by
  rw [it, it, iterate_succ_apply']
  rfl

theorem it_zero (g : ℕ → ℕ) : it g 0 = 0 := rfl

theorem Φ_eq_it (k : ℕ) (g : ℕ → ℕ) : Φ k g = it g (2 ^ k + 1) := rfl

theorem it_const_one : ∀ m : ℕ, it (fun _ => 1) m = m
  | 0 => rfl
  | m + 1 => by rw [it_succ, it_const_one m]

-- ============================================================================
-- 1. ℕ-MCT: the budget descent, with its bound
-- ============================================================================

/-- If the first `j` windows all strictly drop, `b` has lost at least `j` by `it g j`. -/
theorem drops_le (b : ℕ → ℕ) (g : ℕ → ℕ) : ∀ j : ℕ,
    (∀ i < j, b (it g (i + 1)) < b (it g i)) → b (it g j) + j ≤ b (it g 0)
  | 0 => fun _ => by simp
  | j + 1 => fun h => by
      have ih := drops_le b g j (fun i hi => h i (by omega))
      have hj := h j (by omega)
      omega

/-- **ℕ-MCT, iterate form.** An antitone `b` with `b 0 ≤ K` has a flat window among the
first `K + 1` windows `[it g i, it g (i+1)]`, `i ≤ K`: otherwise `b` drops `K + 1` times from
a value `≤ K`. This is `ProofMode/MCT.lean`'s `mct_descent`, on Mathlib. -/
theorem nat_mct (b : ℕ → ℕ) (hanti : Antitone b) (K : ℕ) (hK : b 0 ≤ K) (g : ℕ → ℕ) :
    ∃ i ≤ K, b (it g i) = b (it g (i + 1)) := by
  by_contra hcon
  push_neg at hcon
  have hdrop : ∀ i < K + 1, b (it g (i + 1)) < b (it g i) := fun i hi =>
    lt_of_le_of_ne (hanti (it_mono g (Nat.le_succ i))) (fun h => hcon i (by omega) h.symm)
  have := drops_le b g (K + 1) hdrop
  rw [it_zero] at this
  omega

/-- **ℕ-MCT with the bound `Φℕ K g = it g K`**: the statement `mctStatement` interprets to,
with an explicit `Φ`. -/
theorem nat_mct_window (b : ℕ → ℕ) (hanti : Antitone b) (K : ℕ) (hK : b 0 ≤ K) (g : ℕ → ℕ) :
    ∃ n ≤ Φℕ K g, b n = b (n + g n) := by
  obtain ⟨i, hi, h⟩ := nat_mct b hanti K hK g
  exact ⟨it g i, it_mono g hi, by rw [← it_succ]; exact h⟩

/-- The ramp `K, K−1, …, 1, 0, 0, …`. -/
def ramp (K : ℕ) (n : ℕ) : ℕ := K - n

theorem ramp_antitone (K : ℕ) : Antitone (ramp K) := fun _ _ hij => Nat.sub_le_sub_left hij K

/-- **The ℕ-MCT bound is attained**: for `b := ramp K`, `g ≡ 1`, no window before `n = K`
is flat, and `K = Φℕ K (fun _ => 1)`. -/
theorem nat_mct_attained (K : ℕ) :
    ramp K 0 ≤ K ∧ (∀ n < K, ramp K n ≠ ramp K (n + 1)) ∧ Φℕ K (fun _ => 1) = K := by
  refine ⟨by simp [ramp], fun n hn => ?_, it_const_one K⟩
  simp only [ramp]; omega

-- ============================================================================
-- 2. The coarsening `⌊a n · 2^k⌋₊`
-- ============================================================================

/-- `b n := ⌊a n · 2^k⌋₊` — the ℕ-valued shadow of `a` at precision `k`. -/
noncomputable def floorSeq (k : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℕ := ⌊a n * 2 ^ k⌋₊

theorem floorSeq_antitone (k : ℕ) (a : ℕ → ℝ) (hanti : Antitone a) :
    Antitone (floorSeq k a) := fun _ _ hij =>
  Nat.floor_mono (mul_le_mul_of_nonneg_right (hanti hij) (by positivity))

/-- The budget: `a 0 ≤ 1` gives `b 0 ≤ 2^k` — **this is `K := 2^k`**. -/
theorem floorSeq_zero_le (k : ℕ) (a : ℕ → ℝ) (hub : a 0 ≤ 1) : floorSeq k a 0 ≤ 2 ^ k := by
  unfold floorSeq
  apply Nat.floor_le_of_le
  calc a 0 * 2 ^ k ≤ 1 * 2 ^ k := mul_le_mul_of_nonneg_right hub (by positivity)
    _ = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring

theorem abs_sub_lt_of_floor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ⌊x⌋₊ = ⌊y⌋₊) :
    |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]
  constructor <;> linarith

/-- Equal floors at precision `k` mean `|a p − a q| < 2^{-k}`, strictly. -/
theorem abs_sub_lt_of_floorSeq_eq (k : ℕ) (a : ℕ → ℝ) (hlb : ∀ n, 0 ≤ a n) {p q : ℕ}
    (h : floorSeq k a p = floorSeq k a q) : |a p - a q| < 1 / 2 ^ k := by
  have h1 := abs_sub_lt_of_floor_eq (mul_nonneg (hlb p) (by positivity))
    (mul_nonneg (hlb q) (by positivity)) h
  rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)] at h1
  rwa [lt_div_iff₀ (by positivity)]

-- ============================================================================
-- 3. ℝ-MCT from ℕ-MCT at `K := 2^k`
-- ============================================================================

/-- **The bridge.** `Reference/MCT.lean`'s `metastable`, obtained from ℕ-MCT applied to
`⌊a · 2^k⌋₊` with budget `K := 2^k`. The bound is `Φℕ (2^k) g = (shift g)^[2^k] 0` — one
iterate below the reference's `Φ k g` — and the conclusion is strict. -/
theorem metastable_via_nat (a : ℕ → ℝ) (hanti : Antitone a) (hlb : ∀ n, 0 ≤ a n)
    (hub : a 0 ≤ 1) (k : ℕ) (g : ℕ → ℕ) :
    ∃ n ≤ Φℕ (2 ^ k) g, ∀ i, n ≤ i → i ≤ n + g n → ∀ j, n ≤ j → j ≤ n + g n →
      |a i - a j| < (1 : ℝ) / 2 ^ k := by
  have hb := floorSeq_antitone k a hanti
  obtain ⟨i, hi, hflat⟩ := nat_mct (floorSeq k a) hb (2 ^ k) (floorSeq_zero_le k a hub) g
  refine ⟨it g i, it_mono g hi, ?_⟩
  intro p hp1 hp2 q hq1 hq2
  rw [← it_succ] at hp2 hq2
  have hp : floorSeq k a p = floorSeq k a (it g i) :=
    le_antisymm (hb hp1) (by rw [hflat]; exact hb hp2)
  have hq : floorSeq k a q = floorSeq k a (it g i) :=
    le_antisymm (hb hq1) (by rw [hflat]; exact hb hq2)
  exact abs_sub_lt_of_floorSeq_eq k a hlb (hp.trans hq.symm)

-- ============================================================================
-- 4. The off-by-one against `Reference/MCT.lean`
-- ============================================================================

/-- The bridge's bound never exceeds the reference's. -/
theorem Φℕ_le_Φ (k : ℕ) (g : ℕ → ℕ) : Φℕ (2 ^ k) g ≤ Φ k g :=
  it_mono g (Nat.le_succ _)

/-- …and is strictly below it for `g ≡ 1`: `2^k` against `2^k + 1`. So `Φ k g` is **not**
ℕ-MCT's bound at `K := 2^k`; `it g (2^k)` is. -/
theorem Φℕ_lt_Φ_const_one (k : ℕ) : Φℕ (2 ^ k) (fun _ => 1) < Φ k (fun _ => 1) := by
  show it _ (2 ^ k) < it _ (2 ^ k + 1)
  rw [it_const_one, it_const_one]
  omega

example : Φℕ (2 ^ 3) (fun _ => 1) = 8 ∧ Φ 3 (fun _ => 1) = 9 := by decide

-- ============================================================================
-- 5. Where the reference's slack is: strict descent, and both sharp bounds
-- ============================================================================

/-- Strict descent: `N ≥ 1` windows each dropping by more than `ε` lose more than `N·ε`.
(`Reference/MCT.lean`'s `descent` concludes `≤`, which is why it needs `2^k + 1` windows.) -/
theorem descent_strict (a : ℕ → ℝ) (g : ℕ → ℕ) (ε : ℝ) :
    ∀ N : ℕ, 0 < N → (∀ i < N, ε < a (it g i) - a (it g (i + 1))) →
      (N : ℝ) * ε < a (it g 0) - a (it g N)
  | 0 => fun h => absurd h (lt_irrefl 0)
  | N + 1 => fun _ h => by
      have hstep : ε < a (it g N) - a (it g (N + 1)) := h N (Nat.lt_succ_self N)
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simpa using hstep
      · have ih := descent_strict a g ε N hN (fun i hi => h i (hi.trans (Nat.lt_succ_self N)))
        push_cast
        linarith

/-- **The sharp bound for the non-strict conclusion** `|a i − a j| ≤ 2^{-k}`: `it g (2^k − 1)`,
one below the bridge's and two below the reference's. Only `2^k` windows are needed, because
`2^k` strict drops by more than `2^{-k}` would exceed the total descent `1`. -/
theorem metastable_le_sharp (a : ℕ → ℝ) (hanti : Antitone a) (hlb : ∀ n, 0 ≤ a n)
    (hub : a 0 ≤ 1) (k : ℕ) (g : ℕ → ℕ) :
    ∃ n ≤ it g (2 ^ k - 1), ∀ i, n ≤ i → i ≤ n + g n → ∀ j, n ≤ j → j ≤ n + g n →
      |a i - a j| ≤ (1 : ℝ) / 2 ^ k := by
  set ε : ℝ := (1 : ℝ) / 2 ^ k with hε
  have hgood : ∃ i < 2 ^ k, a (it g i) - a (it g (i + 1)) ≤ ε := by
    by_contra hcon
    push_neg at hcon
    have hd := descent_strict a g ε (2 ^ k) (by positivity) hcon
    have h1 : a (it g 0) ≤ 1 := by rw [it_zero]; exact hub
    have h2 : (0 : ℝ) ≤ a (it g (2 ^ k)) := hlb _
    have hprod : ((2 ^ k : ℕ) : ℝ) * ε = 1 := by
      rw [hε]; push_cast; field_simp
    linarith
  obtain ⟨i, hilt, higood⟩ := hgood
  refine ⟨it g i, it_mono g (by omega), ?_⟩
  intro p hp1 hp2 q hq1 hq2
  rw [← it_succ] at hp2 hq2
  have hple : a (it g (i + 1)) ≤ a p := hanti hp2
  have hqle : a (it g (i + 1)) ≤ a q := hanti hq2
  have hpge : a p ≤ a (it g i) := hanti hp1
  have hqge : a q ≤ a (it g i) := hanti hq1
  rw [abs_le]
  constructor <;> linarith

/-- The real ramp `1, 1 − 2^{-k}, …, 2^{-k}, 0, 0, …`. -/
noncomputable def rampR (k : ℕ) (n : ℕ) : ℝ := ((2 ^ k - n : ℕ) : ℝ) / 2 ^ k

/-- **The strict bound `it g (2^k)` is attained**: for `rampR k` and `g ≡ 1`, every window
before `n = 2^k` drops by exactly `2^{-k}`, so none is `< 2^{-k}`-good. Together with
`metastable_via_nat` this makes `Φℕ (2^k) g` the sharp bound for the strict conclusion — the
one `Metatheorems/RealMCTStatement.lean`'s `rmC` delivers. -/
theorem strict_bound_attained (k : ℕ) :
    Antitone (rampR k) ∧ (∀ n, 0 ≤ rampR k n) ∧ rampR k 0 ≤ 1 ∧
      ∀ n < 2 ^ k, ¬ (|rampR k n - rampR k (n + 1)| < (1 : ℝ) / 2 ^ k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    unfold rampR
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le_sub_left hij (2 ^ k)
  · intro n; unfold rampR; positivity
  · unfold rampR
    rw [div_le_one (by positivity)]
    simp
  · intro n hn
    unfold rampR
    have e : ((2 ^ k - n : ℕ) : ℝ) - ((2 ^ k - (n + 1) : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [← sub_div, e, abs_of_pos (by positivity)]
    exact lt_irrefl _

end MCTBridge
