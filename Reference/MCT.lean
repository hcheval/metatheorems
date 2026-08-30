import Mathlib

/-!
# Monotone convergence, before and after proof mining

Two proofs of the same underlying fact, written side by side:

* **Part 1** — the textbook statement and proof. A bounded nonincreasing sequence of
  reals converges; the Cauchy property follows. The witness `n` is produced from an
  infimum and is not computable from the data.

* **Part 2** — the proof-mining statement and proof, done by hand exactly as one would
  on paper. The classical Cauchy property is replaced by its metastable (Herbrandised)
  form, and the witness is bounded by an explicit, computable, *uniform* `Φ`.

The point of putting them in one file is the contrast between `cauchy` and `metastable`:
same hypotheses, same mathematical content, but the second one carries a number you can
`#eval`, and its bound does not mention the sequence `a` at all.
-/

namespace MCT

open Function

/-! ## Part 1 — the textbook theorem -/

section Textbook

variable (a : ℕ → ℝ)

/-- A bounded nonincreasing sequence of reals converges. -/
theorem textbook (hanti : Antitone a) (hlb : ∀ n, 0 ≤ a n) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro x ⟨n, rfl⟩; exact hlb n⟩⟩

/-- The Cauchy property, in the form that proof mining takes as input.

Note where the ineffectivity sits: `n` is extracted from the infimum `⨅ i, a i` by a
`by_contra`, so nothing about the proof tells you how large `n` has to be. -/
theorem cauchy (hanti : Antitone a) (hlb : ∀ n, 0 ≤ a n) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i ≥ n, ∀ j ≥ n, |a i - a j| ≤ ε := by
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro x ⟨n, rfl⟩; exact hlb n⟩
  have hex : ∃ n, a n < (⨅ i, a i) + ε := by
    by_contra h
    push_neg at h
    have : (⨅ i, a i) + ε ≤ ⨅ i, a i := le_ciInf h
    linarith
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, fun i hi j hj => ?_⟩
  have hLi : (⨅ i, a i) ≤ a i := ciInf_le hbdd i
  have hLj : (⨅ i, a i) ≤ a j := ciInf_le hbdd j
  have hin : a i ≤ a n := hanti hi
  have hjn : a j ≤ a n := hanti hj
  rw [abs_le]
  constructor <;> linarith

end Textbook

/-! ## Part 2 — the mined theorem

The classical statement `∀ε ∃n ∀i,j ≥ n …` is replaced by its metastable form: for every
counterfunction `g`, the Cauchy condition holds on *some* window `[n, n + g n]` with
`n` bounded explicitly. The two are classically equivalent, but only the second has a
bound, and the bound is uniform in `a`. -/

section Mined

/-- The counterfunction shift, `g̃ n = n + g n`. -/
def shift (g : ℕ → ℕ) (n : ℕ) : ℕ := n + g n

/-- The iterates `n₀ = 0`, `nᵢ₊₁ = g̃ nᵢ`. -/
def it (g : ℕ → ℕ) (i : ℕ) : ℕ := (shift g)^[i] 0

/-- **The extracted bound.** Note what it does *not* mention: the sequence. -/
def Φ (k : ℕ) (g : ℕ → ℕ) : ℕ := (shift g)^[2 ^ k + 1] 0

example : Φ 3 (fun n => n + 1) = 511 := by decide

/-! ### Bookkeeping about the iterates -/

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

/-! ### The counting argument

If every one of the first `N` windows drops by more than `ε`, the total descent is at
least `N * ε`. Since the sequence lives in `[0, a 0]`, that caps `N`. -/

theorem descent (a : ℕ → ℝ) (g : ℕ → ℕ) (ε : ℝ) :
    ∀ N : ℕ, (∀ i < N, ε < a (it g i) - a (it g (i + 1))) →
      (N : ℝ) * ε ≤ a (it g 0) - a (it g N) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      intro h
      have hN : (N : ℝ) * ε ≤ a (it g 0) - a (it g N) :=
        ih fun i hi => h i (hi.trans (Nat.lt_succ_self N))
      have hstep : ε < a (it g N) - a (it g (N + 1)) := h N (Nat.lt_succ_self N)
      push_cast
      linarith

/-- **The mined theorem.** For every counterfunction `g` there is an `n` below the
explicit bound `Φ k g` on whose window `[n, n + g n]` the sequence is `2^(-k)`-Cauchy. -/
theorem metastable (a : ℕ → ℝ) (hanti : Antitone a) (hlb : ∀ n, 0 ≤ a n) (hub : a 0 ≤ 1)
    (k : ℕ) (g : ℕ → ℕ) :
    ∃ n ≤ Φ k g, ∀ i, n ≤ i → i ≤ n + g n → ∀ j, n ≤ j → j ≤ n + g n →
      |a i - a j| ≤ (1 : ℝ) / 2 ^ k := by
  set ε : ℝ := (1 : ℝ) / 2 ^ k with hε
  have hεpos : 0 < ε := by positivity
  -- Some window among the first `2^k + 1` must fail to drop by more than `ε`.
  have hgood : ∃ i < 2 ^ k + 1, a (it g i) - a (it g (i + 1)) ≤ ε := by
    by_contra hcon
    push_neg at hcon
    have hdesc := descent a g ε (2 ^ k + 1) hcon
    have h1 : a (it g 0) ≤ 1 := by simpa [it] using hub
    have h2 : (0 : ℝ) ≤ a (it g (2 ^ k + 1)) := hlb _
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hkey : ((2 ^ k + 1 : ℕ) : ℝ) * ε ≤ 1 := by linarith
    rw [hε] at hkey
    push_cast at hkey
    rw [div_eq_mul_inv, ← mul_assoc] at hkey
    -- (2^k + 1) * (1/2^k) ≤ 1  is false
    have : (2 : ℝ) ^ k + 1 ≤ 2 ^ k := by
      have := (mul_inv_le_iff₀ hpow).mp (by simpa [mul_comm] using hkey)
      linarith [this]
    linarith
  obtain ⟨i, hilt, higood⟩ := hgood
  refine ⟨it g i, ?_, ?_⟩
  · exact it_mono g hilt.le
  · intro p hp1 hp2 q hq1 hq2
    rw [← it_succ] at hp2 hq2
    have hple : a (it g (i + 1)) ≤ a p := hanti hp2
    have hqle : a (it g (i + 1)) ≤ a q := hanti hq2
    have hpge : a p ≤ a (it g i) := hanti hp1
    have hqge : a q ≤ a (it g i) := hanti hq1
    rw [abs_le]
    constructor <;> linarith

end Mined

end MCT
