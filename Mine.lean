import Mathlib

/-!
# Bound extraction by composition

A `Bnd Q` is a bound together with its verification. Each combinator corresponds to a proof
rule and **derives** its bound from its inputs — no combinator takes a bound as an argument.

* `Bnd.witness` / `CBnd.witness` — ∃-introduction. Bound := the supplied witness.
* `CBnd.apply` — apply an established bound at a shifted parameter. Bound := precomposition.
* `Bnd.cases`  — case split. Bound := `max` of the branch bounds.
* `Bnd.recN`   — induction on ℕ. Bound := primitive recursion.

What the user writes is proof content only: *which* witness, and *where* the induction
hypothesis is applied. The bound is whatever the composition produces, it appears nowhere in
the proof, and because everything is data rather than `Prop`, it computes — see the `#eval`s.

Smoke test: the ℕ form of metastable monotone convergence.
-/

namespace Mine

/-- A bound for `Q` with its verification. `Q m n` reads: `n` is good for parameter `m`. -/
structure Bnd (Q : ℕ → ℕ → Prop) where
  bound : ℕ → ℕ
  verified : ∀ m, ∃ n ≤ bound m, Q m n

/-- A bound verified only where `P` holds — the branches of a case split. -/
structure CBnd (P : ℕ → Prop) (Q : ℕ → ℕ → Prop) where
  bound : ℕ → ℕ
  verified : ∀ m, P m → ∃ n ≤ bound m, Q m n

/-- ∃-introduction. The bound is the witness. -/
def Bnd.witness {Q : ℕ → ℕ → Prop} (t : ℕ → ℕ) (h : ∀ m, Q m (t m)) : Bnd Q :=
  ⟨t, fun m => ⟨t m, le_rfl, h m⟩⟩

/-- ∃-introduction under a hypothesis. -/
def CBnd.witness {P : ℕ → Prop} {Q : ℕ → ℕ → Prop} (t : ℕ → ℕ)
    (h : ∀ m, P m → Q m (t m)) : CBnd P Q :=
  ⟨t, fun m hp => ⟨t m, le_rfl, h m hp⟩⟩

/-- Apply an established bound at a shifted parameter `f m` — this is how an induction
hypothesis gets used. The bound is `b.bound ∘ f`, *derived*, not supplied. -/
def CBnd.apply {P : ℕ → Prop} {Q Q' : ℕ → ℕ → Prop} (b : Bnd Q) (f : ℕ → ℕ)
    (h : ∀ m n, P m → Q (f m) n → Q' m n) : CBnd P Q' :=
  ⟨fun m => b.bound (f m), fun m hp => by
    obtain ⟨n, hn, hq⟩ := b.verified (f m)
    exact ⟨n, hn, h m n hp hq⟩⟩

/-- Case split. The bound is the `max` of the two branch bounds: at the split neither branch
is known to dominate. This is where every `max` in an extracted bound originates, and what a
human later removes by a monotonicity argument. -/
def Bnd.cases {P : ℕ → Prop} {Q : ℕ → ℕ → Prop}
    (h₁ : CBnd P Q) (h₂ : CBnd (fun m => ¬ P m) Q) : Bnd Q :=
  ⟨fun m => max (h₁.bound m) (h₂.bound m), fun m => by
    rcases Classical.em (P m) with h | h
    · obtain ⟨n, hn, hq⟩ := h₁.verified m h
      exact ⟨n, hn.trans (le_max_left _ _), hq⟩
    · obtain ⟨n, hn, hq⟩ := h₂.verified m h
      exact ⟨n, hn.trans (le_max_right _ _), hq⟩⟩

/-- Induction on ℕ. The bound is a primitive recursion over the base and step bounds. -/
def Bnd.recN {Q : ℕ → ℕ → ℕ → Prop} (h0 : Bnd (Q 0))
    (hs : ∀ K, Bnd (Q K) → Bnd (Q (K + 1))) : ∀ K, Bnd (Q K) :=
  fun K => Nat.rec h0 hs K

/-! ## Smoke test

`a` nonincreasing with `a m ≤ K` can drop at most `K` times, so some window `[n, n + g n]`
is flat. -/

section

variable (g a : ℕ → ℕ)

/-- The predicate being mined. -/
abbrev Flat (K m n : ℕ) : Prop := a m ≤ K → a n = a (n + g n)

def mct (hanti : Antitone a) : ∀ K, Bnd (Flat g a K) :=
  Bnd.recN
    -- base: `a m ≤ 0` forces `a m = 0`, and the sequence cannot rise. Witness: `m`.
    (Bnd.witness (fun m => m) (fun m h0 => by
      change a m = a (m + g m)
      have h2 : a (m + g m) ≤ a m := hanti (Nat.le_add_right _ _)
      omega))
    (fun K ih =>
      Bnd.cases (P := fun m => a m = a (m + g m))
        -- flat already: witness `m`
        (CBnd.witness (fun m => m) (fun m hEq _ => hEq))
        -- otherwise the value drops, so apply the IH at `m + g m`
        (CBnd.apply ih (fun m => m + g m) (fun m n hNe hq hK => by
          refine hq ?_
          change a (m + g m) ≤ K
          have h2 : a (m + g m) ≤ a m := hanti (Nat.le_add_right _ _)
          omega)))

end

/-! ## The extracted bound

Nothing above names a bound. `(mct g a hanti K).bound` mentions only `g` — the sequence is
not in scope, so uniformity is enforced by the elaborator rather than proved. And it computes. -/

def dummy : ℕ → ℕ := fun _ => 0

theorem dummy_anti : Antitone dummy := fun _ _ _ => le_rfl

#eval (mct (fun _ => 1) dummy dummy_anti 5).bound 0     -- 5
#eval (mct (fun n => n + 1) dummy dummy_anti 5).bound 0  -- 31  = 2^5 - 1
#eval (mct (fun n => n + 1) dummy dummy_anti 8).bound 0  -- 255 = 2^8 - 1

/-! ## Tier 2: the ℚ-valued case

Same three combinators, unchanged. Only the predicate and the side conditions differ: induct
on the number of remaining `2^(-k)`-sized drops rather than on the value bound. -/

section Rat

variable (g : ℕ → ℕ) (b : ℕ → ℚ)

/-- `K` drops of size `2^(-k)` still available at `m` ⟹ some window is `2^(-k)`-flat. -/
abbrev FlatQ (k K m n : ℕ) : Prop :=
  b m ≤ (K : ℚ) * (1 / 2 ^ k) → b n - b (n + g n) ≤ 1 / 2 ^ k

def mctQ (hanti : Antitone b) (hlb : ∀ n, 0 ≤ b n) (k : ℕ) :
    ∀ K, Bnd (FlatQ g b k K) :=
  Bnd.recN
    -- base: no drops left, so `b m ≤ 0`; the sequence is ≥ 0, so the window is flat
    (Bnd.witness (fun m => m) (fun m h0 => by
      change b m - b (m + g m) ≤ 1 / 2 ^ k
      have hb : (0 : ℚ) ≤ b (m + g m) := hlb _
      have hpos : (0 : ℚ) < 1 / 2 ^ k := by positivity
      push_cast at h0
      linarith))
    (fun K ih =>
      Bnd.cases (P := fun m => b m - b (m + g m) ≤ 1 / 2 ^ k)
        -- already flat: witness `m`
        (CBnd.witness (fun m => m) (fun m hFlat _ => hFlat))
        -- otherwise the value drops by more than `2^(-k)`, so one fewer drop remains
        (CBnd.apply ih (fun m => m + g m) (fun m n hNot hq hK => by
          refine hq ?_
          change b (m + g m) ≤ (K : ℚ) * (1 / 2 ^ k)
          push_cast at hK
          push_neg at hNot
          linarith)))

/-- **The mined theorem.** `b 0 ≤ 1` means `2^k` drops are available, so instantiate `K := 2^k`.
The bound depends only on `g` and `k`.

The recursion above establishes only the *one-sided* difference `b n - b (n + g n) ≤ 2^(-k)`,
and needs no monotonicity to do so. Monotonicity enters exactly here, to upgrade that to the
Cauchy condition on the whole window — which is what makes this the metastable form of monotone
convergence rather than a statement about forward differences. -/
theorem metastableQ (hanti : Antitone b) (hlb : ∀ n, 0 ≤ b n) (hub : b 0 ≤ 1) (k : ℕ) :
    ∃ n ≤ (mctQ g b hanti hlb k (2 ^ k)).bound 0,
      ∀ i j, n ≤ i → i ≤ n + g n → n ≤ j → j ≤ n + g n → |b i - b j| ≤ 1 / 2 ^ k := by
  obtain ⟨n, hn, hq⟩ := (mctQ g b hanti hlb k (2 ^ k)).verified 0
  have hstep : b n - b (n + g n) ≤ 1 / 2 ^ k := by
    refine hq ?_
    have hpos : (0 : ℚ) < 2 ^ k := by positivity
    push_cast
    field_simp
    exact hub
  refine ⟨n, hn, fun i j hi1 hi2 hj1 hj2 => ?_⟩
  have hi_hi : b i ≤ b n := hanti hi1
  have hi_lo : b (n + g n) ≤ b i := hanti hi2
  have hj_hi : b j ≤ b n := hanti hj1
  have hj_lo : b (n + g n) ≤ b j := hanti hj2
  rw [abs_le]
  constructor <;> linarith

end Rat

/-! The extracted ℚ bound, again mentioning only `g` and `k`. -/

def dummyQ : ℕ → ℚ := fun _ => 0

theorem dummyQ_anti : Antitone dummyQ := fun _ _ _ => le_rfl

theorem dummyQ_lb : ∀ n, (0 : ℚ) ≤ dummyQ n := fun _ => le_rfl

#eval (mctQ (fun n => n + 1) dummyQ dummyQ_anti dummyQ_lb 3 (2 ^ 3)).bound 0  -- 255
#eval (mctQ (fun _ => 1) dummyQ dummyQ_anti dummyQ_lb 4 (2 ^ 4)).bound 0      -- 16

end Mine
