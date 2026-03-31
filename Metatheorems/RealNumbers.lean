/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Language

namespace Metatheorems

/-!
# Real Numbers in WE-HA^{omega}

Real numbers are encoded as rapidly converging Cauchy sequences of rationals.
Following Kohlenbach, the type of reals is `1 = 0 → 0` (functions ℕ → ℕ),
where the natural number `x(n)` encodes a rational approximation to within 2^{-n}.

This file defines:
* The type-level representation of ℝ
* The embedding `(·)_ℝ : ℕ → ℝ` and rounding `(·)_∘ : ℝ → ℕ`
* Equality `=_ℝ` and ordering `≤_ℝ` as formulas
* Basic arithmetic operations (+, ×, etc.) as terms

The exact rational encoding (pairing naturals) is left abstract for now.
-/

/-- The type of real numbers: type level 1 = ℕ → ℕ.
    A real `x : ℝₜ` is a function where `x(n)` encodes a rational
    approximation of the real value to within 2^{-n}. -/
abbrev realTy (ι : Type) : Ty ι := Ty.nat →ₜ Ty.nat

-- TODO: Define the rational coding and real number operations:
-- * Rational encoding: pair of naturals (p, q) representing p/q
-- * Embedding (·)_ℝ : ℕ → ℝₜ (constant sequence)
-- * Rounding (·)_∘ : ℝₜ → ℕ (ceiling function)
-- * Real equality: =_ℝ as a Formula (∀k. |x(k) - y(k)| ≤ 2^{1-k})
-- * Real ordering: ≤_ℝ as a Formula
-- * Arithmetic: +_ℝ, ×_ℝ as Terms

end Metatheorems
