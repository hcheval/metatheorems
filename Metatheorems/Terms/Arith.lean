/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Term

namespace Metatheorems

/-!
# Arithmetic term definitions

The `Term`-level arithmetic of WE-HA^ω: pure `Term` constructions, below `eqAtType` and
`Derivable` in the import order. The proofs about them are in `Arithmetic.lean`. All terms
are polymorphic in the ambient context `Γ`.
-/

variable {ι κ : Type} {F : κ → Ty ι}

namespace Term

/-- Co-sign: sḡ(0) = 1, sḡ(Sn) = 0.
    sḡ = λx. R (S0) (λr k. 0) x
    Used to encode implication in the QF decision function. -/
def sg_bar {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      (.app .succ .zero)                      -- y = S0 = 1
      (Term.lam (Term.lam .zero))             -- z = λr k. 0
      (.var .vz))                             -- x

/-- Predecessor: pd(0) = 0, pd(Sn) = n.
    pd = λx. R 0 (λr k. k) x
    The step z(r, k) = k returns the current counter, not the recursive result. -/
def pd {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat) :=
  Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                   -- y = 0
      (Term.lam (Term.lam (.var .vz)))        -- z = λr k. k  (k = var vz, r = var (vs vz))
      (.var .vz))                             -- x

/-- Addition: x + 0 = x, x + Sn = S(x + n).
    add = λx. λn. R x (λr k. Sr) n -/
def add {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      (.var (.vs .vz))                        -- y = x  (position 1 in [n, x])
      (Term.lam (Term.lam                     -- z = λr k. Sr  (r = vs vz, k = vz)
        (.app .succ (.var (.vs .vz)))))
      (.var .vz)))                            -- n  (position 0 in [n, x])

/-- Multiplication: x · 0 = 0, x · Sn = (x · n) + x.
    mul = λx. λn. R 0 (λr k. add r x) n -/
def mul {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      .zero                                   -- y = 0
      (Term.lam (Term.lam                     -- z = λr k. add r x
        (Term.app2 Term.add
          (.var (.vs .vz))                    --   r  (position 1 in [k, r, n, x])
          (.var (.vs (.vs (.vs .vz)))))))     --   x  (position 3 in [k, r, n, x])
      (.var .vz)))                            -- n  (position 0 in [n, x])

/-- Truncated subtraction (monus): x ∸ 0 = x, x ∸ Sn = pd(x ∸ n).
    monus = λx. λn. R x (λr k. pd r) n -/
def monus {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app3 (.prec Ty.nat)
      (.var (.vs .vz))                        -- y = x  (position 1 in [n, x])
      (Term.lam (Term.lam                     -- z = λr k. pd r
        (.app Term.pd (.var (.vs .vz)))))     --   pd r  (r = var (vs vz) in [k, r, n, x])
      (.var .vz)))                            -- n

/-- Absolute difference: |x − y| = (x ∸ y) + (y ∸ x).
    abs_diff = λx. λy. add (monus x y) (monus y x) -/
def abs_diff {Γ : Ctx ι} : Term F Γ (Ty.nat →ₜ Ty.nat →ₜ Ty.nat) :=
  Term.lam (Term.lam
    (Term.app2 Term.add
      (Term.app2 Term.monus (.var (.vs .vz)) (.var .vz))  -- monus x y  (x = vs vz, y = vz)
      (Term.app2 Term.monus (.var .vz) (.var (.vs .vz))))) -- monus y x

end Term

end Metatheorems
