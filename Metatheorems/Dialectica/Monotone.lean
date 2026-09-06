/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Syntactic

/-!
# The monotone functional interpretation (Kohlenbach, *Applied Proof Theory*, Thm 9.1)

`monotone_soundness` computes, by recursion on a derivation, a **majorant of a Dialectica
realizer** as a semantic value at the hat type, with the realizer itself only existentially
quantified — the book's

    (+)  ∃x (t* maj x ∧ ∀a,y A_D(x a, y, a))

with `t*` the extracted datum and `x` a functional of the free variables `a`. The design and
the measurements behind it are in `ARCHITECTURE.md` §14 and `Probes/MonotoneSpike.lean`
(gate G0); this module is the spike's nine-constructor recursion completed to every
constructor of `Derivable`, with no fallback.

## The statement (`MRealizer`)

`termMajorizer_maj`'s statement one level up, over the derivation:

* the majorant `tstar : ℕ → hat-env → hat-witness` is the data;
* `∃ x : env → 𝕎 A` — **hoisted outside the environment quantifier**, the book's `x a`
  exactly; the per-environment form is a corollary (`MRealizer.pointwise`) and is *not*
  closable at `forall_rule` (see the spike's header);
* `MajEnv` majorization of `x` by `tstar`, correctness of `x` at every counter, and
  self-majorization of `tstar` in its hat environment (what `arrow_intro`'s second clause
  needs).

## Strategy per constructor — the book's own division of labour (p. 142–144)

* **leaf** (Howard, p. 142) — `premise`, `or_weak`, `and_weak`, `and_perm`, `exfalso`,
  `forall_ax`, `exist_ax`, `succ_ne_zero`, `succ_inj`, `beta_eq`, `pair_fst/snd/eta`,
  `rec_zero`, `rec_succ`, `dist_self/comm/tri`, `refl0`, `sym0`, `trans0`, `markov`, `ip`,
  `ac`, `qfac`: `termMajorizer` of the axiom's own realizing term (`ofSRealizer`) — these
  are fixed-size combinators.
* **max** (p. 143, cases 1–3) — `and_contract`, `or_contract`, `or_perm`: `maxT` on the
  counter (resp. witness / flag); no matrix branching, no term.
* **composition, hand-written** (p. 144, cases 5–6) — `mp`, `syllogism`, `exportation`,
  `forall_rule`: the spike's, verbatim — the realizer's λ-term on the hat side, with
  `arrow_intro` discharged from the IH.
* **composition, via the usual λ-terms** (p. 144, case 6) — `importation`, `expansion`,
  `exist_rule`, `univ_gen`, `qfer`, `induction`: `termMajorizer` of the usual
  interpretation's combinator applied to a **variable** standing for the sub-realizer
  (`plug1`/`plug2`/`plugAll`); majorization is `termMajorizer_maj` with the sub-majorant in
  the environment.

The last row is the book's *"the monotone functional interpretation of the remaining
logical rules uses the λ-terms of the usual functional interpretation since they preserve
majorizability"* taken literally: the combinator is a fixed-size closed-shape `Term`, and
the sub-realizer enters it through `Ctx.lookupHat` of the environment, never as a term. So
the composed realizer term — the object whose `Term.weaken`/`Eq.rec` traffic stalled the
term route (`SizeProbe`) — is never built; only the per-node combinator is reduced, which is
the same cost class as the leaf cases.

**`induction`** is the book's `t^M` (p. 144 case 7): `termMajorizer` of `Term.prec` is
`cm.precM`, which in every instance in the tree is `recMaj` — the recursion with a running
`maxT`. It is obtained here by the last row, not by the leaf strategy on the whole
sub-derivation; the sub-realizers of base and step are variables. Lane B (ARCHITECTURE
§14.5) may still want to review this case by hand; what it computes is `t^M` already.
-/

namespace Metatheorems

open Formula

-- ============================================================================
-- The monotone realizer
-- ============================================================================

section Generic

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

set_option linter.unusedVariables false in
/-- **A monotone realizer** of `A` in context `Γ`: a majorant `tstar` at the hat type, together
with a proof that *some* Dialectica realizer — one functional of the environment — is
majorized by it wherever the environment is, and satisfies the matrix everywhere; plus
self-majorization of `tstar`. `termMajorizer_maj`'s statement, one level up.

`cm` does not occur in the body: it is there to pin `am` (the relation the statement is about)
and because the leaf strategy reads its majorants — the same role it has in `termMajorizer`. -/
def MRealizer (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) : Type :=
  { tstar : ℕ → Ctx.interpret X (Γ.map Ty.hat) → Ty.interpret X (wTy A).hat //
    ∀ n, n ≥ am.N →
      (∃ x : Ctx.interpret X Γ → dialecticaWitness X A,
        (∀ (envstar : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
          MajEnv am Γ envstar env → am.maj (wTy A) (tstar n envstar) (x env)) ∧
        ∀ (env : Ctx.interpret X Γ) (y : dialecticaCounter X A),
          dialecticaMatrix si A env (x env) y) ∧
      (∀ (e₁ e₂ : Ctx.interpret X (Γ.map Ty.hat)), SelfMajEnv am Γ e₁ e₂ →
        am.selfMaj (wTy A) (tstar n e₁) (tstar n e₂)) }

/-- The per-environment shape, derived: at every majorized environment there is a realizer
majorized by `tstar`. -/
theorem MRealizer.pointwise {cm : ConstMajorants am} {Γ : Ctx ι} {A : Formula F Γ}
    (r : MRealizer cm A) :
    ∀ n, n ≥ am.N → ∀ (envstar : Ctx.interpret X (Γ.map Ty.hat)) (env : Ctx.interpret X Γ),
      MajEnv am Γ envstar env →
      ∃ x : dialecticaWitness X A,
        am.maj (wTy A) (r.val n envstar) x ∧
        ∀ y : dialecticaCounter X A, dialecticaMatrix si A env x y := by
  intro n hn envstar env henv
  obtain ⟨⟨x, hx, hm⟩, _⟩ := r.property n hn
  exact ⟨x env, hx envstar env henv, hm env⟩

-- ----------------------------------------------------------------------------
-- Short names for the structure's fields, all arguments implicit
-- ----------------------------------------------------------------------------

private theorem mapp {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)} {x_star : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (hf : am.maj (ρ →ₜ τ) f_star f) (hx : am.maj ρ x_star x) :
    am.maj τ (f_star x_star) (f x) :=
  am.app_compat _ _ _ _ hf hx

private theorem mfst {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj ρ p_star.1 p.1 :=
  am.prod_fst _ _ h

private theorem msnd {ρ τ : Ty ι} {p_star : Ty.interpret X (ρ ×ₜ τ).hat}
    {p : Ty.interpret X (ρ ×ₜ τ)} (h : am.maj (ρ ×ₜ τ) p_star p) : am.maj τ p_star.2 p.2 :=
  am.prod_snd _ _ h

private theorem mpair {ρ τ : Ty ι} {a_star : Ty.interpret X ρ.hat} {a : Ty.interpret X ρ}
    {b_star : Ty.interpret X τ.hat} {b : Ty.interpret X τ}
    (ha : am.maj ρ a_star a) (hb : am.maj τ b_star b) :
    am.maj (ρ ×ₜ τ) (a_star, b_star) (a, b) :=
  am.prod_intro _ _ ha hb

private theorem marr {ρ τ : Ty ι} {f_star : Ty.interpret X (ρ →ₜ τ).hat}
    {f : Ty.interpret X (ρ →ₜ τ)}
    (h₁ : ∀ (x_star : Ty.interpret X ρ.hat) (x : Ty.interpret X ρ),
      am.maj ρ x_star x → am.maj τ (f_star x_star) (f x))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat),
      am.selfMaj ρ x y → am.selfMaj τ (f_star x) (f_star y)) :
    am.maj (ρ →ₜ τ) f_star f :=
  am.arrow_intro _ _ h₁ h₂

private theorem sapp {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    {x y : Ty.interpret X ρ.hat} (hf : am.selfMaj (ρ →ₜ τ) f g) (hx : am.selfMaj ρ x y) :
    am.selfMaj τ (f x) (g y) :=
  am.selfMaj_app hf hx

private theorem sfst {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj ρ p.1 q.1 :=
  am.selfMaj_prod_fst _ _ h

private theorem ssnd {ρ τ : Ty ι} {p q : Ty.interpret X (ρ ×ₜ τ).hat}
    (h : am.selfMaj (ρ ×ₜ τ) p q) : am.selfMaj τ p.2 q.2 :=
  am.selfMaj_prod_snd _ _ h

private theorem spair {ρ τ : Ty ι} {a b : Ty.interpret X ρ.hat} {c d : Ty.interpret X τ.hat}
    (h₁ : am.selfMaj ρ a b) (h₂ : am.selfMaj τ c d) :
    am.selfMaj (ρ ×ₜ τ) (a, c) (b, d) :=
  am.selfMaj_prod_intro _ _ h₁ h₂

private theorem sarr {ρ τ : Ty ι} {f g : Ty.interpret X (ρ →ₜ τ).hat}
    (h₁ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (g y))
    (h₂ : ∀ (x y : Ty.interpret X ρ.hat), am.selfMaj ρ x y → am.selfMaj τ (f x) (f y)) :
    am.selfMaj (ρ →ₜ τ) f g :=
  am.selfMaj_arrow_intro _ _ h₁ h₂

private theorem mself {ρ : Ty ι} {a : Ty.interpret X ρ.hat} {x : Ty.interpret X ρ}
    (h : am.maj ρ a x) : am.selfMaj ρ a a :=
  am.maj_selfMaj h

private theorem sself {ρ : Ty ι} {a b : Ty.interpret X ρ.hat} (h : am.selfMaj ρ a b) :
    am.selfMaj ρ a a :=
  am.selfMaj_self h

/-- Majorization transports along a type equation, on both sides at once. -/
theorem maj_cast {σ τ : Ty ι} (h : σ = τ)
    (hh : Ty.interpret X σ.hat = Ty.interpret X τ.hat)
    (hs : Ty.interpret X σ = Ty.interpret X τ)
    {a : Ty.interpret X σ.hat} {x : Ty.interpret X σ} (hm : am.maj σ a x) :
    am.maj τ (cast hh a) (cast hs x) := by
  subst h; exact hm

/-- Self-majorization transports along a type equation. -/
theorem selfMaj_cast {σ τ : Ty ι} (h : σ = τ)
    (hh : Ty.interpret X σ.hat = Ty.interpret X τ.hat)
    {a b : Ty.interpret X σ.hat} (hm : am.selfMaj σ a b) :
    am.selfMaj τ (cast hh a) (cast hh b) := by
  subst h; exact hm

-- ----------------------------------------------------------------------------
-- The leaf strategy: Howard's construction on a syntactic realizer (book p. 142)
-- ----------------------------------------------------------------------------

/-- **Leaf strategy**: a syntactic realizer's term is majorized by its `termMajorizer`. Used
for every axiom, whose realizing term is a fixed-size combinator. -/
def MRealizer.ofSRealizer (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F Γ}
    (r : SRealizer si A) : MRealizer cm A :=
  ⟨fun n e => termMajorizer cm r.val n e, fun n hn =>
    ⟨⟨fun env => Term.interpret si r.val env,
      fun es env henv => (termMajorizer_maj cm r.val n hn).1 es env henv,
      fun env y => r.property env y⟩,
     fun e₁ e₂ he => (termMajorizer_maj cm r.val n hn).2 e₁ e₂ he⟩⟩

-- ----------------------------------------------------------------------------
-- Composition through the usual interpretation's λ-terms (book p. 144, case 6)
-- ----------------------------------------------------------------------------

/-! A rule with one sub-derivation of `P` and conclusion `Q` whose usual realizer is
`t[h]` for a combinator `t` and the sub-realizer `h`: plug the sub-realizer in **as a
variable**. The majorant is `termMajorizer` of `t[var]` with the sub-*majorant* in the hat
environment, the realizer is `Term.interpret` of `t[var]` with the sub-*realizer* in the
environment, and `termMajorizer_maj` relates the two — the sub-realizer enters through
`Ctx.lookupHat`, never as a term. The caller supplies only the correctness of `t`. -/

/-- One sub-realizer in the same context. -/
def MRealizer.plug1 (cm : ConstMajorants am) {Γ : Ctx ι} {P Q : Formula F Γ}
    (h : MRealizer cm P) (t : Term F (wTy P :: Γ) (wTy Q))
    (hc : ∀ (env : Ctx.interpret X Γ) (x : dialecticaWitness X P),
      (∀ y, dialecticaMatrix si P env x y) →
      ∀ y, dialecticaMatrix si Q env (Term.interpret si t (x, env)) y) :
    MRealizer cm Q :=
  ⟨fun n e => termMajorizer cm t n (h.val n e, e), fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    refine ⟨⟨fun env => Term.interpret si t (xh env, env), ?_, ?_⟩, ?_⟩
    · intro es env henv
      exact (termMajorizer_maj cm t n hn).1 _ _ ⟨hxh es env henv, henv⟩
    · intro env y
      exact hc env (xh env) (hmh env) y
    · intro e₁ e₂ he
      exact (termMajorizer_maj cm t n hn).2 _ _ ⟨hsh e₁ e₂ he, he⟩⟩

/-- Two sub-realizers in the same context (`mp`-shaped rules; here `induction`). -/
def MRealizer.plug2 (cm : ConstMajorants am) {Γ : Ctx ι} {P₁ P₂ Q : Formula F Γ}
    (h₁ : MRealizer cm P₁) (h₂ : MRealizer cm P₂)
    (t : Term F (wTy P₂ :: wTy P₁ :: Γ) (wTy Q))
    (hc : ∀ (env : Ctx.interpret X Γ) (x₁ : dialecticaWitness X P₁)
      (x₂ : dialecticaWitness X P₂),
      (∀ y, dialecticaMatrix si P₁ env x₁ y) → (∀ y, dialecticaMatrix si P₂ env x₂ y) →
      ∀ y, dialecticaMatrix si Q env (Term.interpret si t (x₂, x₁, env)) y) :
    MRealizer cm Q :=
  ⟨fun n e => termMajorizer cm t n (h₂.val n e, h₁.val n e, e), fun n hn => by
    obtain ⟨⟨x₁, hx₁, hm₁⟩, hs₁⟩ := h₁.property n hn
    obtain ⟨⟨x₂, hx₂, hm₂⟩, hs₂⟩ := h₂.property n hn
    refine ⟨⟨fun env => Term.interpret si t (x₂ env, x₁ env, env), ?_, ?_⟩, ?_⟩
    · intro es env henv
      exact (termMajorizer_maj cm t n hn).1 _ _ ⟨hx₂ es env henv, hx₁ es env henv, henv⟩
    · intro env y
      exact hc env (x₁ env) (x₂ env) (hm₁ env) (hm₂ env) y
    · intro e₁ e₂ he
      exact (termMajorizer_maj cm t n hn).2 _ _ ⟨hs₂ e₁ e₂ he, hs₁ e₁ e₂ he, he⟩⟩

/-- One sub-realizer under a binder: the sub-derivation lives in `ρ :: Γ`, and enters the
combinator as a variable of **arrow** type `ρ →ₜ wTy P` — the λ-abstracted realizer
`fun z => x (z, env)`, majorized by `fun z => tstar (z, e)` via `arrow_intro` from the IH.
This is what `exist_rule` (and `forall_rule`, were it not hand-written) needs. -/
def MRealizer.plugAll (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι}
    {P : Formula F (ρ :: Γ)} {Q : Formula F Γ}
    (h : MRealizer cm P) (t : Term F ((ρ →ₜ wTy P) :: Γ) (wTy Q))
    (hc : ∀ (env : Ctx.interpret X Γ) (G : Ty.interpret X ρ → dialecticaWitness X P),
      (∀ z y, dialecticaMatrix si P (z, env) (G z) y) →
      ∀ y, dialecticaMatrix si Q env (Term.interpret si t (G, env)) y) :
    MRealizer cm Q :=
  ⟨fun n e => termMajorizer cm t n (fun z => h.val n (z, e), e), fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    refine ⟨⟨fun env => Term.interpret si t (fun z => xh (z, env), env), ?_, ?_⟩, ?_⟩
    · intro es env henv
      refine (termMajorizer_maj cm t n hn).1 _ _ ⟨?_, henv⟩
      exact marr (fun zs z hz => hxh (zs, es) (z, env) ⟨hz, henv⟩)
        (fun z₁ z₂ hz => hsh (z₁, es) (z₂, es) ⟨hz, MajEnv.toSelfMajEnv Γ henv⟩)
    · intro env y
      exact hc env (fun z => xh (z, env)) (fun z => hmh (z, env)) y
    · intro e₁ e₂ he
      refine (termMajorizer_maj cm t n hn).2 _ _ ⟨?_, he⟩
      exact sarr (fun z₁ z₂ hz => hsh (z₁, e₁) (z₂, e₂) ⟨hz, he⟩)
        (fun z₁ z₂ hz => hsh (z₁, e₁) (z₂, e₁) ⟨hz, SelfMajEnv.self Γ he⟩)⟩

end Generic

-- ============================================================================
-- The combinators, with the formula context decoupled from the term context
-- ============================================================================

/-! These are the `wt*` payloads of `Dialectica/Syntactic.lean` with one change: the
formulas live in a context `Δ` **unrelated** to the term's context `Γ`. `wTy`/`cTy` ignore
the context, so the bodies are identical; the decoupling is what lets the sub-realizer be
`Term.var Var.vz` in the context `wTy P :: Γ` while the formulas stay in `Γ`. -/

section Combinators

variable {ι κ : Type} {F : κ → Ty ι} {Γ Δ : Ctx ι}

/-- `wtImportation`, decoupled. -/
def mtImportation {A B C : Formula F Δ} (h : Term F Γ (wTy (A →ᶠ B →ᶠ C))) :
    Term F Γ (wTy (A ∧ᶠ B →ᶠ C)) :=
  .mkPair
    (.lam (.app (.fst (.app (Term.weaken (.fst h)) (.fst (.var .vz)))) (.snd (.var .vz))))
    (.lam (.lam (.mkPair
      (.app (.app (Term.weaken (Term.weaken (.snd h))) (.fst (.var (.vs .vz))))
        (.mkPair (.snd (.var (.vs .vz))) (.var .vz)))
      (.app (.app (.snd (.app (Term.weaken (Term.weaken (.fst h)))
          (.fst (.var (.vs .vz))))) (.snd (.var (.vs .vz)))) (.var .vz)))))

/-- `wtExpansion`, decoupled. -/
def mtExpansion {A B C : Formula F Δ} (h : Term F Γ (wTy (A →ᶠ B))) :
    Term F Γ (wTy (C ∨ᶠ A →ᶠ C ∨ᶠ B)) :=
  .mkPair
    (.lam (.mkPair (.fst (.var .vz)) (.mkPair (.fst (.snd (.var .vz)))
      (.app (Term.weaken (.fst h)) (.snd (.snd (.var .vz)))))))
    (.lam (.lam (.mkPair (.fst (.var .vz))
      (.app (.app (Term.weaken (Term.weaken (.snd h)))
        (.snd (.snd (.var (.vs .vz))))) (.snd (.var .vz))))))

/-- `wtUnivGen`, decoupled. -/
def mtUnivGen {A : Formula F Δ} (ρ : Ty ι) (r : Term F Γ (wTy A)) :
    Term F Γ (wTy (Formula.all ρ (A.weakenBy ρ))) :=
  .lam (Term.castTy (wTy_cTy_renameF A Term.Renaming.shift).1.symm (Term.weaken r))

/-- `wtQfer`, decoupled (the default terms are `Term.defaultOf` at the term's context). -/
def mtQfer {A₀ : Formula F Δ} {ρ σ : Ty ι} {s t : Term F Δ ρ} (r : Term F (ρ :: Δ) σ)
    (ih : Term F Γ (wTy (A₀ →ᶠ eqAtType ρ s t))) :
    Term F Γ (wTy (A₀ →ᶠ eqAtType σ (r.subst0 s) (r.subst0 t))) :=
  .mkPair
    (.lam (Term.weaken (Term.defaultOf (wTy (eqAtType σ (r.subst0 s) (r.subst0 t))))))
    (.lam (.lam (.app (.app (Term.weaken (Term.weaken (.snd ih))) (.var (.vs .vz)))
      (Term.weaken (Term.weaken (Term.defaultOf (cTy (eqAtType ρ s t))))))))

/-- `wtExistRule` at a λ-abstracted sub-realizer `h : ρ →ₜ wTy (A →ᶠ B↑)`: the substitutions
`sb1`/`sb2` of `wtExistRule` become applications of `h` to the witness's first component,
so no `Term.subst` appears. -/
def mtExistRule {ρ : Ty ι} {B : Formula F Δ} {A : Formula F (ρ :: Δ)}
    (h : Term F Γ (ρ →ₜ wTy (A →ᶠ Formula.weakenBy ρ B))) :
    Term F Γ (wTy (Formula.ex ρ A →ᶠ B)) :=
  let hw : wTy (Formula.weakenBy ρ B) = wTy B := (wTy_cTy_renameF B Term.Renaming.shift).1
  let hc : cTy (Formula.weakenBy ρ B) = cTy B := (wTy_cTy_renameF B Term.Renaming.shift).2
  .mkPair
    (.lam (Term.castTy hw
      (.app (.fst (.app (Term.weaken h) (.fst (.var .vz)))) (.snd (.var .vz)))))
    (.lam (.lam (.app (.app (.snd (.app (Term.weaken (Term.weaken h)) (.fst (.var (.vs .vz)))))
      (.snd (.var (.vs .vz)))) (Term.castTy hc.symm (.var .vz)))))

/-- The base of `wtInduction`, named so its interpretation can be stated once. -/
def mtIndBase {A : Formula F (Ty.nat :: Δ)} (hbase : Term F Γ (wTy (A.subst0 Term.zero))) :
    Term F (Ty.nat :: Γ) (wTy A) :=
  Term.castTy (wTy_cTy_substF A (Term.subst0_map _)).1 (Term.weaken hbase)

/-- The step of `wtInduction`, named. -/
def mtIndStep {A : Formula F (Ty.nat :: Δ)}
    (hstep : Term F Γ (wTy (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))))) :
    Term F (Ty.nat :: Γ) (wTy A →ₜ Ty.nat →ₜ wTy A) :=
  .lam (.lam (Term.castTy (wTy_cTy_substF A (Formula.Term.substVar0_map _)).1
    (.app (.fst (.app (Term.weaken (Term.weaken (Term.weaken hstep))) (.var .vz)))
      (.var (.vs .vz)))))

/-- `wtInduction`, decoupled: a `Term.prec` at the object-level witness type, whose
`termMajorizer` is `cm.precM (wTy A)` — the book's `t^M`. -/
def mtInduction {A : Formula F (Ty.nat :: Δ)}
    (hbase : Term F Γ (wTy (A.subst0 Term.zero)))
    (hstep : Term F Γ (wTy (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))))) :
    Term F Γ (wTy (Formula.all Ty.nat A)) :=
  .lam (Term.app3 (.prec (wTy A)) (mtIndBase hbase) (mtIndStep hstep) (.var .vz))

variable {X : ι → Type} {si : SpaceInterp X F}

theorem interpret_mtIndBase {A : Formula F (Ty.nat :: Δ)}
    (hbase : Term F Γ (wTy (A.subst0 Term.zero))) (n : Nat) (env : Ctx.interpret X Γ) :
    Term.interpret si (mtIndBase hbase) (n, env)
      = cast (congrArg (Ty.interpret X) (wTy_cTy_substF A (Term.subst0_map _)).1)
          (Term.interpret si hbase env) := by
  simp only [mtIndBase, interpret_castTy]
  rw [Term.interpret_weaken]

theorem interpret_mtIndStep {A : Formula F (Ty.nat :: Δ)}
    (hstep : Term F Γ (wTy (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz))))))
    (n : Nat) (env : Ctx.interpret X Γ) (ihv : Ty.interpret X (wTy A)) (k : Nat) :
    Term.interpret si (mtIndStep hstep) (n, env) ihv k
      = cast (congrArg (Ty.interpret X) (wTy_cTy_substF A (Formula.Term.substVar0_map _)).1)
          ((Term.interpret si hstep env k).1 ihv) := by
  simp only [mtIndStep, Term.interpret, interpret_castTy]
  rw [Term.interpret_weaken, Term.interpret_weaken, Term.interpret_weaken]
  rfl

/-- **`mtInduction` is correct** — `sInduction`'s proof with the term environment `env'`
decoupled from the formula environment `env`: if the base and step terms realize their
formulas at `env` when interpreted at `env'`, so does the primitive recursion. -/
theorem mtInduction_correct {A : Formula F (Ty.nat :: Δ)}
    (hbase : Term F Γ (wTy (A.subst0 Term.zero)))
    (hstep : Term F Γ (wTy (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz))))))
    (env' : Ctx.interpret X Γ) (env : Ctx.interpret X Δ)
    (hxb : ∀ y, dialecticaMatrix si (A.subst0 Term.zero) env (Term.interpret si hbase env') y)
    (hxs : ∀ y, dialecticaMatrix si (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))) env
      (Term.interpret si hstep env') y) :
    ∀ y, dialecticaMatrix si (Formula.all Ty.nat A) env
      (Term.interpret si (mtInduction hbase hstep) env') y := by
  intro y
  have hw0 : wTy (A.subst0 Term.zero) = wTy A := (wTy_cTy_substF A (Term.subst0_map _)).1
  have hwsv : wTy (A.substVar0 (Term.app Term.succ (.var .vz))) = wTy A :=
    (wTy_cTy_substF A (Formula.Term.substVar0_map _)).1
  have hcsv : cTy (A.substVar0 (Term.app Term.succ (.var .vz))) = cTy A :=
    (wTy_cTy_substF A (Formula.Term.substVar0_map _)).2
  simp only [mtInduction, dialecticaMatrix, Term.interpret, Term.app3]
  suffices hall : ∀ (m : Nat) (z : Ty.interpret X (cTy A)),
      dialecticaMatrix si A (m, env)
        (Nat.rec (Term.interpret si (mtIndBase hbase) (y.1, env'))
          (fun n ihv => (Term.interpret si (mtIndStep hstep) (y.1, env')) ihv n) m) z by
    exact hall y.1 y.2
  intro m
  induction m with
  | zero =>
    intro z
    change dialecticaMatrix si A (Nat.zero, env)
      (Term.interpret si (mtIndBase hbase) (y.1, env')) z
    rw [interpret_mtIndBase]
    have key := (dialecticaMatrix_subst0 si A Term.zero env
      (cast (congrArg (Ty.interpret X) hw0) (Term.interpret si hbase env')) z).mp
    simp only [Term.interpret] at key
    apply key
    rw [cast_cancel (dialecticaWitness_subst0 A Term.zero)]
    exact hxb _
  | succ m ih =>
    intro z
    set Wm := Nat.rec (motive := fun _ => Ty.interpret X (wTy A))
      (Term.interpret si (mtIndBase hbase) (y.1, env'))
      (fun n ihv => (Term.interpret si (mtIndStep hstep) (y.1, env')) ihv n) m with hWm
    change dialecticaMatrix si A (Nat.succ m, env)
      (Term.interpret si (mtIndStep hstep) (y.1, env') Wm m) z
    rw [interpret_mtIndStep]
    set U := Term.interpret si hstep env' with hU
    have hprem := ih ((U m).2 Wm (cast (congrArg (Ty.interpret X) hcsv.symm) z))
    have hconc := hxs (m, (Wm, cast (congrArg (Ty.interpret X) hcsv.symm) z)) hprem
    have hiff := dialecticaMatrix_substVar0 si A (Term.app Term.succ (.var .vz)) m env
      (cast (congrArg (Ty.interpret X) hwsv) ((U m).1 Wm)) z
    have hcc : cast (dialectica_types_substF (X := X) A
          (Formula.Term.substVar0_map (Term.app Term.succ (.var .vz)))).1.symm
        (cast (congrArg (Ty.interpret X) hwsv) ((U m).1 Wm)) = (U m).1 Wm :=
      eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    rw [hcc] at hiff
    simp only [Term.interpret] at hiff
    exact hiff.mp hconc

end Combinators

-- ============================================================================
-- The composition cases
-- ============================================================================

section Composition

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

-- ----------------------------------------------------------------------------
-- Modus ponens (book p. 144, case 5) — from the spike
-- ----------------------------------------------------------------------------

def MRealizer.mp (cm : ConstMajorants am) {Γ : Ctx ι} {A B : Formula F Γ}
    (hA : MRealizer cm A) (hAB : MRealizer cm (A →ᶠ B)) : MRealizer cm B :=
  ⟨fun n e => (hAB.val n e).1 (hA.val n e), fun n hn => by
    obtain ⟨⟨xA, hxA, hmA⟩, hsA⟩ := hA.property n hn
    obtain ⟨⟨xAB, hxAB, hmAB⟩, hsAB⟩ := hAB.property n hn
    refine ⟨⟨fun env => (xAB env).1 (xA env), ?_, ?_⟩, ?_⟩
    · intro es env henv
      exact mapp (mfst (hxAB es env henv)) (hxA es env henv)
    · intro env yB
      exact hmAB env (xA env, yB) (hmA env ((xAB env).2 (xA env) yB))
    · intro e₁ e₂ he
      exact sapp (sfst (hsAB e₁ e₂ he)) (hsA e₁ e₂ he)⟩

-- ----------------------------------------------------------------------------
-- Syllogism (book p. 144, case 5, "the rule … is treated similarly") — from the spike
-- ----------------------------------------------------------------------------

def MRealizer.syllogism (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (hAB : MRealizer cm (A →ᶠ B)) (hBC : MRealizer cm (B →ᶠ C)) : MRealizer cm (A →ᶠ C) :=
  ⟨fun n e =>
    -- SHARING EXPERIMENT (branch `sharing`, 2026-09-06): `hAB.val n e` occurred 3× and
    -- `hBC.val n e` 2× here; `let` binds each once. Definitionally transparent, so the
    -- `Prop` half below is unchanged.
    let a := hAB.val n e
    let b := hBC.val n e
    (fun xA => b.1 (a.1 xA),
     fun xA yC => a.2 xA (b.2 (a.1 xA) yC)),
   fun n hn => by
    obtain ⟨⟨xAB, hxAB, hmAB⟩, hsAB⟩ := hAB.property n hn
    obtain ⟨⟨xBC, hxBC, hmBC⟩, hsBC⟩ := hBC.property n hn
    refine ⟨⟨fun env =>
      (fun xA => (xBC env).1 ((xAB env).1 xA),
       fun xA yC => (xAB env).2 xA ((xBC env).2 ((xAB env).1 xA) yC)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have hab := hxAB es env henv
      have hbc := hxBC es env henv
      have abS := mself hab
      have bcS := mself hbc
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        exact mapp (mfst hbc) (mapp (mfst hab) hx)
      · intro x y hxy
        exact sapp (sfst bcS) (sapp (sfst abS) hxy)
      · intro x_star x hx
        refine marr ?_ ?_
        · intro y_star y hy
          exact mapp (mapp (msnd hab) hx)
            (mapp (mapp (msnd hbc) (mapp (mfst hab) hx)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) (mself hx))
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) (mself hx))) hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) hxy)
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd abS) (sself hxy))
            (sapp (sapp (ssnd bcS) (sapp (sfst abS) (sself hxy))) hy)
    · intro env y hA
      exact hmBC env ((xAB env).1 y.1, y.2)
        (hmAB env (y.1, (xBC env).2 ((xAB env).1 y.1) y.2) hA)
    · intro e₁ e₂ he
      have ab12 := hsAB e₁ e₂ he
      have bc12 := hsBC e₁ e₂ he
      have ab11 := hsAB e₁ e₁ (SelfMajEnv.self _ he)
      have bc11 := hsBC e₁ e₁ (SelfMajEnv.self _ he)
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact sapp (sfst bc12) (sapp (sfst ab12) hxy)
      · intro x y hxy
        exact sapp (sfst bc11) (sapp (sfst ab11) hxy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab12) hxy)
            (sapp (sapp (ssnd bc12) (sapp (sfst ab12) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) (sself hxy))
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) (sself hxy))) hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) hxy)
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) hxy)) hy)
        · intro y₁ y₂ hy
          exact sapp (sapp (ssnd ab11) (sself hxy))
            (sapp (sapp (ssnd bc11) (sapp (sfst ab11) (sself hxy))) hy)⟩

-- ----------------------------------------------------------------------------
-- Exportation — from the spike
-- ----------------------------------------------------------------------------

def MRealizer.exportation (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : MRealizer cm (A ∧ᶠ B →ᶠ C)) : MRealizer cm (A →ᶠ B →ᶠ C) :=
  ⟨fun n e =>
    -- SHARING EXPERIMENT: `h.val n e` occurred 3×.
    let c := h.val n e
    (fun xA => (fun xB => c.1 (xA, xB),
                fun xB yC => (c.2 (xA, xB) yC).2),
     fun xA p => (c.2 (xA, p.1) p.2).1),
   fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    refine ⟨⟨fun env =>
      (fun xA => (fun xB => (xh env).1 (xA, xB),
                  fun xB yC => ((xh env).2 (xA, xB) yC).2),
       fun xA p => ((xh env).2 (xA, p.1) p.2).1), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have hh := hxh es env henv
      have hS := mself hh
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro xA_star xA hxA
        refine mpair (marr ?_ ?_) (marr ?_ ?_)
        · intro xB_star xB hxB
          exact mapp (mfst hh) (mpair hxA hxB)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair (mself hxA) hs)
        · intro xB_star xB hxB
          refine marr ?_ ?_
          · intro y_star y hy
            exact msnd (mapp (mapp (msnd hh) (mpair hxA hxB)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) (mself hxB))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (mself hxA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst hS) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd hS) (spair (sself hA) (sself hs))) hy)
      · intro xA_star xA hxA
        refine marr ?_ ?_
        · intro p_star p hp
          exact mfst (mapp (mapp (msnd hh) (mpair hxA (mfst hp))) (msnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair (mself hxA) (sfst hp))) (ssnd hp))
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd hS) (spair (sself hA) (sfst hp))) (ssnd hp))
    · intro env y hA hB
      exact hmh env ((y.1, y.2.1), y.2.2) ⟨hA, hB⟩
    · intro e₁ e₂ he
      have h12 := hsh e₁ e₂ he
      have h11 := hsh e₁ e₁ (SelfMajEnv.self _ he)
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h12) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h12) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine spair (sarr ?_ ?_) (sarr ?_ ?_)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair hA hs)
        · intro xB₁ xB₂ hs
          exact sapp (sfst h11) (spair (sself hA) hs)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair hA hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
        · intro xB₁ xB₂ hs
          refine sarr ?_ ?_
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) hs)) hy)
          · intro y₁ y₂ hy
            exact ssnd (sapp (sapp (ssnd h11) (spair (sself hA) (sself hs))) hy)
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h12) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair (sself hA) (sfst hp))) (ssnd hp))
      · intro xA₁ xA₂ hA
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair hA (sfst hp))) (ssnd hp))
        · intro p₁ p₂ hp
          exact sfst (sapp (sapp (ssnd h11) (spair (sself hA) (sfst hp))) (ssnd hp))⟩

-- ----------------------------------------------------------------------------
-- The ∀-rule (book p. 144, case 6) — from the spike
-- ----------------------------------------------------------------------------

/-- The realizer is `dialectica_forall_rule`'s, written out; the majorant is the same
λ-term on the hat side, and `arrow_intro`'s two clauses are discharged from the IH at
`(z*, e)` / `(z₁, e₁), (z₂, e₂)`. The type equations `wTy (weakenBy ρ B) = wTy B` and
`cTy (weakenBy ρ B) = cTy B` are propositional, so casts appear on both sides; they are
transported by `maj_cast` / `selfMaj_cast`. -/
def MRealizer.forallRule (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ}
    {A : Formula F (ρ :: Γ)} (h : MRealizer cm (Formula.weakenBy ρ B →ᶠ A)) :
    MRealizer cm (B →ᶠ Formula.all ρ A) :=
  ⟨fun n e =>
    -- SHARING EXPERIMENT: the two occurrences of `h.val n (·, e)` are at *different*
    -- arguments, so only the closure and the two type equations can be shared.
    let hv := fun z => h.val n (z, e)
    let cw := (congrArg (fun σ : Ty ι => Ty.interpret X σ.hat)
      (wTy_cTy_renameF B Term.Renaming.shift).1).symm
    let cc := congrArg (fun σ : Ty ι => Ty.interpret X σ.hat)
      (wTy_cTy_renameF B Term.Renaming.shift).2
    (fun xB z => (hv z).1 (cast cw xB),
     fun xB p => cast cc ((hv p.1).2 (cast cw xB) p.2)),
   fun n hn => by
    obtain ⟨⟨xh, hxh, hmh⟩, hsh⟩ := h.property n hn
    have hw : wTy (Formula.weakenBy ρ B) = wTy B := (wTy_cTy_renameF B Term.Renaming.shift).1
    have hc : cTy (Formula.weakenBy ρ B) = cTy B := (wTy_cTy_renameF B Term.Renaming.shift).2
    refine ⟨⟨fun env =>
      (fun xB z => (xh (z, env)).1 (cast (dialecticaWitness_weaken ρ B).symm xB),
       fun xB p => cast (dialecticaCounter_weaken ρ B)
         ((xh (p.1, env)).2 (cast (dialecticaWitness_weaken ρ B).symm xB) p.2)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      have selfEs := MajEnv.toSelfMajEnv Γ henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro xB_star xB hxB
        refine marr ?_ ?_
        · intro z_star z hz
          exact mapp (mfst (hxh (z_star, es) (z, env) ⟨hz, henv⟩))
            (maj_cast hw.symm _ _ hxB)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩))
            (selfMaj_cast hw.symm _ (mself hxB))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, es) (z₂, es) ⟨hz, selfEs⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB_star xB hxB
        refine marr ?_ ?_
        · intro p_star p hp
          exact maj_cast hc _ _
            (mapp (mapp (msnd (hxh (p_star.1, es) (p.1, env) ⟨mfst hp, henv⟩))
              (maj_cast hw.symm _ _ hxB)) (msnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ (mself hxB))) (ssnd hp))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, es) (p₂.1, es) ⟨sfst hp, selfEs⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))
    · intro env y hprem
      have hcc : cast (dialecticaWitness_weaken ρ B)
          (cast (dialecticaWitness_weaken ρ B).symm y.1) = y.1 :=
        eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
      refine hmh (y.2.1, env) (cast (dialecticaWitness_weaken ρ B).symm y.1, y.2.2) ?_
      refine (dialecticaMatrix_weaken si B env y.2.1 _ _).mpr ?_
      rw [hcc]
      exact hprem
    · intro e₁ e₂ he
      have selfE1 := SelfMajEnv.self Γ he
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₂) ⟨hz, he⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩)) (selfMaj_cast hw.symm _ hs)
        · intro z₁ z₂ hz
          exact sapp (sfst (hsh (z₁, e₁) (z₂, e₁) ⟨hz, selfE1⟩))
            (selfMaj_cast hw.symm _ (sself hs))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₂) ⟨sfst hp, he⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))
      · intro xB₁ xB₂ hs
        refine sarr ?_ ?_
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ hs)) (ssnd hp))
        · intro p₁ p₂ hp
          exact selfMaj_cast hc _
            (sapp (sapp (ssnd (hsh (p₁.1, e₁) (p₂.1, e₁) ⟨sfst hp, selfE1⟩))
              (selfMaj_cast hw.symm _ (sself hs))) (ssnd hp))⟩

-- ----------------------------------------------------------------------------
-- Importation, expansion, universal generalisation, QF-ER, ∃-rule, induction
-- (book p. 144, case 6: "the λ-terms of the usual functional interpretation")
-- ----------------------------------------------------------------------------

/-- Importation. The correctness proof is `sImportation`'s with the sub-realizer term
replaced by the variable. -/
def MRealizer.importation (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : MRealizer cm (A →ᶠ B →ᶠ C)) : MRealizer cm (A ∧ᶠ B →ᶠ C) :=
  MRealizer.plug1 cm h (mtImportation (Term.var Var.vz)) (fun env x hx y hm => by
    simp only [mtImportation, Term.interpret, Term.interpret_weaken, Ctx.lookup] at hm ⊢
    exact hx (y.1.1, y.1.2, y.2) hm.1 hm.2)

/-- Expansion. -/
def MRealizer.expansion (cm : ConstMajorants am) {Γ : Ctx ι} {A B C : Formula F Γ}
    (h : MRealizer cm (A →ᶠ B)) : MRealizer cm (C ∨ᶠ A →ᶠ C ∨ᶠ B) :=
  MRealizer.plug1 cm h (mtExpansion (C := C) (Term.var Var.vz)) (fun env x hx y hm => by
    simp only [mtExpansion, dialecticaMatrix, Term.interpret, Term.interpret_weaken,
      Ctx.lookup] at hm ⊢
    exact ⟨hm.1, fun hne => hx (y.1.2.2, y.2.2) (hm.2 hne)⟩)

/-- Universal generalisation. -/
def MRealizer.univGen (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F Γ}
    (h : MRealizer cm A) : MRealizer cm (Formula.all ρ (A.weakenBy ρ)) :=
  MRealizer.plug1 cm h (mtUnivGen ρ (Term.var Var.vz)) (fun env x hx y => by
    simp only [mtUnivGen, dialecticaMatrix, Term.interpret, Term.interpret_weaken,
      interpret_castTy, Ctx.lookup]
    refine (dialecticaMatrix_weaken si A env y.1 _ y.2).mpr ?_
    rw [cast_cancel (dialecticaWitness_weaken ρ A).symm]
    exact hx _)

/-- QF-ER. The witness is the default (the witness type of an `eqAtType` is a subsingleton);
the counter feeds the sub-realizer a canonical counter, exactly as `sQfer`. -/
def MRealizer.qfer (cm : ConstMajorants am) (eqxi : EqXInterp X F si) {Γ : Ctx ι}
    {A₀ : Formula F Γ} {ρ σ : Ty ι} {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (h : MRealizer cm (A₀ →ᶠ eqAtType ρ s t)) :
    MRealizer cm (A₀ →ᶠ eqAtType σ (r.subst0 s) (r.subst0 t)) :=
  MRealizer.plug1 cm h (mtQfer r (Term.var Var.vz)) (fun env x hx y hA₀ => by
    have ssC : Subsingleton (ℂ X A₀) := (dialecticaWitness_subsingleton A₀ hqf hvf).2
    have ssW : Subsingleton (𝕎 X (eqAtType σ (r.subst0 s) (r.subst0 t))) :=
      dialecticaWitness_eqAtType_ss (X := X) σ (r.subst0 s) (r.subst0 t)
    simp only [mtQfer, Term.interpret, Term.interpret_weaken, interpret_defaultOf,
      Ctx.lookup] at hA₀ ⊢
    have hfull : dialecticaRealizerCtx si (eqAtType ρ s t) env :=
      ⟨x.1 y.1, fun yρ => by
        refine hx (y.1, yρ) ?_
        have hcc : x.2 y.1 yρ = x.2 y.1 (Ty.interpret_default si (cTy (eqAtType ρ s t))) :=
          ssC.elim _ _
        rw [hcc]; exact hA₀⟩
    have hsem : Term.interpret si s env = Term.interpret si t env :=
      eqAtType_to_semEq si eqxi ρ s t env hfull
    have hsem_r : Term.interpret si (r.subst0 s) env = Term.interpret si (r.subst0 t) env := by
      rw [Term.interpret_subst0, Term.interpret_subst0, hsem]
    have hrσ := eqAtType_from_semEq si eqxi σ (r.subst0 s) (r.subst0 t) env hsem_r
    have hwW : hrσ.val = Ty.interpret_default si (wTy (eqAtType σ (r.subst0 s) (r.subst0 t))) :=
      ssW.elim _ _
    rw [← hwW]
    exact hrσ.property y.2)

/-- The ∃-rule. The sub-realizer enters at arrow type (`plugAll`); the correctness proof is
`sExistRule`'s with the two substitutions replaced by applications. -/
def MRealizer.existRule (cm : ConstMajorants am) {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ}
    {A : Formula F (ρ :: Γ)} (h : MRealizer cm (A →ᶠ Formula.weakenBy ρ B)) :
    MRealizer cm (Formula.ex ρ A →ᶠ B) :=
  MRealizer.plugAll cm h (mtExistRule (Term.var Var.vz)) (fun env G hG y hm => by
    have hc : cTy (Formula.weakenBy ρ B) = cTy B := (wTy_cTy_renameF B Term.Renaming.shift).2
    simp only [mtExistRule, Term.interpret, Term.interpret_weaken, interpret_castTy,
      Ctx.lookup] at hm ⊢
    have hstep := hG y.1.1 (y.1.2, cast (congrArg (Ty.interpret X) hc.symm) y.2) hm
    have hfwd := (dialecticaMatrix_weaken si B env y.1.1 _ _).mp hstep
    rwa [cast_cancel (dialecticaCounter_weaken ρ B).symm] at hfwd)

/-- **Induction — the book's `t^M`** (p. 144, case 7). The combinator is `wtInduction`'s
`Term.prec (wTy A)`, whose `termMajorizer` is `cm.precM (wTy A)`; in every instance in the
tree that is `recMaj`, the recursion with a running `maxT`. Base and step sub-realizers
are variables. The correctness proof is `sInduction`'s. -/
def MRealizer.induction (cm : ConstMajorants am) {Γ : Ctx ι} {A : Formula F (Ty.nat :: Γ)}
    (hb : MRealizer cm (A.subst0 Term.zero))
    (hs : MRealizer cm (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz))))) :
    MRealizer cm (Formula.all Ty.nat A) :=
  MRealizer.plug2 cm hb hs (mtInduction (Term.var (Var.vs Var.vz)) (Term.var Var.vz))
    (fun env _ _ hxb hxs => mtInduction_correct _ _ _ env hxb hxs)

end Composition

-- ============================================================================
-- The `max` cases (book p. 143, cases 1–3)
-- ============================================================================

section Max

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si}

/-- **`A → A ∧ A`, monotone (case 1)**: the witness majorant is `λx.(x,x)`, the counter
majorant is `λx y. max(y', y'')` at the hat type. The realizer is `dialectica_and_contract`'s,
which branches on the (decidable) matrix; the majorant does not branch, and mentions no
term. This is the case that stalls the term route (`sAndContract`'s `matrixTerm`). -/
def MRealizer.andContract (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) :
    MRealizer cm (A →ᶠ A ∧ᶠ A) :=
  ⟨fun _ _ => (fun x => (x, x), fun _ y => maxT (cTy A) y.1 y.2),
   fun _ _ => by
    refine ⟨⟨fun env =>
      (fun x => (x, x),
       fun x y => if dialecticaMatrix si A env x y.1 then y.2 else y.1), ?_, ?_⟩, ?_⟩
    · intro es env henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        exact mpair hx hx
      · intro x y hxy
        exact spair hxy hxy
      · intro x_star x hx
        refine marr ?_ ?_
        · intro y_star y hy
          by_cases hd : dialecticaMatrix si A env x y.1
          · simp only [if_pos hd]
            exact am.maxT_maj_right (msnd hy) (sfst (mself hy))
          · simp only [if_neg hd]
            exact am.maxT_maj_left (mfst hy) (ssnd (mself hy))
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
      · intro x y hxy
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
    · intro env y hm
      simp only [dialecticaMatrix] at hm ⊢
      by_cases hd : dialecticaMatrix si A env y.1 y.2.1
      · simp only [if_pos hd] at hm
        exact ⟨hd, hm⟩
      · simp only [if_neg hd] at hm
        exact absurd hm hd
    · intro e₁ e₂ _
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact spair hxy hxy
      · intro x y hxy
        exact spair hxy hxy
      · intro x y _
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
      · intro x y _
        refine sarr ?_ ?_
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)
        · intro y₁ y₂ hy
          exact am.maxT_selfMaj (sfst hy) (ssnd hy)⟩

/-- **`A ∨ A → A`, monotone (case 2)**: `t*_X'' := λz x x'. max(x, x')` — the witness
majorant is the `maxT` of the two disjunct witnesses, and does not look at the flag; the
counter majorant `λx y.(y, y)` is the usual one. The realizer is `dialectica_or_contract`'s. -/
def MRealizer.orContract (cm : ConstMajorants am) {Γ : Ctx ι} (A : Formula F Γ) :
    MRealizer cm (A ∨ᶠ A →ᶠ A) :=
  ⟨fun _ _ => (fun x => maxT (wTy A) x.2.1 x.2.2, fun _ y => (y, y)),
   fun _ _ => by
    refine ⟨⟨fun env =>
      (fun x => if (x.1 : Nat) = 0 then x.2.1 else x.2.2, fun _ y => (y, y)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        by_cases hz : (x.1 : Nat) = 0
        · simp only [if_pos hz]
          exact am.maxT_maj_left (mfst (msnd hx)) (ssnd (ssnd (mself hx)))
        · simp only [if_neg hz]
          exact am.maxT_maj_right (msnd (msnd hx)) (sfst (ssnd (mself hx)))
      · intro x y hxy
        exact am.maxT_selfMaj (sfst (ssnd hxy)) (ssnd (ssnd hxy))
      · intro x_star x hx
        exact marr (fun y_star y hy => mpair hy hy) (fun y₁ y₂ hy => spair hy hy)
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair hy hy) (fun y₁ y₂ hy => spair hy hy)
    · intro env y hm
      simp only [dialecticaMatrix] at hm ⊢
      by_cases hz : (y.1.1 : Nat) = 0
      · simp only [if_pos hz]
        exact hm.1 hz
      · simp only [if_neg hz]
        exact hm.2 hz
    · intro e₁ e₂ _
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact am.maxT_selfMaj (sfst (ssnd hxy)) (ssnd (ssnd hxy))
      · intro x y hxy
        exact am.maxT_selfMaj (sfst (ssnd hxy)) (ssnd (ssnd hxy))
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair hy hy) (fun y₁ y₂ hy => spair hy hy)
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair hy hy) (fun y₁ y₂ hy => spair hy hy)⟩

/-- The majorant of the disjunction flag in `or_perm`: the book's `t*_Z' := λz x u. 1`. The
abstract relation cannot say "`1` majorizes `0`" outright (it has only `nat_order`, one
direction), so `1` is spelled as the `maxT` of the majorants of `S 0` and `0` — which in every
`bezem*` instance *is* `max 1 0 = 1`. -/
def flagM (cm : ConstMajorants am) (n : ℕ) : Ty.interpret X Ty.nat.hat :=
  maxT Ty.nat (cm.succM n (cm.zeroM n)) (cm.zeroM n)

theorem flagM_maj (cm : ConstMajorants am) {n : ℕ} (hn : n ≥ am.N) (z : Nat) :
    am.maj Ty.nat (flagM cm n) (if z = 0 then 1 else 0) := by
  have h1 : am.maj Ty.nat (cm.succM n (cm.zeroM n)) (Nat.succ 0) :=
    mapp (cm.succM_maj n hn) (cm.zeroM_maj n hn)
  have h0 : am.maj Ty.nat (cm.zeroM n) 0 := cm.zeroM_maj n hn
  by_cases hz : z = 0
  · simp only [if_pos hz]
    exact am.maxT_maj_left h1 (mself h0)
  · simp only [if_neg hz]
    exact am.maxT_maj_right h0 (mself h1)

theorem flagM_selfMaj (cm : ConstMajorants am) {n : ℕ} (hn : n ≥ am.N) :
    am.selfMaj Ty.nat (flagM cm n) (flagM cm n) :=
  mself (flagM_maj cm hn 0)

/-- **`A ∨ B → B ∨ A`, monotone (case 3)**: the flag's majorant is the constant `1`
(`flagM`); the rest is the usual λ-term. The realizer is `dialectica_or_perm`'s. -/
def MRealizer.orPerm (cm : ConstMajorants am) {Γ : Ctx ι} (A B : Formula F Γ) :
    MRealizer cm (A ∨ᶠ B →ᶠ B ∨ᶠ A) :=
  ⟨fun n _ => (fun x => (flagM cm n, x.2.2, x.2.1), fun _ y => (y.2, y.1)),
   fun n hn => by
    refine ⟨⟨fun env =>
      (fun x => ((if (x.1 : Nat) = 0 then 1 else 0), x.2.2, x.2.1),
       fun _ y => (y.2, y.1)), ?_, ?_⟩, ?_⟩
    · intro es env henv
      refine mpair (marr ?_ ?_) (marr ?_ ?_)
      · intro x_star x hx
        exact mpair (flagM_maj cm hn _) (mpair (msnd (msnd hx)) (mfst (msnd hx)))
      · intro x y hxy
        exact spair (flagM_selfMaj cm hn) (spair (ssnd (ssnd hxy)) (sfst (ssnd hxy)))
      · intro x_star x hx
        exact marr (fun y_star y hy => mpair (msnd hy) (mfst hy))
          (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
          (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
    · intro env y hm
      simp only [dialecticaMatrix] at hm ⊢
      by_cases hz : (y.1.1 : Nat) = 0
      · refine ⟨fun h => ?_, fun _ => hm.1 hz⟩
        simp only [hz] at h
        exact absurd h one_ne_zero
      · exact ⟨fun _ => hm.2 hz, fun h => absurd (by simp [hz]) h⟩
    · intro e₁ e₂ _
      refine spair (sarr ?_ ?_) (sarr ?_ ?_)
      · intro x y hxy
        exact spair (flagM_selfMaj cm hn) (spair (ssnd (ssnd hxy)) (sfst (ssnd hxy)))
      · intro x y hxy
        exact spair (flagM_selfMaj cm hn) (spair (ssnd (ssnd hxy)) (sfst (ssnd hxy)))
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
          (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
      · intro x y _
        exact sarr (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))
          (fun y₁ y₂ hy => spair (ssnd hy) (sfst hy))⟩

end Max

-- ============================================================================
-- The recursion over the derivation
-- ============================================================================

section Soundness

variable {ι κ : Type} {X : ι → Type} {F : κ → Ty ι} {si : SpaceInterp X F}
    {am : AbstractMajorizability si} {Premises : PremiseSet F}

/-- **The monotone functional interpretation** (Kohlenbach Thm 9.1): every derivation in
`WE-HA^{ω,X} + AC + IP + M` yields a monotone realizer — a majorant of a Dialectica
realizer, computed by structural recursion on the derivation with no realizer term ever
built. Every constructor is treated; the strategy per constructor is in the module header.

`spremise` is the syntactic premise realizer of `syntactic_soundness`; a premise's monotone
realizer is the leaf strategy on its term (for every space in the tree that term is the
information-free `defaultWTerm`, `srealizer_of_pu_val`). -/
def monotone_soundness (eqxi : EqXInterp X F si)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    (cm : ConstMajorants am) :
    {Γ : Ctx ι} → {A : Formula F Γ} →
    @Derivable ι κ F Allowed.extended Premises Γ A → MRealizer cm A
  -- premises: leaf on the supplied term
  | _, _, .premise hp       => .ofSRealizer cm (spremise _ _ hp)
  -- propositional axioms: `max` for the three contraction/permutation ones, leaf otherwise
  | _, _, .or_contract      => .orContract cm _
  | _, _, .and_contract     => .andContract cm _
  | _, _, .or_weak          => .ofSRealizer cm sOrWeak
  | _, _, .and_weak         => .ofSRealizer cm sAndWeak
  | _, _, .or_perm          => .orPerm cm _ _
  | _, _, .and_perm         => .ofSRealizer cm sAndPerm
  | _, _, .exfalso          => .ofSRealizer cm sExfalso
  | _, _, .forall_ax t      => .ofSRealizer cm (sForallAx t)
  | _, _, .exist_ax t _     => .ofSRealizer cm (sExistAx t)
  -- rules: composition
  | _, _, .mp hA hAB        => .mp cm (monotone_soundness eqxi spremise cm hA)
                                  (monotone_soundness eqxi spremise cm hAB)
  | _, _, .syllogism h₁ h₂  => .syllogism cm (monotone_soundness eqxi spremise cm h₁)
                                  (monotone_soundness eqxi spremise cm h₂)
  | _, _, .exportation h'   => .exportation cm (monotone_soundness eqxi spremise cm h')
  | _, _, .importation h'   => .importation cm (monotone_soundness eqxi spremise cm h')
  | _, _, .expansion h'     => .expansion cm (monotone_soundness eqxi spremise cm h')
  | _, _, .forall_rule h'   => .forallRule cm (monotone_soundness eqxi spremise cm h')
  | _, _, .exist_rule h'    => .existRule cm (monotone_soundness eqxi spremise cm h')
  | _, _, .univ_gen h'      => .univGen cm (monotone_soundness eqxi spremise cm h')
  -- arithmetic, β/η, recursor, pseudometric and `=₀` axioms: leaf
  | _, _, .succ_ne_zero     => .ofSRealizer cm sSuccNeZero
  | _, _, .succ_inj         => .ofSRealizer cm sSuccInj
  | _, _, .beta_eq _ _      => .ofSRealizer cm (sBetaEq eqxi)
  | _, _, .pair_fst _ _     => .ofSRealizer cm (sPairFst eqxi)
  | _, _, .pair_snd _ _     => .ofSRealizer cm (sPairSnd eqxi)
  | _, _, .pair_eta _       => .ofSRealizer cm (sPairEta eqxi)
  | _, _, .rec_zero         => .ofSRealizer cm (sRecZero eqxi)
  | _, _, .rec_succ         => .ofSRealizer cm (sRecSucc eqxi)
  | _, _, .dist_self i x    => .ofSRealizer cm (sDistSelf eqxi i x)
  | _, _, .dist_comm i x y  => .ofSRealizer cm (sDistComm eqxi i x y)
  | _, _, .dist_tri i x y z => .ofSRealizer cm (sDistTri eqxi i x y z)
  | _, _, .refl0            => .ofSRealizer cm sRefl0
  | _, _, .sym0             => .ofSRealizer cm sSym0
  | _, _, .trans0           => .ofSRealizer cm sTrans0
  -- QF-ER and induction: composition
  | _, _, .qfer hqf hvf h'  => .qfer cm eqxi hqf hvf (monotone_soundness eqxi spremise cm h')
  | _, _, .induction hb hs  => .induction cm (monotone_soundness eqxi spremise cm hb)
                                  (monotone_soundness eqxi spremise cm hs)
  -- the extension principles: leaf (their realizers are fixed combinators)
  | _, _, .markov _ hqf hvf => .ofSRealizer cm (sMarkov hqf hvf)
  | _, _, .ip _ hqf hvf     => .ofSRealizer cm (sIP hqf hvf)
  | _, _, .ac _             => .ofSRealizer cm sAC
  | _, _, .qfac _ _ _       => .ofSRealizer cm sAC
  | _, _, .lem h_lem        => absurd h_lem (by decide)

-- ----------------------------------------------------------------------------
-- Reading `U` and `V` off a monotone realizer — `extractUTerm`/`extractVTerm`, semantically
-- ----------------------------------------------------------------------------

/-- The `U`-majorant of a monotone realizer of `∀x(∀u B₀ → ∃v C₀)`, read off exactly as
`extractUTerm` reads it off the realizing term: the `.snd` of the implication's majorant,
applied to the majorants of the default witness and counter, first projection. The default
terms live in context `[ρ]`, as in `extractUTerm`; their majorants are environment-independent. -/
def mfiU {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]} (cm : ConstMajorants am)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).2
    (termMajorizer cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N (xs, ()))
    (termMajorizer cm (defaultCTerm (Formula.ex Ty.nat C₀)) am.N (xs, ()))).1

/-- The `V`-majorant, as `extractVTerm`. -/
def mfiV {ρ : Ty ι} {B₀ C₀ : Formula F [Ty.nat, ρ]} (cm : ConstMajorants am)
    (r : MRealizer cm (Formula.all ρ (Formula.imp (Formula.all Ty.nat B₀)
      (Formula.ex Ty.nat C₀)))) :
    Ty.interpret X ρ.hat → ℕ :=
  fun xs => ((r.val am.N () xs).1
    (termMajorizer cm (defaultWTerm (Formula.all Ty.nat B₀)) am.N (xs, ()))).1

end Soundness

-- ============================================================================
-- Axiom hygiene — verify by name, after a completed `lake build`
-- ============================================================================

#print axioms MRealizer.pointwise
#print axioms MRealizer.ofSRealizer
#print axioms MRealizer.plug1
#print axioms MRealizer.plug2
#print axioms MRealizer.plugAll
#print axioms MRealizer.mp
#print axioms MRealizer.syllogism
#print axioms MRealizer.exportation
#print axioms MRealizer.forallRule
#print axioms MRealizer.importation
#print axioms MRealizer.expansion
#print axioms MRealizer.univGen
#print axioms MRealizer.qfer
#print axioms MRealizer.existRule
#print axioms MRealizer.induction
#print axioms MRealizer.andContract
#print axioms MRealizer.orContract
#print axioms MRealizer.orPerm
#print axioms monotone_soundness
#print axioms mfiU
#print axioms mfiV

end Metatheorems
