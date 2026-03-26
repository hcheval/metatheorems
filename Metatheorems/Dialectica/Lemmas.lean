/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horatiu
-/
import Metatheorems.Dialectica.Defs

/-!
# Dialectica Soundness Lemmas

One lemma per axiom/rule of WE-HA^{ω,X} + AC + IP + M^ω, showing that
the Dialectica interpretation is satisfied. These are assembled into
the main soundness proof in `dialectica_soundness`.

Each lemma constructs the witness values explicitly. All lemmas are
generalized to work for arbitrary contexts `Γ` and environments
`env : interpCtx X Γ`, returning a `dialecticaRealizerCtx` (a subtype
living in `Type`, not `Prop`). The witness can be extracted computably
via `.val`.
-/

open Formula

variable {ι : Type} {X : ι → Type} {F : ι → Ty ι} (si : SpaceInterp X F)
variable {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) →
          Formula F Γ}
variable (eqxi : EqXInterp X F si EqX)

-- ============================================================================
-- Modus ponens
-- ============================================================================

def dialectica_mp {Γ : Ctx ι} {A B : Formula F Γ} (env : interpCtx X Γ)
    (hA : dialecticaRealizerCtx si A env)
    (hAB : dialecticaRealizerCtx si (A →ᶠ B) env) :
    dialecticaRealizerCtx si B env :=
  ⟨hAB.val.1 hA.val, fun yB => hAB.property (hA.val, yB) (hA.property (hAB.val.2 hA.val yB))⟩

-- ============================================================================
-- Ex falso quodlibet
-- ============================================================================

def dialectica_exfalso {Γ : Ctx ι} {A : Formula F Γ} (env : interpCtx X Γ)
    (inhW : dialecticaWitness X A) (inhC : dialecticaCounter X A) :
    dialecticaRealizerCtx si (⊥ᶠ →ᶠ A) env :=
  ⟨⟨fun _ => inhW, fun _ _ => ()⟩, fun ⟨(), _⟩ h => absurd h id⟩

-- ============================================================================
-- ∧-weakening: A ∧ B → A
-- ============================================================================

def dialectica_and_weak {Γ : Ctx ι} {A B : Formula F Γ} (env : interpCtx X Γ)
    (inhC : dialecticaCounter X B) :
    dialecticaRealizerCtx si (A ∧ᶠ B →ᶠ A) env :=
  ⟨⟨fun xAB => xAB.1, fun _ yA => (yA, inhC)⟩, fun ⟨⟨_, _⟩, _⟩ h => h.1⟩

-- ============================================================================
-- ∧-permutation: A ∧ B → B ∧ A
-- ============================================================================

def dialectica_and_perm {Γ : Ctx ι} {A B : Formula F Γ} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (A ∧ᶠ B →ᶠ B ∧ᶠ A) env :=
  ⟨⟨fun xAB => (xAB.2, xAB.1), fun _ yBA => (yBA.2, yBA.1)⟩,
   fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h => ⟨h.2, h.1⟩⟩

-- ============================================================================
-- ∨-weakening: A → A ∨ B
-- ============================================================================

def dialectica_or_weak {Γ : Ctx ι} {A B : Formula F Γ} (env : interpCtx X Γ)
    (inhW : dialecticaWitness X B) :
    dialecticaRealizerCtx si (A →ᶠ A ∨ᶠ B) env :=
  ⟨⟨fun xA => (true, xA, inhW), fun _ yAB => yAB.1⟩,
   fun ⟨_, ⟨yA, _⟩⟩ h => ⟨fun _ => h, fun hf => Bool.noConfusion hf⟩⟩

-- ============================================================================
-- ∨-permutation: A ∨ B → B ∨ A
-- ============================================================================

def dialectica_or_perm {Γ : Ctx ι} {A B : Formula F Γ} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (A ∨ᶠ B →ᶠ B ∨ᶠ A) env :=
  ⟨⟨fun xAB => (!xAB.1, xAB.2.2, xAB.2.1), fun _ yBA => (yBA.2, yBA.1)⟩,
   fun ⟨⟨z, _, _⟩, ⟨_, _⟩⟩ ⟨hT, hF⟩ =>
     ⟨fun h => hF (by cases z <;> simp_all),
      fun h => hT (by cases z <;> simp_all)⟩⟩

-- ============================================================================
-- ∨-contraction: A ∨ A → A
-- ============================================================================

def dialectica_or_contract {Γ : Ctx ι} {A : Formula F Γ} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (A ∨ᶠ A →ᶠ A) env :=
  ⟨⟨fun xAA => if xAA.1 then xAA.2.1 else xAA.2.2, fun _ yA => (yA, yA)⟩,
   fun ⟨⟨z, _, _⟩, yA⟩ h => by cases z <;> simp_all [dialecticaMatrix]⟩

-- ============================================================================
-- ∧-contraction: A → A ∧ A
-- ============================================================================

def dialectica_and_contract {Γ : Ctx ι} {A : Formula F Γ} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (A →ᶠ A ∧ᶠ A) env :=
  ⟨⟨fun xA => (xA, xA),
    fun xA ⟨y1, y2⟩ =>
      letI : Decidable (dialecticaMatrix si A env xA y1) :=
        dialecticaMatrix_decidable si A env xA y1
      if dialecticaMatrix si A env xA y1 then y2 else y1⟩,
   fun ⟨xA, ⟨y1, y2⟩⟩ hm => by
     simp only [dialecticaMatrix] at hm ⊢
     by_cases hd : dialecticaMatrix si A env xA y1
     · simp only [if_pos hd] at hm; exact ⟨hd, hm⟩
     · simp only [if_neg hd] at hm; exact absurd hm hd⟩

-- ============================================================================
-- Syllogism
-- ============================================================================

def dialectica_syllogism {Γ : Ctx ι} {A B C : Formula F Γ} (env : interpCtx X Γ)
    (hAB : dialecticaRealizerCtx si (A →ᶠ B) env)
    (hBC : dialecticaRealizerCtx si (B →ᶠ C) env) :
    dialecticaRealizerCtx si (A →ᶠ C) env :=
  let ⟨⟨U_AB, Y_AB⟩, h_AB⟩ := hAB
  let ⟨⟨U_BC, Y_BC⟩, h_BC⟩ := hBC
  ⟨⟨fun xA => U_BC (U_AB xA), fun xA yC => Y_AB xA (Y_BC (U_AB xA) yC)⟩,
   fun ⟨xA, yC⟩ hA => h_BC (U_AB xA, yC) (h_AB (xA, Y_BC (U_AB xA) yC) hA)⟩

-- ============================================================================
-- Exportation: A ∧ B → C implies A → (B → C)
-- ============================================================================

def dialectica_exportation {Γ : Ctx ι} {A B C : Formula F Γ} (env : interpCtx X Γ)
    (h : dialecticaRealizerCtx si (A ∧ᶠ B →ᶠ C) env) :
    dialecticaRealizerCtx si (A →ᶠ B →ᶠ C) env :=
  let ⟨⟨V, Z⟩, hV⟩ := h
  ⟨⟨fun xA => ⟨fun xB => V (xA, xB), fun xB yC => (Z (xA, xB) yC).2⟩,
    fun xA ⟨xB, yC⟩ => (Z (xA, xB) yC).1⟩,
   fun ⟨xA, xB, yC⟩ hA hB => hV ⟨(xA, xB), yC⟩ ⟨hA, hB⟩⟩

-- ============================================================================
-- Importation: A → (B → C) implies A ∧ B → C
-- ============================================================================

def dialectica_importation {Γ : Ctx ι} {A B C : Formula F Γ} (env : interpCtx X Γ)
    (h : dialecticaRealizerCtx si (A →ᶠ B →ᶠ C) env) :
    dialecticaRealizerCtx si (A ∧ᶠ B →ᶠ C) env :=
  let ⟨⟨U, Y⟩, hU⟩ := h
  ⟨⟨fun xAB => (U xAB.1).1 xAB.2, fun xAB yC => (Y xAB.1 (xAB.2, yC), (U xAB.1).2 xAB.2 yC)⟩,
   fun ⟨⟨xA, xB⟩, yC⟩ ⟨hA, hB⟩ => hU (xA, (xB, yC)) hA hB⟩

-- ============================================================================
-- Expansion: A → B implies C ∨ A → C ∨ B
-- ============================================================================

def dialectica_expansion {Γ : Ctx ι} {A B C : Formula F Γ} (env : interpCtx X Γ)
    (h : dialecticaRealizerCtx si (A →ᶠ B) env) :
    dialecticaRealizerCtx si (C ∨ᶠ A →ᶠ C ∨ᶠ B) env :=
  let ⟨⟨U_AB, Y_AB⟩, h_AB⟩ := h
  ⟨⟨fun xCA => (xCA.1, xCA.2.1, U_AB xCA.2.2),
    fun xCA yCB => (yCB.1, Y_AB xCA.2.2 yCB.2)⟩,
   fun ⟨⟨z, xC, xA⟩, ⟨yC, yB⟩⟩ ⟨hC, hA⟩ => ⟨hC, fun hz => h_AB (xA, yB) (hA hz)⟩⟩

-- ============================================================================
-- Equality axioms
-- ============================================================================

def dialectica_refl0 {Γ : Ctx ι} {t : Term F Γ Ty.nat} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (.eq0 t t) env :=
  ⟨(), fun () => rfl⟩

def dialectica_sym0 {Γ : Ctx ι} {s t : Term F Γ Ty.nat} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (.eq0 s t →ᶠ .eq0 t s) env :=
  ⟨⟨fun _ => (), fun _ _ => ()⟩, fun ⟨(), ()⟩ h => h.symm⟩

def dialectica_trans0 {Γ : Ctx ι} {s t u : Term F Γ Ty.nat} (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (.eq0 s t ∧ᶠ .eq0 t u →ᶠ .eq0 s u) env :=
  ⟨⟨fun _ => (), fun _ _ => ((), ())⟩, fun ⟨((), ()), ()⟩ ⟨h1, h2⟩ => h1.trans h2⟩

-- ============================================================================
-- QF-ER (qfer): A₀ →ᶠ eqAtType EqX ρ s t  implies  A₀ →ᶠ eqAtType EqX σ (r.subst0 s) (r.subst0 t)
-- ============================================================================

/-- A canonical element of `interpTy X ρ`, using `si.zeroInterp` at base types. -/
private def interpTy_default' {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) : ∀ (ρ : Ty ι), interpTy X ρ
  | .nat    => Nat.zero
  | .base i => si.zeroInterp i
  | .arr _ τ => fun _ => interpTy_default' si τ

-- The QF-ER helpers below use section variables {EqX} and (eqxi) automatically.
-- They avoid `induction` in `def` bodies to prevent the "code generator does not
-- support recursor Ty.rec" error; use term-mode `match` instead.

/-- A canonical counter for `eqAtType EqX ρ s t`. -/
private def eqAtType_default_ctr {Γ : Ctx ι} (ρ : Ty ι) (s t : Term F Γ ρ) :
    dialecticaCounter X (eqAtType EqX ρ s t) :=
  match ρ, s, t with
  | .nat,      _, _  => ()
  | .base i,   s, t  => eqxi.counterDefault i s t
  | .arr ρ' τ, s, t  =>
    (interpTy_default' si ρ',
     eqAtType_default_ctr τ (s.weaken.app (.var .vz)) (t.weaken.app (.var .vz)))

/-- A canonical witness for `eqAtType EqX ρ s t`. -/
private def eqAtType_default_wit {Γ : Ctx ι} (ρ : Ty ι) (s t : Term F Γ ρ) :
    dialecticaWitness X (eqAtType EqX ρ s t) :=
  match ρ, s, t with
  | .nat,      _, _  => ()
  | .base i,   s, t  => eqxi.witnessDefault i s t
  | .arr ρ' τ, s, t  =>
    fun _ => eqAtType_default_wit τ (s.weaken.app (.var .vz)) (t.weaken.app (.var .vz))

/-- The witness type for `eqAtType EqX ρ s t` is a subsingleton.
    At `nat` the witness is `Unit`; at `base i` this follows from `EqX` being purely
    universal (encoded in `eqxi.witnessSubsingleton`); at function types the witness
    is a function into a subsingleton, which is again a subsingleton. -/
private lemma dialecticaWitness_eqAtType_ss (eqxi : EqXInterp X F si EqX) (ρ : Ty ι) :
    ∀ {Γ : Ctx ι} (s t : Term F Γ ρ),
    Subsingleton (dialecticaWitness X (eqAtType EqX ρ s t)) := by
  induction ρ with
  | nat    => intro Γ s t; simp only [eqAtType, dialecticaWitness]; exact ⟨fun _ _ => rfl⟩
  | base i => intro Γ s t; exact eqxi.witnessSubsingleton i s t
  | arr ρ' τ _ ih_τ =>
    intro Γ s t
    simp only [eqAtType, dialecticaWitness]
    exact ⟨fun f g => funext (fun z =>
      (ih_τ (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))).elim (f z) (g z))⟩

/-- Extract semantic equality from a full realizer for `eqAtType EqX ρ s t`. -/
private noncomputable def eqAtType_to_semEq {Γ : Ctx ι} (ρ : Ty ι) (s t : Term F Γ ρ)
    (env : interpCtx X Γ) (h : dialecticaRealizerCtx si (eqAtType EqX ρ s t) env) :
    interpTerm si s env = interpTerm si t env := by
  induction ρ generalizing Γ env with
  | nat    => exact h.property ()
  | base i => exact eqxi.extract i s t env h
  | arr ρ' τ _ ih_τ =>
      funext z
      have hz : dialecticaRealizerCtx si
          (eqAtType EqX τ (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz)))
          (z, env) :=
        ⟨h.val z, fun yτ => h.property (z, yτ)⟩
      have heq := ih_τ (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz)) (z, env) hz
      simp only [interpTerm, interpTerm_weaken, lookupVar] at heq
      exact heq

/-- Build a full realizer for `eqAtType EqX ρ s t` from a semantic equality.
    The `base i` case uses `eqxi.realize`, which encodes the semantic correctness
    of the base-type equality predicate `EqX i`. -/
private noncomputable def eqAtType_from_semEq {Γ : Ctx ι} (ρ : Ty ι) (s t : Term F Γ ρ)
    (env : interpCtx X Γ) (h : interpTerm si s env = interpTerm si t env) :
    dialecticaRealizerCtx si (eqAtType EqX ρ s t) env := by
  induction ρ generalizing Γ env with
  | nat    => exact ⟨(), fun () => h⟩
  | base i => exact eqxi.realize i s t env h
  | arr ρ' τ _ ih_τ =>
      have eq_z : ∀ z : interpTy X ρ',
          interpTerm si (Term.app s.weaken (.var .vz)) (z, env) =
          interpTerm si (Term.app t.weaken (.var .vz)) (z, env) := fun z => by
        simp only [interpTerm, interpTerm_weaken, lookupVar]; exact congr_fun h z
      exact ⟨fun z => (ih_τ (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))
                           (z, env) (eq_z z)).val,
             fun (z, yτ) => (ih_τ (Term.app s.weaken (.var .vz)) (Term.app t.weaken (.var .vz))
                                  (z, env) (eq_z z)).property yτ⟩

/-- Dialectica soundness for the QF-ER (qfer) rule.
    Requires A₀ to be QF and ∨-free so that `dialecticaCounter X A₀` is a
    subsingleton; this lets us lift a single-counter hypothesis to a full
    realizer for `eqAtType EqX ρ s t`, extract the semantic equality, and then
    rebuild the conclusion's realizer using `eqxi`. -/
noncomputable def dialectica_qfer {Γ : Ctx ι} {A₀ : Formula F Γ} {ρ σ : Ty ι}
    {s t : Term F Γ ρ} {r : Term F (ρ :: Γ) σ}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (ih : ∀ env, dialecticaRealizerCtx si (A₀ →ᶠ eqAtType EqX ρ s t) env) :
    ∀ env, dialecticaRealizerCtx si (A₀ →ᶠ eqAtType EqX σ (r.subst0 s) (r.subst0 t)) env := by
  intro env
  have ssC : Subsingleton (dialecticaCounter X A₀) :=
    (dialecticaWitness_subsingleton A₀ hqf hvf).2
  have ssW_σ : Subsingleton (dialecticaWitness X (eqAtType EqX σ (r.subst0 s) (r.subst0 t))) :=
    dialecticaWitness_eqAtType_ss si eqxi σ (r.subst0 s) (r.subst0 t)
  let yρ_default := eqAtType_default_ctr si eqxi ρ s t
  let wσ_default := eqAtType_default_wit si eqxi σ (r.subst0 s) (r.subst0 t)
  obtain ⟨⟨U₀, Y₀⟩, hprop⟩ := ih env
  refine ⟨⟨fun _ => wσ_default, fun xA₀ _ => Y₀ xA₀ yρ_default⟩, ?_⟩
  intro ⟨xA₀, yEqσ⟩ hA₀
  have hfull : dialecticaRealizerCtx si (eqAtType EqX ρ s t) env :=
    ⟨U₀ xA₀, fun yρ => by
      have hcc : Y₀ xA₀ yρ = Y₀ xA₀ yρ_default := ssC.elim _ _
      exact hprop (xA₀, yρ) (by
        show dialecticaMatrix si A₀ env xA₀ (Y₀ xA₀ yρ)
        rw [hcc]; exact hA₀)⟩
  have hsem : interpTerm si s env = interpTerm si t env :=
    eqAtType_to_semEq si eqxi ρ s t env hfull
  have hsem_r : interpTerm si (r.subst0 s) env = interpTerm si (r.subst0 t) env := by
    rw [interpTerm_subst0, interpTerm_subst0, hsem]
  have hrσ := eqAtType_from_semEq si eqxi σ (r.subst0 s) (r.subst0 t) env hsem_r
  have hwW : hrσ.val = wσ_default := ssW_σ.elim _ _
  rw [← hwW]
  exact hrσ.property yEqσ

-- ============================================================================
-- ∀-axiom: ∀x^ρ A → A[t/x]
-- ============================================================================

def dialectica_forall_ax {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (env : interpCtx X Γ) (t : Term F Γ ρ) :
    dialecticaRealizerCtx si (Formula.all ρ A →ᶠ A.subst0 t) env :=
  let hW := dialecticaWitness_subst0 (X := X) A t
  let hC := dialecticaCounter_subst0 (X := X) A t
  ⟨⟨fun f => cast hW.symm (f (interpTerm si t env)),
    fun _ zc => (interpTerm si t env, cast hC zc)⟩,
   fun ⟨f, zc⟩ hyp => by
     have key := (dialecticaMatrix_subst0 si A t env
       (f (interpTerm si t env)) (cast hC zc)).mpr hyp
     rwa [cast_cancel hC] at key⟩

-- ============================================================================
-- ∃-axiom: A[t/x] → ∃x^ρ A
-- ============================================================================

def dialectica_exist_ax {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F (ρ :: Γ)}
    (env : interpCtx X Γ) (t : Term F Γ ρ) :
    dialecticaRealizerCtx si (A.subst0 t →ᶠ Formula.ex ρ A) env :=
  let hW := dialecticaWitness_subst0 (X := X) A t
  let hC := dialecticaCounter_subst0 (X := X) A t
  ⟨⟨fun w => (interpTerm si t env, cast hW w), fun _ yA => cast hC.symm yA⟩,
   fun ⟨w, yA⟩ hyp => by
     have key := (dialecticaMatrix_subst0 si A t env (cast hW w) yA).mp
     rw [cast_cancel hW w] at key
     exact key hyp⟩

-- ============================================================================
-- ∀-rule: (B.weakenBy ρ → A) implies B → ∀x A
-- ============================================================================

def dialectica_forall_rule
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : ∀ env, dialecticaRealizerCtx si (Formula.weakenBy ρ B →ᶠ A) env) :
    ∀ env, dialecticaRealizerCtx si (B →ᶠ Formula.all ρ A) env := by
  intro env
  refine ⟨⟨fun xB z => (h (z, env)).val.1
                (cast (dialecticaWitness_weaken ρ B).symm xB),
            fun xB p => cast (dialecticaCounter_weaken ρ B)
              ((h (p.1, env)).val.2
                (cast (dialecticaWitness_weaken ρ B).symm xB) p.2)⟩, ?_⟩
  intro p hprem
  obtain ⟨xB, z, yA⟩ := p
  set xB' := cast (dialecticaWitness_weaken ρ B).symm xB
  exact (h (z, env)).property ⟨xB', yA⟩
    ((dialecticaMatrix_weaken si B env z xB' ((h (z, env)).val.2 xB' yA)).mpr
      (by have hcc : cast (dialecticaWitness_weaken ρ B) xB' = xB :=
            eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
          rw [hcc]; exact hprem))

-- ============================================================================
-- ∃-rule: (A → B.weakenBy ρ) implies ∃x A → B
-- ============================================================================

def dialectica_exist_rule
    {Γ : Ctx ι} {ρ : Ty ι} {B : Formula F Γ} {A : Formula F (ρ :: Γ)}
    (h : ∀ env, dialecticaRealizerCtx si (A →ᶠ Formula.weakenBy ρ B) env) :
    ∀ env, dialecticaRealizerCtx si (Formula.ex ρ A →ᶠ B) env := by
  intro env
  refine ⟨⟨fun p => cast (dialecticaWitness_weaken ρ B)
                ((h (p.1, env)).val.1 p.2),
            fun p yB => (h (p.1, env)).val.2 p.2
              (cast (dialecticaCounter_weaken ρ B).symm yB)⟩, ?_⟩
  intro p hprem
  obtain ⟨⟨z, xA⟩, yB⟩ := p
  have hstep := (h (z, env)).property ⟨xA, cast (dialecticaCounter_weaken ρ B).symm yB⟩ hprem
  have hfwd := (dialecticaMatrix_weaken si B env z
    ((h (z, env)).val.1 xA)
    (cast (dialecticaCounter_weaken ρ B).symm yB)).mp hstep
  have hcc : cast (dialecticaCounter_weaken ρ B)
               (cast (dialecticaCounter_weaken ρ B).symm yB) = yB :=
    eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  rw [hcc] at hfwd; exact hfwd

-- ============================================================================
-- Universal generalization
-- ============================================================================

def dialectica_univ_gen {Γ : Ctx ι} {ρ : Ty ι} {A : Formula F Γ}
    (env : interpCtx X Γ)
    (hA : dialecticaRealizerCtx si A env) :
    dialecticaRealizerCtx si (Formula.all ρ (A.weakenBy ρ)) env :=
  let hW := dialecticaWitness_weaken (X := X) ρ A
  let hC := dialecticaCounter_weaken (X := X) ρ A
  ⟨fun _ => cast hW.symm hA.val, fun ⟨z, yA⟩ =>
    (dialecticaMatrix_weaken si A env z (cast hW.symm hA.val) yA).mpr
      ((cast_cancel hW.symm hA.val).symm ▸ hA.property (cast hC yA))⟩

-- ============================================================================
-- Induction
-- ============================================================================

def dialectica_induction {Γ : Ctx ι} {A : Formula F (Ty.nat :: Γ)} (env : interpCtx X Γ)
    (hbase : dialecticaRealizerCtx si (A.subst0 Term.zero) env)
    (hstep : dialecticaRealizerCtx si (Formula.all Ty.nat
      (A →ᶠ Formula.substVar0 A (Term.app Term.succ (.var .vz)))) env) :
    dialecticaRealizerCtx si (Formula.all Ty.nat A) env := by
  have hW0  := dialecticaWitness_subst0 (X := X) A Term.zero
  have hC0  := dialecticaCounter_subst0 (X := X) A Term.zero
  have hW_sv : dialecticaWitness X (A.substVar0 (Term.app Term.succ (.var .vz))) =
               dialecticaWitness X A :=
    (dialectica_types_substF (X := X) A (Formula.Term.substVar0_map _)).1
  have hC_sv : dialecticaCounter X (A.substVar0 (Term.app Term.succ (.var .vz))) =
               dialecticaCounter X A :=
    (dialectica_types_substF (X := X) A (Formula.Term.substVar0_map _)).2
  -- Base witness w₀ : dW(A)
  let w₀ : dialecticaWitness X A := cast hW0 hbase.val
  have hbase_A : ∀ y : dialecticaCounter X A,
      dialecticaMatrix si A (Nat.zero, env) w₀ y := by
    intro y
    have hcc : cast hW0.symm w₀ = hbase.val :=
      eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    have key : dialecticaMatrix si (A.subst0 Term.zero) env (cast hW0.symm w₀) (cast hC0.symm y) →
        dialecticaMatrix si A (Nat.zero, env) w₀ y := by
      have h := (dialecticaMatrix_subst0 si A Term.zero env w₀ y).mp
      simp only [interpTerm] at h; exact h
    apply key; rw [hcc]
    exact hbase.property (cast hC0.symm y)
  -- Step witness
  let U := hstep.val
  -- Full witness by nat.rec
  let W : ℕ → dialecticaWitness X A :=
    fun n => Nat.rec w₀ (fun n ih => cast hW_sv ((U n).1 ih)) n
  refine ⟨W, fun ⟨n, y⟩ => ?_⟩
  change dialecticaMatrix si A (n, env) (W n) y
  suffices h : ∀ m (y : dialecticaCounter X A),
      dialecticaMatrix si A (m, env) (W m) y from h n y
  intro m
  induction m with
  | zero => exact hbase_A
  | succ m ih =>
    intro y
    have hprem := ih ((U m).2 (W m) (cast hC_sv.symm y))
    have hconc := hstep.property (m, (W m, cast hC_sv.symm y)) hprem
    have iff_step : dialecticaMatrix si (A.substVar0 (Term.app Term.succ (.var .vz))) (m, env)
        ((U m).1 (W m)) (cast hC_sv.symm y) ↔
        dialecticaMatrix si A (m.succ, env) (cast hW_sv ((U m).1 (W m))) y := by
      have h := dialecticaMatrix_substVar0 si A (Term.app Term.succ (.var .vz)) m env
          (cast hW_sv ((U m).1 (W m))) y
      have hcc_W : cast hW_sv.symm (cast hW_sv ((U m).1 (W m))) = (U m).1 (W m) :=
        eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
      rw [hcc_W] at h
      simp only [interpTerm, lookupVar] at h
      exact h
    exact iff_step.mp hconc

-- ============================================================================
-- Nonemptiness helpers (needed for exfalso / and_weak / or_weak)
-- ============================================================================

/-- `interpTy X ρ` is always nonempty given a `SpaceInterp`. -/
private lemma interpTy_nonempty {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) (ρ : Ty ι) : Nonempty (interpTy X ρ) := by
  induction ρ with
  | nat    => exact ⟨Nat.zero⟩
  | base i => exact ⟨si.zeroInterp i⟩
  | arr _ _ _ ihτ => exact ⟨fun _ => ihτ.some⟩

/-- Both `dialecticaWitness X A` and `dialecticaCounter X A` are nonempty. -/
private lemma dialectica_nonempty {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    (si : SpaceInterp X F) {Γ : Ctx ι} (A : Formula F Γ) :
    Nonempty (dialecticaWitness X A) ∧ Nonempty (dialecticaCounter X A) := by
  induction A with
  | bot     => exact ⟨⟨()⟩, ⟨()⟩⟩
  | eq0 _ _ => exact ⟨⟨()⟩, ⟨()⟩⟩
  | and _ _ ihA ihB =>
    exact ⟨⟨ihA.1.some, ihB.1.some⟩, ⟨ihA.2.some, ihB.2.some⟩⟩
  | or  _ _ ihA ihB =>
    exact ⟨⟨true, ihA.1.some, ihB.1.some⟩, ⟨ihA.2.some, ihB.2.some⟩⟩
  | imp _ _ ihA ihB =>
    exact ⟨⟨fun _ => ihB.1.some, fun _ _ => ihA.2.some⟩, ⟨ihA.1.some, ihB.2.some⟩⟩
  | all ρ _ ihA =>
    exact ⟨⟨fun _ => ihA.1.some⟩, ⟨(interpTy_nonempty si ρ).some, ihA.2.some⟩⟩
  | ex  ρ _ ihA =>
    exact ⟨⟨(interpTy_nonempty si ρ).some, ihA.1.some⟩, ⟨ihA.2.some⟩⟩

-- ============================================================================
-- Markov's principle
-- ============================================================================

def dialectica_markov {Γ : Ctx ι} {ρ : Ty ι} {A₀ : Formula F (ρ :: Γ)}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (env : interpCtx X Γ) :
    dialecticaRealizerCtx si (¬ᶠ(¬ᶠ(Formula.ex ρ A₀)) →ᶠ Formula.ex ρ A₀) env := by
  have hss := dialecticaWitness_subsingleton (X := X) A₀ hqf hvf
  have ssW : Subsingleton (dialecticaWitness X A₀) := hss.1
  have ssC : Subsingleton (dialecticaCounter X A₀) := hss.2
  set dfl := dialecticaDefault (X := X) A₀ hqf hvf
  set xN₀ : dialecticaWitness X (Formula.ex ρ A₀ →ᶠ ⊥ᶠ) :=
    (fun _ => (), fun _ _ => dfl.2)
  refine ⟨⟨fun xP => ((xP.2 xN₀ ()).1.1, dfl.1),
           fun _ _ => (xN₀, ())⟩, ?_⟩
  intro ⟨xP, yQ⟩ hprem
  have hprem' : dialecticaMatrix si (¬ᶠ¬ᶠex ρ A₀) env xP (xN₀, ()) := hprem
  have hyQ : yQ = dfl.2 := ssC.elim yQ dfl.2
  have hW : (xP.2 xN₀ ()).1.2 = dfl.1 := ssW.elim _ _
  change dialecticaMatrix si A₀ ((xP.2 xN₀ ()).1.1, env) dfl.1 yQ
  rw [hyQ, ← hW]
  exact Classical.not_not.mp hprem'

-- ============================================================================
-- Independence of premise
-- ============================================================================

def dialectica_ip {Γ : Ctx ι} {ρ σ : Ty ι}
    {A₀ : Formula F (σ :: Γ)} {B : Formula F (ρ :: Γ)}
    (hqf : A₀.isQF = true) (hvf : A₀.isVFree = true)
    (env : interpCtx X Γ) :
    dialecticaRealizerCtx si
      ((Formula.all σ A₀ →ᶠ Formula.ex ρ B) →ᶠ
       Formula.ex ρ ((Formula.all σ A₀).weakenBy ρ →ᶠ B)) env := by
  have hss := dialecticaWitness_subsingleton (X := X) A₀ hqf hvf
  have ssW : Subsingleton (dialecticaWitness X A₀) := hss.1
  have ssC : Subsingleton (dialecticaCounter X A₀) := hss.2
  set dfl := dialecticaDefault (X := X) A₀ hqf hvf
  have ssWAll : Subsingleton (dialecticaWitness X (Formula.all σ A₀)) :=
    ⟨fun f g => funext (fun _ => ssW.elim _ _)⟩
  set w₀ : dialecticaWitness X (Formula.all σ A₀) := fun _ => dfl.1
  set hWA := dialecticaWitness_weaken (X := X) ρ (Formula.all σ A₀)
  set hCA := dialecticaCounter_weaken (X := X) ρ (Formula.all σ A₀)
  refine ⟨⟨fun xH =>
            ((xH.1 w₀).1,
             (fun w' => (xH.1 (cast hWA w')).2,
              fun w' yB => cast hCA.symm (xH.2 (cast hWA w') yB))),
           fun xH ⟨w', yB⟩ => (cast hWA w', yB)⟩, ?_⟩
  intro ⟨⟨f, g⟩, ⟨w', yB⟩⟩ hprem
  have hw_eq : w₀ = cast hWA w' := ssWAll.elim _ _
  have hprem' : (dialecticaMatrix si A₀ ((g (cast hWA w') yB).1, env)
      (cast hWA w' (g (cast hWA w') yB).1) (g (cast hWA w') yB).2 →
      dialecticaMatrix si B ((f (cast hWA w')).1, env) (f (cast hWA w')).2 yB) := hprem
  change dialecticaMatrix si (weakenBy ρ (all σ A₀)) ((f w₀).1, env) w'
      (cast hCA.symm (g (cast hWA w') yB)) →
      dialecticaMatrix si B ((f w₀).1, env) (f (cast hWA w')).2 yB
  rw [hw_eq]
  intro hA
  apply hprem'
  -- The ∀σA₀ matrix at env from the weakened version
  have key := (dialecticaMatrix_weaken si (Formula.all σ A₀) env
    ((f (cast hWA w')).1) w'
    (cast hCA.symm (g (cast hWA w') yB))).mp hA
  have hcc : cast hCA (cast hCA.symm (g (cast hWA w') yB)) =
             g (cast hWA w') yB :=
    eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  rw [hcc] at key
  exact key

-- ============================================================================
-- Axiom of choice
-- ============================================================================

def dialectica_ac {Γ : Ctx ι} {ρ τ : Ty ι} {A : Formula F (τ :: ρ :: Γ)}
    (env : interpCtx X Γ) :
    dialecticaRealizerCtx si
      ((Formula.all ρ (Formula.ex τ A)) →ᶠ
       Formula.ex (ρ →ₜ τ) (Formula.all ρ (Formula.substF Formula.acSubst A))) env := by
  have hwA := (dialectica_types_substF (X := X) A (Formula.acSubst (ρ := ρ) (τ := τ))).1
  have hcA := (dialectica_types_substF (X := X) A (Formula.acSubst (ρ := ρ) (τ := τ))).2
  have acSubst_env : ∀ (x : interpTy X ρ) (Y : interpTy X ρ → interpTy X τ),
      interpCtxSubst si (Formula.acSubst (ρ := ρ) (τ := τ) (F := F) (Γ := Γ))
        (x, Y, env) = (Y x, x, env) := fun x Y => by
    simp only [Formula.acSubst, interpCtxSubst, interpTerm, lookupVar]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    have h1 : (fun {τ' : Ty ι} (v : Var Γ τ') =>
                (Term.var (Var.vs (Var.vs v)) : Term F (ρ :: (ρ →ₜ τ) :: Γ) τ')) =
              (fun {τ' : Ty ι} (v : Var Γ τ') =>
                (Term.var (Var.vs v) : Term F ((ρ →ₜ τ) :: Γ) τ').weaken) := by
      funext τ' v; rfl
    rw [h1, interpCtxSubst_weaken_eq]
    have h2 : (fun {τ' : Ty ι} (v : Var Γ τ') =>
                (Term.var (Var.vs v) : Term F ((ρ →ₜ τ) :: Γ) τ')) =
              (fun {τ' : Ty ι} (v : Var Γ τ') =>
                (Term.var v : Term F Γ τ').weaken) := by
      funext τ' v; rfl
    rw [h2, interpCtxSubst_weaken_eq, interpCtxSubst_id]
  exact ⟨⟨
    fun fp => ((fun x => (fp x).1), fun x => cast hwA.symm (fp x).2),
    fun fp xc => (xc.1, cast hcA xc.2)
  ⟩, fun ⟨fp, x, c'⟩ h => by
    simp only [dialecticaMatrix] at h ⊢
    have hcc : cast hcA.symm (cast hcA c') = c' := cast_cancel hcA c'
    rw [← hcc]
    rw [dialecticaMatrix_substF si A Formula.acSubst (x, fun z => (fp z).1, env) (fp x).2
          (cast hcA c')]
    rw [acSubst_env x (fun z => (fp z).1)]
    exact h⟩

-- ============================================================================
-- Soundness for the base Derivable proof system
-- ============================================================================

-- ============================================================================
-- Main soundness theorem (Theorem 3.0.7) — proved here to avoid circular import
-- ============================================================================

/-- Generalized Dialectica realizer for any context and environment.
    Matches on all constructors of `Derivable F EqX Allowed.extended`. -/
noncomputable def dialectica_soundness_ctx' {Γ : Ctx ι} (A : Formula F Γ) (env : interpCtx X Γ)
    (h : @Derivable ι F EqX Allowed.extended Γ A) : dialecticaRealizerCtx si A env := by
  suffices h_all : ∀ env' : interpCtx X Γ, dialecticaRealizerCtx si A env' from h_all env
  clear env
  induction h with
  -- Base constructors
  | or_contract   => intro env; exact dialectica_or_contract si env
  | and_contract  => intro env; exact dialectica_and_contract si env
  | or_weak       => intro env
                     exact dialectica_or_weak si env (dialectica_nonempty si _).1.some
  | and_weak      => intro env
                     exact dialectica_and_weak si env (dialectica_nonempty si _).2.some
  | or_perm       => intro env; exact dialectica_or_perm si env
  | and_perm      => intro env; exact dialectica_and_perm si env
  | exfalso       => intro env
                     exact dialectica_exfalso si env
                       (dialectica_nonempty si _).1.some
                       (dialectica_nonempty si _).2.some
  | forall_ax t   => intro env; exact dialectica_forall_ax si env t
  | exist_ax t _  => intro env; exact dialectica_exist_ax si env t
  | mp _ _ iha ihab =>
    intro env; exact dialectica_mp si env (iha env) (ihab env)
  | syllogism _ _ ihAB ihBC =>
    intro env; exact dialectica_syllogism si env (ihAB env) (ihBC env)
  | exportation _ ih =>
    intro env; exact dialectica_exportation si env (ih env)
  | importation _ ih =>
    intro env; exact dialectica_importation si env (ih env)
  | expansion _ ih =>
    intro env; exact dialectica_expansion si env (ih env)
  | forall_rule _ ih => exact dialectica_forall_rule si ih
  | exist_rule _ ih  => exact dialectica_exist_rule si ih
  | univ_gen _ ih =>
    intro env; exact dialectica_univ_gen si env (ih env)
  | succ_ne_zero =>
    intro env
    exact ⟨fun _ => ⟨id, fun _ _ => ()⟩,
           fun ⟨n, (), ()⟩ h => by
             simp only [dialecticaMatrix, interpTerm, lookupVar] at h ⊢
             exact Nat.succ_ne_zero n h⟩
  | succ_inj =>
    intro env
    exact ⟨fun _ _ => ⟨id, fun _ _ => ()⟩,
           fun ⟨m, n, (), ()⟩ h => by
             simp only [dialecticaMatrix, interpTerm, lookupVar] at h ⊢
             exact Nat.succ.inj h⟩
  | proj_ax =>
    intro env
    exact eqAtType_from_semEq si eqxi _ _ _ env (by simp [interpTerm, Term.app2])
  | comb_ax =>
    intro env
    exact eqAtType_from_semEq si eqxi _ _ _ env (by simp [interpTerm, Term.app3])
  | rec_zero =>
    intro env
    exact eqAtType_from_semEq si eqxi _ _ _ env (by simp [interpTerm, Term.app3]; rfl)
  | rec_succ =>
    intro env
    exact eqAtType_from_semEq si eqxi _ _ _ env (by simp [interpTerm, Term.app3, Term.app2])
  | refl0  => intro env; exact dialectica_refl0 si env
  | sym0   => intro env; exact dialectica_sym0 si env
  | trans0 => intro env; exact dialectica_trans0 si env
  | qfer hqf hvf _ ih =>
    intro env; exact dialectica_qfer si eqxi hqf hvf ih env
  | «induction» _ _ ih_base ih_step =>
    intro env
    exact dialectica_induction si env (ih_base env) (ih_step env)
  -- Extension constructors
  | markov _ hqf hvf   => intro env; exact dialectica_markov si hqf hvf env
  | ip _ hqf hvf       => intro env; exact dialectica_ip si hqf hvf env
  | ac _               => intro env; exact dialectica_ac si env
  -- Impossible (Allowed.extended.lem = false, qfac = false)
  | lem h_lem          => exact absurd h_lem (by decide)
  | qfac h_qfac _      => exact absurd h_qfac (by decide)

/-- **Dialectica Soundness Theorem** (Theorem 3.0.7). -/
noncomputable def dialectica_soundness' (A : Formula F ([] : Ctx ι))
    (h : @Derivable ι F EqX Allowed.extended [] A) : dialecticaRealizer si A :=
  dialectica_soundness_ctx' si eqxi A () h
