import Metatheorems.Dialectica.Syntactic
import Metatheorems.NegTrans

namespace Metatheorems

/-- Syntactic ND: classical derivation of `A` → a **term** realizing `Aᴺᵀ`. -/
def syntactic_nd_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    {EqX : (i : ι) → {Γ : Ctx ι} → Term F Γ (Ty.base i) → Term F Γ (Ty.base i) → Formula F Γ}
    (eqxi : EqXInterp X F si EqX)
    {Premises : PremiseSet F}
    (adm : AdmissibleEqX EqX Premises)
    (nts : NTStableD EqX Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : @Derivable ι F EqX Allowed.classical Premises Γ A) :
    SRealizer si Aᴺᵀ :=
  syntactic_soundness eqxi spremise
    ((negTrans_sound adm nts h).castAllowed (by constructor <;> decide))

end Metatheorems
