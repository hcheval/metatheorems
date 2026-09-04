import Metatheorems.Dialectica.Syntactic
import Metatheorems.NegTrans

namespace Metatheorems

/-- Syntactic ND: classical derivation of `A` → a **term** realizing `Aᴺᵀ`. -/
def syntactic_nd_soundness
    {ι : Type} {X : ι → Type} {F : ι → Ty ι}
    {si : SpaceInterp X F}
    (eqxi : EqXInterp X F si)
    {Premises : PremiseSet F}
    (nts : NTStableD Premises)
    (spremise : ∀ (Γ' : Ctx ι) (B : Formula F Γ'), Premises ⟨Γ', B⟩ → SRealizer si B)
    {Γ : Ctx ι} {A : Formula F Γ}
    (h : @Derivable ι ι F Allowed.classical Premises Γ A) :
    SRealizer si Aᴺᵀ :=
  syntactic_soundness eqxi spremise
    ((negTrans_sound nts h).castAllowed (by constructor <;> decide))

end Metatheorems
