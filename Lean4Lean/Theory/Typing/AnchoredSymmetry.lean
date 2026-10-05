import Lean4Lean.Theory.Typing.AnchoredRankLaws

namespace Lean4Lean.AnchoredSemantics
open VEnv AnchoredProfiles
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem Related.symm
    (henv : env.Ordered)
    {Γ : List VExpr} {left right type : VExpr} {value typeProfile : Profile n}
    (H : Related env U registry Γ left right type value typeProfile) :
    Related env U registry Γ right left type value typeProfile :=
  (rankLaws henv n).termSymm _ _ _ _ _ _ H

end Lean4Lean.AnchoredSemantics
