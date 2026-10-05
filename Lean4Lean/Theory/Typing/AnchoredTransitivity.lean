import Lean4Lean.Theory.Typing.AnchoredRankLaws

namespace Lean4Lean.AnchoredSemantics
open VEnv AnchoredProfiles
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem Related.trans
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left middle right type : VExpr}
    {value firstType secondType : Profile n}
    (first : Related env U registry Γ left middle type value firstType)
    (second : Related env U registry Γ middle right type value secondType) :
    Related env U registry Γ left right type value secondType :=
  (rankLaws henv n).termTrans hscoped _ _ _ _ _ _ _ _ first second

end Lean4Lean.AnchoredSemantics
