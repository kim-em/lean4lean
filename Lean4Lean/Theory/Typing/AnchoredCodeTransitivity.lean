import Lean4Lean.Theory.Typing.AnchoredRankLaws

namespace Lean4Lean.AnchoredSemantics
open VEnv AnchoredProfiles
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem TypeRelated.trans
    (henv : env.Ordered) {Γ : List VExpr} {left middle right : VExpr}
    {profile : Profile n}
    (first : TypeRelated env U registry Γ left middle profile)
    (second : TypeRelated env U registry Γ middle right profile) :
    TypeRelated env U registry Γ left right profile :=
  (rankLaws henv n).codeTrans _ _ _ _ _ first second

end Lean4Lean.AnchoredSemantics
