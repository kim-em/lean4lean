import Lean4Lean.Theory.Typing.AnchoredSupportLaws

/-! The joint induction boundary for code and term equality. A family code
observes lower-rank terms as its arguments, so code support and term equality
must be established together at each rank. -/

namespace Lean4Lean.AnchoredSemantics
open VEnv AnchoredProfiles

structure RankLaws (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (n : Nat) : Prop extends SupportLaws env U registry n where
  codeTrans : ∀ Γ left middle right (profile : Profile n),
    TypeRelated env U registry Γ left middle profile →
    TypeRelated env U registry Γ middle right profile →
    TypeRelated env U registry Γ left right profile
  termSymm : ∀ Γ left right type (value support : Profile n),
    Related env U registry Γ left right type value support →
    Related env U registry Γ right left type value support
  termTrans : registry.Scoped → ∀ Γ left middle right type (value first second : Profile n),
    Related env U registry Γ left middle type value first →
    Related env U registry Γ middle right type value second →
    Related env U registry Γ left right type value second

end Lean4Lean.AnchoredSemantics
