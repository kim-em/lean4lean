import Lean4Lean.Theory.Typing.AnchoredDomainChain

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def DomainChain.view
    {input : Profile n} (chain : DomainChain env U registry Γ input left right)
    (anchor : VExpr) (output : Atom n) :
    AtomView env U registry Γ (n := n + 1)
      (.fn ⟨left, anchor, input⟩ output) (.fn ⟨right, anchor, input⟩ output) := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    exact .trans (.domainRekey path typed formed related) ih

end Lean4Lean.AnchoredSemantics
