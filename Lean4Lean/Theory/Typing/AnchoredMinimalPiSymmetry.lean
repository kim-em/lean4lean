import Lean4Lean.Theory.Typing.AnchoredSupportBasis
import Lean4Lean.Theory.Typing.AnchoredFrame
import Lean4Lean.Theory.Typing.DependentTypeConversion

/-! Symmetry of an actual Pi witness. Each raw-key domain bridge is rebuilt
at a finite hereditary support before changing the displayed left endpoint.
All assumed semantic operations concern the strictly smaller rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def PiWitness.symm
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lowerFocus : ∀ Γ left right (value support bound : Profile n),
      Minimal value support → value.HasType support → support ≤ bound →
      TypeRelated env U registry Γ left right bound →
      TypeRelated env U registry Γ left right support)
    (lowerCompose : ∀ Γ left middle right (value support other : Profile n),
      Minimal value support → value.HasType other →
      TypeRelated env U registry Γ left middle support →
      TypeRelated env U registry Γ middle right other →
      TypeRelated env U registry Γ left right support)
    (lowerSymm : ∀ Γ left right (support : Profile n), support.WF →
      TypeRelated env U registry Γ left right support →
      TypeRelated env U registry Γ right left support)
    {Γ : List VExpr} {left right A B : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)}
    (domainWF : domain.WF)
    (rowsWF : ∀ key output, (key, output) ∈ rows → output.WF)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ right left A B domain rows := by
  have hΓ := display.leftExposure.terminal.targetWF henv
    (display.leftExposure.post.targetWF henv)
  have change : ∀ C D, TypeConversion env U (display.leftDomain :: display.context) C D →
      TypeConversion env U (display.rightDomain :: display.context) C D := by
    intro C D path
    obtain ⟨u, hu⟩ := display.leftDomainType
    obtain ⟨v, hv⟩ := display.rightDomainType
    exact TypeConversion.changeDomain henv hΓ hv hu display.domains.symm path
  have bodies := change _ _ display.bodies.symm
  have prototype := change _ _ (display.bodies.symm.trans display.prototypeBodyPath)
  refine {
    context := display.context
    map := display.map
    leftDomain := display.rightDomain
    leftBody := display.rightBody
    rightDomain := display.leftDomain
    rightBody := display.leftBody
    leftExposure := display.rightExposure
    rightExposure := display.leftExposure
    leftDomainType := display.rightDomainType
    rightDomainType := display.leftDomainType
    leftBodyType := display.rightBodyType
    rightBodyType := display.leftBodyType
    domains := display.domains.symm
    bodies := bodies
    prototypeDomainPath := display.domains.symm.trans display.prototypeDomainPath
    prototypeBodyPath := prototype
    domainRelated := lowerSymm _ _ _ _ (Profile.rename_wf_iff.mpr domainWF)
      display.domainRelated
    rowDomains := ?_
    rowBodies := ?_ }
  · intro key output hm
    obtain ⟨support, hs, hsort, hle, path, link⟩ := display.rowDomains key output hm
    obtain ⟨selected, hselected⟩ := Basis.exists hs
    obtain ⟨selectedTyped, selectedBound⟩ := Basis.valid hselected
    have selectedMinimal := Basis.minimal hselected
    have focused := lowerFocus _ _ _ _ _ _ selectedMinimal selectedTyped selectedBound link
    have largeTyped := hs.enlarge hle (Profile.rename_wf_iff.mpr domainWF)
    have bridge := lowerCompose _ _ _ _ _ _ _ selectedMinimal largeTyped focused
      display.domainRelated
    exact ⟨selected, selectedTyped,
      hsort.restrict selectedBound selectedTyped.wf_type,
      Profile.le_trans selectedBound hle, path.trans display.domains, bridge⟩
  · intro key output hm Δ ρ future x y admitted
    obtain ⟨hl, hr, hc⟩ := display.rowBodies key output hm Δ ρ future x y admitted
    exact ⟨hr, hl, lowerSymm _ _ _ _ (Profile.rename_wf_iff.mpr (rowsWF key output hm)) hc⟩

end Lean4Lean.AnchoredSemantics
