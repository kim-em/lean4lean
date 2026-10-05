import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental

/-! A concrete forward source observer and an already proved reverse rule
give the forward semantic comparison. Original left-side adequacy supplies
only the caller's requested type support; the reverse rule supplies the cross
comparison at the actual returned observation's grade. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GradedResult.forwardComparison
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    {left right assigned : VExpr} {demand : Profile n} {footprint : Footprint}
    (original : GradedTransfer env U registry target locals σ σ available left left assigned)
    (reverse : Transfer env U registry target locals σ σ available right left assigned)
    (observation : Obs env U registry target locals σ left demand footprint)
    (resources : footprint.Available available)
    (forward : GradedResult env U registry target locals σ available right demand) :
    Nonempty (GradedTransferResult env U registry target locals σ σ
      available left right assigned demand) := by
  obtain ⟨self⟩ := original observation resources
  obtain ⟨back⟩ := reverse forward.observation forward.resources
  have originalTyped := Profile.HasType.raise forward.bound self.requestedTyped
  have originalCode := TypeRelated.raise henv forward.bound
    (TypeRelated.lower henv self.bound self.typeCode)
  have wf := originalTyped.wf_type.union back.typed.wf_type
  have typed := originalTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := back.typed.enlarge (Profile.le_union_right _ _) wf
  have code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ)
      ((raiseProfile forward.rank forward.bound (lowerProfile n self.bound self.support)).union
        back.support) := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => originalCode.singleton h) (fun h => back.typeCode.singleton h)
  have cross := NormalProfileAdapter.termMap forward.adapter henv hscoped hTarget
    typed code (Related.symm henv back.related)
  exact ⟨{
    rank := forward.rank
    bound := forward.bound
    rawDemand := forward.raw
    resultFootprint := forward.footprint
    observation := forward.observation
    adapter := forward.adapter
    resultAvailable := forward.resources
    support := _
    typeFootprint := self.typeFootprint ++ back.typeFootprint
    certificate := .union (self.requestedCertificate.raise forward.bound) back.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (self.typeAvailable i need) (back.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := cross
    rawRelated := Related.retag henv rawTyped code back.related.left_diagonal }⟩

end Lean4Lean.AnchoredSource.Adapted
