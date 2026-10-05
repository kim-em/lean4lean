import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def GradedTransferResult.empty :
    GradedTransferResult env U registry target locals σ τ available
      left right sourceType (Profile.empty (n := n)) where
  rank := n
  bound := Nat.le_refl _
  rawDemand := .empty
  resultFootprint := []
  observation := .empty
  adapter := by rw [raiseProfile_self]; exact .nil _
  resultAvailable := fun _ _ h => nomatch h
  support := .empty
  typeFootprint := []
  certificate := .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  typeAvailable := fun _ _ h => nomatch h
  typed := by rw [raiseProfile_self]; exact Profile.HasType.empty Profile.WF.empty
  rawTyped := Profile.HasType.empty Profile.WF.empty
  typeCode := by
    cases n <;> exact fun Δ ρ insertion atom hm => nomatch hm
  related := by
    rw [raiseProfile_self]
    cases n <;> exact fun _ h => nomatch h
  rawRelated := by cases n <;> exact fun _ h => nomatch h

end Lean4Lean.AnchoredSource.Adapted
