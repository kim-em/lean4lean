import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalPiLevels

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Universe equality comes from a real literal-sort query at the two
assigned original formations, including a proof-relevant flag of false. -/
theorem OriginalRichDisplayCoherence.sortLevels
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    {leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable}
    {rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable}
    (answer : OriginalRichDisplayCoherence leftFrame rightFrame)
    (formed : OnCtx target (env.IsType U))
    (leftSort : left.sourceType = .sort leftLevel)
    (rightSort : right.sourceType = .sort rightLevel) : leftLevel ≈ rightLevel := by
  classical
  have flag : ∃ relevant, Relevant leftLevel relevant := by
    by_cases zero : leftLevel ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  obtain ⟨relevant, flag⟩ := flag
  let query : RichCert leftEnv env U registry target left.node.typeFormation.node leftLocals
      (left.sourceSubst common) true (Profile.sort (n := 0) relevant) [] := .legacy (by
    rw [leftSort]
    exact .seed (.sort flag) (Profile.HasType.sort relevant))
  obtain ⟨result⟩ := answer.queries query (fun _ _ member => nomatch member)
  have related := result.related
  rw [leftSort, rightSort] at related
  exact TypeRelated.literalSortLevels formed related

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
