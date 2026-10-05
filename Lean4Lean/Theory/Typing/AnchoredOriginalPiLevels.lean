import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy

/-! Universe equality read from an actual finite code query on the fixed
original pair. This uses literal canonical exposure, not raw sort injectivity. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem SortRelated.literal_levels
    (related : SortRelated env U registry target (.sort left) (.sort right) flag) :
    left ≈ right := by
  obtain ⟨_, _, _, _, ⟨leftExposure⟩, ⟨rightExposure⟩, equal, _⟩ := related
  have leftEq := VExpr.sort.inj leftExposure.literalSort_head
  have rightEq := VExpr.sort.inj rightExposure.literalSort_head
  exact leftEq ▸ rightEq ▸ equal

theorem TypeRelated.literalSortLevels
    (hTarget : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort left) (.sort right)
      (Profile.sort (n := 0) flag)) : left ≈ right := by
  have witness := related target .refl (.refl hTarget) flag (List.mem_singleton_self _)
  exact SortRelated.literal_levels witness

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- A fixed original C answer has enough finite information to compare the
levels of literal assigned sorts, independently of its raw conversion path. -/
theorem DisplayCoherenceAnswer.sortLevels
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    (answer : DisplayCoherenceAnswer env registry target left right common available leftLocals rightLocals)
    (hTarget : OnCtx target (env.IsType U))
    (leftSort : left.sourceType = .sort leftLevel)
    (rightSort : right.sourceType = .sort rightLevel) : leftLevel ≈ rightLevel := by
  classical
  have flag : ∃ relevant, Relevant leftLevel relevant := by
    by_cases zero : leftLevel ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  obtain ⟨relevant, flag⟩ := flag
  let query : CodeCert env U registry target leftLocals (left.sourceSubst common)
      left.sourceType (Profile.sort (n := 0) relevant) [] := by
    rw [leftSort]
    exact .seed (.sort flag) (Profile.HasType.sort relevant)
  obtain ⟨result⟩ := answer.queries query (fun _ _ member => nomatch member)
  have relation := result.related
  rw [leftSort, rightSort] at relation
  exact TypeRelated.literalSortLevels hTarget relation

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
