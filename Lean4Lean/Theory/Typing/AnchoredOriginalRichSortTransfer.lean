import Lean4Lean.Theory.Typing.AnchoredOriginalRichSortQueries
import Lean4Lean.Theory.Typing.AnchoredSortableSortRule
import Lean4Lean.Theory.Typing.AnchoredSortableReflection
import Lean4Lean.Theory.Typing.AnchoredSortableRealization
import Lean4Lean.Theory.Typing.AnchoredSortableScope
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRichComparison

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- Literal universe transfer rebuilds every finite code/action wrapper at
its actual destination formation. Its source syntax has no local leaves. -/
theorem RichCodeTransfer.literalSort
    {left : EndpointState leftEnv U leftSource (.sort leftLevel) (.sort leftAssigned)}
    {right : EndpointState rightEnv U rightSource (.sort rightLevel) (.sort rightAssigned)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : leftAvailable.AtomClosed)
    (leftWF : leftLevel.WF U) (rightWF : rightLevel.WF U)
    (equal : leftLevel ≈ rightLevel) :
    RichCodeTransfer env U registry target left right leftLocals rightLocals σ τ
      leftAvailable rightAvailable := by
  intro relevant n profile footprint query resources
  obtain ⟨_, ⟨query⟩, resources⟩ := query.sortQuery closed resources
  obtain ⟨answer⟩ := query.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed formed resources
  obtain ⟨required, ⟨certificate⟩, same⟩ := answer.certificate.reflectSource (e := .sort rightLevel) .refl rfl rightLocals
  have certificate : SortableCert env U registry target rightLocals τ (.sort rightLevel)
      relevant profile required := by simpa only [Subst.lift_l_refl] using certificate
  have available : required.Available rightAvailable := by
    intro index need member
    have impossible := certificate.scoped (count := 0) trivial index need member
    omega
  exact ⟨⟨required, .legacy certificate, available, answer.related⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
