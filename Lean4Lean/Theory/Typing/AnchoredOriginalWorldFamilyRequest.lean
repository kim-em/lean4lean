import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySourceRequests
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation

/-! The selected source request is shared by family parsing and productive
projection-field replay. Keep its exact observer and annotation together. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false

/-- The selected request owns its actual query and its control evidence in
one packet, so later selection cannot choose a different unannotated query. -/
structure WorldRichFamilySourceRequest
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (request : DataRequest (Profile n)) where
  argument : RichFamilyArgumentQuery root env registry target source locals σ available expression request.input
  controlled : ControlledStoredQuery controls frontier (.observation argument.query.observation)
  anchor : env.IsDefEq U target request.anchor (expression.subst σ) request.domain


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
