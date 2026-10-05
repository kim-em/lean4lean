import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax

/-! Inward exposure of a query at an actual original reference. The finite
query is traversed structurally; projected fields and majors keep their
original endpoints. No semantic comparison of the reference and its exposed
child is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option Elab.async false

/-- Remove only the initial exposure from an actual projection route. -/
def exposeProjectionReference
    {reference : EndpointRef sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead (.ref reference)) : ProjectionHead reference.expose := by
  rcases head with ⟨info, registered, levels, levelsWF, levelCount, parameters,
    parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
    fieldLevel, fieldWF, field, originalMajor, closed, relevance, route⟩
  cases route with
  | expose reference rest =>
    exact ⟨info, registered, levels, levelsWF, levelCount, parameters,
      parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
      fieldLevel, fieldWF, field, originalMajor, closed, relevance, rest⟩

mutual
/-- Expose an original code reference without replacing any retained child. -/
def RichCert.exposeReference
    {reference : EndpointRef sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target (.ref reference)
      locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target reference.expose
      locals σ relevant profile footprint := by
  match certificate with
  | .legacy source => exact .legacy source
  | .recipe code => exact .recipe code
  | .observe source formed => exact .observe source.exposeReference formed
  | .route (.done _) source => exact source.exposeReference
  | .route (.expose _ rest) source => exact .route rest source
  | .union first second => exact .union first.exposeReference second.exposeReference
  | .pad source => exact .pad source.exposeReference
  | .down source => exact .down source.exposeReference
  | .map view source => exact .map view source.exposeReference
  | .support action source => exact .support action source.exposeReference
  | .select source member => exact .select source.exposeReference member
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; all_goals omega

/-- Full rich observation exposure, including native projection metadata,
arbitrary finite wrappers, and earlier declaration queries. -/
def RichObs.exposeReference
    {reference : EndpointRef sourceEnv U source expression assigned}
    (observation : RichObs sourceEnv env U registry target (.ref reference)
      locals σ profile footprint) :
    RichObs sourceEnv env U registry target reference.expose locals σ profile footprint := by
  match observation with
  | .rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed =>
    exact .rigidFamily (node := reference.expose) origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed
  | .family (name := name) (levels := levels) origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .family (node := reference.expose) origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .constructor (name := name) (levels := levels) origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .constructor (node := reference.expose) origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .canonicalDelta (name := name) (levels := levels) (strata := strata) lookup nameEq registered seedWF seedLength levelsWF
      equivalent bodyClosed typeClosed certificate typed body =>
    exact .canonicalDelta (node := reference.expose) (strata := strata) lookup nameEq registered seedWF seedLength levelsWF
      equivalent bodyClosed typeClosed certificate typed body
  | .canonicalConst (name := name) (levels := levels) origin realization query resources =>
    exact .canonicalConst (node := reference.expose) origin realization query resources
  | .legacy source => exact .legacy source
  | .code source => exact .code source.exposeReference
  | .projection head nameEq member majorObservation fieldCertificate typed alignment =>
    rcases head with ⟨info, registered, levels, levelsWF, levelCount, parameters,
      parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
      fieldLevel, fieldWF, field, originalMajor, closed, relevance, route⟩
    cases route with
    | expose reference rest =>
      exact .projection ⟨info, registered, levels, levelsWF, levelCount, parameters,
        parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
        fieldLevel, fieldWF, field, originalMajor, closed, relevance, rest⟩
        nameEq member majorObservation fieldCertificate typed alignment
  | .projectionSortable head nameEq member majorObservation selectedAtom path sortable fieldCertificate typed =>
    rcases head with ⟨info, registered, levels, levelsWF, levelCount, parameters,
      parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
      fieldLevel, fieldWF, field, originalMajor, closed, relevance, route⟩
    cases route with
    | expose reference rest =>
      exact .projectionSortable ⟨info, registered, levels, levelsWF, levelCount, parameters,
        parameterCount, indices, indexCount, sourceMajor, fieldType, selected,
        fieldLevel, fieldWF, field, originalMajor, closed, relevance, rest⟩
        nameEq member majorObservation selectedAtom path sortable fieldCertificate typed
  | .route (.done _) source => exact source.exposeReference
  | .route (.expose _ rest) source => exact .route rest source
  | .union first second => exact .union first.exposeReference second.exposeReference
  | .view source view => exact .view source.exposeReference view
  | .action source action => exact .action source.exposeReference action
  | .select source member => exact .select source.exposeReference member
  | .pad source => exact .pad source.exposeReference
  | .unpad source => exact .unpad source.exposeReference
termination_by sizeOf observation
decreasing_by all_goals simp_wf; all_goals omega
end

/-- References with the same actual exposure share the complete source query.
Only the reference route changes; its profile and resources are identical. -/
def RichObs.changeReference
    {first second : EndpointRef sourceEnv U source expression assigned}
    (same : first.expose = second.expose)
    (observation : RichObs sourceEnv env U registry target (.ref first)
      locals σ profile footprint) :
    RichObs sourceEnv env U registry target (.ref second) locals σ profile footprint :=
  .route (.expose second (.done _)) (same ▸ observation.exposeReference)

def RichCert.changeReference
    {first second : EndpointRef sourceEnv U source expression assigned}
    (same : first.expose = second.expose)
    (certificate : RichCert sourceEnv env U registry target (.ref first)
      locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target (.ref second) locals σ relevant profile footprint :=
  .route (.expose second (.done _)) (same ▸ certificate.exposeReference)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
