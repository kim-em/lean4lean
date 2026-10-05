import Lean4Lean.Theory.Typing.AnchoredRecordIntroduction
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginTransport
import Lean4Lean.Theory.Typing.AnchoredTraceTerm

/-! Literal constructors provide record fields by actual primitive projection
steps. Each field keeps its original frozen domain, input and support. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem RankedData.ProjectionOrigin.typed
    (origin : RankedData.ProjectionOrigin env U Γ info name index major assignedType domain) :
    env.HasType U Γ (.proj name index major) domain :=
  origin.fieldPath.cast (.projDF origin.registered origin.levelsWF origin.levelCount
    origin.paramCount origin.indexCount origin.selected origin.formation origin.majorEq
    origin.majorEq origin.ctorClosed origin.guard)

private theorem projection_trace
    (lookup : registry.projections name = some info)
    (selected : args[info.nparams + index]? = some field) :
    CanonicalDataHead.Trace registry
      (.proj name index (mkApps (.const info.ctorName levels) args)) [] field := by
  apply CanonicalDataHead.Trace.next (out := ⟨[], field⟩) _ .refl
  have projected : CanonicalDataHead.project registry name index
      (mkApps (.const info.ctorName levels) args) = some field := by
    simp only [CanonicalDataHead.project, lookup, bind, Option.bind_some,
      spine_mkApps_exact (.const info.ctorName levels) args rfl, ↓reduceIte, selected]
  simp only [CanonicalDataHead.step, CanonicalHead.step, getAppFnArgs, getAppFnArgs.go,
    CanonicalHead.spineStep, projected]

private theorem prepend_closed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right result result' domain : VExpr} {input support : Profile n}
    (leftTrace : CanonicalDataHead.Trace registry left [] result)
    (rightTrace : CanonicalDataHead.Trace registry right [] result')
    (leftEq : env.IsDefEq U Γ left result domain)
    (rightEq : env.IsDefEq U Γ right result' domain)
    (related : Related env U registry Γ result result' domain input support) :
    Related env U registry Γ left right domain input support := by
  apply Related.prependEndpoints henv hscoped (.traced leftTrace) (.traced rightTrace)
    (show ProofInsertion env U Γ ([] ++ Γ) (.skipN .refl [].length) from .refl formed)
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using leftEq
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using rightEq
  · simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl, Profile.rename_refl] using related

theorem RankedData.RequestAdmission.literalProjection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {info : VProjectionInfo} {name : Name} {index : Nat}
    {levels levels' : List VLevel} {args args' : List VExpr} {field field' type : VExpr}
    {request : DataRequest (Profile n)}
    (lookup : registry.projections name = some info)
    (leftOrigin : RankedData.ProjectionOrigin env U Γ info name index
      (mkApps (.const info.ctorName levels) args) type request.domain)
    (rightOrigin : RankedData.ProjectionOrigin env U Γ info name index
      (mkApps (.const info.ctorName levels') args') type request.domain)
    (leftSelected : args[info.nparams + index]? = some field)
    (rightSelected : args'[info.nparams + index]? = some field')
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) Γ
      request field field') :
    RankedData.RequestAdmission env U (relations env U registry n) Γ request
      (.proj name index (mkApps (.const info.ctorName levels) args))
      (.proj name index (mkApps (.const info.ctorName levels') args')) := by
  have leftEq := IsDefEq.projIota leftOrigin.registered leftOrigin.typed
    leftSelected admitted.2.1.hasType.1
  have rightEq := IsDefEq.projIota rightOrigin.registered rightOrigin.typed
    rightSelected admitted.2.1.hasType.2
  have leftTrace := projection_trace (levels := levels) lookup leftSelected
  have rightTrace := projection_trace (levels := levels') lookup rightSelected
  refine ⟨admitted.1.trans leftEq.symm, leftEq.trans (admitted.2.1.trans rightEq.symm),
    admitted.2.2.1, admitted.2.2.2.1, admitted.2.2.2.2.1, ?_, ?_⟩
  · exact prepend_closed henv hscoped formed .refl leftTrace
      admitted.1.hasType.1 leftEq admitted.2.2.2.2.2.1
  · exact prepend_closed henv hscoped formed leftTrace rightTrace
      leftEq rightEq admitted.2.2.2.2.2.2

end Lean4Lean.AnchoredSemantics
