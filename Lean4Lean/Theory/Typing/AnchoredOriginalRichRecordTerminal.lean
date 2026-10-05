import Lean4Lean.Theory.Typing.AnchoredOriginalSelectedRecordCaptures
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyCaptures
import Lean4Lean.Theory.Typing.AnchoredRecordIntroduction

/-! A record terminal uses the constructor's actual original header and
target projection registration. It opens no projection metadata proof root.
Selected fields retain demand order, including repeated and empty requests.
The elimination guard is needed only when at least one field is requested. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem recordCaptureAt (count : Nat) (σ : Subst) (i : Nat) (hi : i < count) :
    nativeCaptureSubst (realizedCaptures count σ) i = σ i := by
  simp [nativeCaptureSubst, realizedCaptures, constantCaptureVariables, hi,
    List.getElem_reverse, List.getElem_range]
  congr 1 <;> omega

private theorem captureVariableBound
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (member : .bvar index ∈ expressions) : index < source.length := by
  match captures with
  | .nil => cases member
  | .cons lookup value adapter alignment anchor tail =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact lookup.lt
    · exact captureVariableBound tail later
termination_by sizeOf captures
decreasing_by simp_wf; omega

/-- The semantic record terminal has no recursive original call: its family
support is already interpreted, and the exact selected field admissions come
from the actual header frame. In particular, target registration need not be
present in the original constructor environment. -/
theorem richRecordTerminal
    {info : VConstant} {levels : List VLevel} {demand : RecordData (Profile n)}
    {signature : ConstantTelescope (info.type.instL levels)}
    {header : EndpointRef headerEnv U [] (info.type.instL levels) (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {headerSource : List VExpr} {context : ContextDerivation headerEnv U headerSource}
    (sourceEq : headerSource = signature.domains.reverse)
    (resultNode : EndpointState headerEnv U headerSource signature.result (.sort resultLevel))
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {projection : VProjectionInfo}
    (registered : env.projections demand.family.name projection)
    (projectionLookup : registry.projections demand.family.name = some projection)
    (unindexed : projection.nindices = 0)
    (lookup : env.constants projection.ctorName = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelLength : levels.length = info.uvars)
    (inert : CanonicalDataHead.HeadInert registry projection.ctorName)
    (relevant : demand.fields ≠ [] → (projection.resultLevel.inst levels).IsNeverZero)
    (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    {target : List VExpr} {arguments : List VExpr} {σ τ : Subst}
    {footprint : Footprint} {available : Valuation}
    (saturated : arguments.length = signature.domains.length)
    (captures : FamilyCaptures env U registry target headerSource (List.range arguments.length)
      σ (demand.fields.map fun entry => .bvar
        (arguments.length - 1 - (projection.nparams + entry.1)))
      (demand.fields.map (·.2)) footprint)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target
      context (List.range arguments.length) σ τ available)
    (resources : footprint.Available available)
    {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.record demand)).HasType support)
    (code : TypeRelated env U registry target (signature.result.subst σ) (signature.result.subst σ) support) :
    Related env U registry target
      (mkApps (.const projection.ctorName levels) (realizedCaptures arguments.length σ))
      (mkApps (.const projection.ctorName levels) (realizedCaptures arguments.length τ))
      (signature.result.subst σ) (Profile.singleton (n := n + 1) (.record demand)) support := by
  have count : headerSource.length = arguments.length := by
    simp only [sourceEq, List.length_reverse, saturated]
  have actualFields := captures.interpretRichFrame henv hscoped formed frame substitutions resources
  have finiteCaptures := captures.atRealizedPrefix (CtxWF.closed henv substitutions.wf)
  have finiteRaw := realizedCaptureSubstitution henv substitutions.wf substitutions
  rw [count] at finiteCaptures finiteRaw
  have lengthσ : (realizedCaptures arguments.length σ).length = arguments.length := by
    simp [realizedCaptures, constantCaptureVariables]
  have lengthτ : (realizedCaptures arguments.length τ).length = arguments.length := by
    simp [realizedCaptures, constantCaptureVariables]
  have resultClosed : signature.result.ClosedN arguments.length := by
    simpa only [count] using VExpr.WF.closedN henv
      ⟨_, resultNode.sound.defeq.mono below⟩ (CtxWF.closed henv substitutions.wf)
  have resultSame : signature.result.subst
      (nativeCaptureSubst (realizedCaptures arguments.length σ)) = signature.result.subst σ :=
    subst_congr_closedN resultClosed (recordCaptureAt arguments.length σ)
  have fieldAt : ∀ entry ∈ demand.fields,
      arguments.length - 1 - (projection.nparams + entry.1) < arguments.length := by
    intro entry member
    simpa only [count] using captureVariableBound captures (List.mem_map_of_mem member)
  have realizedFields (realization : Subst) :
      demand.fields.map (fun entry => nativeCaptureSubst (realizedCaptures arguments.length realization)
        (arguments.length - 1 - (projection.nparams + entry.1))) =
      demand.fields.map (fun entry => realization
        (arguments.length - 1 - (projection.nparams + entry.1))) := by
    apply List.map_congr_left
    intro entry member
    exact recordCaptureAt arguments.length realization _ (fieldAt entry member)
  have selected := FamilyCaptures.registeredLiteralRecordSelected henv hscoped formed
    registered projectionLookup unindexed inert lookup levelsWF levelLength relevant resultShape
    (lengthσ.trans saturated) (lengthτ.trans lengthσ.symm)
    (by simpa only [sourceEq, lengthσ] using finiteCaptures)
    (by simpa only [sourceEq] using finiteRaw) bounded
    (by
      simpa only [List.map_map, Function.comp_def, subst_bvar, lengthσ,
        realizedFields] using actualFields)
    (by simpa only [resultSame] using code.familyRelation typed.record_family_mem)
  apply Related.record henv hscoped typed code
  simpa only [resultSame] using selected

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
