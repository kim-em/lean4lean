import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordTerminal
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginReduction

/-! A record terminal retains actual primitive projection guards at the
source realization. Paired constructor equality transports those finite
origins to the other realization. No result-sort comparison is required. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 800000

private theorem recordCaptureAt (count : Nat) (σ : Subst) (i : Nat) (hi : i < count) :
    nativeCaptureSubst (realizedCaptures count σ) i = σ i := by
  simp [nativeCaptureSubst, realizedCaptures, constantCaptureVariables, hi,
    List.getElem_reverse, List.getElem_range]
  congr 1 <;> omega

/-- The only field guards are the finite original primitive-projection
origins. They may use the proof-field guard even when the family universe
is zero. The exact frozen field requests and their order remain unchanged. -/
theorem richRecordTerminalFromOrigins
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
    (lookup : env.constants projection.ctorName = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelLength : levels.length = info.uvars)
    (inert : CanonicalDataHead.HeadInert registry projection.ctorName)
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
    (origins : ∀ entry ∈ demand.fields,
      Nonempty (RankedData.ProjectionOrigin env U target projection demand.family.name entry.1
        (mkApps (.const projection.ctorName levels) (realizedCaptures arguments.length σ))
        (signature.result.subst σ) entry.2.domain))
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
  have finiteRaw := realizedCaptureSubstitution henv substitutions.wf substitutions
  rw [count] at finiteRaw
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
  obtain ⟨pair, _⟩ := signature.prefixArgumentsEqual henv formed
    (.const lookup levelsWF levelLength) (Nat.le_refl _)
    (lengthσ.trans saturated) (lengthτ.trans saturated)
    (by simpa only [List.take_length, sourceEq] using finiteRaw)
  simp only [List.drop_length, wrapForalls, List.foldr_nil, resultSame] at pair
  let leftHeader : ConstructorResultHeader env projection.ctorName demand.family.name levels
      (realizedCaptures arguments.length σ) := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := saturated.symm.trans lengthσ.symm }
  obtain ⟨domains, result, _, layout, domainShape, _⟩ := leftHeader.registered_domains henv registered
  change signature.domains = domains.map (·.instL levels) at domainShape
  have layoutActual : arguments.length = projection.nparams + projection.numFields := by
    rw [saturated, domainShape, List.length_map, layout]
  apply Related.record henv hscoped typed code
  apply RankedData.literalRecord henv hscoped formed projectionLookup inert bounded
    (code.familyRelation typed.record_family_mem) pair.hasType.1 pair.hasType.2 origins
    (fun entry member => by
      obtain ⟨origin⟩ := origins entry member
      exact ⟨origin.replaceMajor pair⟩)
  intro entry member
  have fieldBound : projection.nparams + entry.1 < arguments.length := by
    have := bounded entry member
    omega
  have leftBound : projection.nparams + entry.1 < (realizedCaptures arguments.length σ).length := by omega
  have rightBound : projection.nparams + entry.1 < (realizedCaptures arguments.length τ).length := by omega
  refine ⟨(realizedCaptures arguments.length σ)[projection.nparams + entry.1],
    (realizedCaptures arguments.length τ)[projection.nparams + entry.1],
    List.getElem?_eq_getElem leftBound, List.getElem?_eq_getElem rightBound, ?_⟩
  simp only [List.map_map, Function.comp_def] at actualFields
  have admitted := actualFields.map_member member
  simpa only [List.map_map, Function.comp_def, subst_bvar, realizedCaptures,
    constantCaptureVariables, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range, subst_bvar] using admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
