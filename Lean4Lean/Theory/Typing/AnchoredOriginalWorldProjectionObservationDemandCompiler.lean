import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionVariableDemandCompiler

/-! Total demand return for an actual projection observation on a caller
variable. Literal projection syntax executes directly; the charged case
normalizes its exact retained recipe and computes the entire caller scope. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private appendPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

/-- No terminal, trace, finite input program or semantic major answer is
supplied. The retained raw request and its output admission come from the
same actual physical leaf reached by this observation's finite program. -/
theorem ControlledStoredQuery.projectionVariableDemandWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation callerEnv U callerSource}
    {callerNode : EndpointState callerEnv U callerSource (.proj name index (.bvar caller)) callerAssigned}
    (callerHead : ProjectionHead callerNode)
    (controls : OriginalWorldControls strata callerEnv)
    (frontier : List (World strata.rules.length))
    {query : RichObs callerEnv env U registry target callerNode locals σ profile footprint}
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (provenance : EndpointProvenance context callerNode)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : callerEnv ≤ env) (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured]))
    (selected : atom ∈ profile.atoms)
    {m : Nat} {output : Atom m}
    (path : GeneralOutputPath env U registry target atom output) :
    ∃ rank, ∃ record : RecordData (Profile rank), ∃ request : DataRequest (Profile rank),
    ∃ majorQuery : RichGradedResult callerEnv env U registry target (.ref (.right callerHead.major))
        locals σ available (Profile.singleton (n := rank+1) (.record record)),
    ∃ _majorReady : ControlledStoredQuery controls frontier (.observation majorQuery.observation),
    ∃ value : RichComputationalValue callerEnv env U registry target (.ref (.right callerHead.major))
        locals σ τ available (Profile.singleton (n := rank+1) (.record record)),
      Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation value.rightQuery.observation)) ∧
      RankedData.RequestAdmission env U (relations env U registry rank) target request
        (.proj name index (σ caller)) (.proj name index (τ caller)) ∧
      Admitted env U registry target
        (show Key m from ⟨request.domain,request.anchor,Profile.singleton output⟩)
        (.proj name index (σ caller)) (.proj name index (τ caller)) ∧
      record.family.name = name ∧ (index, request) ∈ record.fields ∧
      ∃ requestAtom : Atom rank, requestAtom ∈ request.input.atoms ∧
        Nonempty (GeneralOutputPath env U registry target requestAtom output) := by
  obtain ⟨origin,children,⟨selectedPath⟩,included,worlds,rooted,smaller,depth⟩ :=
    ready.annotation.retainedProjectionOriginSized provenance.location selected
      (budget := sizeOf (show WorldObsProvenance strata query from ready.annotation)) (Nat.le_refl _)
  have supplied : origin.footprint.Available available :=
    fun i need member => resources i need (included member)
  cases origin with
  | original actual =>
    obtain ⟨majorQuery,majorReady,value,certificateReady,valueReady,admitted,outputAdmitted⟩ :=
      actual.returnVariableDemandWorld (.initial available) supplied closed rfl callerHead provenance controls
        frame captured frontier data closed substitutions henv hscoped formed paid bank
        (appendPath selectedPath path)
    exact ⟨actual.rank,actual.record,actual.request,majorQuery,majorReady,value,
      certificateReady,valueReady,admitted,outputAdmitted,actual.nameEq,actual.member,
      actual.output,actual.selected,⟨appendPath selectedPath path⟩⟩
  | charged actual =>
    cases children with
    | charged annotation =>
      obtain ⟨recipeReady,same,terminal,trace,⟨answer⟩⟩ :=
        WorldCodeRecipeProvenance.compileProjectionVariableDemandWorld callerHead controls frontier output
          annotation ready worlds depth provenance frame captured data closed substitutions supplied
          henv hscoped formed sourceBelow sourceClosed paid bank actual.selected (appendPath selectedPath path)
      exact ⟨terminal.opening.origin.rank,terminal.opening.origin.record,terminal.opening.origin.request,
        answer.query,answer.queryReady,answer.value,⟨answer.certificateReady⟩,⟨answer.valueReady⟩,
        answer.admitted,answer.outputAdmitted,answer.nameEq,answer.member,
        terminal.opening.origin.output,terminal.opening.origin.selected,⟨terminal.opening.output⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
