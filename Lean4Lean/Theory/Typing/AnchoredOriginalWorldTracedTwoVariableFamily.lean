import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTracedTwoVariablePreparation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldMappedTwoVariableFamily
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedConstantReturn

/-! Consume the complete source trace of an actual two-variable caller
family. The original caller applications and both parameter queries are
computed; canonical return follows the saved charge stack. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem finishTwoVariableConstant
    {state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (answer : RetainedConstantReturn state name levels key output)
    (expressionEq : state.expression = .app (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex))
    (henv : env.Ordered)
    (destination : EndpointState state.sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    ∃ result : RichGradedResult state.sourceEnv env U registry target destination locals σ available
        (Profile.fn key output),
      Nonempty (ControlledStoredQuery state.controls frontier (.observation result.observation)) := by
  rcases answer with raw | graded
  · rcases raw with ⟨sourceLevels, path, equal, assigned, site, query, ready, depth, live⟩
    have same : sourceLevels = levels := by
      rw [expressionEq] at path
      exact path.twoVariableLevels
    cases same
    obtain ⟨query, ready, _, _⟩ := ready.pruneConstantFunction destination locals σ
    let result : RichGradedResult state.sourceEnv env U registry target destination locals σ available
        (Profile.fn key output) := {
      rank := _, bound := Nat.le_refl _, raw := Profile.fn key output, footprint := []
      observation := query
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := fun _ _ impossible => nomatch impossible
      live := live }
    exact ⟨result, ⟨ready⟩⟩
  · obtain ⟨result, ready, _, _, _, _⟩ := graded.result.pruneConstantFunctionWorld graded.ready henv
      destination locals σ available
    exact ⟨result, ⟨ready⟩⟩

/-- A concrete complete trace consumer for `((S #i) #j)`. Its only semantic
inputs are the original diagonal caller frame and the lower unary bank.
Both application answers, both finite parameter queries, and the entire
nested canonical return are computed from that SAME initial query. -/
theorem EndpointRef.tracedTwoVariableFamilyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (root : EndpointRef sourceEnv U source
      (.app (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex)) assigned)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ σ source)
    {demand : FamilyData (Profile q)} {profile : Profile (q+1)}
    {query : RichCert sourceEnv env U registry target (.ref root) locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (resources : footprint.Available available) (below : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured]))
    (member : (show Atom (q+1) from .family demand) ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none) :
    ∃ nextFootprint, ∃ certificate : RichCert sourceEnv env U registry target (.ref root) locals σ relevant
        (.singleton (show Atom (q+1) from .family demand)) nextFootprint,
    ∃ _nextReady : ControlledStoredQuery controls frontier (.certificate certificate),
      nextFootprint.Available available ∧
      WorldFamilyRequestProperty controls frontier root registry target locals σ available
        name levels [.bvar firstIndex, .bvar secondIndex] demand := by
  let provenance : EndpointProvenance context (.ref root) := .ofLocation .here context
  let initial := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources below paid bank .application member
  let initialData := RetainedProgramCallerData.ofRichApplication ready provenance frame captured data closed substitutions
    resources below paid bank member
  obtain ⟨terminal, trace, opening, same, firstMapped, secondMapped, firstAnchor, secondAnchor⟩ :=
    EndpointRef.prepareTwoVariableWorld root context controls frontier frame captured data closed substitutions
      ready resources below paid bank member henv hscoped formed sourceClosed
  obtain ⟨sourceLevels, functionEq, argumentEq, equal⟩ := opening.twoVariableShape
  obtain ⟨inner, innerAnswer, innerPath, constantAssigned, constantSite, constantQuery, constantReady, worlds, depth⟩ :=
    opening.constantFunctionWorld functionEq henv hscoped formed
  let raw : RetainedRawConstant terminal.state name levels inner.key inner.output := {
    sourceLevels := sourceLevels
    path := by rw [opening.expressionEq, functionEq]; exact .function (.function .here)
    equal := equal
    assigned := constantAssigned, site := constantSite, query := constantQuery, ready := constantReady
    depth := depth
    live := innerAnswer.functionValue.related.live henv hscoped formed }
  let outerCaller := applicationPrefix (root := root) Located.here
  let innerCaller := applicationPrefix (Located.appFunction outerCaller.view.location)
  let constantHead := constantPrefix innerCaller.view.function
  obtain ⟨primitiveConstant⟩ := EndpointRef.closedPrimitiveConstant constantHead.reference rfl constantHead.primitive
  obtain ⟨returned⟩ := trace.returnConstant (.inl raw) (.function .here) primitiveConstant.levelsWF
    henv formed sourceClosed
  obtain ⟨constant, ⟨returnedReady⟩⟩ := finishTwoVariableConstant returned rfl henv
    innerCaller.view.function locals σ available
  let finalScope := (trace.callerData initialData henv hscoped formed).scope
  let familyPath := opening.terminal.output
  rcases opening with ⟨function, argument, expressionEq, outer, rooted, children, childWorlds, childDepth,
    supplied, outerAnswer, ρ, functionLevels, argumentLevels, selectedPath, finalPath, normalized, readback⟩
  dsimp only at functionEq argumentEq
  cases functionEq
  cases argumentEq
  obtain ⟨factor, factorReady, finalFootprint, certificate, certificateReady, finalResources, included, requests⟩ :=
    compileMappedTwoVariableFamilyWorld inner outer terminal.state.controls frontier innerAnswer outerAnswer innerPath
      henv hscoped formed closed
      innerCaller.view.domainWF innerCaller.view.bodyWF outerCaller.view.domainWF outerCaller.view.bodyWF
      innerCaller.route firstAnchor secondAnchor controls constant returnedReady finalScope terminal.state.closed
      firstMapped secondMapped controls.ordered frame outerCaller.view.location below captured data substitutions
      paid notDefinition notNative bank familyPath (query.formed.singleton_of_mem member)
  let restored : RichCert sourceEnv env U registry target (.ref root) locals σ relevant
      (.singleton (show Atom (q+1) from .family demand)) finalFootprint :=
    .route outerCaller.route certificate
  let restoredReady : ControlledStoredQuery controls frontier (.certificate restored) := {
    annotation := .route outerCaller.route certificateReady.annotation
    within := by
      intro control active
      simpa only [restored, StoredOriginalQuery.headDepth, RichCert.headDepth] using
        certificateReady.within control active
    sponsored := certificateReady.sponsored }
  exact ⟨finalFootprint, restored, restoredReady, finalResources, requests⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
