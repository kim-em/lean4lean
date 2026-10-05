import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex

/-! Extract raw projection guards from the actual original projection rule.
The sole semantic call compares the assigned types of its real major child
and the common major. An empty code query suffices, so even an unobserved
field needs no invented atom or global nonzero family-level premise. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalFactorCut
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open private Located.dependencyEnvironment_of_prefix_nil
  from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
open private projectionMajor_cost_lt
  from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut.ProjectionHead.originAtStaged
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major assigned commonType : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (common : EndpointRef sourceEnv U source major commonType)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage callStage))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (scheduled : Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .assignedComparison
      ((Closure.close ((EndpointState.ref common).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost +
       (Closure.close ((EndpointState.ref (.right head.major)).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)) (stage, limit)) :
    Nonempty (RankedData.ProjectionOrigin env U target head.info name index
      (major.subst σ) (commonType.subst σ) (assigned.subst σ)) := by
  let base := frame.captureBase substitutions
  let left := OriginalNestedDisplay.identity base (.ref common) (.ofLocation .here context)
  let right := OriginalNestedDisplay.identity base (.ref (.right head.major)) (.ofLocation .here context)
  have generation : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ left.graph base.identityRealization.frame.raw := .identity ambient sources
  let certificate : RichCert sourceEnv env U registry target
      left.node.typeFormation.node locals (Subst.id.comp σ) true (.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  obtain ⟨answer⟩ := bank.assigned callStage base base.initialCaps left right σ σ ordered ordered
    base.identityRealization generation closed base.identityRealization generation closed
    scheduled certificate (by intro _ _ member; cases member)
  have path : TypeConversion env U target (commonType.subst σ)
      ((mkApps (.const name head.levels) (head.parameters ++ head.indices)).subst σ) := by
    simpa only [left, right, OriginalNestedDisplay.identity,
      OriginalNestedDisplay.formationDisplay, OriginalRichFrame.captureBase, subst_id] using answer.path
  let original := RankedData.ProjectionOrigin.ofRule (below.projections head.registered)
    head.levelsWF head.levelCount head.parameterCount head.indexCount head.selected
    (head.field.sound.defeq.mono below) (head.major.forget.defeq.mono below)
    head.closed head.relevance
  let natural := original.substitute henv formed substitutions
  let aligned := natural.convertAssignedType path.symm
  have fieldPath := head.route.targetPath henv below formed substitutions
  exact ⟨{ aligned with fieldPath := aligned.fieldPath.trans fieldPath.symm }⟩

/-- Both original major roots are strictly below the actual structure-eta
rule in the current dependency measure, for any captured environment. -/
theorem etaProjectionOrigin_dependency_schedule
    (ordered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation sourceEnv U source expression expression
      (mkApps (.const name levels) parameters))
    (constructor : Derivation sourceEnv U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields) (captured : List Closure) :
    let head := projectionHead (etaProjectionArgument constructor index bound).node
    richSchedule .assignedComparison
      ((Closure.close (major.dependencyOrigin ordered) captured).cost +
       (Closure.close (head.major.dependencyOrigin ordered) captured).cost) <
    richSchedule .fundamental (Closure.close
      ((Derivation.structEta registered parameterCount noIndices major constructor).dependencyOrigin ordered)
      captured).cost := by
  dsimp only
  let argument := etaProjectionArgument constructor index bound
  have argBound := argument.location.dependency_cost_le ordered captured
  rw [Located.dependencyEnvironment_of_prefix_nil ordered argument.location argument.prefix_eq] at argBound
  have majorBound := projectionMajor_cost_lt (projectionHead argument.node) ordered captured
  have smaller := Nat.lt_of_lt_of_le majorBound argBound
  have parent := original_two_children (major.dependencyOrigin ordered)
    (constructor.dependencyOrigin ordered) [] captured
  apply richSchedule_strict
  rw [Derivation.dependencyOrigin.eq_def ordered
    (Derivation.structEta registered parameterCount noIndices major constructor)]
  exact Nat.lt_trans (Nat.add_lt_add_left smaller _) parent

/-- The retained constructor premise of structure eta supplies every raw
field guard, including proof-valued fields and empty observation inputs.
The assigned-type comparison is invoked at its proved smaller schedule. -/
theorem etaProjectionOriginStaged
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {info : VProjectionInfo}
    {parameters : List VExpr} {levels : List VLevel} {expression : VExpr}
    (registered : sourceEnv.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation sourceEnv U source expression expression
      (mkApps (.const name levels) parameters))
    (constructor : Derivation sourceEnv U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (bank : StagedOriginalLowerCallBank env U registry stage
      (richSchedule .fundamental (Closure.close
        ((Derivation.structEta registered parameterCount noIndices major constructor).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)) :
    Nonempty (RankedData.ProjectionOrigin env U target info name index
      (expression.subst σ) ((mkApps (.const name levels) parameters).subst σ)
      ((etaProjectionArgument constructor index bound).type.subst σ)) := by
  let head := projectionHead (etaProjectionArgument constructor index bound).node
  obtain ⟨origin⟩ := head.originAtStaged (.left major) henv ordered below context frame
    ambient sources closed formed substitutions bank
    (.right _ (etaProjectionOrigin_dependency_schedule ordered registered parameterCount noIndices
      major constructor index bound (frame.dependencyEnvironment ordered)))
  have same : head.info = info := ordered.projections_unique head.registered registered
  exact ⟨by simpa only [same] using origin⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
