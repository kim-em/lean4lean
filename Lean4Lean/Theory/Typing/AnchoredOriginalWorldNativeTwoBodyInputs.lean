import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedInputReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationArgument

/-! The concrete two-binder caller inputs come from the actual `.body`
resources and the actual ranked native-row continuations. Their anchors are
read back through the retained source renaming; neither the renaming nor
whole substitutions are identified with the caller's. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- These are exactly the two head resources introduced by two real recipe
body constructors; arbitrary resources below those binders are retained. -/
theorem twoRecipeBodyNeeds
    {footprint : Footprint} {callerAvailable : Valuation}
    {firstInput : Profile firstRank} {secondInput : Profile secondRank}
    (resources : Footprint.Available
      ((0, Need.mk secondRank secondInput) ::
        Footprint.sourceLift (.skip .refl) ((0, Need.mk firstRank firstInput) :: footprint.sourceLift (.skip .refl)))
      callerAvailable) :
    Need.mk firstRank firstInput ∈ callerAvailable 1 ∧
      Need.mk secondRank secondInput ∈ callerAvailable 0 := by
  constructor
  · apply resources 1 _
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(0, Need.mk firstRank firstInput),
      List.mem_cons_self, rfl⟩)
  · exact resources 0 _ List.mem_cons_self

/-- Mixed-rank pending input operations execute on the exposed caller leaf.
No membership at the old key's rank is required or manufactured. -/
noncomputable def RankedPendingNativeRow.inputFromCallerNeed
    {callerAvailable : Valuation}
    {table : List (Key n × Profile n)} {key : Key m} {result : Profile m}
    (pending : RankedPendingNativeRow env U registry target table relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (member : Need.mk m key.input ∈ callerAvailable index) :
    VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) index pending.oldKey.input :=
  pending.replayInput henv hscoped formed (.leaf (need := Need.mk m key.input) member)

/-- Both concrete compiler inputs are constructed from the same caller
resource proof and the exact original native rows, including pad/down. -/
noncomputable def twoRecipeBodyPrograms
    {footprint : Footprint} {callerAvailable : Valuation}
    {firstTable : List (Key n × Profile n)} {secondTable : List (Key k × Profile k)}
    {firstKey : Key m} {secondKey : Key r} {firstResult : Profile m} {secondResult : Profile r}
    (first : RankedPendingNativeRow env U registry target firstTable relevant firstKey firstResult)
    (second : RankedPendingNativeRow env U registry target secondTable relevant secondKey secondResult)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (resources : Footprint.Available
      ((0, Need.mk r secondKey.input) ::
        Footprint.sourceLift (.skip .refl) ((0, Need.mk m firstKey.input) :: footprint.sourceLift (.skip .refl)))
      callerAvailable) :
    VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 1 first.oldKey.input ×
    VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 0 second.oldKey.input :=
  let selected := twoRecipeBodyNeeds resources
  ⟨first.inputFromCallerNeed henv hscoped formed selected.1,
    second.inputFromCallerNeed henv hscoped formed selected.2⟩

private theorem variableLevelsIndex
    (levels : EqUpToLevels U (.bvar sourceIndex) (.bvar callerIndex)) : sourceIndex = callerIndex := by
  cases levels
  rfl

/-- The terminal's actual operand-level witnesses determine which source
indices implement the caller indices. Its readback equality then supplies
the exact two anchors, even for a nonidentity source insertion. -/
theorem nativeTwoVariableReadbackAnchors
    (ρ : Lift)
    (functionLevels : EqUpToLevels U (.app (.const name sourceLevels) (.bvar 1))
      ((.app (.const name callerLevels) (.bvar firstIndex) : VExpr).lift' ρ))
    (argumentLevels : EqUpToLevels U (.bvar 0) ((.bvar secondIndex : VExpr).lift' ρ))
    (readback :
      (((.app (.const name callerLevels) (.bvar firstIndex) : VExpr).subst (Subst.lift_l ρ sourceτ)),
        ((.bvar secondIndex : VExpr).subst (Subst.lift_l ρ sourceτ))) =
      (((.app (.const name callerLevels) (.bvar firstIndex) : VExpr).subst callerτ),
        ((.bvar secondIndex : VExpr).subst callerτ))) :
    sourceτ 1 = callerτ firstIndex ∧ sourceτ 0 = callerτ secondIndex := by
  have firstIndexEq : 1 = ρ.liftVar firstIndex := by
    change EqUpToLevels U (.app (.const name sourceLevels) (.bvar 1))
      (.app (.const name callerLevels) (.bvar (ρ.liftVar firstIndex))) at functionLevels
    cases functionLevels with
    | app constant argument => exact variableLevelsIndex argument
  have secondIndexEq : 0 = ρ.liftVar secondIndex := variableLevelsIndex argumentLevels
  have functionEq := congrArg Prod.fst readback
  have argumentEq := congrArg Prod.snd readback
  change VExpr.app _ (sourceτ (ρ.liftVar firstIndex)) = VExpr.app _ (callerτ firstIndex) at functionEq
  change sourceτ (ρ.liftVar secondIndex) = callerτ secondIndex at argumentEq
  exact ⟨by simpa only [← firstIndexEq] using (VExpr.app.inj functionEq).2,
    by simpa only [← secondIndexEq] using argumentEq⟩

/-- Rebuild the actual returned source bvar query using the computed pending
input program. This consumes its finite leaves, not an argument answer. -/
theorem nativeVariableAtCallerProgram
    {strata : EquationStratification env}
    {sourceNode : EndpointState sourceEnv U source (.bvar sourceIndex) sourceAssigned}
    (query : RichGradedResult sourceEnv env U registry target sourceNode sourceLocals sourceσ sourceAvailable requested)
    (closed : sourceAvailable.AtomClosed)
    (input : Profile n)
    (fits : ∀ need ∈ sourceAvailable sourceIndex, Need.Fits input need)
    (program : VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) index input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ argument : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
      Nonempty (ControlledStoredQuery controls frontier (.observation argument.observation)) := by
  obtain ⟨used, ⟨trace⟩, resources⟩ := query.observation.variableDependency closed query.resources
  let supplied (i : Nat) (need : Need) (member : (i, need) ∈ used) :
      VariableDependencyProgram env U registry target (fun i need => need ∈ callerAvailable i) index need.profile := by
    have same := trace.indices member
    subst i
    have fit := fits need (resources sourceIndex need member)
    exact program.localDemand need fit.1 fit.2
  let replay := (SortableVariableTrace.replayPrograms henv hscoped formed trace supplied).adaptRequest
    henv hscoped formed query.bound query.adapter
  let dependency : WorldVariableDependency env U registry target callerAvailable index requested := {
    rank := replay.rank, bound := replay.bound, raw := replay.raw, footprint := replay.footprint
    trace := replay.trace, resources := replay.resources, adapter := replay.adapter }
  exact ⟨dependency.atNode henv hscoped formed ordered frame node,
    ⟨dependency.atNode_controlled controls frontier henv hscoped formed ordered frame node⟩⟩

/-- The two genuine body executions provide source tables, BinderPacks and
closure. The caller recipe resources and retained row programs compute both
caller queries; terminal readback computes both anchors. -/
theorem compileTwoExecutedBinderProgramsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {firstTable : List (Key n × Profile n)} {secondTable : List (Key k × Profile k)}
    {firstKey : Key m} {secondKey : Key r} {firstResult : Profile m} {secondResult : Profile r}
    (firstPending : RankedPendingNativeRow env U registry target firstTable relevant firstKey firstResult)
    (secondPending : RankedPendingNativeRow env U registry target secondTable relevant secondKey secondResult)
    {firstDomain : EndpointRef sourceEnv U source A (.sort firstU)}
    {firstBody : EndpointState sourceEnv U (A :: source) B (.sort firstV)}
    {firstRow : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref firstDomain) firstBody firstPending.oldKey firstPending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (firstExecution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier firstDomain firstBody firstRow τ firstAnchor firstHU firstHV parentEnvironment)
    {secondDomain : EndpointRef sourceEnv U (A :: source) C (.sort secondU)}
    {secondBody : EndpointState sourceEnv U (C :: A :: source) D (.sort secondV)}
    {secondRow : RichPiRowCertificate env U registry target (Locals.push locals)
      (σ.cons firstPending.oldKey.anchor)
      (available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons))
      relevant (.ref secondDomain) secondBody secondPending.oldKey secondPending.oldResult}
    (secondExecution : RichPiRowBodyExecution (P := P) (context := .cons context firstDomain)
      controls frontier secondDomain secondBody secondRow (τ.cons firstAnchor) secondAnchor
      secondHU secondHV firstExecution.captured)
    {sourceFirst : EndpointState sourceEnv U (C :: A :: source) (.bvar 1) sourceFirstAssigned}
    {sourceSecond : EndpointState sourceEnv U (C :: A :: source) (.bvar 0) sourceSecondAssigned}
    (firstQuery : RichGradedResult sourceEnv env U registry target sourceFirst
      (Locals.push (Locals.push locals)) ((τ.cons firstAnchor).cons secondAnchor)
      ((available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)) firstRequested)
    (secondQuery : RichGradedResult sourceEnv env U registry target sourceSecond
      (Locals.push (Locals.push locals)) ((τ.cons firstAnchor).cons secondAnchor)
      ((available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)) secondRequested)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerFirst : EndpointState callerEnv U callerSource (.bvar 1) callerFirstAssigned)
    (callerSecond : EndpointState callerEnv U callerSource (.bvar 0) callerSecondAssigned)
    (callerControls : OriginalWorldControls strata callerEnv)
    (firstProgram : VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 1 firstPending.oldKey.input)
    (secondProgram : VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 0 secondPending.oldKey.input)
    (ρ : Lift)
    (functionLevels : EqUpToLevels U (.app (.const name sourceLevels) (.bvar 1))
      ((.app (.const name callerLevels) (.bvar 1) : VExpr).lift' ρ))
    (argumentLevels : EqUpToLevels U (.bvar 0) ((.bvar 0 : VExpr).lift' ρ))
    (readback :
      (((.app (.const name callerLevels) (.bvar 1) : VExpr).subst
          (Subst.lift_l ρ ((τ.cons firstAnchor).cons secondAnchor))),
        ((.bvar 0 : VExpr).subst (Subst.lift_l ρ ((τ.cons firstAnchor).cons secondAnchor)))) =
      (((.app (.const name callerLevels) (.bvar 1) : VExpr).subst callerσ),
        ((.bvar 0 : VExpr).subst callerσ))) :
    ∃ first : RichGradedResult callerEnv env U registry target callerFirst callerLocals callerσ callerAvailable firstRequested,
    ∃ second : RichGradedResult callerEnv env U registry target callerSecond callerLocals callerσ callerAvailable secondRequested,
      Nonempty (ControlledStoredQuery callerControls frontier (.observation first.observation)) ∧
      Nonempty (ControlledStoredQuery callerControls frontier (.observation second.observation)) ∧
      firstAnchor = callerσ 1 ∧ secondAnchor = callerσ 0 := by
  obtain ⟨first, firstReady⟩ := nativeVariableAtCallerProgram firstQuery secondExecution.closed
    firstPending.oldKey.input (fun need member => by
      obtain ⟨bound, covered⟩ := firstRow.pack.atomized_localNeeds need member
      exact ⟨bound, fun atom present => firstRow.covered atom (covered atom present)⟩)
    firstProgram henv hscoped formed ordered callerFrame callerFirst callerControls frontier
  obtain ⟨second, secondReady⟩ := nativeVariableAtCallerProgram secondQuery secondExecution.closed
    secondPending.oldKey.input (fun need member => by
      obtain ⟨bound, covered⟩ := secondRow.pack.atomized_localNeeds need member
      exact ⟨bound, fun atom present => secondRow.covered atom (covered atom present)⟩)
    secondProgram henv hscoped formed ordered callerFrame callerSecond callerControls frontier
  have anchors := nativeTwoVariableReadbackAnchors ρ functionLevels argumentLevels readback
  exact ⟨first, second, firstReady, secondReady, anchors⟩

/-- Literal double-body resources remain a specialization of finite program replay. -/
theorem compileTwoExecutedBinderArgumentsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {firstTable : List (Key n × Profile n)} {secondTable : List (Key k × Profile k)}
    {firstKey : Key m} {secondKey : Key r} {firstResult : Profile m} {secondResult : Profile r}
    (firstPending : RankedPendingNativeRow env U registry target firstTable relevant firstKey firstResult)
    (secondPending : RankedPendingNativeRow env U registry target secondTable relevant secondKey secondResult)
    {firstDomain : EndpointRef sourceEnv U source A (.sort firstU)}
    {firstBody : EndpointState sourceEnv U (A :: source) B (.sort firstV)}
    {firstRow : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref firstDomain) firstBody firstPending.oldKey firstPending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (firstExecution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier firstDomain firstBody firstRow τ firstAnchor firstHU firstHV parentEnvironment)
    {secondDomain : EndpointRef sourceEnv U (A :: source) C (.sort secondU)}
    {secondBody : EndpointState sourceEnv U (C :: A :: source) D (.sort secondV)}
    {secondRow : RichPiRowCertificate env U registry target (Locals.push locals)
      (σ.cons firstPending.oldKey.anchor)
      (available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons))
      relevant (.ref secondDomain) secondBody secondPending.oldKey secondPending.oldResult}
    (secondExecution : RichPiRowBodyExecution (P := P) (context := .cons context firstDomain)
      controls frontier secondDomain secondBody secondRow (τ.cons firstAnchor) secondAnchor
      secondHU secondHV firstExecution.captured)
    {sourceFirst : EndpointState sourceEnv U (C :: A :: source) (.bvar 1) sourceFirstAssigned}
    {sourceSecond : EndpointState sourceEnv U (C :: A :: source) (.bvar 0) sourceSecondAssigned}
    (firstQuery : RichGradedResult sourceEnv env U registry target sourceFirst
      (Locals.push (Locals.push locals)) ((τ.cons firstAnchor).cons secondAnchor)
      ((available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)) firstRequested)
    (secondQuery : RichGradedResult sourceEnv env U registry target sourceSecond
      (Locals.push (Locals.push locals)) ((τ.cons firstAnchor).cons secondAnchor)
      ((available.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)) secondRequested)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerFirst : EndpointState callerEnv U callerSource (.bvar 1) callerFirstAssigned)
    (callerSecond : EndpointState callerEnv U callerSource (.bvar 0) callerSecondAssigned)
    (callerControls : OriginalWorldControls strata callerEnv)
    {callerFootprint : Footprint}
    (callerResources : Footprint.Available
      ((0, Need.mk r secondKey.input) ::
        Footprint.sourceLift (.skip .refl) ((0, Need.mk m firstKey.input) :: callerFootprint.sourceLift (.skip .refl)))
      callerAvailable)
    (ρ : Lift)
    (functionLevels : EqUpToLevels U (.app (.const name sourceLevels) (.bvar 1))
      ((.app (.const name callerLevels) (.bvar 1) : VExpr).lift' ρ))
    (argumentLevels : EqUpToLevels U (.bvar 0) ((.bvar 0 : VExpr).lift' ρ))
    (readback :
      (((.app (.const name callerLevels) (.bvar 1) : VExpr).subst
          (Subst.lift_l ρ ((τ.cons firstAnchor).cons secondAnchor))),
        ((.bvar 0 : VExpr).subst (Subst.lift_l ρ ((τ.cons firstAnchor).cons secondAnchor)))) =
      (((.app (.const name callerLevels) (.bvar 1) : VExpr).subst callerσ),
        ((.bvar 0 : VExpr).subst callerσ))) :
    ∃ first : RichGradedResult callerEnv env U registry target callerFirst callerLocals callerσ callerAvailable firstRequested,
    ∃ second : RichGradedResult callerEnv env U registry target callerSecond callerLocals callerσ callerAvailable secondRequested,
      Nonempty (ControlledStoredQuery callerControls frontier (.observation first.observation)) ∧
      Nonempty (ControlledStoredQuery callerControls frontier (.observation second.observation)) ∧
      firstAnchor = callerσ 1 ∧ secondAnchor = callerσ 0 := by
  let programs := twoRecipeBodyPrograms firstPending secondPending henv hscoped formed callerResources
  exact compileTwoExecutedBinderProgramsWorld firstPending secondPending firstExecution secondExecution
    firstQuery secondQuery henv hscoped formed ordered callerFrame callerFirst callerSecond callerControls
    programs.1 programs.2 ρ functionLevels argumentLevels readback

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
