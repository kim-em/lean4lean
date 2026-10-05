import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoBodyInputs
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoVariableApplication

/-! Execute the two-variable caller reconstruction from the actual two
retained binder executions. Caller Needs, input adapters and anchor equations
are computed internally, including mixed-grade row continuations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private compileNativeTwoVariableArgumentsWorld from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoVariableApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- The actual execution transcript supplies both source BinderPacks and
caller neutral queries. The canonical constant keeps its original mask, and
the two ordinary caller applications are constructed with those same queries. -/
theorem compileNativeTwoBodyApplicationProgramsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {baseContext : ContextDerivation owner.selected.origin.source U baseSource}
    (sourceControls : OriginalWorldControls strata owner.selected.origin.source)
    (frontier : List (World strata.rules.length))
    {firstTable : List (Key n × Profile n)} {secondTable : List (Key k × Profile k)}
    {firstKey : Key m} {secondKey : Key r} {firstResult : Profile m} {secondResult : Profile r}
    (firstPending : RankedPendingNativeRow env U registry target firstTable relevant firstKey firstResult)
    (secondPending : RankedPendingNativeRow env U registry target secondTable relevant secondKey secondResult)
    {sourceFirstDomain : EndpointRef owner.selected.origin.source U baseSource A (.sort sourceFirstU)}
    {sourceFirstBody : EndpointState owner.selected.origin.source U (A :: baseSource) B (.sort sourceFirstV)}
    {firstRow : RichPiRowCertificate env U registry target baseLocals baseσ baseAvailable relevant
      (.ref sourceFirstDomain) sourceFirstBody firstPending.oldKey firstPending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (firstExecution : RichPiRowBodyExecution (P := P) (context := baseContext)
      sourceControls frontier sourceFirstDomain sourceFirstBody firstRow baseτ firstAnchor
      sourceFirstHU sourceFirstHV parentEnvironment)
    {sourceSecondDomain : EndpointRef owner.selected.origin.source U (A :: baseSource) C (.sort sourceSecondU)}
    {sourceSecondBody : EndpointState owner.selected.origin.source U (C :: A :: baseSource) D (.sort sourceSecondV)}
    {secondRow : RichPiRowCertificate env U registry target (Locals.push baseLocals)
      (baseσ.cons firstPending.oldKey.anchor)
      (baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons))
      relevant (.ref sourceSecondDomain) sourceSecondBody secondPending.oldKey secondPending.oldResult}
    (secondExecution : RichPiRowBodyExecution (P := P) (context := .cons baseContext sourceFirstDomain)
      sourceControls frontier sourceSecondDomain sourceSecondBody secondRow (baseτ.cons firstAnchor) secondAnchor
      sourceSecondHU sourceSecondHV firstExecution.captured)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target (C :: A :: baseSource)
      (Locals.push (Locals.push baseLocals)) ((baseσ.cons firstPending.oldKey.anchor).cons secondPending.oldKey.anchor)
      (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target (C :: A :: baseSource)
      (Locals.push (Locals.push baseLocals)) ((baseσ.cons firstPending.oldKey.anchor).cons secondPending.oldKey.anchor)
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier ((baseτ.cons firstAnchor).cons secondAnchor)
      ((baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)))
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier ((baseτ.cons firstAnchor).cons secondAnchor)
      ((baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)))
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank + 1) from .fn outer.key outer.output))
    (constantReady : ControlledStoredQuery sourceControls frontier (.observation inner.function))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerOrdered : callerEnv.Ordered) (callerClosed : callerAvailable.AtomClosed)
    {firstDomain : EndpointState callerEnv U callerSource firstA (.sort firstU)}
    {firstBody : EndpointState callerEnv U (firstA :: callerSource) firstB (.sort firstV)}
    {callerConstant : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE firstA firstB)}
    {callerFirst : EndpointState callerEnv U callerSource (.bvar 1) firstA}
    {firstResult : EndpointState callerEnv U callerSource (firstB.inst (.bvar 1)) (.sort firstV)}
    (firstHU : firstU.WF U) (firstHV : firstV.WF U)
    {secondDomain : EndpointState callerEnv U callerSource secondA (.sort secondU)}
    {secondBody : EndpointState callerEnv U (secondA :: callerSource) secondB (.sort secondV)}
    {callerFunction : EndpointState callerEnv U callerSource (.app (.const name nextLevels) (.bvar 1))
      (.forallE secondA secondB)}
    {callerSecond : EndpointState callerEnv U callerSource (.bvar 0) secondA}
    {secondResult : EndpointState callerEnv U callerSource (secondB.inst (.bvar 0)) (.sort secondV)}
    (secondHU : secondU.WF U) (secondHV : secondV.WF U)
    (functionRoute : PrefixRoute callerEnv U callerSource (.app (.const name nextLevels) (.bvar 1))
      callerFunction (.app firstHU firstHV firstDomain firstBody callerConstant callerFirst firstResult))
    (firstProgram : VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 1 firstPending.oldKey.input)
    (secondProgram : VariableDependencyProgram env U registry target
      (fun i need => need ∈ callerAvailable i) 0 secondPending.oldKey.input)
    (ρ : Lift)
    (functionLevels : EqUpToLevels U (.app (.const name levels) (.bvar 1))
      ((.app (.const name nextLevels) (.bvar 1) : VExpr).lift' ρ))
    (argumentLevels : EqUpToLevels U (.bvar 0) ((.bvar 0 : VExpr).lift' ρ))
    (readback :
      (((.app (.const name nextLevels) (.bvar 1) : VExpr).subst
          (Subst.lift_l ρ ((baseτ.cons firstAnchor).cons secondAnchor))),
        ((.bvar 0 : VExpr).subst (Subst.lift_l ρ ((baseτ.cons firstAnchor).cons secondAnchor)))) =
      (((.app (.const name nextLevels) (.bvar 1) : VExpr).subst callerσ),
        ((.bvar 0 : VExpr).subst callerσ)))
    (caller : EndpointState callerEnv U fundingSource fundingExpression fundingAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U fundingEnvironment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (sorted : (Profile.singleton outer.output).HasType (.sort outputRelevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ outputRelevant (.singleton outer.output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds := by
  obtain ⟨first, second, ⟨firstReady⟩, ⟨secondReady⟩, firstAnchorEq, secondAnchorEq⟩ :=
    compileTwoExecutedBinderProgramsWorld firstPending secondPending firstExecution secondExecution
      innerAnswer.argumentValue.rightQuery outerAnswer.argumentValue.rightQuery
      henv hscoped formed callerOrdered callerFrame callerFirst callerSecond controls firstProgram secondProgram
      ρ functionLevels argumentLevels readback
  have equal : EqUpToLevels U (.const name levels) (.const name nextLevels) := by
    change EqUpToLevels U (.app (.const name levels) (.bvar 1))
      (.app (.const name nextLevels) (.bvar (ρ.liftVar 1))) at functionLevels
    cases functionLevels with
    | app constant argument => exact constant
  exact compileNativeTwoVariableArgumentsWorld owner inner outer sourceControls frontier
    innerAnswer outerAnswer innerPath constantReady henv hscoped formed callerClosed
    firstHU firstHV secondHU secondHV functionRoute firstAnchorEq secondAnchorEq equal caller controls
    first firstReady second secondReady baseline paid sourceReady masked bank sorted

/-- Compatibility entry for two literal caller body resources. -/
theorem compileNativeTwoBodyApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {baseContext : ContextDerivation owner.selected.origin.source U baseSource}
    (sourceControls : OriginalWorldControls strata owner.selected.origin.source)
    (frontier : List (World strata.rules.length))
    {firstTable : List (Key n × Profile n)} {secondTable : List (Key k × Profile k)}
    {firstKey : Key m} {secondKey : Key r} {firstResult : Profile m} {secondResult : Profile r}
    (firstPending : RankedPendingNativeRow env U registry target firstTable relevant firstKey firstResult)
    (secondPending : RankedPendingNativeRow env U registry target secondTable relevant secondKey secondResult)
    {sourceFirstDomain : EndpointRef owner.selected.origin.source U baseSource A (.sort sourceFirstU)}
    {sourceFirstBody : EndpointState owner.selected.origin.source U (A :: baseSource) B (.sort sourceFirstV)}
    {firstRow : RichPiRowCertificate env U registry target baseLocals baseσ baseAvailable relevant
      (.ref sourceFirstDomain) sourceFirstBody firstPending.oldKey firstPending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (firstExecution : RichPiRowBodyExecution (P := P) (context := baseContext)
      sourceControls frontier sourceFirstDomain sourceFirstBody firstRow baseτ firstAnchor
      sourceFirstHU sourceFirstHV parentEnvironment)
    {sourceSecondDomain : EndpointRef owner.selected.origin.source U (A :: baseSource) C (.sort sourceSecondU)}
    {sourceSecondBody : EndpointState owner.selected.origin.source U (C :: A :: baseSource) D (.sort sourceSecondV)}
    {secondRow : RichPiRowCertificate env U registry target (Locals.push baseLocals)
      (baseσ.cons firstPending.oldKey.anchor)
      (baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons))
      relevant (.ref sourceSecondDomain) sourceSecondBody secondPending.oldKey secondPending.oldResult}
    (secondExecution : RichPiRowBodyExecution (P := P) (context := .cons baseContext sourceFirstDomain)
      sourceControls frontier sourceSecondDomain sourceSecondBody secondRow (baseτ.cons firstAnchor) secondAnchor
      sourceSecondHU sourceSecondHV firstExecution.captured)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target (C :: A :: baseSource)
      (Locals.push (Locals.push baseLocals)) ((baseσ.cons firstPending.oldKey.anchor).cons secondPending.oldKey.anchor)
      (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target (C :: A :: baseSource)
      (Locals.push (Locals.push baseLocals)) ((baseσ.cons firstPending.oldKey.anchor).cons secondPending.oldKey.anchor)
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier ((baseτ.cons firstAnchor).cons secondAnchor)
      ((baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)))
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier ((baseτ.cons firstAnchor).cons secondAnchor)
      ((baseAvailable.push (firstRow.bodyFootprint.localNeeds ++ firstRow.bodyFootprint.localNeeds.flatMap Need.singletons)).push
        (secondRow.bodyFootprint.localNeeds ++ secondRow.bodyFootprint.localNeeds.flatMap Need.singletons)))
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank + 1) from .fn outer.key outer.output))
    (constantReady : ControlledStoredQuery sourceControls frontier (.observation inner.function))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerOrdered : callerEnv.Ordered) (callerClosed : callerAvailable.AtomClosed)
    {firstDomain : EndpointState callerEnv U callerSource firstA (.sort firstU)}
    {firstBody : EndpointState callerEnv U (firstA :: callerSource) firstB (.sort firstV)}
    {callerConstant : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE firstA firstB)}
    {callerFirst : EndpointState callerEnv U callerSource (.bvar 1) firstA}
    {firstResult : EndpointState callerEnv U callerSource (firstB.inst (.bvar 1)) (.sort firstV)}
    (firstHU : firstU.WF U) (firstHV : firstV.WF U)
    {secondDomain : EndpointState callerEnv U callerSource secondA (.sort secondU)}
    {secondBody : EndpointState callerEnv U (secondA :: callerSource) secondB (.sort secondV)}
    {callerFunction : EndpointState callerEnv U callerSource (.app (.const name nextLevels) (.bvar 1))
      (.forallE secondA secondB)}
    {callerSecond : EndpointState callerEnv U callerSource (.bvar 0) secondA}
    {secondResult : EndpointState callerEnv U callerSource (secondB.inst (.bvar 0)) (.sort secondV)}
    (secondHU : secondU.WF U) (secondHV : secondV.WF U)
    (functionRoute : PrefixRoute callerEnv U callerSource (.app (.const name nextLevels) (.bvar 1))
      callerFunction (.app firstHU firstHV firstDomain firstBody callerConstant callerFirst firstResult))
    {callerFootprint : Footprint}
    (callerResources : Footprint.Available
      ((0, Need.mk r secondKey.input) ::
        Footprint.sourceLift (.skip .refl) ((0, Need.mk m firstKey.input) :: callerFootprint.sourceLift (.skip .refl)))
      callerAvailable)
    (ρ : Lift)
    (functionLevels : EqUpToLevels U (.app (.const name levels) (.bvar 1))
      ((.app (.const name nextLevels) (.bvar 1) : VExpr).lift' ρ))
    (argumentLevels : EqUpToLevels U (.bvar 0) ((.bvar 0 : VExpr).lift' ρ))
    (readback :
      (((.app (.const name nextLevels) (.bvar 1) : VExpr).subst
          (Subst.lift_l ρ ((baseτ.cons firstAnchor).cons secondAnchor))),
        ((.bvar 0 : VExpr).subst (Subst.lift_l ρ ((baseτ.cons firstAnchor).cons secondAnchor)))) =
      (((.app (.const name nextLevels) (.bvar 1) : VExpr).subst callerσ),
        ((.bvar 0 : VExpr).subst callerσ)))
    (caller : EndpointState callerEnv U fundingSource fundingExpression fundingAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U fundingEnvironment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (sorted : (Profile.singleton outer.output).HasType (.sort outputRelevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ outputRelevant (.singleton outer.output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds := by
  let programs := twoRecipeBodyPrograms firstPending secondPending henv hscoped formed callerResources
  exact compileNativeTwoBodyApplicationProgramsWorld owner sourceControls frontier firstPending secondPending
    firstExecution secondExecution inner outer innerAnswer outerAnswer innerPath constantReady
    henv hscoped formed callerFrame callerOrdered callerClosed firstHU firstHV secondHU secondHV
    functionRoute programs.1 programs.2 ρ functionLevels argumentLevels readback caller controls
    baseline paid sourceReady masked bank sorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
