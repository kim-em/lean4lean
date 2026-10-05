import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoBodyApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOperandFamilyConsumption

/-! The concrete execution trace reconstructs the caller family certificate
and its requested parameter observers together. The final output operations
are the retained machine path, not a path invented from the graded adapter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem compileNativeTwoBodyFamilyProgramsWorld
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
      callerLocals callerσ callerσ callerAvailable)
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
    {callerRoot : EndpointRef callerEnv U callerSource callerExpression callerAssigned}
    (location : Located callerRoot
      (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult))
    (controls : OriginalWorldControls strata callerEnv) (below : callerEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U (callerFrame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier callerFrame captured)
    (substitutions : Ctx.SubstEq env U target callerσ callerσ callerSource)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref callerRoot) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref callerRoot) captured]))
    {demand : FamilyData (Profile q)}
    (path : GeneralOutputPath env U registry target outer.output (show Atom (q+1) from .family demand))
    (sorted : (Profile.singleton (show Atom (q+1) from .family demand)).HasType (.sort outputRelevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ outputRelevant (.singleton (show Atom (q+1) from .family demand)) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds ∧
      WorldFamilyRequestProperty controls frontier callerRoot registry target callerLocals callerσ callerAvailable
        name nextLevels [.bvar 1, .bvar 0] demand := by
  obtain ⟨sourceRelevant, sourceSorted, ⟨change⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  obtain ⟨factor, operandReady, footprint, certificate, ready, resources, worlds⟩ :=
    compileNativeTwoBodyApplicationProgramsWorld owner sourceControls frontier firstPending secondPending
      firstExecution secondExecution inner outer innerAnswer outerAnswer innerPath constantReady
      henv hscoped formed callerFrame callerOrdered callerClosed firstHU firstHV secondHU secondHV
      functionRoute firstProgram secondProgram ρ functionLevels argumentLevels readback (.ref callerRoot) controls
      captured paid sourceReady masked bank sourceSorted
  have requests := factor.familyRequestsAlongPathOfBank location henv hscoped callerContext controls below
    callerFrame captured frontier data callerClosed formed substitutions paid notDefinition notNative
    (by rfl) operandReady path bank
  obtain ⟨nextFootprint, next, annotation, supplied, included, depth⟩ :=
    certificate.codeAction_worlds_depth ready.annotation change resources
  let nextReady : ControlledStoredQuery controls frontier (.certificate next) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (included member) }
  exact ⟨factor, operandReady, nextFootprint, next, nextReady, supplied,
    fun world member => worlds (included member), requests⟩

/-- Compatibility entry for two literal caller body resources. -/
theorem compileNativeTwoBodyFamilyWorld
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
      callerLocals callerσ callerσ callerAvailable)
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
    {callerRoot : EndpointRef callerEnv U callerSource callerExpression callerAssigned}
    (location : Located callerRoot
      (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult))
    (controls : OriginalWorldControls strata callerEnv) (below : callerEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U (callerFrame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier callerFrame captured)
    (substitutions : Ctx.SubstEq env U target callerσ callerσ callerSource)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref callerRoot) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref callerRoot) captured]))
    {demand : FamilyData (Profile q)}
    (path : GeneralOutputPath env U registry target outer.output (show Atom (q+1) from .family demand))
    (sorted : (Profile.singleton (show Atom (q+1) from .family demand)).HasType (.sort outputRelevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ outputRelevant (.singleton (show Atom (q+1) from .family demand)) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds ∧
      WorldFamilyRequestProperty controls frontier callerRoot registry target callerLocals callerσ callerAvailable
        name nextLevels [.bvar 1, .bvar 0] demand := by
  let programs := twoRecipeBodyPrograms firstPending secondPending henv hscoped formed callerResources
  exact compileNativeTwoBodyFamilyProgramsWorld owner sourceControls frontier firstPending secondPending
    firstExecution secondExecution inner outer innerAnswer outerAnswer innerPath constantReady
    henv hscoped formed callerFrame callerOrdered callerClosed firstHU firstHV secondHU secondHV
    functionRoute programs.1 programs.2 ρ functionLevels argumentLevels readback location controls below
    captured data substitutions paid notDefinition notNative sourceReady masked bank path sorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
