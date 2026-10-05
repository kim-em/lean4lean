import Lean4Lean.Theory.Typing.AnchoredNativeTerminalInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedTerminalProtected
import Lean4Lean.Theory.Typing.AnchoredBoundedCaptureReplay

/-! The native machine terminal consumes bounded predecessor semantics only.
The actual output certificate retains the same current-header fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private raised_expression plan_added_length from Lean4Lean.Theory.Typing.AnchoredNativeTerminalInterpretation
set_option backward.isDefEq.respectTransparency false

theorem NativeFullCaptureReplay.terminalRelatedBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program next : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data) (notDefinition : registry.definitions data.name = none)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {witnesses newValues : List VExpr} {argumentAvailable : Valuation}
    (literal : program.prefixArgs = nativeEquationArguments program witnesses)
    (newLength : newValues.length = program.prefixArgs.length)
    (selectedNew : data.saturatedProgram program.levels newValues = some next)
    (nextLevels : next.levels = program.levels) (nextBody : next.equationBody = program.equationBody)
    (nextTrailing : next.trailing = [])
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : Staged.PairedFits current fuel env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) argumentAvailable)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level))
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL program.levels) demand footprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (full : NativeFullCaptureReplay sourceEnv env U registry target program signature witnesses
      newValues argumentAvailable footprint next.state)
    (fullBound : full.replay.nativeDepth current ≤ fuel) :
    ∃ result : NativeTerminalRelatedResult env U registry target program signature witnesses newValues demand,
      result.certificate.nativeDepth current ≤ fuel := by
  have spec := saturatedProgram_spec selected
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have parsedRight := right
  have parsedFormation := formation
  rw [← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at parsedRight
  rw [← parts.2.2, instL_wrapForalls] at parsedFormation
  have oldLength : program.prefixArgs.length = signature.domains.length :=
    spec.2.2.1.trans (takeForalls_length signature.telescope).symm
  obtain ⟨supported, supportedBound⟩ := full.replay.declaredTerminalPairProtectedBounded henv hscoped hsource hle earlier
    hTarget newValues (by simpa using newLength.trans oldLength) rawArguments argumentFits fullBound full.closed
    parsedRight parsedFormation body bodyBound full.resources
  obtain ⟨generated, paired, _⟩ := full.replay.canonicalPairBounded henv hscoped hle earlier hTarget
    newValues (by simpa using newLength.trans oldLength) rawArguments argumentFits fullBound
  have opened := SaturatedProgram.openEquation_originalBounded (program := program) henv hscoped hle earlier registered selected levelsWF
    left right formation
  have canonicalEquation := opened.substDF henv paired.wf (generated.targetWF henv) paired
  rw [raised_expression, raised_expression, nativeEquationArguments_lhs selected witnesses,
    ← literal] at canonicalEquation
  have rhsScope := opened.hasType.2.closedN henv (CtxWF.closed henv paired.wf)
  have machineRhs : (program.equationBody.rhs.instL program.levels).subst
      (full.plan.captures (nativeCaptureSubst newValues)) = next.result := by
    simp only [SaturatedProgram.result, nextTrailing, List.map_nil, mkApps, List.foldl_nil,
      SaturatedProgram.rhs, nextLevels, nextBody]
    apply subst_congr_closedN rhsScope
    intro i hi
    exact (full.matched.captures i hi).symm
  have residual : signature.result.subst (nativeCaptureSubst program.prefixArgs) =
      (program.equationBody.type.instL program.levels).subst (nativeCaptureSubst witnesses) := by
    rw [literal]
    exact signature.equationResult registered selected witnesses
  have argumentsEqual := (signature.argumentsEqual henv hTarget registered levelsWF spec.2.1
    oldLength (newLength.trans oldLength) rawArguments).1.symm
  rw [residual] at argumentsEqual
  have rawRight := (argumentsEqual.weak' henv generated.weakening).trans canonicalEquation
  rw [machineRhs, ← residual] at rawRight
  have rawLeft := canonicalEquation.hasType.2
  have witnessedTyped := opened.hasType.2.substDF henv paired.wf (generated.targetWF henv) paired.left
  rw [raised_expression, raised_expression, ← residual] at witnessedTyped
  have machineRelated := supported.related
  rw [machineRhs, ← residual] at machineRelated
  have addedLength : next.state.added.length = full.plan.count := by
    rw [full.matched.added, plan_added_length]
  have machineGenerated : ProofInsertion env U target (next.state.added ++ target)
      (.skipN .refl next.state.added.length) := by
    rw [full.matched.added, plan_added_length]
    exact generated
  have machineTrace : CanonicalHead.Trace registry
      (mkApps (.const data.name program.levels) newValues) next.state.added next.result := by
    have step : CanonicalHead.step registry (mkApps (.const data.name program.levels) newValues) =
        some ⟨next.state.added, next.result⟩ := by
      rw [CanonicalHead.step, spine_mkApps_exact _ _ rfl]
      simp only [CanonicalHead.spineStep, notDefinition, lookup, ↓reduceIte,
        CanonicalHead.nativeOutput, selectedNew, Option.map_some]
    exact CanonicalHead.Trace.next step .refl
  have expanded : Related env U registry target
      ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
      (mkApps (.const data.name program.levels) newValues)
      (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand supported.support := by
    apply Related.prependEndpoints henv hscoped (.lifted) (.traced (CanonicalDataHead.Trace.ofLegacy machineTrace)) machineGenerated
    · simpa only [full.matched.added, plan_added_length] using witnessedTyped
    · simpa only [full.matched.added, plan_added_length] using rawRight
    · simpa only [full.matched.added, plan_added_length] using machineRelated
  exact ⟨{
    available := full.available
    support := supported.support
    footprint := supported.footprint
    certificate := supported.certificate
    resources := supported.resources
    typed := supported.typed
    typeCode := by rw [residual]; exact supported.typeCode
    witnessed := by rw [residual]; exact supported.witnessed
    related := expanded }, supportedBound⟩

theorem NativeCaptures.terminalRelatedBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data) (notDefinition : registry.definitions data.name = none)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {witnesses newValues : List VExpr} {argumentAvailable : Valuation}
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    (witnessPrefix : witnesses.take data.indexOffset = program.prefixArgs.take data.indexOffset)
    (literal : program.prefixArgs = nativeEquationArguments program witnesses)
    (newLength : newValues.length = program.prefixArgs.length)
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : Staged.PairedFits current fuel env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) argumentAvailable)
    (closed : argumentAvailable.AtomClosed)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level))
    {demand : Profile n} {footprint nativeFootprint : Footprint}
    (body : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL program.levels) demand footprint)
    (captures : NativeCaptures env U registry target program witnesses program.instructions.length
      footprint nativeFootprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (capturesBound : captures.nativeDepth current ≤ fuel)
    (resources : nativeFootprint.Available argumentAvailable) :
    ∃ result : NativeTerminalRelatedResult env U registry target program signature witnesses newValues demand,
      result.certificate.nativeDepth current ≤ fuel := by
  have spec := saturatedProgram_spec selected
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have parsedFormation := formation
  rw [← parts.2.2, instL_wrapForalls] at parsedFormation
  obtain ⟨replayed, replayedBound⟩ := captures.toSupport.toReplayBounded signature selected witnessPrefix
    ⟨level, parsedFormation⟩ parsedFormation.sourcePiFormation.1 closed resources
    (by simpa only [NativeCaptures.nativeDepth_toSupport] using capturesBound)
  have scope := parsedFormation.defeq.closedN hsource (by trivial)
  obtain ⟨next, nextSelected, nextLevels, _, nextTrailing, _, nextBody, _, run⟩ :=
    SaturatedProgram.reapply selected newValues newLength
  obtain ⟨full, fullBound⟩ := replayed.fullBounded selected witnessLength newValues newLength run scope replayedBound
  exact full.terminalRelatedBounded henv hscoped hsource hle earlier hTarget registered lookup notDefinition
    selected levelsWF literal newLength nextSelected nextLevels nextBody nextTrailing
    rawArguments argumentFits left right formation body bodyBound fullBound


theorem NativeCaptures.terminalPairBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data) (notDefinition : registry.definitions data.name = none)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {witnesses newValues : List VExpr} {argumentAvailable : Valuation}
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    (witnessPrefix : witnesses.take data.indexOffset = program.prefixArgs.take data.indexOffset)
    (literal : program.prefixArgs = nativeEquationArguments program witnesses)
    (newLength : newValues.length = program.prefixArgs.length)
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : Staged.PairedFits current fuel env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) argumentAvailable)
    (closed : argumentAvailable.AtomClosed)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level))
    {demand : Profile n} {footprint nativeFootprint : Footprint}
    (body : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL program.levels) demand footprint)
    (captures : NativeCaptures env U registry target program witnesses program.instructions.length
      footprint nativeFootprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (capturesBound : captures.nativeDepth current ≤ fuel)
    (resources : nativeFootprint.Available argumentAvailable) :
    ∃ result : NativeTerminalPairResult env U registry target program signature witnesses newValues demand,
      result.certificate.nativeDepth current ≤ fuel := by
  obtain ⟨next, nextBound⟩ := captures.terminalRelatedBounded henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition selected levelsWF witnessLength witnessPrefix literal newLength
    rawArguments argumentFits closed left right formation body bodyBound capturesBound resources
  obtain ⟨original, _⟩ := captures.terminalRelatedBounded henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition selected levelsWF witnessLength witnessPrefix literal rfl
    rawArguments.left argumentFits.left closed left right formation body bodyBound capturesBound resources
  exact ⟨{ next with nativeRelated :=
    (original.related.symm henv).trans henv hscoped next.related }, nextBound⟩


end Lean4Lean.AnchoredSource.Adapted
