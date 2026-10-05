import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredTerminalProtected
import Lean4Lean.Theory.Typing.AnchoredNativeReplayMachine
import Lean4Lean.Theory.Typing.AnchoredNativePlanBridge
import Lean4Lean.Theory.Typing.NativeTerminalSoundness
import Lean4Lean.Theory.Typing.AnchoredTraceTerm

/-! Connect the actual native capture tree to its deterministic saturated
machine. Literal constructor-index alignment is explicit: raw equality of
argument tuples alone does not transfer semantic result-type support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem run_reindex {indices newIndices : List VExpr}
    {instructions : List CaptureInstruction} {state final : SaturatedCaptureState}
    (run : state.run indices instructions = some final)
    (length : newIndices.length = indices.length) (newState : SaturatedCaptureState) :
    ∃ result, newState.run newIndices instructions = some result := by
  induction instructions generalizing state newState with
  | nil => exact ⟨newState, rfl⟩
  | cons instruction rest ih =>
    simp only [SaturatedCaptureState.run, bind, Option.bind_eq_some_iff] at run ⊢
    obtain ⟨next, step, run⟩ := run
    cases instruction with
    | index domain slot =>
      simp only [SaturatedCaptureState.step, bind, Option.bind_eq_some_iff] at step
      obtain ⟨value, lookup, _⟩ := step
      have bound : slot < newIndices.length := length ▸ (List.getElem?_eq_some_iff.mp lookup).1
      let next := { newState with captures := newState.captures ++
        [(newIndices[slot]).liftN newState.added.length] }
      obtain ⟨result, rest⟩ := ih run next
      exact ⟨result, next, by simp [SaturatedCaptureState.step, next, List.getElem?_eq_getElem bound], rest⟩
    | proof domain =>
      let next : SaturatedCaptureState := {
        added := instantiateParams domain newState.captures :: newState.added
        captures := newState.captures.map VExpr.lift ++ [.bvar 0] }
      obtain ⟨result, rest⟩ := ih run next
      exact ⟨result, next, rfl, rest⟩

/-- A replacement tuple of the same saturated length runs the same fixed
instructions. No target typing or reconstructed-index guard selects syntax. -/
theorem SaturatedProgram.reapply
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (newValues : List VExpr) (length : newValues.length = program.prefixArgs.length) :
    ∃ next : SaturatedProgram data,
      data.saturatedProgram program.levels newValues = some next ∧
      next.levels = program.levels ∧ next.prefixArgs = newValues ∧ next.trailing = [] ∧
      next.equation = program.equation ∧ next.equationBody = program.equationBody ∧
      next.instructions = program.instructions ∧
      SaturatedCaptureState.run ((newValues.drop data.indexOffset).take data.numIndices)
        program.instructions { added := [], captures := newValues.take data.indexOffset } = some next.state := by
  have spec := saturatedProgram_spec selected
  have newLength : newValues.length = data.majorOffset + 1 := length.trans spec.2.2.1
  generalize hl : program.levels = levels at selected ⊢
  generalize ha : program.prefixArgs ++ program.trailing = oldArgs at selected
  unfold saturatedProgram at selected ⊢
  dsimp only at selected ⊢
  split at selected <;> try contradiction
  rename_i levelCheck
  rw [if_neg levelCheck]
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, split, major, majorAt, source, sourceAt, selected⟩ := selected
  split at selected <;> try contradiction
  rename_i sourceCheck
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨equation, equationAt, body, bodyAt, selected⟩ := selected
  split at selected <;> try contradiction
  rename_i bodyCheck
  split at selected <;> try contradiction
  rename_i headCheck
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨state, run, equality⟩ := selected
  cases equality
  have bound : data.majorOffset < newValues.length := by omega
  obtain ⟨nextState, nextRun⟩ := run_reindex run
    (newIndices := (newValues.drop data.indexOffset).take data.numIndices)
    (by simp only [List.length_take, List.length_drop]; rw [length])
    { added := [], captures := newValues.take data.indexOffset }
  refine ⟨⟨_, newValues, [], newValues[data.majorOffset], source, equation, body, _, nextState⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, nextRun⟩
  have splitNew : splitSaturated (data.majorOffset + 1) newValues = some (newValues, []) := by
    rw [← newLength]
    simp [splitSaturated]
  simp only [splitNew, ↓reduceIte, bind, Option.bind_some, List.getElem?_eq_getElem bound,
    sourceAt, sourceCheck, equationAt, bodyAt, bodyCheck, headCheck, nextRun]
  rfl

private theorem capture_total {data : NativeRecursorData} {program : SaturatedProgram data}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program) :
    data.indexOffset + program.instructions.length = program.equationBody.domains.length := by
  have spec := saturatedProgram_spec selected
  have run := spec.2.2.2.2.2.2.2.2.2.2.2.1
  have counts := (SaturatedCaptureState.run_counts run).1
  have prefixBound : data.indexOffset ≤ program.prefixArgs.length := by
    rw [spec.2.2.1, majorOffset]
    omega
  simp only [List.length_take, Nat.min_eq_left prefixBound] at counts
  exact counts.symm.trans spec.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The replay at the final capture count is literally the full equation
context. Its machine match is retained through this dependent reindexing. -/
structure NativeFullCaptureReplay
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses newValues : List VExpr) (argumentAvailable : Valuation)
    (required : Footprint) (state : SaturatedCaptureState) where
  available : Valuation
  plan : CapturePlan (program.equationBody.domains.map (·.instL program.levels)).reverse
  replay : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
    (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) argumentAvailable
    _ plan (nativeCaptureSubst witnesses) (List.range program.equationBody.domains.length) available
  matched : NativePlanMatches (nativeCaptureSubst newValues) plan state
  closed : available.AtomClosed
  resources : required.Available available

theorem NativeCaptureReplayResult.full
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {witnesses : List VExpr} {available : Valuation} {required : Footprint}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    (newValues : List VExpr) (newLength : newValues.length = program.prefixArgs.length)
    {state : SaturatedCaptureState}
    (runNew : SaturatedCaptureState.run ((newValues.drop data.indexOffset).take data.numIndices)
      program.instructions { added := [], captures := newValues.take data.indexOffset } = some state)
    {bodyType : VExpr}
    (scope : (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) bodyType).Closed)
    (result : NativeCaptureReplayResult sourceEnv env U registry target program signature witnesses
      available program.instructions.length required) :
    Nonempty (NativeFullCaptureReplay sourceEnv env U registry target program signature witnesses
      newValues available required state) := by
  have matched := result.machineMatchRun selected newValues newLength runNew scope
  have package : Nonempty (Σ plan : CapturePlan
      ((program.equationBody.domains.take (data.indexOffset + program.instructions.length)).map
        (·.instL program.levels)).reverse,
      { replay : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
          (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) available
          _ plan (nativeCaptureSubst (witnesses.take (data.indexOffset + program.instructions.length)))
          (List.range (data.indexOffset + program.instructions.length)) result.available //
        NativePlanMatches (nativeCaptureSubst newValues) plan state }) :=
    ⟨⟨result.plan, result.replay, matched⟩⟩
  have total := capture_total selected
  rw [total, List.take_length] at package
  have takeWitnesses : witnesses.take program.equationBody.domains.length = witnesses := by
    rw [← witnessLength, List.take_length]
  rw [takeWitnesses] at package
  obtain ⟨⟨plan, replay, matched⟩⟩ := package
  exact ⟨⟨result.available, plan, by simpa only [witnessLength] using replay,
    matched, result.closed, result.resources⟩⟩

private theorem plan_added_length (plan : CapturePlan declared) (arguments : Subst) :
    (plan.added arguments).length = plan.count := by
  induction plan with
  | nil => rfl
  | index _ _ ih => exact ih
  | proof _ ih => exact congrArg (· + 1) ih

private theorem raised_expression (expression : VExpr) (captures : Subst) (count : Nat) :
    expression.subst (raisedSubst captures count) =
      (expression.subst captures).lift' (.skipN .refl count) := by
  have eq : captures.lift_r (.skipN .refl count) = raisedSubst captures count := by
    funext i
    exact lift'_consN_skipN (k := 0)
  rw [← eq, ← lift'_subst]

/-- Source certificate provenance remains at the actual equation template;
the semantic assigned type is the literal registered occurrence residual. -/
structure NativeTerminalRelatedResult (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses newValues : List VExpr) (demand : Profile n) where
  available : Valuation
  support : Profile n
  footprint : Footprint
  certificate : CodeCert env U registry target (List.range program.equationBody.domains.length)
    (nativeCaptureSubst witnesses) (program.equationBody.type.instL program.levels) support footprint
  resources : footprint.Available available
  typed : demand.HasType support
  typeCode : TypeRelated env U registry target
    (signature.result.subst (nativeCaptureSubst program.prefixArgs))
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) support
  witnessed : Related env U registry target
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support
  related : Related env U registry target
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support

/-- The actual machine and its supported replay close one side of the native
comparison. The literal original tuple equation is essential here; an arbitrary
raw argument equality is not used as a semantic type conversion. -/
theorem NativeFullCaptureReplay.terminalRelated
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
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
    (argumentFits : PairedFits env U registry signature.domains.reverse target
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
    (full : NativeFullCaptureReplay sourceEnv env U registry target program signature witnesses
      newValues argumentAvailable footprint next.state) :
    Nonempty (NativeTerminalRelatedResult env U registry target program signature witnesses newValues demand) := by
  have spec := saturatedProgram_spec selected
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have parsedRight := right
  have parsedFormation := formation
  rw [← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at parsedRight
  rw [← parts.2.2, instL_wrapForalls] at parsedFormation
  have oldLength : program.prefixArgs.length = signature.domains.length :=
    spec.2.2.1.trans (takeForalls_length signature.telescope).symm
  obtain ⟨supported⟩ := full.replay.declaredTerminalPairProtected henv hscoped hsource hle earlier
    hTarget newValues (by simpa using newLength.trans oldLength) rawArguments argumentFits full.closed
    parsedRight parsedFormation body full.resources
  obtain ⟨generated, paired, _⟩ := full.replay.canonicalPair henv hscoped hle earlier hTarget
    newValues (by simpa using newLength.trans oldLength) rawArguments argumentFits
  have opened := SaturatedProgram.openEquation_original (program := program) henv hscoped hle earlier registered selected levelsWF
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
    related := expanded }⟩

/-- Interpret the actual mutual native terminal's capture children. The only
semantic induction premise is the strict predecessor-stage theorem; machine
success, full capture correspondence, and raw native expansion are produced
inside this theorem. -/
theorem NativeCaptures.terminalRelated
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
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
    (argumentFits : PairedFits env U registry signature.domains.reverse target
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
    (resources : nativeFootprint.Available argumentAvailable) :
    Nonempty (NativeTerminalRelatedResult env U registry target program signature witnesses newValues demand) := by
  have spec := saturatedProgram_spec selected
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have parsedFormation := formation
  rw [← parts.2.2, instL_wrapForalls] at parsedFormation
  obtain ⟨replayed⟩ := captures.toSupport.toReplay signature selected witnessPrefix
    ⟨level, parsedFormation⟩ parsedFormation.sourcePiFormation.1 closed resources
  have scope := parsedFormation.defeq.closedN hsource (by trivial)
  obtain ⟨next, nextSelected, nextLevels, _, nextTrailing, _, nextBody, _, run⟩ :=
    SaturatedProgram.reapply selected newValues newLength
  obtain ⟨full⟩ := replayed.full selected witnessLength newValues newLength run scope
  exact full.terminalRelated henv hscoped hsource hle earlier hTarget registered lookup notDefinition
    selected levelsWF literal newLength nextSelected nextLevels nextBody nextTrailing
    rawArguments argumentFits left right formation body

structure NativeTerminalPairResult (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses newValues : List VExpr) (demand : Profile n)
    extends NativeTerminalRelatedResult env U registry target program signature witnesses newValues demand where
  nativeRelated : Related env U registry target
    (mkApps (.const data.name program.levels) program.prefixArgs)
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support

/-- Both saturated heads are interpreted at the original registered residual.
Each actual machine gets its own supported proof front; closed semantic
transitivity joins the two comparisons through the witnessed original RHS. -/
theorem NativeCaptures.terminalPair
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
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
    (argumentFits : PairedFits env U registry signature.domains.reverse target
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
    (resources : nativeFootprint.Available argumentAvailable) :
    Nonempty (NativeTerminalPairResult env U registry target program signature witnesses newValues demand) := by
  obtain ⟨next⟩ := captures.terminalRelated henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition selected levelsWF witnessLength witnessPrefix literal newLength
    rawArguments argumentFits closed left right formation body resources
  obtain ⟨original⟩ := captures.terminalRelated henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition selected levelsWF witnessLength witnessPrefix literal rfl
    rawArguments.left argumentFits.left closed left right formation body resources
  exact ⟨{ next with nativeRelated :=
    (original.related.symm henv).trans henv hscoped next.related }⟩

end Lean4Lean.AnchoredSource.Adapted
