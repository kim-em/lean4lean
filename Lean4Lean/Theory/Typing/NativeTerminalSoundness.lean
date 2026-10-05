import Lean4Lean.Theory.Typing.NativeResultBridge
import Lean4Lean.Theory.Typing.AnchoredNativeRhsBeta
import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredBody
import Lean4Lean.Theory.Typing.AnchoredNativeCapturePlanSyntax

/-! Raw equality for the actual saturated native computation. Equation opening
uses original declared body typing; the registered residual is aligned by the
generated syntax bridge, not by comparing two typings. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredSemantics InductiveSignature NativeRecursorData
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
open private rebuild_spine from Lean4Lean.Theory.Inductive.CaseReductionData
set_option backward.isDefEq.respectTransparency false

private theorem eta_spine (n : Nat) (fn : VExpr) :
    nativeEtaBody n fn = mkApps (fn.liftN n) (vars n 0) := by
  induction n generalizing fn with
  | zero => simp [nativeEtaBody, vars, mkApps, liftN_zero]
  | succ n ih =>
    rw [nativeEtaBody, ih]
    have hv : vars (n+1) 0 = .bvar n :: vars n 0 := by
      simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, Nat.zero_add]
    rw [hv]
    simp only [lift, liftN, liftN_liftN, Nat.add_comm 1]
    rfl

private theorem capture_vars (arguments : List VExpr) :
    (vars arguments.length 0).map (·.subst (nativeCaptureSubst arguments)) = arguments := by
  apply List.ext_getElem
  · simp [vars]
  · intro i hi hi'
    have hj : arguments.length - 1 - i < arguments.length := by omega
    have he : arguments.length - 1 - (arguments.length - 1 - i) = i := by omega
    simp [vars, List.getElem_reverse, instantiateParams, subst, hj, he]

private theorem open_equality {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.Ordered) (domains : List VExpr)
    (equal : env.IsDefEq U Γ left right (wrapForalls domains result)) :
    env.IsDefEq U (domains.reverse ++ Γ) (nativeEtaBody domains.length left)
      (nativeEtaBody domains.length right) result := by
  induction domains generalizing Γ left right with
  | nil => exact equal
  | cons domain rest ih =>
    have next := IsDefEq.appDF (equal.weak henv (B := domain))
      (IsDefEq.bvar (Lookup.zero (Γ := Γ) (ty := domain)))
    simp only [lift, instN_bvar0] at next
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, nativeEtaBody] using ih next

private theorem trace_equality (trace : TypedBetaTrace env U Γ type left right) :
    env.IsDefEq U Γ left right type := by
  induction trace with
  | refl typed => exact typed
  | next _ equal _ ih => exact equal.trans ih

/-- Open a closed lambda equation once both original bodies have been
aligned with its declared result by the prior-stage producer. -/
theorem native_openEquation {env : VEnv} {U : Nat} (henv : env.Ordered)
    {domains : List VExpr} {lhs rhs result : VExpr}
    (context : OnCtx domains.reverse (env.IsType U))
    (leftTyped : env.HasType U domains.reverse lhs result)
    (rightTyped : env.HasType U domains.reverse rhs result)
    (equation : env.IsDefEq U [] (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains result)) :
    env.IsDefEq U domains.reverse lhs rhs result := by
  have leftTrace := TypedBetaTrace.nativeRhs (Γ := []) henv domains
    (by simpa only [List.append_nil] using context) (by simpa only [List.append_nil] using leftTyped)
  have rightTrace := TypedBetaTrace.nativeRhs (Γ := []) henv domains
    (by simpa only [List.append_nil] using context) (by simpa only [List.append_nil] using rightTyped)
  simpa only [List.append_nil] using
    (trace_equality leftTrace).symm.trans ((open_equality henv domains equation).trans
      (trace_equality rightTrace))

/-- Both declared body typings come from original earlier-stage lambda
payloads. No synthesized cast-body proof is recursively interpreted. -/
theorem native_openEquation_original
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {domains : List VExpr} {lhs rhs result : VExpr}
    (left : sourceEnv.HasTypeStrong U [] (wrapLams domains lhs) (wrapForalls domains result) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs) (wrapForalls domains result) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (equation : env.IsDefEq U [] (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains result)) :
    env.IsDefEq U domains.reverse lhs rhs result := by
  have context := (HasType.native_open henv (by trivial) (left.refl.defeq.mono hle)).1
  obtain ⟨_, _, _, _, leftTyped⟩ := HasTypeStrong.openDeclaredBody henv hscoped hle earlier left formation context
  obtain ⟨_, _, _, _, rightTyped⟩ := HasTypeStrong.openDeclaredBody henv hscoped hle earlier right formation context
  exact native_openEquation henv (by simpa only [List.append_nil] using context)
    (by simpa only [List.append_nil] using leftTyped)
    (by simpa only [List.append_nil] using rightTyped) equation

/-- A raw paired native argument telescope gives equality at the registered
residual and the corresponding result-type conversion. -/
theorem NativeConstantSignature.argumentsEqual
    {env : VEnv} {U : Nat} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (registered : NativeRecursorRegistered env data)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelLength : levels.length = data.uvars)
    {left right : List VExpr}
    (leftLength : left.length = signature.domains.length)
    (rightLength : right.length = signature.domains.length)
    (arguments : Ctx.SubstEq env U target (nativeCaptureSubst left)
      (nativeCaptureSubst right) signature.domains.reverse) :
    env.IsDefEq U target (mkApps (.const data.name levels) left)
      (mkApps (.const data.name levels) right)
      (signature.result.subst (nativeCaptureSubst left)) ∧
    TypeConversion env U target
      (signature.result.subst (nativeCaptureSubst left))
      (signature.result.subst (nativeCaptureSubst right)) := by
  have constant : env.HasType U [] (.const data.name levels)
      (wrapForalls signature.domains signature.result) := by
    rw [← telescope_eq signature.telescope]
    exact .const (registered.recursorType signature.typeOrigin) levelsWF levelLength
  obtain ⟨context, opened⟩ := HasType.native_open henv (by trivial) constant
  simp only [List.append_nil, eta_spine, liftN] at context opened
  have raw := opened.substDF henv context hTarget arguments
  simp only [subst_mkApps, subst_const, ← leftLength, capture_vars] at raw
  rw [leftLength, ← rightLength, capture_vars] at raw
  obtain ⟨u, formed⟩ := opened.isType henv context
  have result := formed.substDF henv context hTarget arguments
  exact ⟨raw, .single result⟩

private theorem selected_head
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments : List VExpr}
    (selected : data.saturatedProgram levels arguments = some program) :
    program.equationBody.lhs.getAppFnArgs.1 = .const data.name (VLevel.params data.uvars) := by
  unfold saturatedProgram at selected
  dsimp only at selected
  split at selected <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, _, major, _, source, _, selected⟩ := selected
  split at selected <;> try contradiction
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨equation, _, body, _, selected⟩ := selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  rename_i hhead
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨state, _, he⟩ := selected
  cases he
  simp only [Bool.or_eq_true, bne_iff_ne, not_or] at hhead
  exact Classical.not_not.mp hhead.1

/-- The equation's parsed native head is the actual registered constant,
including its universe packet. -/
theorem nativeEquationArguments_lhs
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments : List VExpr}
    (selected : data.saturatedProgram levels arguments = some program)
    (witnesses : List VExpr) :
    (program.equationBody.lhs.instL program.levels).subst (nativeCaptureSubst witnesses) =
      mkApps (.const data.name program.levels) (nativeEquationArguments program witnesses) := by
  have spec := saturatedProgram_spec selected
  have head : (program.equationBody.lhs.instL program.levels).getAppFnArgs.1 =
      .const data.name program.levels := by
    rw [getAppFnArgs_instL]
    change (program.equationBody.lhs.getAppFnArgs.1).instL program.levels = _
    rw [selected_head selected]
    simp only [instL, VLevel.params_map_inst program.levels ((congrArg List.length spec.1).trans spec.2.1)]
  have expression := (rebuild_spine (program.equationBody.lhs.instL program.levels)).symm
  rw [head] at expression
  rw [expression, subst_mkApps, subst_const]
  rfl

/-- The native argument alignment and captured equation give the actual
computation at the registered residual. The capture substitution may pair
the witnessed constructor fields with the machine's canonical fields. -/
theorem NativeConstantSignature.terminalEqual
    {env : VEnv} {U : Nat} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data} {arguments : List VExpr}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {actual witnesses canonical : List VExpr}
    (actualLength : actual.length = signature.domains.length)
    (alignment : Ctx.SubstEq env U target (nativeCaptureSubst actual)
      (nativeCaptureSubst (nativeEquationArguments program witnesses)) signature.domains.reverse)
    (captures : Ctx.SubstEq env U target (nativeCaptureSubst witnesses)
      (nativeCaptureSubst canonical) (program.equationBody.domains.map (·.instL program.levels)).reverse)
    (equation : env.IsDefEq U (program.equationBody.domains.map (·.instL program.levels)).reverse
      (program.equationBody.lhs.instL program.levels) (program.equationBody.rhs.instL program.levels)
      (program.equationBody.type.instL program.levels)) :
    env.IsDefEq U target (mkApps (.const data.name program.levels) actual)
      ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst canonical))
      (signature.result.subst (nativeCaptureSubst actual)) := by
  have length := (nativeEquationArguments_length (witnesses := witnesses) selected).trans
    (takeForalls_length signature.telescope).symm
  obtain ⟨nativeEqual, residual⟩ := signature.argumentsEqual henv hTarget registered levelsWF
    (saturatedProgram_spec selected).2.1 actualLength length alignment
  rw [signature.equationResult registered selected witnesses] at residual
  have substituted := equation.substDF henv captures.wf hTarget captures
  rw [nativeEquationArguments_lhs selected witnesses] at substituted
  exact nativeEqual.trans (residual.symm.cast substituted)

/-- Open the actual installed rule using the original predecessor-stage
typing of both closed endpoints. The rule and its parser are fixed by the
selected program; no additional equation premise is needed. -/
theorem SaturatedProgram.openEquation_original
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {data : NativeRecursorData} {program : SaturatedProgram data} {arguments : List VExpr}
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level)) :
    env.IsDefEq U (program.equationBody.domains.map (·.instL program.levels)).reverse
      (program.equationBody.lhs.instL program.levels) (program.equationBody.rhs.instL program.levels)
      (program.equationBody.type.instL program.levels) := by
  have spec := saturatedProgram_spec selected
  have selection := spec.2.2.2.2.2.2.2.2.1
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have equation : env.IsDefEq U [] (program.equation.lhs.instL program.levels)
      (program.equation.rhs.instL program.levels) (program.equation.type.instL program.levels) :=
    .extra (registered.singletonEquation selection) levelsWF
      (spec.2.1.trans (singletonEquation_uvars selection).symm)
  rw [← parts.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at left
  rw [← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at right
  rw [← parts.2.2, instL_wrapForalls] at formation
  rw [← parts.1, ← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapLams,
    instL_wrapForalls] at equation
  exact native_openEquation_original henv hscoped hle earlier left right formation equation

/-- Complete raw replay from the original installed equation evidence and
the actual paired argument/capture substitutions. Its type is precisely the
registered residual at the actual native occurrence. -/
theorem NativeConstantSignature.terminalEqual_original
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data} {arguments : List VExpr}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {actual witnesses canonical : List VExpr}
    (actualLength : actual.length = signature.domains.length)
    (alignment : Ctx.SubstEq env U target (nativeCaptureSubst actual)
      (nativeCaptureSubst (nativeEquationArguments program witnesses)) signature.domains.reverse)
    (captures : Ctx.SubstEq env U target (nativeCaptureSubst witnesses)
      (nativeCaptureSubst canonical) (program.equationBody.domains.map (·.instL program.levels)).reverse)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level)) :
    env.IsDefEq U target (mkApps (.const data.name program.levels) actual)
      ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst canonical))
      (signature.result.subst (nativeCaptureSubst actual)) :=
  signature.terminalEqual henv hTarget registered selected levelsWF actualLength alignment captures
    (SaturatedProgram.openEquation_original henv hscoped hle earlier registered selected levelsWF
      left right formation)

/-- Replace the plan substitution by the actual deterministic machine
captures. Equality beyond the finite declared telescope is not required. -/
theorem NativePlanMatches.pairedCaptures
    {env : VEnv} {U : Nat} {target declared : List VExpr}
    (henv : env.Ordered) {arguments witnessed : Subst}
    {plan : CapturePlan declared} {state : SaturatedCaptureState}
    (matched : NativePlanMatches arguments plan state)
    (captures : Ctx.SubstEq env U target witnessed (plan.captures arguments) declared) :
    Ctx.SubstEq env U target witnessed (nativeCaptureSubst state.captures) declared :=
  native_substEq_prefix henv captures (fun _ _ => rfl)
    (fun i hi => (matched.captures i hi).symm)

/-- Direct consumer of `machineMatch` or `machineMatchRun`: the raw paired
capture proof returned by canonical replay is enough to compute to the
machine's actual RHS, at the registered occurrence residual. -/
theorem NativeConstantSignature.terminalEqual_machine
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data} {arguments : List VExpr}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {actual witnesses : List VExpr}
    (actualLength : actual.length = signature.domains.length)
    (alignment : Ctx.SubstEq env U target (nativeCaptureSubst actual)
      (nativeCaptureSubst (nativeEquationArguments program witnesses)) signature.domains.reverse)
    {plan : CapturePlan (program.equationBody.domains.map (·.instL program.levels)).reverse}
    {planArguments : Subst} {state : SaturatedCaptureState}
    (matched : NativePlanMatches planArguments plan state)
    (captures : Ctx.SubstEq env U target (nativeCaptureSubst witnesses)
      (plan.captures planArguments) (program.equationBody.domains.map (·.instL program.levels)).reverse)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level)) :
    env.IsDefEq U target (mkApps (.const data.name program.levels) actual)
      (instantiateParams (program.equationBody.rhs.instL program.levels) state.captures)
      (signature.result.subst (nativeCaptureSubst actual)) :=
  signature.terminalEqual_original henv hscoped hle earlier hTarget registered selected levelsWF
    actualLength alignment (matched.pairedCaptures henv captures) left right formation

end Lean4Lean.AnchoredSource.Adapted
