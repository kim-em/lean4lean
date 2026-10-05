import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCaptureSpineReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalNativeEquationBodyOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQuerySiteReady

/-! The native terminal's query is interpreted at its actual open original
body occurrence. Its frame is produced by finite capture replay and its exact
cost is the original location cost, not an independently supplied budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private def castLocatedSource
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (same : source = source') :
    Located root (same ▸ node : EndpointState sourceEnv U source' expression assigned) := by
  cases same
  exact location

/-- Exact context-indexed extraction for the native parser's RHS. The
dependent transport preserves the selected original endpoint and path. -/
noncomputable def nativeRhsOccurrence
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {body : InductiveSignature.CaseSchema.EquationBody}
    (extracted : InductiveSignature.CaseSchema.EquationBody.extract
      rule.lhs rule.rhs rule.type = some body) :
    Σ assigned, Σ node : EndpointState origin.source U
      (body.domains.map (·.instL levels)).reverse (body.rhs.instL levels) assigned,
      Located (.left (EquationHeaderOrigin.instantiatedRhs origin levelsWF)) node := by
  let selected := EquationHeaderOrigin.nativeRhsBody origin levelsWF extracted
  have same : selected.context = (body.domains.map (·.instL levels)).reverse := by
    simpa only [List.append_nil] using selected.context_eq
  exact ⟨selected.type, same ▸ selected.endpoint, castLocatedSource selected.location same⟩

private theorem frame_ambient_mpr
    {context : ContextDerivation sourceEnv U source}
    (same : locals = locals')
    (types : OriginalRichFrame sourceEnv env U registry target context locals σ τ available =
      OriginalRichFrame sourceEnv env U registry target context locals' σ τ available)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals' σ τ available) :
    (types.mpr frame).Ambient ↔ frame.Ambient := by
  cases same
  rfl

theorem NativeCertificateSpine.frame_ambient
    (spine : NativeCertificateSpine env U registry target source σ τ available)
    (context : ContextDerivation sourceEnv U source) (below : sourceEnv ≤ env) :
    (spine.frame context).Ambient := by
  induction spine with
  | nil =>
    cases context
    rw [NativeCertificateSpine.frame.eq_1, OriginalRichFrame.Ambient,
      RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨below, trivial⟩
  | cons previous certificate resources typed arguments needs bounded covered ih =>
    cases context with
    | cons tail domain =>
      rw [NativeCertificateSpine.frame.eq_2]
      apply (frame_ambient_mpr (by
        simp only [List.length_cons, List.range_succ_eq_map]) _ _).mpr
      rw [OriginalRichFrame.Ambient, RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨below, ih tail⟩

theorem NativeSupportedReplay.originalFrame_ambient
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available)
    (context : ContextDerivation frameEnv U declared) (below : frameEnv ≤ env) :
    (NativeSupportedReplay.originalFrame henv formed argumentContext argumentsSpine replay context).Ambient := by
  unfold NativeSupportedReplay.originalFrame
  generalize NativeSupportedReplay.certificateSpine henv formed argumentContext argumentsSpine replay = retained
  rcases retained with ⟨spine, same⟩
  cases same
  exact spine.frame_ambient context below

noncomputable def NativeSupportedReplay.locatedOccurrence
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (ordered : frameEnv.Ordered)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    OriginalRichOccurrenceFrame location .nil env registry target locals captures captures available ordered [] := by
  refine {
    frame := NativeSupportedReplay.originalFrame henv formed argumentContext argumentsSpine replay
      (location.contextDerivation .nil)
    substitutions := NativeSupportedReplay.originalFrame_substitutions henv formed below argumentsSpine argumentsRaw replay
    environment_le := ?_ }
  rw [NativeSupportedReplay.originalFrame_environment,
    location.contextDerivation_dependencyClosures]
  exact Nat.le_refl _

theorem NativeSupportedReplay.locatedOccurrence_cost_le
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (ordered : frameEnv.Ordered)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    (Closure.close (node.dependencyOrigin ordered)
      ((NativeSupportedReplay.locatedOccurrence location ordered henv formed below argumentContext
        argumentsSpine argumentsRaw replay).frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (root.dependencyOrigin ordered) []).cost :=
  (NativeSupportedReplay.locatedOccurrence location ordered henv formed below argumentContext
    argumentsSpine argumentsRaw replay).cost_le

/-- Construct the site's exact location-derived world ledger using the
retained equation controls. This does not allocate a new sponsor. -/
noncomputable def NativeSupportedReplay.locatedSite
    {strata : EquationStratification env}
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata frameEnv)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    WorldQuerySite (registry := registry) (target := target) strata node locals captures := by
  let occurrence := NativeSupportedReplay.locatedOccurrence location controls.ordered henv formed below
    argumentContext argumentsSpine argumentsRaw replay
  have exactEnvironment : occurrence.frame.dependencyEnvironment controls.ordered =
      location.dependencyEnvironment controls.ordered [] := by
    change (NativeSupportedReplay.originalFrame henv formed argumentContext argumentsSpine replay
      (location.contextDerivation .nil)).dependencyEnvironment controls.ordered = _
    rw [NativeSupportedReplay.originalFrame_environment,
      location.contextDerivation_dependencyClosures]
    rfl
  exact occurrence.worldSite controls
    (exactEnvironment.symm ▸ WorldEnvironmentProvenance.located controls location .nil)

theorem NativeSupportedReplay.locatedSite_ready
    {strata : EquationStratification env}
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata frameEnv)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (frameBelow : frameEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available)
    (closed : available.AtomClosed)
    (body : Obs env U registry target locals captures expression profile footprint)
    (resources : footprint.Available available) :
    (NativeSupportedReplay.locatedSite location controls henv formed below argumentContext
      argumentsSpine argumentsRaw replay).Ready (RichObs.legacy (.legacy body)) := by
  exact ⟨frameBelow,
    NativeSupportedReplay.originalFrame_ambient henv formed argumentContext argumentsSpine replay
      (location.contextDerivation .nil) frameBelow,
    NativeSupportedReplay.originalFrame_substitutions henv formed below argumentsSpine argumentsRaw replay,
    closed, resources⟩

/-- The native terminal site is now computed from the retained original
equation itself. Neither its body node nor its source frame is a premise. -/
noncomputable def nativeTerminalSite
    {strata : EquationStratification env}
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {body : InductiveSignature.CaseSchema.EquationBody}
    (extracted : InductiveSignature.CaseSchema.EquationBody.extract
      rule.lhs rule.rhs rule.type = some body)
    (controls : OriginalWorldControls strata origin.source)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    {plan : CapturePlan (body.domains.map (·.instL levels)).reverse}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable
      (body.domains.map (·.instL levels)).reverse plan captures locals available) :
    WorldQuerySite (registry := registry) (target := target) strata
      (nativeRhsOccurrence origin levelsWF extracted).2.1 locals captures :=
  NativeSupportedReplay.locatedSite
    (nativeRhsOccurrence origin levelsWF extracted).2.2
    controls henv formed below argumentContext argumentsSpine argumentsRaw replay

theorem nativeTerminalSite_ready
    {strata : EquationStratification env}
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {body : InductiveSignature.CaseSchema.EquationBody}
    (extracted : InductiveSignature.CaseSchema.EquationBody.extract
      rule.lhs rule.rhs rule.type = some body)
    (controls : OriginalWorldControls strata origin.source)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    {plan : CapturePlan (body.domains.map (·.instL levels)).reverse}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable
      (body.domains.map (·.instL levels)).reverse plan captures locals available)
    (closed : available.AtomClosed)
    (query : Obs env U registry target locals captures (body.rhs.instL levels) profile footprint)
    (resources : footprint.Available available) :
    (nativeTerminalSite origin levelsWF extracted controls henv formed below argumentContext
      argumentsSpine argumentsRaw replay).Ready (RichObs.legacy (.legacy query)) :=
  NativeSupportedReplay.locatedSite_ready _ controls henv formed below origin.sourceBelow
    argumentContext argumentsSpine argumentsRaw replay closed query resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
