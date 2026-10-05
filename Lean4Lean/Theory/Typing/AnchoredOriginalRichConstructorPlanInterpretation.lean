import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorTerminalInterpretation

/-! Native constructor plans retain every original domain and result occurrence.
The sole original result call is paid by the enclosing constant's header reserve;
future binders preserve its exact original context environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem RichConstructorPlan.supported
    {info : VConstant} {header : EndpointRef headerEnv U [] (info.type.instL levels) (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldAssigned}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {signature : ConstantTelescope (info.type.instL levels)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : headerEnv.Ordered) (capturedOrdered : sourceEnv.Ordered)
    (headerBelow : headerEnv ≤ env) (capturedBelow : sourceEnv ≤ env)
    (bank : OriginalLowerCallBank env U registry limit)
    (headerBound : richSchedule .fundamental (Closure.close (header.dependencyOrigin ordered) []).cost < limit)
    (lookup : env.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {target arguments headerSource} {context : ContextDerivation headerEnv U headerSource}
    {σ τ : Subst} {demand support : Profile n} {footprint available}
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint)
    (formed : OnCtx target (env.IsType U)) (bound : arguments.length ≤ signature.domains.length)
    (sourceEq : headerSource = (signature.domains.take arguments.length).reverse)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context (List.range arguments.length) σ τ available)
    (exactEnvironment : frame.dependencyEnvironment ordered capturedOrdered [] = context.dependencyClosures ordered)
    (resources : footprint.Available available) (typed : demand.HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) support) :
    Related env U registry target (mkApps (.const name levels) (realizedCaptures arguments.length σ))
      (mkApps (.const name levels) (realizedCaptures arguments.length τ))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) demand support := by
  match n, demand, footprint, plan with
  | _ + 1, _, _, .terminal saturated resultShape relevant resultNode resultLocation resultLineage captures resultCode =>
    have fullSource : headerSource = signature.domains.reverse := by
      simpa only [saturated, List.take_length] using sourceEq
    have cost := frame.constructorResult_cost_le ordered capturedOrdered resultLocation resultLineage exactEnvironment
    have scheduled : richSchedule .fundamental
        (Closure.close (resultNode.dependencyOrigin ordered)
          ((OriginalRichFrame.header capturedOrdered [] frame).dependencyEnvironment ordered)).cost < limit := by
      change richSchedule .fundamental
        (Closure.close (resultNode.dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered capturedOrdered [])).cost < limit
      unfold richSchedule at *
      omega
    rw [saturated, List.drop_length] at code ⊢
    simp only [wrapForalls, List.foldr_nil] at code ⊢
    have frameAmbient : (OriginalRichFrame.header capturedOrdered [] frame).Ambient := by
      change (RawOriginalRichFrame.header capturedOrdered [] frame).Ambient
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨headerBelow, capturedBelow⟩
    have terminal := richConstructorTerminal (arguments := arguments) (context := context) resultLocation resultLineage fullSource henv hscoped ordered headerBelow capturedOrdered [] bank
      lookup levelsWF levelCount ⟨notDefinition, notNative, Or.inr notQuotient⟩ resultShape saturated
      captures resultCode formed closed substitutions frame
      frameAmbient
      scheduled resources typed code
    simpa only [saturated] using terminal
  | _ + 1, _, _, .terminalRecord registered projectionLookup constructorName bounded saturated
      resultShape resultNode resultLocation resultLineage captures resultCode origins =>
    have fullSource : headerSource = signature.domains.reverse := by
      simpa only [saturated, List.take_length] using sourceEq
    rw [saturated, List.drop_length] at code ⊢
    simp only [wrapForalls, List.foldr_nil] at code ⊢
    cases constructorName
    have terminal := richRecordTerminalFromOrigins (arguments := arguments) (context := context)
      fullSource resultNode henv hscoped headerBelow registered projectionLookup
      lookup levelsWF levelCount ⟨notDefinition, notNative, Or.inr notQuotient⟩ bounded
      resultShape saturated captures formed substitutions frame
      (fun i need member => resources i need (List.mem_append_left _ member)) origins typed code
    simpa only [saturated] using terminal
  | _ + 1, _, _, .binder origin original location lineage domainCode guard body pack covered =>
    apply RichConstructorPlanSupported.binder henv hscoped headerBelow ordered capturedOrdered
      (fun child formed bound sourceEq closed substitutions frame exactEnvironment resources typed code =>
        child.supported henv hscoped ordered capturedOrdered headerBelow capturedBelow bank headerBound
          lookup levelsWF levelCount notDefinition notNative notQuotient
          formed bound sourceEq closed substitutions frame exactEnvironment resources typed code)
      origin original location lineage domainCode guard body pack covered formed sourceEq closed
      substitutions frame exactEnvironment resources typed code
  | _, _, _, .view child change =>
    have inverse := change.inverse henv
    have before := child.supported henv hscoped ordered capturedOrdered headerBelow capturedBelow bank headerBound
      lookup levelsWF levelCount notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame exactEnvironment resources
      (inverse.mapType_typed typed) (inverse.codeMap henv hscoped code)
    exact (change.termMap henv hscoped formed before).retag henv typed code
  | _ + 1, _, _, .pad child =>
    have before := child.supported henv hscoped ordered capturedOrdered headerBelow capturedBelow bank headerBound
      lookup levelsWF levelCount notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame exactEnvironment resources typed.pad_inv (code.down henv)
    exact (before.pad henv).retag henv typed code
termination_by (n, sizeOf plan)
decreasing_by all_goals simp_wf; omega

theorem RichConstructorPlan.bareSupported
    {info : VConstant} {header : EndpointRef headerEnv U [] (info.type.instL levels) (.sort headerLevel)}
    {signature : ConstantTelescope (info.type.instL levels)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : headerEnv.Ordered) (headerBelow : headerEnv ≤ env)
    (bank : OriginalLowerCallBank env U registry limit)
    (headerBound : richSchedule .fundamental (Closure.close (header.dependencyOrigin ordered) []).cost < limit)
    (lookup : env.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (typeClosed : info.type.Closed) (formed : OnCtx target (env.IsType U))
    (plan : RichConstructorPlan env U registry target header name levels signature .nil σ [] demand [])
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target (info.type.instL levels) (info.type.instL levels) support) :
    Related env U registry target (.const name levels) (.const name levels) (info.type.instL levels) demand support := by
  have residual : (wrapForalls (signature.domains.drop 0) signature.result).subst σ = info.type.instL levels := by
    rw [List.drop_zero, ← signature.type_eq]
    exact typeClosed.instL.subst_eq .zero
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have result := plan.supported (field := header) (major := header) henv hscoped ordered ordered
    headerBelow headerBelow bank headerBound lookup levelsWF levelCount
    notDefinition notNative notQuotient formed (Nat.zero_le _) rfl emptyClosed
    (τ := σ) .nil (.captured .nil) rfl (by intro _ _ member; cases member) typed
    (by simpa only [List.length_nil, residual] using code)
  simpa only [realizedCaptures, constantCaptureVariables, List.length_nil, List.range_zero,
    List.reverse_nil, List.map_nil, mkApps, List.foldl_nil, residual] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
