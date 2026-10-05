import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNestedConstantReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedConstantPruning
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationExecution
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels

/-! A closed, genuinely sort-typed source argument can return under the saved
canonical owner as actual code. The certificate is the selected source reply;
its inner charges are retained. This does not assert that an arbitrary
application argument has such an original or that open terms can be closed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem RichRecipeContext.returnClosedCodeWorld
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target callerSource callerLocals callerLeft
      callerExpression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    {caller : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (controls : OriginalWorldControls input.strata callerEnv)
    (baseline : WorldEnvironmentProvenance input.strata U environment)
    (frontier : List (World input.strata.rules.length))
    (callerReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := caller) recipe)))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (source : EndpointState input.owner.selected.origin.source U [] sourceExpression (.sort level))
    (provenance : EndpointProvenance .nil source)
    (closed : sourceExpression.Closed)
    (equal : EqUpToLevels U sourceExpression expression)
    (certificate : RichCert input.owner.selected.origin.source env U registry target
      source [] realization codeRelevant requested used)
    (resources : used.Available (fun _ => []))
    (sourceReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.certificate certificate))
    (destination : EndpointState destinationEnv U destinationSource expression destinationAssigned)
    (locals : List Nat) (σ : Subst) :
    ∃ next : RichCert destinationEnv env U registry target destination locals σ codeRelevant requested [],
    ∃ ready : ControlledStoredQuery controls frontier (.certificate next),
      ready.annotation.worlds =
        (WorldQuerySite.empty (registry := registry) (target := target)
          (canonicalQueryControls input.owner.selected
            (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
          provenance realization).worlds ++ sourceReady.annotation.worlds := by
  let childControls := canonicalQueryControls input.owner.selected
    (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
  let next : RichCert destinationEnv env U registry target destination locals σ codeRelevant requested [] :=
    .recipe (.root destinationSource locals σ input.owner source closed equal realization certificate resources)
  let annotation : WorldCertProvenance input.strata next :=
    .recipe (.root destinationSource locals σ input.owner source closed equal realization certificate resources
      sourceReady.annotation childControls provenance)
  have bounded : WithinAbove controls.cutoff controls.fuel
      (headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have original := callerReady.within control active
    simp only [StoredOriginalQuery.headDepth, RichCert.headDepth] at original
    have bound := Nat.le_trans (pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)) original
    simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCert.stratifiedDepth,
      RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, headDepth] using bound
  have sitePaid : Sponsored frontier
      (WorldQuerySite.empty (registry := registry) (target := target) childControls provenance realization).worlds := by
    intro world member
    change world ∈ [originalCallWorld childControls .fundamental source .nil] at member
    cases List.mem_singleton.mp member
    have lower : WorldBelow input.strata.rules.length
        (originalCallWorld childControls .fundamental source .nil)
        (originalCallWorld controls .fundamental caller baseline) := by
      apply Below.root
        (EquationStratifiedFuel.openingDecrease input.owner.selected.ordinal_pos input.owner.selected.ordinal_le
          controls.cutoffBound bounded controls.ordered.constantCount
          (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
          input.owner.selected.origin.ordered.constantCount
          (richSchedule .fundamental (Closure.close (source.dependencyOrigin input.owner.selected.origin.ordered) []).cost))
      intro value member
      cases member
    obtain ⟨sponsor, present, paid⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less input.strata.rules.length)
      EquationControlMeasure.less_trans lower paid⟩
  let ready : ControlledStoredQuery controls frontier (.certificate next) := {
    annotation := annotation
    within := by
      intro control active
      simp only [StoredOriginalQuery.headDepth, next, RichCert.headDepth, RichCodeRecipe.headDepth,
        stratifiedHeadPolicy, input.owner.headOrdinal_eq]
      exact EquationStratifiedFuel.rebuild input.owner.selected.ordinal_pos bounded sourceReady.within control active
    sponsored := sitePaid.merge sourceReady.sponsored }
  exact ⟨next, ready, rfl⟩


/-- Execute the actual source application's proper child Fs, then return its
constant function and genuinely closed type argument under the saved charge.
The source-sort equation and closedness are deliberate structural limits of
this pilot; they are not inferred from a sortable ambient observation. -/
theorem RichAppOrigin.closedArgumentApplicationWorld
    {argument A B : VExpr} {u v : VLevel}
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target callerSource callerLocals callerLeft
      callerExpression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    {caller : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (controls : OriginalWorldControls input.strata callerEnv)
    (baseline : WorldEnvironmentProvenance input.strata U environment)
    (frontier : List (World input.strata.rules.length))
    (callerReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := caller) recipe)))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    {root : EndpointRef input.owner.selected.origin.source U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target [] [] σ (.const name levels) argument)
    (sourceProvenance : EndpointProvenance .nil origin.node)
    (argumentSort : origin.A = .sort argumentLevel)
    (argumentClosed : argument.Closed)
    (sorted : origin.rawInput.HasType (.sort argumentRelevant))
    (sourceFrame : OriginalRichFrame input.owner.selected.origin.source env U registry target
      .nil [] σ τ (fun _ => []))
    (sourceCaptured : WorldEnvironmentProvenance input.strata U
      (sourceFrame.dependencyEnvironment input.owner.selected.origin.ordered))
    (sourceData : WorldUnaryFrameData P
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier sourceFrame sourceCaptured)
    (sourceSubstitutions : Ctx.SubstEq env U target σ τ [])
    (sourceResources : (origin.functionFootprint ++ origin.argumentFootprint).Available (fun _ => []))
    (functionReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.observation origin.function))
    (argumentReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.observation origin.argument))
    (sourceBelow : input.owner.selected.origin.source ≤ env)
    (sourcePaid : Sponsored frontier [originalCallWorld
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      .fundamental origin.node sourceCaptured])
    (sourceBank : WorldBoundedUnaryCallBank env U registry input.strata P
      (frontier ++ [originalCallWorld
        (canonicalQueryControls input.owner.selected
          (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
        .fundamental origin.node sourceCaptured]))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {callerFunction : EndpointState callerEnv U callerSource (.const name levels) (.forallE A B)}
    {callerArgument : EndpointState callerEnv U callerSource nextArgument A}
    (domain : EndpointState callerEnv U callerSource A (.sort u))
    (body : EndpointState callerEnv U (A :: callerSource) B (.sort v))
    (result : EndpointState callerEnv U callerSource (B.inst nextArgument) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (equal : EqUpToLevels U argument nextArgument)
    (callerClosed : callerAvailable.AtomClosed) :
    ∃ next : RichGradedResult callerEnv env U registry target
      (.app hu hv domain body callerFunction callerArgument result) callerLocals callerLeft callerAvailable
      (.singleton origin.output),
      Nonempty (ControlledStoredQuery controls frontier (.observation next.observation)) := by
  let sourceControls := canonicalQueryControls input.owner.selected
    (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
  have sourceClosed : Valuation.AtomClosed (fun _ => ([] : List Need)) := by
    intro index need member
    cases member
  obtain ⟨answer⟩ := origin.executeWorld (.done _) sourceProvenance sourceControls sourceFrame
    sourceCaptured frontier sourceData sourceClosed formed sourceSubstitutions sourceResources
    functionReady argumentReady henv hscoped sourceBelow sourcePaid sourceBank
  obtain ⟨constant, constantReady, _, _, _, _⟩ :=
    answer.functionValue.rightQuery.pruneConstantFunctionWorld answer.functionQuery henv
      (.ref (constantOriginAt input.owner origin.functionNode).site) [] input.realization (fun _ => [])
  obtain ⟨function, functionControlled, _, _, _⟩ := pending.returnConstantWorld
    controls baseline frontier callerReady callerPaid origin.functionNode constant constantReady
    callerFunction callerLocals callerLeft callerAvailable
  obtain ⟨used, certificate, certificateReady, resources, _⟩ :=
    answer.argumentValue.rightQuery.code_controlled henv sourceControls answer.argumentQuery sorted
  have argumentLive := answer.argumentValue.related.live henv hscoped formed
  have admission := answer.admitted
  rcases origin with ⟨oldA, oldB, oldU, oldV, oldHU, oldHV, oldDomain, oldBody,
    oldFunction, oldArgument, oldResult, oldLocation, rank, key, output,
    fnFootprint, argFootprint, fn, rawInput, arg, arguments, admitted⟩
  dsimp only at argumentSort
  subst oldA
  let argumentProvenance : EndpointProvenance .nil oldArgument := {
    rootSource := sourceProvenance.rootSource
    rootExpression := sourceProvenance.rootExpression
    rootType := sourceProvenance.rootType
    root := sourceProvenance.root
    initial := sourceProvenance.initial
    location := .appArgument sourceProvenance.location
    context_eq := sourceProvenance.context_eq }
  obtain ⟨returnedCode, returnedReady, _⟩ := pending.returnClosedCodeWorld
    controls baseline frontier callerReady callerPaid oldArgument argumentProvenance argumentClosed equal
    certificate resources certificateReady callerArgument callerLocals callerLeft
  let returnedArgument : RichGradedResult callerEnv env U registry target callerArgument
      callerLocals callerLeft callerAvailable rawInput := {
    rank := rank
    bound := Nat.le_refl _
    raw := rawInput
    footprint := []
    observation := .code returnedCode
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by intro _ _ member; cases member
    live := argumentLive }
  let returnedArgumentReady : ControlledStoredQuery controls frontier
      (.observation returnedArgument.observation) := {
    annotation := .code returnedReady.annotation
    within := by
      simpa only [returnedArgument, StoredOriginalQuery.headDepth, RichObs.headDepth] using returnedReady.within
    sponsored := returnedReady.sponsored }
  have nextClosed : nextArgument.Closed := equal.closedN_iff.mp argumentClosed
  have realized : EqUpToLevels U (argument.subst τ) (nextArgument.subst callerLeft) := by
    rw [argumentClosed.subst_eq Subst.Fixes.zero, nextClosed.subst_eq Subst.Fixes.zero]
    exact equal
  have admittedNext := admission.levels henv formed realized realized
  obtain ⟨next, ready, _, _, _⟩ := RichGradedResult.appControlled henv hscoped formed callerClosed
    domain body result hu hv function returnedArgument arguments admittedNext controls
    functionControlled returnedArgumentReady
  exact ⟨next, ⟨ready⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
